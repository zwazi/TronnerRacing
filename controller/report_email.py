"""Bounded, idempotent delivery through the existing report email provider."""

import hashlib
import json
import time
import urllib.error
import urllib.request


def send_report_email(api_key, recipient, sender, subject, body, endpoint, timeout_seconds):
    payload = json.dumps({
        "from": sender, "to": [recipient], "subject": subject, "text": body,
    }, ensure_ascii=False).encode("utf-8")
    request = urllib.request.Request(endpoint, data=payload, headers={
        "Accept": "application/json",
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
        "User-Agent": "TronnerRacing/1.0",
        # The complete immutable email includes the report's timestamp and
        # authenticated identity. All retries of this report use the same key.
        "Idempotency-Key": "tronner-report-" + hashlib.sha256(payload).hexdigest(),
    }, method="POST")
    deadline = time.monotonic() + max(0.1, timeout_seconds)
    for attempt in range(3):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise RuntimeError("report service timed out")
        delay = 0.25 * (2 ** attempt)
        try:
            with urllib.request.urlopen(request, timeout=remaining) as response:
                status = response.getcode()
                response_body = response.read(16384)
        except urllib.error.HTTPError as error:
            status = error.code
            response_body = error.read(16384)
            retry_after = error.headers.get("Retry-After", "") if error.headers else ""
            try:
                delay = max(delay, float(retry_after))
            except ValueError:
                pass
        except (urllib.error.URLError, TimeoutError, OSError) as error:
            if attempt == 2 or deadline - time.monotonic() <= delay:
                raise RuntimeError("report service could not be reached") from error
            time.sleep(delay)
            continue
        if 200 <= status < 300:
            try:
                result = json.loads(response_body.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise RuntimeError("report service returned an invalid response") from error
            if not isinstance(result, dict) or not result.get("id"):
                raise RuntimeError("report service rejected the submission")
            return
        if (status != 429 and not 500 <= status < 600) or attempt == 2 or deadline - time.monotonic() <= delay:
            raise RuntimeError(f"report service returned HTTP {status}")
        time.sleep(delay)
