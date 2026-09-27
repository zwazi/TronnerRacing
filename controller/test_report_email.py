import io
import unittest
import urllib.error
from unittest import mock
from report_email import send_report_email


class ReportEmailTests(unittest.TestCase):
    def send(self):
        send_report_email("secret", "owner@example.com", "sender@example.com", "Report", "Details", "https://api.resend.com/emails", 10)

    def response(self):
        response = mock.MagicMock()
        response.__enter__.return_value = response
        response.getcode.return_value = 200
        response.read.return_value = b'{"id":"ack"}'
        return response

    @mock.patch("report_email.time.sleep")
    def test_transient_failure_retries_identical_payload_with_idempotency(self, sleep):
        error = urllib.error.HTTPError("url", 503, "Unavailable", {}, io.BytesIO(b""))
        with mock.patch("report_email.urllib.request.urlopen", side_effect=[error, self.response()]) as send:
            self.send()
        self.assertEqual(send.call_count, 2)
        first, second = [c.args[0] for c in send.call_args_list]
        self.assertEqual(first.data, second.data)
        self.assertEqual(first.headers["Idempotency-key"], second.headers["Idempotency-key"])
        self.assertTrue(first.headers["Idempotency-key"].startswith("tronner-report-"))
        self.assertLessEqual(send.call_args_list[1].kwargs["timeout"], 10)

    @mock.patch("report_email.time.sleep")
    def test_network_failures_have_bounded_attempts_and_safe_error(self, sleep):
        with mock.patch("report_email.urllib.request.urlopen", side_effect=urllib.error.URLError("secret")) as send:
            with self.assertRaisesRegex(RuntimeError, "could not be reached"):
                self.send()
        self.assertEqual(send.call_count, 3)

    def test_permanent_rejection_is_not_retried(self):
        error = urllib.error.HTTPError("url", 403, "Denied", {}, io.BytesIO(b""))
        with mock.patch("report_email.urllib.request.urlopen", side_effect=error) as send:
            with self.assertRaisesRegex(RuntimeError, "403"):
                self.send()
        self.assertEqual(send.call_count, 1)

    def test_rate_limit_longer_than_budget_is_not_retried(self):
        error = urllib.error.HTTPError("url", 429, "Busy", {"Retry-After":"30"}, io.BytesIO(b""))
        with mock.patch("report_email.urllib.request.urlopen", side_effect=error) as send:
            with self.assertRaisesRegex(RuntimeError, "429"):
                self.send()
        self.assertEqual(send.call_count, 1)
