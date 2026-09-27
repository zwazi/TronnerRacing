# Report and suggestion email delivery

`/report` and `/suggest` use the configured Resend API directly, with credentials
outside the repository. No shell mail command or desktop mail application is
involved. The controller calls `report_email.send_report_email` in its existing
worker thread.

The helper retries connection failures, HTTP 429, and HTTP 5xx at most three
times within the configured timeout budget. It honors numeric Retry-After when
the delay fits within that budget. Authentication and other permanent errors do
not retry. All attempts use the same immutable email body and Resend idempotency
key. Success still requires a provider message ID before the player sees a
confirmation or their successful-send quota advances.

These are bounded in-process retries, not a persistent outbox. A prolonged
outage still returns the existing explicit failure message; the player can try
again. The provider's idempotency guarantee lasts 24 hours. The existing
cooldowns, monthly guard, sender, recipient, and report formatting are retained.

Validate with `python3 -m unittest test_report test_report_email` from controller/.
Deploy the helper beside TronnerRacing.py and gracefully reload tronner-racing.
Do not restart the game engine. When the production controller has unrelated
work, apply only the exact reviewed wrapper replacement to a copy of the current
production file; verify the expected original hash before installing it. Keep
the old controller as the rollback artifact. Restore that file and reload the
controller to roll back; the unused helper can remain harmlessly in place.
