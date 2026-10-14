# track

Status items for open work on molt-petit. Convention (from George's master session, 2026-10-14):

- `items/<NNNN>-<slug>.md`, one per piece of work over about an hour, and per experiment.
- Header fields: id, kind (task|experiment|finding|decision|question), status (open|active|blocked|done|dropped),
  title, owner (session, host), created, updated, needs_george ("" or one sentence),
  data (long-term storage URIs), commits (repo@sha). Body: free Markdown.
- Commit and push code at every milestone; results go to long-term storage, URI in `data`.
- Findings are written down as items, not only in chat.
- Blocked on George: set needs_george and status blocked.
- Push to `track` directly; no PRs.
