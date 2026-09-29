# Anonymous submission export

`make_anonymous_submission.py` creates a separate double-blind artifact.  It
does not edit the provenance-preserving source bundle.

```bash
python3 make_anonymous_submission.py \
  --output /path/to/ideal_forest_fixed_accuracy_anonymous \
  --archive /path/to/ideal_forest_fixed_accuracy_anonymous.zip
```

The archive format is selected from its suffix.  Submission ZIP files are the
recommended output; deterministic `.tar.gz` and `.tgz` output remains available
for compatibility.

Use repeated `--extra-token` options for collaborator, institution, machine,
or private-repository names not already represented by the local username or
home directory:

```bash
python3 make_anonymous_submission.py \
  --output /path/to/anonymous_artifact \
  --archive /path/to/anonymous_artifact.zip \
  --extra-token "Private Lab Name" \
  --extra-token "private-host"
```

The exporter:

- omits Git history, full rerun provenance, machine logs, environment records,
  compiled caches, and local export tooling;
- redacts Unix and Windows home directories, local/cluster hostnames, email
  addresses, repository URLs, the current username, and additional tokens;
- replaces every contiguous Japanese-text run in file contents with
  `REDACTED`, and anonymizes any Japanese filename component;
- always redacts and hard-fail scans the two explicitly requested personal
  tokens, regardless of the account running the exporter;
- retains experiment code, canonical/fresh result records, figures, and the
  fresh-reproduction entry point;
- writes new `SHA256SUMS`, `SOURCE_MANIFEST.json`, and
  `ANONYMIZATION_REPORT.json` files for the transformed artifact;
- fails if the final directory still contains a recognized identity leak; and
- writes deterministic archive metadata: ZIP entries use the fixed DOS epoch,
  relative paths, no comment, and normalized modes; tar entries use
  `uid=gid=0`, anonymous owner/group, and `mtime=0`.

Before uploading, extract the archive into a fresh directory and run:

```bash
shasum -a 256 -c SHA256SUMS
```

Do not submit the working repository or its `.git` directory; upload only the
generated `.zip` artifact.
