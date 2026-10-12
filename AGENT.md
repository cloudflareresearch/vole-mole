# Notes for agents

- Meson applies subproject patches (`subprojects/packagefiles/`) only on first download, and
  `meson.build` detects stale checkouts by hashing only the `.wrap`. When editing an existing patch,
  also change its wrap (e.g., rename the patch and update `diff_files`). To refresh a checkout:
  `meson subprojects update --reset <name>`.
