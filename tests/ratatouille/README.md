# Ratatouille known-answer tests

To regenerate the test vectors, run the following commands from the root project
directory:

```sh
meson setup --reconfigure build
meson compile -C build gen_ratatouille_kat
./build/tests/gen_ratatouille_kat tests/ratatouille/ratatouille_kat.txt
meson test -C build ratatouille --print-errorlogs
```
