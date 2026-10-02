# Moussaka known-answer tests

To regenerate the test vectors, run the following commands from the root project
directory:

```sh
meson setup --reconfigure build
meson compile -C build gen_moussaka_kat
./build/tests/gen_moussaka_kat tests/moussaka/moussaka_kat.txt
meson test -C build moussaka --print-errorlogs
```
