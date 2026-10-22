# Moussaka known-answer tests

To regenerate the test vectors, run the following commands from the root project
directory:

```sh
meson setup --reconfigure build
meson compile -C build gen_moussaka_kat  # standard
./build/tests/gen_moussaka_kat tests/moussaka/moussaka_kat.txt
meson test -C build moussaka --print-errorlogs
meson compile -C build gen_unbound_moussaka_kat  # unbound
./build/tests/gen_unbound_moussaka_kat tests/moussaka/unbound_moussaka_kat.txt
meson test -C build unbound-moussaka --print-errorlogs
```
