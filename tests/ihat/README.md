# VOLE-IHAT known-answer tests

To regenerate the test vectors, run the following commands from the root project
directory:

```sh
meson setup --reconfigure build
meson compile -C build gen_ihat_kat  # standard
./build/tests/gen_ihat_kat tests/ihat/ihat_kat.txt
meson test -C build ihat --print-errorlogs
meson compile -C build gen_unbound_ihat_kat  # unbound
./build/tests/gen_unbound_ihat_kat tests/ihat/unbound_ihat_kat.txt
meson test -C build unbound-ihat --print-errorlogs
```
