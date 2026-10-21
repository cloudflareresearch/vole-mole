# VOLE-ACT known-answer tests

To regenerate the test vectors, run the following commands from the root project
directory:

```sh
meson setup --reconfigure build
meson compile -C build gen_act_kat
./build/tests/gen_act_kat tests/act/act_kat.txt
meson test -C build act --print-errorlogs
```
