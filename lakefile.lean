import Lake

open Lake DSL

package potkin3

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "378b908c009ef82cf9584cba7447c44a5a89e58a"

@[default_target]
lean_lib Potkin
