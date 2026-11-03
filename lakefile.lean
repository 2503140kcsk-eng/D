import Lake
open Lake DSL

package hakuiKoyoriNumber where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib HakuiKoyori
