import Lake
open Lake DSL

package jsp437

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib JSP437 where
  globs := #[.andSubmodules `JSP437]
