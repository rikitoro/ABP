import Lake
open Lake DSL

package "ABP" where
  version := v!"0.1.0"

@[default_target]
lean_lib «ABP» where
  -- add library configuration options here
