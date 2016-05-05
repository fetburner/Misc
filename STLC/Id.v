Require Import FSets OrderedTypeEx.

Definition t := nat.

Module FSet := FSetList.Make (Nat_as_OT).
