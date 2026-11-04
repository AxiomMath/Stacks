module

public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.RingTheory.Tor.Balancing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of Tor over a field

Every module over a field is flat, so all the higher Tor modules of two vector spaces vanish.
This is recorded for both Tor bifunctors on `ModuleCat`: `Tor`, which derives the second
variable, and `Tor'`, which derives the first.

## Main results

* `isZero_Tor_succ_of_field`: `Torₙ₊₁(M, N) = 0` for vector spaces `M` and `N` over a field.
* `isZero_Tor'_succ_of_field`: the same vanishing for `Tor'`.

## References

* [The Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Over a field all higher Tor modules vanish: `Torₙ₊₁(M, N) = 0`, because every module over
a field is flat. -/
@[ega "III 7.6.4" "special case"]
public theorem isZero_Tor_succ_of_field {k : Type u} [Field k] (M N : ModuleCat.{u} k) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} k) (n + 1)).obj M).obj N) :=
  isZero_Tor_succ_of_flat M N n

/-- Over a field all higher `Tor'` modules vanish: `Tor'ₙ₊₁(M, N) = 0`. This is the vanishing
of `Tor` transported along the balancing isomorphism. -/
public theorem isZero_Tor'_succ_of_field {k : Type u} [Field k] (M N : ModuleCat.{u} k) (n : ℕ) :
    IsZero (((Tor' (ModuleCat.{u} k) (n + 1)).obj M).obj N) :=
  IsZero.of_iso (isZero_Tor_succ_of_field M N n)
    (((Tor_iso_Tor' k (n + 1)).app M).app N).symm

/-- Over a field the first `Tor'` module of two vector spaces vanishes. -/
public theorem isZero_Tor'_one_of_field {k : Type u} [Field k] (M N : ModuleCat.{u} k) :
    IsZero (((Tor' (ModuleCat.{u} k) 1).obj M).obj N) :=
  isZero_Tor'_succ_of_field M N 0

end
