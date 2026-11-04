module

public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Tor.BaseChangeOfUniverse

/-!
# Tor commutes with localization

Let `R` be a commutative ring, `S ⊆ R` a multiplicative subset and `A` a localization of `R` at
`S`. For `R`-modules `M` and `N` the canonical base-change map

`Tor_i^R(M, N) ⊗_R A → Tor_i^A(M ⊗_R A, N ⊗_R A)`

is an isomorphism.

## Main definitions

* `Stacks.Intersection.Diagonal.torLocalizationIso`: the base-change comparison
  `Tor_i^R(M, N) ⊗_R A ≅ Tor_i^A(M ⊗_R A, N ⊗_R A)` for a localization `A` of `R`.

## Main results

* `Stacks.Intersection.Diagonal.isIso_torBaseChangeIso_of_isLocalization`: the canonical
  comparison map itself is invertible.

## References

* [Stacks Project, Lemma 10.76.2 (Tag 00M8)](https://stacks.math.columbia.edu/tag/00M8)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 0B0U](https://stacks.math.columbia.edu/tag/0B0U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Intersection.Diagonal

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (S : Submonoid R)
  [IsLocalization S A]

/-- **Tor commutes with localization.** For a localization `A` of a commutative ring `R` at a
multiplicative subset `S` and `R`-modules `M`, `N`, the base change of `Tor_i^R(M, N)` to `A` is
`Tor_i^A` of the base changes. -/
noncomputable def torLocalizationIso (i : ℕ) (M N : ModuleCat.{u} R) :
    (torBaseChangeOfUniverse (S := R) (S' := A)).obj
        (((Tor (ModuleCat.{u} R) i).obj M).obj N) ≅
      ((Tor (ModuleCat.{u} A) i).obj
          ((torBaseChangeOfUniverse (S := R) (S' := A)).obj M)).obj
        ((torBaseChangeOfUniverse (S := R) (S' := A)).obj N) :=
  haveI : Module.Flat R A := IsLocalization.flat A S
  torBaseChangeIsoOfUniverse (S := R) (S' := A) i M N

/-- The canonical base-change comparison map `Tor_i^R(M, N) ⊗_R A → Tor_i^A(M ⊗_R A, N ⊗_R A)`
is invertible for a localization `A` of `R`. -/
theorem isIso_torBaseChangeIso_of_isLocalization (i : ℕ) (M N : ModuleCat.{u} R) :
    letI : Module.Flat R A := IsLocalization.flat A S
    IsIso (torBaseChangeIsoOfUniverse (S := R) (S' := A) i M N).hom :=
  have : Module.Flat R A := IsLocalization.flat A S
  flat_base_change_tor_of_universe A i M N

end Stacks.Intersection.Diagonal

end
