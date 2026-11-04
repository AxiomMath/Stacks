module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.QuasiRegular
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.AffineRegular
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# A regular ideal sheaf is quasi-regular

A regular sheaf of ideals on a scheme is quasi-regular, and a regular immersion is a
quasi-regular immersion. No Noetherian or quasi-coherence hypothesis is needed.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegular_ofFn_of_isWeaklyRegular`: a weakly
  regular family in a commutative ring is quasi-regular.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegularIdealSheaf_of_isRegularIdealSheaf`: a
  regular ideal sheaf is quasi-regular.
* `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isRegularImmersion`: a regular immersion
  is a quasi-regular immersion.

## References

* [Stacks Project, Lemma 31.20.6 (Tag 063I)](https://stacks.math.columbia.edu/tag/063I)
* [Stacks Project, Lemma 31.20.3 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Lemma 15.30.2 (Tag 062F)](https://stacks.math.columbia.edu/tag/062F)
* [Stacks Project, Lemma 15.30.5 (Tag 062I)](https://stacks.math.columbia.edu/tag/062I)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

/-- A weakly regular family `f₁, …, f_r` in a commutative ring is quasi-regular. -/
theorem isQuasiRegular_ofFn_of_isWeaklyRegular {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (h : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) :
    RingTheory.Sequence.IsQuasiRegular R (List.ofFn f) :=
  Koszul.isQuasiRegular_of_isH1RegularOn
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1 h).isH1RegularOn

/-- A regular ideal sheaf on a scheme is quasi-regular. -/
theorem isQuasiRegularIdealSheaf_of_isRegularIdealSheaf (X : Scheme.{u})
    (J : (structureSheafModule X.toRingedSpace).Submodule)
    (h : IsRegularIdealSheaf X.toRingedSpace J) :
    IsQuasiRegularIdealSheaf X.toRingedSpace J :=
  (isQuasiRegularIdealSheaf_iff_exists_affine_generators X J).2 fun x hx ↦
    let ⟨U, hxU, r, f, hgen, hwr⟩ := (isRegularIdealSheaf_iff_exists_affine_generators X J).1 h x hx
    ⟨U, hxU, r, f, hgen, isQuasiRegular_ofFn_of_isWeaklyRegular f hwr⟩

end Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- A regular immersion of schemes is a quasi-regular immersion. -/
theorem isQuasiRegularImmersion_of_isRegularImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (h : IsRegularImmersion i) : IsQuasiRegularImmersion i :=
  RegularIdealSheaf.isQuasiRegularIdealSheaf_of_isRegularIdealSheaf
    i.coborderRange.toScheme (definingIdeal i) h

end Stacks.AlgebraicGeometry

end
