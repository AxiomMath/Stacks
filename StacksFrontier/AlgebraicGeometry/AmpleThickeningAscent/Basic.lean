module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.Limit
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningLimit.Basic
public import StacksFrontier.AlgebraicGeometry.ThickeningInvertible.Basic

/-!
# Stacks Tags 09MW and 0D2R, with nothing carried

[Stacks, Tag 09MW]: for a closed immersion `i : Z ⟶ X` inducing a homeomorphism of underlying
spaces and an invertible `𝒪_X`-module `𝓛`, `i^* 𝓛` is ample if and only if `𝓛` is.

[Stacks, Tag 0D2R]: for a morphism of thickenings `(f, f') : (X ⊆ X') → (S ⊆ S')` and an
invertible `𝒪_{X'}`-module `𝓛'` with restriction `𝓛` to `X`, `𝓛'` is `f'`-ample if and only if
`𝓛` is `f`-ample.

`StacksFrontier/AlgebraicGeometry/ThickeningInvertible/Basic.lean` proves Tag 0D2R granted the
hypothesis `Stacks.ThickeningInvertible.AmpleReflectedByThickening`, the hard implication of
Tag 09MW, and `StacksFrontier/AlgebraicGeometry/AmpleThickeningLimit/Basic.lean` proves that
implication only over a locally Noetherian base and granted a cohomological lift. Both are
discharged here by `Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isThickening`:
the square-zero case by an elementary Čech computation in local coordinates
(`StacksFrontier/AlgebraicGeometry/AmpleThickeningAscent/FirstOrder.lean`), the finite-order case by
the filtration by powers of the ideal sheaf, and the general case by the limit argument of the
source (`StacksFrontier/AlgebraicGeometry/AmpleThickeningAscent/Limit.lean`).

## Main results

* `Stacks.AmpleThickeningAscent.ampleReflectedByThickening`: the hypothesis
  `Stacks.ThickeningInvertible.AmpleReflectedByThickening`, proved.
* `Stacks.AmpleThickeningAscent.isAmple_modulePullback_iff`: **[Stacks, Tag 09MW].**
* `Stacks.AmpleThickeningAscent.isRelativelyAmple_iff`: **[Stacks, Tag 0D2R].**

## References

* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 0D2R](https://stacks.math.columbia.edu/tag/0D2R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.Thickenings
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.RelativeAmple (IsRelativelyAmple)

universe u

namespace Stacks.AmpleThickeningAscent

/-- **The implication `k^* M` ample `⟹` `M` ample of [Stacks, Tag 09MW], for every thickening**:
the hypothesis `Stacks.ThickeningInvertible.AmpleReflectedByThickening`, proved. -/
theorem ampleReflectedByThickening : Stacks.ThickeningInvertible.AmpleReflectedByThickening.{u} :=
  fun _ _ _ M _ hk h => isAmple_of_isAmple_pullback_of_isThickening hk M h

/-- **[Stacks, Tag 09MW].** Let `i : Z ⟶ X` be a closed immersion of schemes inducing a
homeomorphism of underlying topological spaces, and `𝓛` an invertible `𝒪_X`-module. Then `i^* 𝓛`
is ample on `Z` if and only if `𝓛` is ample on `X`. No Noetherian hypothesis.

The implication `𝓛` ample `⟹` `i^* 𝓛` ample is
`Stacks.AmpleThickeningLimit.isAmple_modulePullback`; the converse is
`Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isThickening`. -/
@[stacks 09MW]
theorem isAmple_modulePullback_iff {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : IsHomeomorph i.base) (L : X.Modules) [IsInvertibleModule X L] :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  ⟨isAmple_of_isAmple_pullback_of_isThickening ⟨inferInstance, hi.surjective⟩ L,
    Stacks.AmpleThickeningLimit.isAmple_modulePullback i L hi⟩

/-- **[Stacks, Tag 0D2R].** Let `(f, f') : (X ⊆ X') → (S ⊆ S')` be a morphism of thickenings —
a commutative square `i ≫ f' = f ≫ j` in which `i : X ⟶ X'` and `j : S ⟶ S'` are thickenings —
and let `𝓛'` be an invertible `𝒪_{X'}`-module, with restriction `𝓛 = i^* 𝓛'` to `X`. Then `𝓛'`
is `f'`-ample if and only if `𝓛` is `f`-ample.

This is `Stacks.ThickeningInvertible.isRelativelyAmple_iff` with its hypothesis
`Stacks.ThickeningInvertible.AmpleReflectedByThickening` discharged by
`Stacks.AmpleThickeningAscent.ampleReflectedByThickening`. -/
@[stacks 0D2R]
theorem isRelativelyAmple_iff {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'} {f : X ⟶ S}
    {f' : X' ⟶ S'} (hi : IsThickening i) (hj : IsThickening j) (hsq : i ≫ f' = f ≫ j)
    (L' : X'.Modules) [IsInvertibleModule X' L'] :
    IsRelativelyAmple f' L' ↔ IsRelativelyAmple f (pullbackModule i L') :=
  Stacks.ThickeningInvertible.isRelativelyAmple_iff L' ampleReflectedByThickening hi hj hsq

end Stacks.AmpleThickeningAscent

end
