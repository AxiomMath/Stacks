module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Classes

/-!
# Cohomological dimension one for a scheme covered by two affine opens

A scheme `X` that is the union of two affine opens `U` and `V` whose intersection is affine has
cohomological dimension at most one for quasi-coherent modules: `Hᵖ(X, ℱ) = 0` for every `p ≥ 2`
and every quasi-coherent `ℱ`.

This is the part of Mayer--Vietoris that needs no glueing hypothesis. A class in `Hᵖ(X, ℱ)` with
`p ≥ 2` restricts to zero on `U` and on `V` by Serre vanishing ([Stacks, Tag 01XB]), so it is the
connecting image of a class in `Hᵖ⁻¹(U ⊓ V, ℱ)`; and `p - 1 ≥ 1`, so that class vanishes by Serre
vanishing on the affine `U ⊓ V`. In degree one the argument stops short — there the connecting
class lives in `H⁰(U ⊓ V, ℱ)`, which is not zero, and a hypothesis is needed. That degree is the
subject of
`Stacks.AlmostBlowUp.isZero_hgroup_unit_of_two_affine_cover`
(`StacksFrontier/AlgebraicGeometry/Topologies/WeakNormalization/TwoGeneratorCohomology.lean`), which
covers all positive degrees for the structure sheaf at the price of assuming the degree-one
glueing. The statement here assumes nothing beyond the cover, and holds for every quasi-coherent
module, but only from degree two.

## Main results

* `Stacks.Cohomology.AmbientMayerVietoris.isZero_hgroup_of_two_affine_cover_of_two_le`

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01E0](https://stacks.math.columbia.edu/tag/01E0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology

universe u

namespace Stacks.Cohomology.AmbientMayerVietoris

/-- Every element of a positive-degree cohomology group of a quasi-coherent module on an affine
open is zero. -/
private theorem eq_zero_of_isAffineOpen (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (W : X.Opens) (hW : IsAffineOpen W) {n : ℕ} (hn : 0 < n)
    (x : Hgroup X.ringCatSheaf W n F) : x = 0 :=
  @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F W hW n hn)) _ _

/-- **Cohomological dimension at most one for a cover by two affine opens.** If a scheme `X` is
the union of two affine opens `U` and `V` whose intersection is affine, then `Hᵖ(X, ℱ) = 0` for
every quasi-coherent module `ℱ` and every `p ≥ 2`.

No glueing hypothesis is needed: Mayer--Vietoris presents a class of degree `p` restricting to
zero on `U` and on `V` as the connecting image of a class of degree `p - 1` on `U ⊓ V`, and for
`p ≥ 2` that degree is still positive, so Serre vanishing on the affine `U ⊓ V` kills it. -/
public theorem isZero_hgroup_of_two_affine_cover_of_two_le (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 2 ≤ p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 2 := ⟨p - 2, by omega⟩
  have hzero : ∀ x : (Hgroup X.ringCatSheaf ⊤ (q + 2) F : Type u), x = 0 := by
    intro x
    have hxU : Hrestrict X.ringCatSheaf (le_top (a := U)) (q + 2) F x = 0 :=
      eq_zero_of_isAffineOpen X F U hU (by omega) _
    have hxV : Hrestrict X.ringCatSheaf (le_top (a := V)) (q + 2) F x = 0 :=
      eq_zero_of_isAffineOpen X F V hV (by omega) _
    obtain ⟨θ, hθ⟩ := exists_ambientDelta_eq X.ringCatSheaf U V F ⊤ le_top le_top hcover
      (q + 1) x hxU hxV
    have hθ0 : θ = 0 :=
      eq_zero_of_isAffineOpen X F (U ⊓ V) hUV (by omega) _
    rw [← hθ, hθ0, map_zero]
  have : Subsingleton (Hgroup X.ringCatSheaf ⊤ (q + 2) F) :=
    ⟨fun a b => by rw [hzero a, hzero b]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

end Stacks.Cohomology.AmbientMayerVietoris

end
