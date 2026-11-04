module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.PolynomialSurjection
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.AffineBaseChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A relative `Proj` over an affine base is a closed subscheme of a projective space

Let `s` be a relative `Proj` situation whose base has affine top open, whose graded algebra is
generated in degree one over `⊤`, whose degree-zero identification at `⊤` is an isomorphism, and
whose degree-one global sections are spanned by finitely many of them. This file produces the
graded ring homomorphism

`Γ(S, ⊤)[T₀, …, T_d] ⟶ Γ(S, ⊤, s)`

sending the variables to those spanning sections and the coefficients through the degree-zero
identification. It is surjective in every degree, so [Stacks, Tag 01N0] makes the induced
morphism of absolute `Proj`s a closed immersion, and the degree-one twists correspond.

## Main definitions

* `Stacks.RelativeProj.Situation.topGens`: the spanning family, indexed by `Fin (d + 1)`.
* `Stacks.RelativeProj.Situation.topPolyHom`: the graded ring homomorphism above.
* `Stacks.RelativeProj.Situation.topProjHom`: the induced morphism
  `Proj Γ(S, ⊤, s) ⟶ Proj Γ(S, ⊤)[T₀, …, T_d]`.

## Main results

* `Stacks.RelativeProj.Situation.surjective_topPolyHom`: the homomorphism is surjective.
* `Stacks.RelativeProj.Situation.isClosedImmersion_topProjHom`: **the induced morphism is a closed
  immersion.**
* `Stacks.RelativeProj.Situation.nonempty_pullback_topProjHom_twistingSheaf`: **the degree-`n`
  twist pulls back to the degree-`n` twist.**
* `Stacks.RelativeProj.Situation.topProjHom_comp_projToSpecCoeff`: **the closed immersion is a
  morphism over the base**, which is the clause the degree-zero computation is for.

## Implementation notes

The coefficient ring is `Γ(S, ⊤)` rather than the degree-zero part of the section ring, so that
the target of the morphism is a projective space over the base itself and the structure morphism
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff` is the one over `Spec Γ(S, ⊤)`. The
homomorphism is therefore the composite of coefficient change along
`Stacks.RelativeProj.Situation.sectionRingZeroMap` with the evaluation map
`Stacks.AlgebraicGeometry.RelativeProjChain.polyGradedHom` over the degree-zero part; its
degree-zero component is the degree-zero identification itself, which is exactly what the
over-the-base clause needs.

The index type is `Fin (g.card + 1)` and not `Fin g.card`: a projective space in this library has
at least one homogeneous coordinate, and a redundant generator costs nothing because only the
inclusion of the spanning family in the range of the indexed family is used.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite DirectSum
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.RelativeProjChain

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SetLike.GradeZero.instCommRing

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (g : Finset (s.sectionPieces ⊤ 1))

/-! ### The spanning family as an indexed family -/

/-- The spanning family of degree-one sections, read as a family indexed by `Fin (g.card + 1)`
with a redundant zero in the last place. -/
def topGens : Fin (g.card + 1) → s.sectionRing ⊤ := fun i =>
  if h : (i : ℕ) < g.card then
    DirectSum.of (s.sectionPieces ⊤) 1 ((g.equivFin.symm ⟨(i : ℕ), h⟩ : s.sectionPieces ⊤ 1))
  else 0

/-- Every member of the family is homogeneous of degree one. -/
theorem topGens_mem (i : Fin (g.card + 1)) : topGens s g i ∈ s.sectionRingGrading ⊤ 1 := by
  rw [topGens]
  split_ifs with h
  · exact ⟨_, rfl⟩
  · exact zero_mem _

/-- The image of the spanning family lies in the range of the indexed family. -/
theorem image_of_one_subset_range_topGens :
    (fun x : s.sectionPieces ⊤ 1 => DirectSum.of (s.sectionPieces ⊤) 1 x) ''
        (g : Set (s.sectionPieces ⊤ 1)) ⊆ Set.range (topGens s g) := by
  rintro z ⟨y, hy, rfl⟩
  refine ⟨⟨((g.equivFin ⟨y, hy⟩ : Fin g.card) : ℕ), by omega⟩, ?_⟩
  have hlt : (((g.equivFin ⟨y, hy⟩ : Fin g.card) : ℕ)) < g.card :=
    (g.equivFin ⟨y, hy⟩).2
  rw [topGens, dite_eq_left hlt]
  congr 1
  rw [show (⟨(((g.equivFin ⟨y, hy⟩ : Fin g.card) : ℕ)), hlt⟩ : Fin g.card) =
    g.equivFin ⟨y, hy⟩ from Fin.ext rfl, Equiv.symm_apply_apply]

/-- **The indexed family generates the section ring over its degree-zero part.** -/
theorem adjoin_range_topGens_eq_top (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
    (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
      (g : Set (s.sectionPieces ⊤ 1)) = ⊤) :
    Algebra.adjoin (s.sectionRingGrading ⊤ 0) (Set.range (topGens s g)) = ⊤ :=
  top_unique (le_of_eq_of_le (adjoin_image_of_one_eq_top s ⊤ hgen g hg).symm
    (Algebra.adjoin_mono (image_of_one_subset_range_topGens s g)))

/-! ### The graded presentation over the sections of the base -/

/-- **The graded ring homomorphism `Γ(S, ⊤)[T₀, …, T_d] ⟶ Γ(S, ⊤, s)`** sending the variables to
the spanning family and the coefficients through the degree-zero identification. -/
def topPolyHom : polyGrading ↥Γ(s.base, ⊤) g.card →+*ᵍ s.sectionRingGrading ⊤ :=
  (polyGradedHom (s.sectionRingGrading ⊤) (R := ↥(s.sectionRingGrading ⊤ 0))
      (fun r => r.2) (topGens s g) (topGens_mem s g)).comp
    (coeffGradedHom ↥Γ(s.base, ⊤) g.card (sectionRingZeroMap s ⊤).hom)

/-- **The presentation is surjective.** Coefficient change along a surjection is surjective, and
the evaluation map is surjective because the family generates. -/
theorem surjective_topPolyHom (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
    (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
      (g : Set (s.sectionPieces ⊤ 1)) = ⊤)
    (hzero : Function.Surjective (sectionRingZeroMap s ⊤).hom) :
    Function.Surjective (topPolyHom s g :
      MvPolynomial (Fin (g.card + 1)) ↥Γ(s.base, ⊤) → s.sectionRing ⊤) := by
  have h1 : Function.Surjective
      (MvPolynomial.aeval (R := ↥(s.sectionRingGrading ⊤ 0)) (topGens s g)) := by
    intro z
    have hmem : z ∈ (MvPolynomial.aeval (R := ↥(s.sectionRingGrading ⊤ 0))
        (topGens s g)).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, adjoin_range_topGens_eq_top s g hgen hg]
      trivial
    exact hmem
  exact h1.comp (MvPolynomial.map_surjective (sectionRingZeroMap s ⊤).hom hzero)

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` at the presentation. -/
theorem irrelevant_le_map_topPolyHom (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
    (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
      (g : Set (s.sectionPieces ⊤ 1)) = ⊤)
    (hzero : Function.Surjective (sectionRingZeroMap s ⊤).hom) :
    HomogeneousIdeal.irrelevant (s.sectionRingGrading ⊤) ≤
      (HomogeneousIdeal.irrelevant (polyGrading ↥Γ(s.base, ⊤) g.card)).map (topPolyHom s g) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
    (surjective_topPolyHom s g hgen hg hzero)

/-- **The morphism `Proj Γ(S, ⊤, s) ⟶ Proj Γ(S, ⊤)[T₀, …, T_d]`** induced by the
presentation. -/
def topProjHom (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
    (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
      (g : Set (s.sectionPieces ⊤ 1)) = ⊤)
    (hzero : Function.Surjective (sectionRingZeroMap s ⊤).hom) :
    AlgebraicGeometry.Proj (s.sectionRingGrading ⊤) ⟶
      AlgebraicGeometry.Proj (polyGrading ↥Γ(s.base, ⊤) g.card) :=
  AlgebraicGeometry.Proj.map (topPolyHom s g) (irrelevant_le_map_topPolyHom s g hgen hg hzero)

/-- **The morphism is a closed immersion**, by [Stacks, Tag 01N0] part (2). -/
theorem isClosedImmersion_topProjHom (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
    (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
      (g : Set (s.sectionPieces ⊤ 1)) = ⊤)
    (hzero : Function.Surjective (sectionRingZeroMap s ⊤).hom) :
    IsClosedImmersion (topProjHom s g hgen hg hzero) :=
  AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective' _
    (surjective_topPolyHom s g hgen hg hzero)

/-- **The degree-`n` twist pulls back to the degree-`n` twist** along the closed immersion, by
[Stacks, Tag 01N1] part (3): the presentation is surjective and the polynomial ring is generated
in degree one. -/
theorem nonempty_pullback_topProjHom_twistingSheaf
    (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
    (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
      (g : Set (s.sectionPieces ⊤ 1)) = ⊤)
    (hzero : Function.Surjective (sectionRingZeroMap s ⊤).hom) (n : ℤ) :
    Nonempty ((Scheme.Modules.pullback (topProjHom s g hgen hg hzero)).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          (polyGrading ↥Γ(s.base, ⊤) g.card) n) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (s.sectionRingGrading ⊤) n) :=
  Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap _ _ (topPolyHom s g)
    (irrelevant_le_map_topPolyHom s g hgen hg hzero) (surjective_topPolyHom s g hgen hg hzero)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (g.card + 1)) _) n

/-- **The closed immersion is a morphism over `Spec Γ(S, ⊤)`.** Its degree-zero component is the
degree-zero identification `Stacks.RelativeProj.Situation.sectionRingZeroMap`: a constant
polynomial is carried by coefficient change to the constant with the transported coefficient, and
the evaluation map sends that to the coefficient itself. -/
@[ega "II 2.8.5" "ψ = identity of Γ(S"]
theorem topProjHom_comp_projToSpecCoeff (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
    (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
      (g : Set (s.sectionPieces ⊤ 1)) = ⊤)
    (hzero : Function.Surjective (sectionRingZeroMap s ⊤).hom) :
    topProjHom s g hgen hg hzero ≫ projToSpecCoeff ↥Γ(s.base, ⊤) g.card =
      AlgebraicGeometry.Proj.toSpecZero (s.sectionRingGrading ⊤) ≫
        Spec.map (sectionRingZeroMap s ⊤) := by
  have hring : CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' (polyGrading ↥Γ(s.base, ⊤) g.card)).comp
          (algebraMap ↥Γ(s.base, ⊤) (MvPolynomial (Fin (g.card + 1)) ↥Γ(s.base, ⊤)))) ≫
        CommRingCat.ofHom (topPolyHom s g).gradedZeroRingHom =
      sectionRingZeroMap s ⊤ := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    refine Subtype.ext ?_
    have hz : ((GradedRing.projZeroRingHom' (polyGrading ↥Γ(s.base, ⊤) g.card)
          (algebraMap ↥Γ(s.base, ⊤) (MvPolynomial (Fin (g.card + 1)) ↥Γ(s.base, ⊤)) r) :
          polyGrading ↥Γ(s.base, ⊤) g.card 0) :
        MvPolynomial (Fin (g.card + 1)) ↥Γ(s.base, ⊤)) =
        MvPolynomial.C r := by
      rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
        MvPolynomial.algebraMap_eq]
      exact DirectSum.decompose_of_mem_same _
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ r))
    change (topPolyHom s g
        ((GradedRing.projZeroRingHom' (polyGrading ↥Γ(s.base, ⊤) g.card)
          (algebraMap ↥Γ(s.base, ⊤) (MvPolynomial (Fin (g.card + 1)) ↥Γ(s.base, ⊤)) r) :
          polyGrading ↥Γ(s.base, ⊤) g.card 0) :
          MvPolynomial (Fin (g.card + 1)) ↥Γ(s.base, ⊤)) :
        s.sectionRing ⊤) = _
    rw [hz]
    change (MvPolynomial.aeval (R := ↥(s.sectionRingGrading ⊤ 0)) (topGens s g)
        (MvPolynomial.map (sectionRingZeroMap s ⊤).hom (MvPolynomial.C r)) :
        s.sectionRing ⊤) = _
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    rfl
  rw [topProjHom, projToSpecCoeff, AlgebraicGeometry.Proj.map_toSpecZero_assoc,
    ← Spec.map_comp, hring]

end Stacks.RelativeProj.Situation

end
