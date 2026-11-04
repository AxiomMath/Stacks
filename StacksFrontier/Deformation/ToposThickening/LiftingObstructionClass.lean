module

public import StacksFrontier.Deformation.ToposThickening.LiftingObstructionSufficiency
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClassVanishing
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPresentationComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction class of Stacks 08UG on one site

Steps 1 to 3 of the proof of [Stacks Project, Tag 08UG] (in
`StacksFrontier/Deformation/ToposThickening/LiftingObstructionPresentation.lean`,
`LiftingObstructionFactorization.lean` and `LiftingObstructionSufficiency.lean`) attach to a
`Deformation.ToposThickening.FirstOrderLiftDiagram` the presentation
`α : ℰ = 𝒪'₁ ×_{𝒪₂} 𝒪'₂ ⟶ 𝒪₁` of the front reduced structure sheaf over its base, the
homomorphism `ξ : ℐ/ℐ² ⟶ g_*𝒢₂` out of the conormal sheaf of that presentation, and prove that a
lift of the diagram exists exactly when `ξ` factors through the differential
`ℐ/ℐ² ⟶ Ω = NL(α)⁰`.

This file closes the source's Step 2 ("`[ξ]` is zero if and only if `ξ` is a composition
`ℐ/ℐ² ⟶ Ω ⟶ 𝒢₂`") by taking the class `[ξ] ∈ Ext¹(NL(α), g_*𝒢₂)` and carrying it, along the
canonical isomorphism `NL(α) ≅ NL_{𝒪₁/𝒪_{ℬ₁}}` of [Stacks Project, Tag 08TY], to the
canonical naive cotangent complex. The result is the class of clause (1) of the lemma in the
one-site situation to which the source's proof reduces, with its vanishing criterion.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram.presentationObstructionClass`: the class
  `[ξ] ∈ Ext¹_{𝒪₁}(NL(α), g_*𝒢₂)` of Step 1.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.obstructionClass`: its image in
  `Ext¹_{𝒪₁}(NL_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)`.

## Main results

* `Deformation.ToposThickening.FirstOrderLiftDiagram.presentationObstructionClass_eq_zero_iff`
  and `obstructionClass_eq_zero_iff`: either class vanishes exactly when a lift exists.

## Implementation notes

The Ext groups are Hom groups of the derived category of sheaves of `𝒪₁`-modules for an
arbitrary `HasDerivedCategory` instance. The class is pinned, not asserted to exist: it is the
class of the homomorphism `ξ`, which is itself the unique homomorphism of Step 1
(`existsUnique_obstructionConormalHom`), transported along the inverse of the localization of
the canonical comparison chain map `NL(α) ⟶ NL_{𝒪₁/𝒪_{ℬ₁}}`.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sites.FreeAlgebra

universe t v u w

namespace Deformation.ToposThickening.FirstOrderLiftDiagram

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)
  [hD : HasDerivedCategory.{t}
    (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O))]

/-- The naive cotangent complex `NL(α)` of the presentation of Step 1 of the source's proof. -/
abbrev presentationNL :
    CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O))
      ℤ :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex.{v, u, max u v w, max u v w} J
    D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D)

/-- The naive cotangent complex `NL_{𝒪₁/𝒪_{ℬ₁}}` of the front reduced structure sheaf over its
base. -/
abbrev frontNL :
    CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O))
      ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, max u v w} J
    D.front.OB D.front.O D.front.f

/-- The homomorphism `ξ : ℐ/ℐ² ⟶ g_*𝒢₂` of Step 1, with its source spelled as the degree `-1`
term of the conormal sequence of the presentation. -/
abbrev xiSeq : (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, max u v w} J
    D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D)).X₁ ⟶ pushedIdeal D :=
  obstructionConormalHom D

/-- **The class `[ξ]` of Step 1 of the proof of Stacks 08UG**: the class in
`Ext¹_{𝒪₁}(NL(α), g_*𝒢₂)` of the homomorphism `ξ : ℐ/ℐ² ⟶ g_*𝒢₂` out of the conormal sheaf of
the presentation `α : ℰ ⟶ 𝒪₁`. -/
def presentationObstructionClass :
    DerivedCategory.Ext (DerivedCategory.Q.obj (presentationNL D))
      ((DerivedCategory.singleFunctor _ 0).obj (pushedIdeal D)) 1 :=
  Stacks.SheafOfModules.presentationConormalExtClass.{v, u, max u v w, t} J D.front.OB D.front.O
    D.front.f (pairPresheaf D) (pairAlpha D) (pushedIdeal D) (xiSeq D)

/-- **The class `[ξ]` vanishes exactly when a lift exists** (Steps 2 and 3 of the source's
proof). -/
theorem presentationObstructionClass_eq_zero_iff :
    presentationObstructionClass D = 0 ↔ Nonempty (Lift D) :=
  (Stacks.SheafOfModules.presentationConormalExtClass_eq_zero_iff.{t, max u v w, v, u} J
    D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D) (pushedIdeal D)
    (xiSeq D)).trans (nonempty_lift_iff_exists_factorization D).symm

/-- The localization of the canonical comparison `NL(α) ⟶ NL_{𝒪₁/𝒪_{ℬ₁}}` is invertible, by
[Stacks Project, Tag 08TY]. -/
instance isIso_Q_map_naiveCotangentComplexComparison :
    IsIso (DerivedCategory.Q.map
      (Stacks.SheafOfModules.naiveCotangentComplexComparison.{v, u, max u v w, max u v w} J
        D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D))) := by
  have := Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison_site.{v, u,
    max u v w, max u v w} J D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D)
  infer_instance

/-- The canonical identification `NL(α) ≅ NL_{𝒪₁/𝒪_{ℬ₁}}` in the derived category, by
[Stacks Project, Tag 08TY]. -/
abbrev presentationNLIso :
    DerivedCategory.Q.obj (presentationNL D) ≅ DerivedCategory.Q.obj (frontNL D) :=
  asIso (DerivedCategory.Q.map
    (Stacks.SheafOfModules.naiveCotangentComplexComparison.{v, u, max u v w, max u v w} J
      D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D)))

/-- **The obstruction class of Stacks 08UG, clause (1), on one site**: the class `[ξ]` of
Step 1 of the source's proof, read in `Ext¹_{𝒪₁}(NL_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)` through the
canonical identification `NL(α) ≅ NL_{𝒪₁/𝒪_{ℬ₁}}` of Stacks 08TY. -/
def obstructionClass :
    DerivedCategory.Ext (DerivedCategory.Q.obj (frontNL D))
      ((DerivedCategory.singleFunctor _ 0).obj (pushedIdeal D)) 1 :=
  (presentationNLIso D).inv ≫ presentationObstructionClass D

/-- **Stacks 08UG, clause (1), on one site**: the obstruction class in
`Ext¹_{𝒪₁}(NL_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)` vanishes if and only if a morphism fitting into the
diagram compatibly with `ν` exists. -/
theorem obstructionClass_eq_zero_iff :
    obstructionClass D = 0 ↔ Nonempty (Lift D) := by
  rw [← presentationObstructionClass_eq_zero_iff, obstructionClass]
  constructor
  · intro h
    have h' := congrArg (fun k => (presentationNLIso D).hom ≫ k) h
    simpa using h'
  · intro h
    rw [h, comp_zero]

end Deformation.ToposThickening.FirstOrderLiftDiagram

end
