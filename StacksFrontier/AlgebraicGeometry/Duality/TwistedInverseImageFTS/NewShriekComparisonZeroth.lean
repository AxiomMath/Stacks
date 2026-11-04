module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparisonPlusIso
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekRelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModuleMap
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# `H⁰(g_new^! 𝒪_Y) ≅ H⁰(g^! 𝒪_Y)` through an identification of `g^!K`

For a separated morphism `g : X ⟶ Y` of schemes of finite type over a Noetherian base, a
compactification `j`, a dualizing complex `K` on `Y` and an identification `e : g^!K ≅ ω`, the
isomorphism `g^! ≅ g_new^!` of [Stacks, Tag 0AUE] at `𝒪_Y` gives `H⁰(g_new^! 𝒪_Y) ≅ H⁰(g^! 𝒪_Y)`.
It does not depend on the compactification ([Stacks, Tag 0AA0]).

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.upperShriekStructureSheafZerothIsoOfIso`.

## Main results

* `upperShriekStructureSheafZerothIsoOfIso_compactificationIso`,
  `upperShriekStructureSheafZerothIsoOfIso_trans_upperShriekStructureSheafZerothIso`:
  independence of the compactification.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

/-- The comparison of the two models of `D(𝒪_X)` carries a morphism back to itself. -/
theorem comparison_functor_map_inverse_map {X : Scheme.{u}} {E F : DerivedCategory X.Modules}
    (φ : E ⟶ F) : (comparison X).functor.map ((comparison X).inverse.map φ) = φ :=
  Equiv.apply_symm_apply _ φ

end Stacks.Duality.TwistedInverseImageDuality

namespace Stacks.Duality.NormalizedOnOpens

open Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (g : X ⟶ Y)
  (j : CompactificationOf (Over.mk g.left)) {K : Std Y.left} (hK : IsDualizing K) {ω : Std X.left}

/-- `H⁰(g_new^! 𝒪_Y) ≅ H⁰(g^! 𝒪_Y)` through an identification `e : g^!K ≅ ω`. -/
def upperShriekStructureSheafZerothIsoOfIso (e : upperShriekDualizing g j hK ≅ ω) :
    (@DerivedCategory.homologyFunctor X.left.Modules _ _
        (PerfectApproximation.standardModel X.left) 0).obj
        ((fNewShriekStd g.left ω K).obj (structureStd Y.left)) ≅
      upperShriekStructureSheafZeroth g j :=
  (@DerivedCategory.homologyFunctor X.left.Modules _ _
      (PerfectApproximation.standardModel X.left) 0).mapIso
      ((upperShriekStdIsoFNewShriekOfIso g j hK e).app
        ⟨structureStd Y.left, plusCoh_structureStd Y.left⟩).symm ≪≫
    (PerfectApproximation.homologyStandardIso _ 0).symm

/-- The chase behind `upperShriekStructureSheafZerothIsoOfIso_compactificationIso`. -/
theorem upperShriekStructureSheafZerothIsoOfIso_chase {𝒞 : Type*} [Category 𝒞] {A E₁ E₂ L₁ L₂ : 𝒞}
    (a : A ⟶ E₁) (b : A ⟶ E₂) (p : E₁ ⟶ E₂) (q : L₁ ⟶ L₂) (s₁ : L₁ ≅ E₁) (s₂ : L₂ ≅ E₂)
    (hab : a ≫ p = b) (hN : q ≫ s₂.hom = s₁.hom ≫ p) : (a ≫ s₁.inv) ≫ q = b ≫ s₂.inv := by
  rw [← hab, Category.assoc, Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hN, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- An isomorphism `α` equal to `p ≫ β`, read on inverses. -/
theorem inv_comp_eq_inv_of_comp_hom_eq {𝒞 : Type*} [Category 𝒞] {a b c : 𝒞} (α : c ≅ a) (β : c ≅ b)
    (p : a ⟶ b) (h : p ≫ β.inv = α.inv) : α.hom ≫ p = β.hom := by
  rw [← Category.comp_id p, ← β.inv_hom_id, ← Category.assoc p, h, Iso.hom_inv_id_assoc]

/-- **`H⁰(g_new^! 𝒪_Y) ≅ H⁰(g^! 𝒪_Y)` does not depend on the compactification.** -/
theorem upperShriekStructureSheafZerothIsoOfIso_compactificationIso
    (j₁ j₂ : CompactificationOf (Over.mk g.left))
    (hKb : DerivedCategoryB.IsBoundedBelow (dualizingQCoh hK).obj)
    (e : upperShriekDualizing g j₂ hK ≅ ω) :
    upperShriekStructureSheafZerothIsoOfIso g j₁ hK
        (upperShriekDualizingPlusIso g j₁ j₂ hK hKb ≪≫ e) ≪≫
        upperShriekStructureSheafZerothCompactificationIso j₁ j₂ =
      upperShriekStructureSheafZerothIsoOfIso g j₂ hK e := by
  have B := upperShriekStdIsoFNewShriekOfIso_upperShriekPlusIso g j₁ j₂ hK hKb
    ⟨structureStd Y.left, plusCoh_structureStd Y.left⟩
    (KoszulRegular.isBoundedBelow_singleFunctor_obj _) e
  have N := PerfectApproximation.homologyStandardIso_naturality
    ((comparison X.left).inverse.map
        ((DominatingCompactification.upperShriekPlusIso g j₁ j₂).hom.app
          (structurePlus Y)).hom.hom) 0
  ext1
  refine upperShriekStructureSheafZerothIsoOfIso_chase _ _
    ((@DerivedCategory.homologyFunctor X.left.Modules _ _
      (PerfectApproximation.standardModel X.left) 0).map ((comparison X.left).inverse.map
        ((DominatingCompactification.upperShriekPlusIso g j₁ j₂).hom.app
          (structurePlus Y)).hom.hom)) _ _ _ ?_
    ((congrArg (fun φ => (DerivedCategory.homologyFunctor X.left.Modules 0).map φ ≫ _)
      (comparison_functor_map_inverse_map _).symm).trans N)
  refine ((@DerivedCategory.homologyFunctor X.left.Modules _ _
      (PerfectApproximation.standardModel X.left) 0).map_comp _ _).symm.trans ?_
  exact congrArg (@DerivedCategory.homologyFunctor X.left.Modules _ _
      (PerfectApproximation.standardModel X.left) 0).map
    (inv_comp_eq_inv_of_comp_hom_eq
      (((upperShriekStdIsoFNewShriekOfIso g j₁ hK
          (upperShriekDualizingPlusIso g j₁ j₂ hK hKb ≪≫ e)).app
        ⟨structureStd Y.left, plusCoh_structureStd Y.left⟩).symm)
      (((upperShriekStdIsoFNewShriekOfIso g j₂ hK e).app
        ⟨structureStd Y.left, plusCoh_structureStd Y.left⟩).symm) _ B)

/-- **`H⁰(g_new^! 𝒪_Y) ≅ M|_X` does not depend on the compactification**, for a factorization
`g = π ∘ i` with `π` finite, `M = H⁰(a_π 𝒪_Y)`. -/
theorem upperShriekStructureSheafZerothIsoOfIso_trans_upperShriekStructureSheafZerothIso
    (F : OpenFiniteFactorization g) (j₁ j₂ : CompactificationOf (Over.mk g.left))
    (hKb : DerivedCategoryB.IsBoundedBelow (dualizingQCoh hK).obj)
    (e : upperShriekDualizing g j₂ hK ≅ ω) :
    upperShriekStructureSheafZerothIsoOfIso g j₁ hK
        (upperShriekDualizingPlusIso g j₁ j₂ hK hKb ≪≫ e) ≪≫
        upperShriekStructureSheafZerothIso F j₁ =
      upperShriekStructureSheafZerothIsoOfIso g j₂ hK e ≪≫
        upperShriekStructureSheafZerothIso F j₂ := by
  rw [upperShriekStructureSheafZerothIso_eq_trans F j₁ j₂, ← Iso.trans_assoc,
    upperShriekStructureSheafZerothIsoOfIso_compactificationIso]

end Stacks.Duality.NormalizedOnOpens

namespace Stacks.Duality.NormalizedOnOpens

open Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)

/-- `H⁰(f_new^! 𝒪_Y) ≅ H⁰(f^! 𝒪_Y)` is the isomorphism attached to `ω_X^• ≅ f^! ω_Y^•`. -/
theorem newShriekStructureSheafZerothIso_eq :
    haveI := hq.source_noetherian
    newShriekStructureSheafZerothIso c hpe hωS hf 𝒦X 𝒦Y =
      upperShriekStructureSheafZerothIsoOfIso (ftsHomSelf hf) (c f hf)
        (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y)
        ((comparison X).inverse.mapIso
          ((ObjectProperty.ι _).mapIso ((upperShriek (ftsHomSelf hf) (c f hf)).mapIso
              (dualizingQCohIso c 𝒦Y (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y))) ≪≫
            (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso
              (upperShriekObjIso c hpe hωS hf 𝒦X 𝒦Y).symm))) :=
  rfl

end Stacks.Duality.NormalizedOnOpens
