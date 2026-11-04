module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalUnitBridge
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormula
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic

/-!
# Multiplication by a nonvanishing global section is injective on sections

Clause 2 of [Stacks, Tag 01CY] says that a global section `σ` of an invertible `𝒪_X`-module `M`
trivialises `M` over its nonvanishing open `X_σ`. Its *whiskered* form — the one a twisting
argument consumes — is that for an arbitrary `𝒪_X`-module `F` the multiplication
`t ↦ t ⊗ σ|_U : Γ(F, U) ⟶ Γ(F ⊗ M, U)` is injective for every open `U ⊆ X_σ`. Both halves of
that statement are available separately:

* `Stacks.SectionProduct.bijective_mapFun_mulRight_of_app_bijective`
  (`StacksFrontier/AlgebraicGeometry/SectionProduct/BijStalk.lean`) whiskers a section that is
  bijective on the sections over every small enough open into a stalkwise bijection; and
* `Stacks.SectionProduct.app_bijective_of_le_nonvanishingLocus` (same file) supplies that
  hypothesis for a section of a module trivialised by a pairing, on every open inside its
  nonvanishing locus.

This file performs the composition. Four things had to be supplied, and two of them were already
present elsewhere:

* the monoidal-unit transport `Stacks.SectionProduct.mulRight_ofUnitHom` and the composed stalk
  statement `Stacks.SectionProduct.bijective_mapFun_mulRight_unitHomEquiv_symm`
  (`StacksFrontier/AlgebraicGeometry/SectionProduct/MonoidalUnitBridge.lean`);
* the section-level formula `Stacks.SectionProduct.mulSec_eq_tensorSection`
  (`StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormula.lean`), which identifies
  `Stacks.TensorSectionNonvanishing.mulSec` with the elementary tensor product of sections;
* the trivialization `tensorSheaf X.toRingedSpace M N ≅ SheafOfModules.unit _`, which the second
  half takes as an argument and which invertibility supplies only existentially — and
  only after `Stacks.Ample.IsInvertibleModule`, an
  `AlgebraicGeometry.SheafOfModules.IsInvertible`, is transported to the
  `Stacks.SheafOfModules.IsInvertible` of the development the nonvanishing locus is built in;
* the passage from `Stacks.Ample.nonvanishingLocus`, which
  `Stacks.AmpleTheory.powNonvanishingOpen` is built from, to
  `Stacks.SheafOfModules.nonvanishingLocus`, which the second half is stated over. That is
  `Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq`.

The stalk statement concludes bijectivity on *stalks*, so the last step is that a section
of a sheaf whose germs all vanish is zero.

## Main results

* `Stacks.SectionProduct.isInvertible_stacks`: the transport of invertibility between the two
  developments of [Stacks, Tag 01CS], by rebuilding the universal property record.
* `Stacks.SectionProduct.exists_tensorSheaf_iso_unit`: the trivialization of an invertible module
  on a scheme, in the ringed-space tensor spelling the nonvanishing locus is stated over.
* `Stacks.SectionProduct.app_monoidalUnitSection_ofUnitHom`: a morphism out of the monoidal unit
  re-seated from Mathlib's unit carries the canonical unit section over `U` to the value over `U`
  of the global section it names. This is the right triangle identity of sheafification, and it
  is the only place a formula for the comparison isomorphism is needed.
* `Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero`: **the whiskered clause 2 of
  [Stacks, Tag 01CY] on sections**, with its hypothesis discharged from nonvanishing rather than
  assumed.

## Implementation notes

No `@[stacks]` attribute is attached: clause 2 of Tag 01CY is attached to the trivialization
statements in `StacksFrontier/AlgebraicGeometry/NonvanishingTrivialization/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/NonvanishingSpelling/Trivialize.lean`, and what is added here is
the whiskering, which the source states as part of the same clause but which this repository
already carries unwhiskered under that label.

`Stacks.SectionProduct.isInvertible_stacks` is a plain theorem rather than an instance: its
conclusion and its hypothesis have the same class head, so offering instance search a step from
`IsInvertible` to `IsInvertible` is not worth the risk for the two call sites here. The same
caution is recorded, with its measurement, at
`Stacks.NonvanishingSpelling.isInvertible_toRingedSpace`.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.TensorSheafification
open Stacks.NonvanishingSpelling
open Stacks.SectionTensorFormula (tensorSection)

universe u

namespace Stacks.SectionProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-- Transport of invertibility between the two developments of [Stacks, Tag 01CS]. -/
theorem isInvertible_stacks (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M := by
  obtain ⟨F, hF, ⟨u⟩⟩ :=
    (‹Stacks.Ample.IsInvertibleModule X M› :
      AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (structureSheafRing X.toRingedSpace).property M).exists_tensorFunctor
  exact ⟨F, hF, ⟨{ ι := u.ι, bijective := u.bijective }⟩⟩

/-- The trivialization of an invertible module on a scheme, in the ringed-space tensor
spelling. -/
theorem exists_tensorSheaf_iso_unit (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] :
    ∃ N : X.Modules, Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj M).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :=
  have := isInvertible_stacks M
  (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X.toRingedSpace).property) M).mp ‹_›

/-! ### The unit section and the comparison isomorphism -/

/-- The right triangle identity of sheafification at Mathlib's unit. -/
theorem toSheafify_comp_unitIso_hom_val (X : Scheme.{u}) :
    toSheafify X.presheaf (hStruct X)
          (_root_.SheafOfModules.unit X.ringCatSheaf).val ≫
        (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom.val =
      𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf).val :=
  (sheafifyAdjunction X.presheaf (hStruct X)).right_triangle_components
    (_root_.SheafOfModules.unit X.ringCatSheaf)

/-- **The section of `M` over `U` named by a re-seated global section** is the value over `U`
of that section. The comparison isomorphism sends the canonical section of the monoidal unit to
`1`, by the right triangle identity of the sheafification adjunction. -/
theorem app_monoidalUnitSection_ofUnitHom (M : X.Modules) (s : M.sections) (U : X.Opens) :
    (ofUnitHom (M.unitHomEquiv.symm s)).app U (monoidalUnitSection X U) = s.eval (op U) :=
  have h1 : (ofUnitHom (M.unitHomEquiv.symm s)).app U (monoidalUnitSection X U) =
      (M.unitHomEquiv.symm s).val.app (op U)
        ((toSheafify X.presheaf (hStruct X)
              (_root_.SheafOfModules.unit X.ringCatSheaf).val ≫
            (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
              (hStruct X)).hom.val).app (op U) (1 : Γ(X, U))) := rfl
  have h2 := congrArg
    (fun α : (_root_.SheafOfModules.unit X.ringCatSheaf).val ⟶
        (_root_.SheafOfModules.unit X.ringCatSheaf).val =>
      (M.unitHomEquiv.symm s).val.app (op U) (α.app (op U) (1 : Γ(X, U))))
    (toSheafify_comp_unitIso_hom_val X)
  have h3 : (M.unitHomEquiv.symm s).val.app (op U) (1 : Γ(X, U)) = s.eval (op U) :=
    congrArg (fun r : M.sections => r.eval (op U)) (M.unitHomEquiv.apply_symm_apply s)
  h1.trans (h2.trans h3)

/-- **The product of a section with a re-seated global section, on sections.** -/
theorem mulSec_ofUnitHom_eq_tensorSection (F M : X.Modules) (s : M.sections) {U : X.Opens}
    (m : Γ(F, U)) :
    Stacks.TensorSectionNonvanishing.mulSec F (ofUnitHom (M.unitHomEquiv.symm s)) m =
      tensorSection F M m (s.eval (op U)) :=
  (mulSec_eq_tensorSection F M (ofUnitHom (M.unitHomEquiv.symm s)) m).trans
    (congrArg (fun n : Γ(M, U) => tensorSection F M m n)
      (app_monoidalUnitSection_ofUnitHom M s U))

/-! ### Injectivity on sections -/

/-- **A section of a sheaf of modules on a scheme all of whose germs vanish is zero.** -/
theorem eq_zero_of_germ_eq_zero (F : X.Modules) {U : X.Opens} (t : Γ(F, U))
    (h : ∀ y, ∀ hy : y ∈ U, (F.presheaf.germ U y hy).hom t = 0) : t = 0 :=
  TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) ⟨F.val.presheaf, F.isSheaf⟩ U t 0
    fun y hy => (h y hy).trans (map_zero (F.presheaf.germ U y hy).hom).symm

/-- **Multiplication by a nonvanishing global section of an invertible module is injective on
the sections over an open inside its nonvanishing locus.** This is the whiskered clause 2 of
[Stacks, Tag 01CY] read on sections: the stalk statement is
`Stacks.SectionProduct.bijective_mapFun_mulRight_unitHomEquiv_symm`, and a section of a sheaf
whose germs all vanish is zero. -/
theorem eq_zero_of_tensorSection_eq_zero (F M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤)) {U : X.Opens}
    (hU : ∀ y ∈ U, y ∈ Stacks.Ample.nonvanishingLocus M σ) {t : Γ(F, U)}
    (ht : tensorSection F M t (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op σ) = 0) :
    t = 0 := by
  obtain ⟨N, ⟨ψ⟩⟩ := exists_tensorSheaf_iso_unit M
  have hW : ∀ y ∈ U, y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M
      ((sectionsEquiv X M).symm σ) :=
    fun y hy => (stalkNonvanishingLocus_symm_eq X M σ).ge (hU y hy)
  have hzero : (Stacks.TensorSectionNonvanishing.mulRight F
      (ofUnitHom (M.unitHomEquiv.symm ((sectionsEquiv X M).symm σ)))).app U t = 0 :=
    (mulSec_ofUnitHom_eq_tensorSection F M ((sectionsEquiv X M).symm σ) t).trans ht
  refine eq_zero_of_germ_eq_zero F t fun y hy => ?_
  refine (bijective_mapFun_mulRight_unitHomEquiv_symm F M N ψ
    ((sectionsEquiv X M).symm σ) hy hW).1 ?_
  rw [Stacks.ModuleStalk.mapFun_germ, hzero, map_zero]
  exact (map_zero (Stacks.ModuleStalk.map (Stacks.TensorSectionNonvanishing.mulRight F
    (ofUnitHom (M.unitHomEquiv.symm ((sectionsEquiv X M).symm σ)))) y)).symm

end Stacks.SectionProduct

end
