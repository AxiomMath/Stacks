module

public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFibreSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRelativeDirectImage
public import StacksFrontier.Deformation.Artin.FormalObject.Realization

/-!
# Effective formal objects of the stack of proper flat algebraic spaces, over their own base

Let `ξ = (R, ξ_n, f_n)` be a formal object (Stacks 07X4) of the stack
`p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶ (Sch/S)_{fppf}` of Stacks 0D1D. If `ξ` is
effective (Stacks 07X7), it is realized by a finitely presented, flat and proper family over
`Spec R`, viewed over `S`. This file moves that family to the big fppf site of `Spec R` itself,
along the equivalence of Stacks 04SG between algebraic spaces over `Spec R` and algebraic spaces
over `S` with a morphism to `Spec R`, and identifies its adic fibres
`X ×_{Spec R} Spec(R / 𝔪 ^ (n + 1))` with the levels `ξ_n` of the formal object, compatibly with
the projections to the thickenings and with the transitions.

This is the form in which effectivity is contradicted in the proof of Stacks 0D1R: the results
used there are stated for an algebraic space over `Spec R` with its system of adic fibres
(`AlgebraicGeometry.Space.adicFibreSpaceOf`).

## Main definitions

* `AlgebraicGeometry.formalBaseHom`: the structure morphism `Spec R ⟶ S` of a complete local base,
  as a morphism of the big fppf site.
* `AlgebraicGeometry.relocalizeAdicThickeningIso`: the lower-shriek extension to `S` of the `n`-th
  adic thickening of `Spec R`, as an object over `Spec R`, is the `n`-th truncation over `S`.
* `AlgebraicGeometry.properFlatLevelStructure`: the structure morphism of a level of a formal
  object of `p'_{fp, flat, proper}` to its truncation.
* `AlgebraicGeometry.relocalizeAdicFibreLevelIso`: for a realization `x` of `ξ` over `Spec R` and
  an algebraic space `X` over `Spec R` with `Λ X ≅ x` over `Spec R`, the extension to `S` of the
  `n`-th adic fibre of `X` is the `n`-th level `ξ_n`.

## Main results

* `AlgebraicGeometry.exists_relocalizeSpace_adicFibreSpaceOf_iso_of_isEffective`: an effective
  formal object of `p'_{fp, flat, proper}` comes from an algebraic space over `Spec R` which is of
  finite presentation, flat and proper over `Spec R`, whose adic fibres, extended to `S`, are the
  levels of the formal object, compatibly with the projections to the thickenings and with the
  transitions.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
* [Stacks Project, Tag 0D1D](https://stacks.math.columbia.edu/tag/0D1D)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

open Space Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The thickenings over `Spec R` and over `S` -/

/-- The structure morphism `Spec R ⟶ S` of a complete local base, as a morphism of the big fppf
site. The complete local base `Spec R` over `S` is `Over.mk (formalBaseHom hS A hA)`, which is
`Deformation.Artin.baseOver`. -/
abbrev formalBaseHom (hS : B.Contains S) (A : FormalBase S) (hA : B.Contains (Spec (.of A.R))) :
    B.obj hA ⟶ B.obj hS :=
  ObjectProperty.homMk A.toS

section Thickenings

variable (A : FormalBase S) (hA : B.Contains (Spec (.of A.R)))

/-- The complete local base, as an object of the big fppf site over `S`, is the object attached
to `AlgebraicGeometry.formalBaseHom`. -/
theorem baseOver_eq_mk_formalBaseHom :
    baseOver B S hS A hA = Over.mk (formalBaseHom hS A hA) :=
  rfl

/-- The truncations of a complete local base are its adic thickenings. -/
theorem formalBase_truncation_eq (n : ℕ) :
    A.truncation n = adicThickening A.R (maximalIdeal A.R) n :=
  rfl

variable (contains : ∀ n, B.Contains (A.truncation n))

/-- The `n`-th adic thickening of `Spec R`, as an object over `Spec R`, viewed over `S` along
`Spec R ⟶ S`, is the `n`-th truncation of the complete local base over `S`. -/
theorem overMap_adicThickeningObject (n : ℕ) :
    (Over.map (formalBaseHom hS A hA)).obj
        (adicThickeningObject A.R (maximalIdeal A.R) B hA (contains_adicThickening _ _ B hA) n) =
      truncationOver B S hS A contains n :=
  rfl

/-- The inclusion of one adic thickening of `Spec R` in the next, viewed over `S`, is the
inclusion of one truncation in the next. -/
theorem overMap_adicThickeningSuccMap (n : ℕ) :
    (Over.map (formalBaseHom hS A hA)).map
        (adicThickeningSuccMap A.R (maximalIdeal A.R) B hA (contains_adicThickening _ _ B hA) n) =
      truncationOverSucc B S hS A contains n :=
  rfl

/-- **The extended thickenings are the truncations.** The lower-shriek extension to `S`, along
`Spec R ⟶ S`, of the `n`-th adic thickening `Spec(R / 𝔪 ^ (n + 1))` of `Spec R` regarded as an
algebraic space over `Spec R`, is the `n`-th truncation of the complete local base over `S`. -/
def relocalizeAdicThickeningIso (n : ℕ) :
    Space.relocalizeSpace B hA hS (formalBaseHom hS A hA)
        (schemeSpace (adicThickeningObject A.R (maximalIdeal A.R) B hA
          (contains_adicThickening _ _ B hA) n)) ≅
      schemeSpace (truncationOver B S hS A contains n) :=
  ObjectProperty.isoMk _ ((OverShriek.relocalizeYonedaIso (formalBaseHom hS A hA)).app
    (adicThickeningObject A.R (maximalIdeal A.R) B hA (contains_adicThickening _ _ B hA) n))

/-- Under `AlgebraicGeometry.relocalizeAdicThickeningIso`, the extension of the map from a
thickening to `Spec R` is the inclusion of the truncation in the complete local base. -/
theorem relocalizeHom_adicThickeningMap_comp_relocalizeBaseHom (n : ℕ) :
    Space.relocalizeHom B hA hS (formalBaseHom hS A hA)
        (schemeSpaceMap (adicThickeningMap A.R (maximalIdeal A.R) B hA
          (contains_adicThickening _ _ B hA) n)) ≫
        Space.relocalizeBaseHom B hA hS (formalBaseHom hS A hA) =
      (relocalizeAdicThickeningIso A hA contains n).hom ≫
        schemeSpaceMap (restrictionToBase B S hS A hA contains n) := by
  apply ObjectProperty.hom_ext
  ext W ⟨⟨ψ, s⟩, h⟩
  apply Over.OverMorphism.ext
  exact (Over.w s).symm

/-- The isomorphisms `AlgebraicGeometry.relocalizeAdicThickeningIso` commute with the inclusions
of one thickening in the next. -/
theorem relocalizeHom_adicThickeningSuccMap_comp_relocalizeAdicThickeningIso (n : ℕ) :
    Space.relocalizeHom B hA hS (formalBaseHom hS A hA)
        (schemeSpaceMap (adicThickeningSuccMap A.R (maximalIdeal A.R) B hA
          (contains_adicThickening _ _ B hA) n)) ≫
        (relocalizeAdicThickeningIso A hA contains (n + 1)).hom =
      (relocalizeAdicThickeningIso A hA contains n).hom ≫
        schemeSpaceMap (truncationOverSucc B S hS A contains n) :=
  ObjectProperty.hom_ext _
    ((OverShriek.relocalizeYonedaIso (formalBaseHom hS A hA)).hom.naturality
      (adicThickeningSuccMap A.R (maximalIdeal A.R) B hA (contains_adicThickening _ _ B hA) n))

end Thickenings

/-! ### The levels of a formal object of `p'_{fp, flat, proper}` -/

section Levels

variable (ξ : FormalObject B S hS (cartesianProperFlatProjection B S hS))

/-- The `n`-th level of a formal object of `p'_{fp, flat, proper}` lies over the `n`-th
truncation of its complete local base: `Deformation.Artin.FormalObject.level_eq`, read on the
underlying family. -/
theorem properFlatLevel_right_eq (n : ℕ) :
    (ξ.level n).obj.obj.right = truncationOver B S hS ξ.base ξ.contains n :=
  ξ.level_eq n

/-- The structure morphism of the `n`-th level of a formal object of `p'_{fp, flat, proper}` to
the `n`-th truncation of its complete local base. -/
def properFlatLevelStructure (n : ℕ) :
    (ξ.level n).obj.obj.left ⟶ schemeSpace (truncationOver B S hS ξ.base ξ.contains n) :=
  commaHomAsSpaceMap (ξ.level n).obj.obj ≫ schemeSpaceMap (eqToHom (properFlatLevel_right_eq ξ n))

/-- The structure morphism of a level is the structure morphism of the underlying family. -/
theorem properFlatLevelStructure_hom (n : ℕ) :
    (properFlatLevelStructure ξ n).hom =
      (ξ.level n).obj.obj.hom ≫ yoneda.map (eqToHom (properFlatLevel_right_eq ξ n)) :=
  rfl

/-- The transition of a formal object of `p'_{fp, flat, proper}`, on the bases of the
families, is the inclusion of one truncation in the next. -/
theorem properFlatLevel_transition_right (n : ℕ) :
    (ξ.transition n).hom.hom.right ≫ eqToHom (properFlatLevel_right_eq ξ (n + 1)) =
      eqToHom (properFlatLevel_right_eq ξ n) ≫ truncationOverSucc B S hS ξ.base ξ.contains n := by
  have ht : (ξ.transition n).hom.hom.right =
      eqToHom (properFlatLevel_right_eq ξ n) ≫ truncationOverSucc B S hS ξ.base ξ.contains n ≫
        eqToHom (properFlatLevel_right_eq ξ (n + 1)).symm :=
    FormalObject.map_transition ξ n
  rw [ht]
  simp

/-- The transitions of a formal object of `p'_{fp, flat, proper}` lie over the inclusions of
one truncation in the next. -/
theorem properFlatLevel_transition_comp_properFlatLevelStructure (n : ℕ) :
    (ξ.transition n).hom.hom.left ≫ properFlatLevelStructure ξ (n + 1) =
      properFlatLevelStructure ξ n ≫
        schemeSpaceMap (truncationOverSucc B S hS ξ.base ξ.contains n) := by
  apply ObjectProperty.hom_ext
  have hw : (ξ.transition n).hom.hom.left.hom ≫ (ξ.level (n + 1)).obj.obj.hom =
      (ξ.level n).obj.obj.hom ≫ yoneda.map (ξ.transition n).hom.hom.right :=
    (ξ.transition n).hom.hom.w
  change (ξ.transition n).hom.hom.left.hom ≫ (ξ.level (n + 1)).obj.obj.hom ≫
      yoneda.map (eqToHom (properFlatLevel_right_eq ξ (n + 1))) =
    ((ξ.level n).obj.obj.hom ≫ yoneda.map (eqToHom (properFlatLevel_right_eq ξ n))) ≫
      yoneda.map (truncationOverSucc B S hS ξ.base ξ.contains n)
  rw [← Category.assoc, hw, Category.assoc, ← Functor.map_comp,
    properFlatLevel_transition_right, Functor.map_comp, Category.assoc]

end Levels

/-! ### A realization over the base, moved to the base -/

section Rebase

variable {ξ : FormalObject B S hS (cartesianProperFlatProjection B S hS)}
  {hA : B.Contains (Spec (.of ξ.base.R))} {x : CartesianProperFlatSpaces B S hS}

/-- The structure morphism of a family of `Spaces'_{fp, flat, proper}` lying over the complete
local base `Spec R`, to `Spec R` regarded over `S`. -/
def realizingStructure (hx : x.obj.obj.right = baseOver B S hS ξ.base hA) :
    x.obj.obj.left ⟶ schemeSpace (baseOver B S hS ξ.base hA) :=
  commaHomAsSpaceMap x.obj.obj ≫ schemeSpaceMap (eqToHom hx)

/-- A family of `Spaces'_{fp, flat, proper}` whose base is identified with `T` is of finite
presentation, flat and proper over `T`. -/
theorem isProperFlatSpace_comp_eqToHom
    {Y : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {T : BigFppfOver B S hS} (hY : Y.right = T) (h : isProperFlatSpace B S hS Y) :
    Space.IsFinitePresentation B S hS (Y.hom ≫ yoneda.map (eqToHom hY)) ∧
      Space.IsFlat B S hS (Y.hom ≫ yoneda.map (eqToHom hY)) ∧
      Space.IsProper B S hS (Y.hom ≫ yoneda.map (eqToHom hY)) := by
  obtain ⟨L, R, f⟩ := Y
  subst hY
  simp only [eqToHom_refl]
  exact h

variable {hx : x.obj.obj.right = baseOver B S hS ξ.base hA}
  (Rz : FormalObject.Realization ξ hA x hx)

include Rz in
/-- **The `n`-th level is the base change of the realizing family to the `n`-th truncation.**
The arrow `ξ_n ⟶ x` of a realization is cartesian over the inclusion of the truncation. -/
theorem isPullback_realization (n : ℕ) :
    IsPullback (Rz.r n).hom.hom.left.hom (properFlatLevelStructure ξ n).hom
      (realizingStructure hx).hom
      (yoneda.map (restrictionToBase B S hS ξ.base hA ξ.contains n)) := by
  have hcart := isPullback_hom_of_isStronglyCartesian B S hS (Rz.r n).hom.hom (Rz.r n).property
  have hm : (Rz.r n).hom.hom.right = eqToHom (properFlatLevel_right_eq ξ n) ≫
      restrictionToBase B S hS ξ.base hA ξ.contains n ≫ eqToHom hx.symm :=
    Rz.map_eq n
  have key : (Rz.r n).hom.hom.right ≫ eqToHom hx =
      eqToHom (properFlatLevel_right_eq ξ n) ≫ restrictionToBase B S hS ξ.base hA ξ.contains n := by
    rw [hm]
    simp
  refine hcart.flip.of_iso (Iso.refl _) (Iso.refl _)
    (yoneda.mapIso (eqToIso (properFlatLevel_right_eq ξ n))) (yoneda.mapIso (eqToIso hx))
    (by simp) ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · exact (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map key).trans (yoneda.map_comp _ _))

variable {X : AlgebraicSpaces B (Spec (.of ξ.base.R)) hA}
  {eQ : Space.relocalizeSpace B hA hS (formalBaseHom hS ξ.base hA) X ≅ x.obj.obj.left}
  (heQ : eQ.hom ≫ realizingStructure hx =
    Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA) (Space.toFinalHom B hA X) ≫
      Space.relocalizeBaseHom B hA hS (formalBaseHom hS ξ.base hA))

include heQ in
/-- **The extension of the `n`-th adic fibre is the base change of the realizing family to the
`n`-th truncation.** The lower-shriek extension preserves fibre products, and it carries the
thickening `Spec(R / 𝔪 ^ (n + 1)) ⟶ Spec R` to the inclusion of the `n`-th truncation. -/
theorem isPullback_relocalize_adicFibre (n : ℕ) :
    IsPullback
      ((OverShriek.relocalizePresheafFunctor (formalBaseHom hS ξ.base hA)).map
          (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) n).hom ≫ eQ.hom.hom)
      ((OverShriek.relocalizePresheafFunctor (formalBaseHom hS ξ.base hA)).map
          (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) n).hom ≫
        (relocalizeAdicThickeningIso ξ.base hA ξ.contains n).hom.hom)
      (realizingStructure hx).hom
      (yoneda.map (restrictionToBase B S hS ξ.base hA ξ.contains n)) := by
  have h := (IsPullback.of_hasPullback (Space.toFinalHom B hA X).hom
    (yoneda.map (adicThickeningMap ξ.base.R (maximalIdeal ξ.base.R) B hA
      (contains_adicThickening _ _ B hA) n))).map
    (OverShriek.relocalizePresheafFunctor (formalBaseHom hS ξ.base hA))
  refine h.of_iso (Iso.refl _) ((ObjectProperty.ι _).mapIso eQ)
    ((ObjectProperty.ι _).mapIso (relocalizeAdicThickeningIso ξ.base hA ξ.contains n))
    ((ObjectProperty.ι _).mapIso
      (asIso (Space.relocalizeBaseHom B hA hS (formalBaseHom hS ξ.base hA))))
    (Category.id_comp _).symm (Category.id_comp _).symm ?_ ?_
  · exact (congrArg (fun φ => φ.hom) heQ).symm
  · exact congrArg (fun φ => φ.hom)
      (relocalizeHom_adicThickeningMap_comp_relocalizeBaseHom (hS := hS) ξ.base hA ξ.contains n)

/-- **The extended `n`-th adic fibre is the `n`-th level**, as algebraic spaces over `S`: the
two are base changes of the realizing family to the `n`-th truncation. -/
def relocalizeAdicFibreLevelIso (n : ℕ) :
    Space.relocalizeSpace B hA hS (formalBaseHom hS ξ.base hA)
        (adicFibreSpaceOf ξ.base.R (maximalIdeal ξ.base.R) B hA X (Space.toFinalHom B hA X) n) ≅
      (ξ.level n).obj.obj.left :=
  ObjectProperty.isoMk _
    ((isPullback_relocalize_adicFibre heQ n).isoIsPullback _ _ (isPullback_realization Rz n))

/-- The identification of the extended `n`-th adic fibre with the `n`-th level is one over the
realizing family. -/
theorem relocalizeAdicFibreLevelIso_hom_comp_realization (n : ℕ) :
    (relocalizeAdicFibreLevelIso Rz heQ n).hom.hom ≫ (Rz.r n).hom.hom.left.hom =
      (OverShriek.relocalizePresheafFunctor (formalBaseHom hS ξ.base hA)).map
          (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) n).hom ≫ eQ.hom.hom :=
  (isPullback_relocalize_adicFibre heQ n).isoIsPullback_hom_fst _ _ (isPullback_realization Rz n)

/-- The identification of the extended `n`-th adic fibre with the `n`-th level is one over the
`n`-th truncation. -/
theorem relocalizeAdicFibreLevelIso_hom_comp_properFlatLevelStructure (n : ℕ) :
    (relocalizeAdicFibreLevelIso Rz heQ n).hom ≫ properFlatLevelStructure ξ n =
      Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
          (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) n) ≫
        (relocalizeAdicThickeningIso ξ.base hA ξ.contains n).hom :=
  ObjectProperty.hom_ext _
    ((isPullback_relocalize_adicFibre heQ n).isoIsPullback_hom_snd _ _
      (isPullback_realization Rz n))

/-- The identifications of the extended adic fibres with the levels carry the extended
transitions of the adic fibres to the transitions of the formal object. -/
theorem relocalizeHom_adicFibreSuccMap_comp_relocalizeAdicFibreLevelIso (n : ℕ) :
    Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
        (adicFibreSuccMap (maximalIdeal ξ.base.R) X (Space.toFinalHom B hA X) n) ≫
        (relocalizeAdicFibreLevelIso Rz heQ (n + 1)).hom =
      (relocalizeAdicFibreLevelIso Rz heQ n).hom ≫ (ξ.transition n).hom.hom.left := by
  let Λ := OverShriek.relocalizePresheafFunctor (formalBaseHom hS ξ.base hA)
  let ι := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)
  let succ := (adicFibreSuccMap (maximalIdeal ξ.base.R) X (Space.toFinalHom B hA X) n).hom
  let E₀ := (relocalizeAdicFibreLevelIso Rz heQ n).hom.hom
  let E₁ := (relocalizeAdicFibreLevelIso Rz heQ (n + 1)).hom.hom
  let T := (ξ.transition n).hom.hom.left.hom
  have hT : T ≫ (Rz.r (n + 1)).hom.hom.left.hom = (Rz.r n).hom.hom.left.hom :=
    congrArg (fun φ => φ.hom.hom.left.hom) (Rz.comp_transition n)
  have hincl : succ ≫ (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA X
      (Space.toFinalHom B hA X) (n + 1)).hom =
      (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA X
        (Space.toFinalHom B hA X) n).hom :=
    congrArg (fun φ => φ.hom) (adicFibreSuccMap_adicFibreInclusion (maximalIdeal ξ.base.R) X
      (Space.toFinalHom B hA X) n)
  have hproj : succ ≫ (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
      (Space.toFinalHom B hA X) (n + 1)).hom =
      (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
        (Space.toFinalHom B hA X) n ≫
        schemeSpaceMap (adicThickeningSuccMap ξ.base.R (maximalIdeal ξ.base.R) B hA
          (contains_adicThickening _ _ B hA) n)).hom :=
    pullback.lift_snd _ _ _
  have hsnd (k : ℕ) := congrArg (fun φ => φ.hom)
    (relocalizeAdicFibreLevelIso_hom_comp_properFlatLevelStructure Rz heQ k)
  have hlev := congrArg (fun φ => φ.hom)
    (properFlatLevel_transition_comp_properFlatLevelStructure ξ n)
  have hthick := congrArg (fun φ => φ.hom)
    (relocalizeHom_adicThickeningSuccMap_comp_relocalizeAdicThickeningIso (hS := hS) ξ.base hA
      ξ.contains n)
  apply ObjectProperty.hom_ext
  change Λ.map succ ≫ E₁ = E₀ ≫ T
  apply (isPullback_realization Rz (n + 1)).hom_ext
  · calc (Λ.map succ ≫ E₁) ≫ (Rz.r (n + 1)).hom.hom.left.hom
        = Λ.map succ ≫ (E₁ ≫ (Rz.r (n + 1)).hom.hom.left.hom) := Category.assoc _ _ _
      _ = Λ.map succ ≫ (Λ.map (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) (n + 1)).hom ≫ eQ.hom.hom) :=
          whisker_eq _ (relocalizeAdicFibreLevelIso_hom_comp_realization Rz heQ (n + 1))
      _ = Λ.map (succ ≫ (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) (n + 1)).hom) ≫ eQ.hom.hom :=
          ((eq_whisker (Λ.map_comp _ _) _).trans (Category.assoc _ _ _)).symm
      _ = Λ.map (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) n).hom ≫ eQ.hom.hom :=
          congrArg (fun φ => Λ.map φ ≫ eQ.hom.hom) hincl
      _ = E₀ ≫ (Rz.r n).hom.hom.left.hom :=
          (relocalizeAdicFibreLevelIso_hom_comp_realization Rz heQ n).symm
      _ = E₀ ≫ (T ≫ (Rz.r (n + 1)).hom.hom.left.hom) := whisker_eq _ hT.symm
      _ = (E₀ ≫ T) ≫ (Rz.r (n + 1)).hom.hom.left.hom := (Category.assoc _ _ _).symm
  · calc (Λ.map succ ≫ E₁) ≫ (properFlatLevelStructure ξ (n + 1)).hom
        = Λ.map succ ≫ (E₁ ≫ (properFlatLevelStructure ξ (n + 1)).hom) := Category.assoc _ _ _
      _ = Λ.map succ ≫ (Λ.map (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) (n + 1)).hom ≫
            (relocalizeAdicThickeningIso ξ.base hA ξ.contains (n + 1)).hom.hom) :=
          whisker_eq _ (hsnd (n + 1))
      _ = Λ.map (succ ≫ (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) (n + 1)).hom) ≫
            (relocalizeAdicThickeningIso ξ.base hA ξ.contains (n + 1)).hom.hom :=
          ((eq_whisker (Λ.map_comp _ _) _).trans (Category.assoc _ _ _)).symm
      _ = Λ.map (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) n ≫
            schemeSpaceMap (adicThickeningSuccMap ξ.base.R (maximalIdeal ξ.base.R) B hA
              (contains_adicThickening _ _ B hA) n)).hom ≫
            (relocalizeAdicThickeningIso ξ.base hA ξ.contains (n + 1)).hom.hom :=
          congrArg (fun φ => Λ.map φ ≫
            (relocalizeAdicThickeningIso ξ.base hA ξ.contains (n + 1)).hom.hom) hproj
      _ = Λ.map (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X
            (Space.toFinalHom B hA X) n).hom ≫
            ((relocalizeAdicThickeningIso ξ.base hA ξ.contains n).hom.hom ≫
              (schemeSpaceMap (truncationOverSucc B S hS ξ.base ξ.contains n)).hom) :=
          (eq_whisker (Λ.map_comp _ _) _).trans ((Category.assoc _ _ _).trans
            (whisker_eq _ hthick))
      _ = (E₀ ≫ (properFlatLevelStructure ξ n).hom) ≫
            (schemeSpaceMap (truncationOverSucc B S hS ξ.base ξ.contains n)).hom :=
          (Category.assoc _ _ _).symm.trans (eq_whisker (hsnd n).symm _)
      _ = E₀ ≫ ((properFlatLevelStructure ξ n).hom ≫
            (schemeSpaceMap (truncationOverSucc B S hS ξ.base ξ.contains n)).hom) :=
          Category.assoc _ _ _
      _ = E₀ ≫ (T ≫ (properFlatLevelStructure ξ (n + 1)).hom) := whisker_eq _ hlev.symm
      _ = (E₀ ≫ T) ≫ (properFlatLevelStructure ξ (n + 1)).hom := (Category.assoc _ _ _).symm

end Rebase

/-! ### Effective formal objects over their own base -/

/-- **An effective formal object of `p'_{fp, flat, proper}` is the system of adic fibres of a
proper flat algebraic space over its own base.** Let `ξ = (R, ξ_n, f_n)` be an effective formal
object (Stacks 07X7) of the stack `p'_{fp, flat, proper}` of Stacks 0D1D over the big fppf site
of `S`. Then there is an algebraic space `X` over `Spec R`, of finite presentation, flat and
proper over `Spec R`, together with isomorphisms of algebraic spaces over `S`

  `Λ (X ×_{Spec R} Spec(R / 𝔪 ^ (n + 1))) ≅ ξ_n`,

where `Λ` is the lower-shriek extension along `Spec R ⟶ S` of Stacks 04SG, which carry the
extended projection to the thickening to the structure morphism of `ξ_n` (through
`AlgebraicGeometry.relocalizeAdicThickeningIso`) and the extended transition of the adic fibres
to the transition `f_n` of `ξ`. -/
theorem exists_relocalizeSpace_adicFibreSpaceOf_iso_of_isEffective
    (ξ : FormalObject B S hS (cartesianProperFlatProjection B S hS))
    (hξ : FormalObject.IsEffective B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) ξ)
    (hA : B.Contains (Spec (.of ξ.base.R))) :
    ∃ (X : AlgebraicSpaces B (Spec (.of ξ.base.R)) hA)
      (f : X ⟶ schemeSpace (baseObject ξ.base.R B hA)),
      Space.IsFinitePresentation B (Spec (.of ξ.base.R)) hA f.hom ∧
      Space.IsFlat B (Spec (.of ξ.base.R)) hA f.hom ∧
      Space.IsProper B (Spec (.of ξ.base.R)) hA f.hom ∧
      ∃ e : ∀ n, Space.relocalizeSpace B hA hS (formalBaseHom hS ξ.base hA)
          (adicFibreSpaceOf ξ.base.R (maximalIdeal ξ.base.R) B hA X f n) ≅
            (ξ.level n).obj.obj.left,
        (∀ n, (e n).hom ≫ properFlatLevelStructure ξ n =
          Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
              (adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA X f n) ≫
            (relocalizeAdicThickeningIso ξ.base hA ξ.contains n).hom) ∧
        (∀ n, Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
              (adicFibreSuccMap (maximalIdeal ξ.base.R) X f n) ≫ (e (n + 1)).hom =
            (e n).hom ≫ (ξ.transition n).hom.hom.left) := by
  obtain ⟨x, hx, ⟨Rz⟩⟩ := FormalObject.exists_realization_of_isEffective (hA := hA)
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) hξ
  have hx' : x.obj.obj.right = baseOver B S hS ξ.base hA := hx
  obtain ⟨X, eQ, heQ⟩ := exists_relocalizeSpace_iso B hA hS (formalBaseHom hS ξ.base hA)
    x.obj.obj.left (realizingStructure hx')
  have hprop := isProperFlatSpace_comp_eqToHom hx' x.obj.property
  have hiso : IsIso (Space.relocalizeBaseHom B hA hS (formalBaseHom hS ξ.base hA)).hom :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map
      (Space.relocalizeBaseHom B hA hS (formalBaseHom hS ξ.base hA))))
  have : IsIso eQ.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map eQ.hom))
  have hproper : Space.IsProper B (Spec (.of ξ.base.R)) hA (Space.toFinalHom B hA X).hom := by
    have h1 : Space.IsProper B S hS (eQ.hom.hom ≫ (realizingStructure hx').hom) :=
      (isProper_isIso_comp_iff B S hS _ _).2 hprop.2.2
    have h2 : eQ.hom.hom ≫ (realizingStructure hx').hom =
        (Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA) (Space.toFinalHom B hA X)).hom ≫
          (Space.relocalizeBaseHom B hA hS (formalBaseHom hS ξ.base hA)).hom :=
      congrArg (fun φ => φ.hom) heQ
    rw [h2] at h1
    replace h1 := (@isProper_comp_isIso_iff B S hS _ _ _ _ _ hiso).1 h1
    exact (isProper_relocalizeSpaceMap_iff (h := formalBaseHom hS ξ.base hA)
      (Space.toFinalHom B hA X)).1 h1
  exact ⟨X, Space.toFinalHom B hA X,
    (isFinitePresentation_iff_of_relocalizeSpace_iso eQ heQ).1 hprop.1,
    (isFlat_iff_of_relocalizeSpace_iso eQ heQ).1 hprop.2.1, hproper,
    relocalizeAdicFibreLevelIso Rz heQ,
    relocalizeAdicFibreLevelIso_hom_comp_properFlatLevelStructure Rz heQ,
    relocalizeHom_adicFibreSuccMap_comp_relocalizeAdicFibreLevelIso Rz heQ⟩

end AlgebraicGeometry

end
