module

public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtensionClassification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bijection of Stacks 0GPZ is the canonical one

The proof of **Stacks 0GPZ** applies the torsor statement of **Stacks 08UC** to the problem whose
base row is `0 ⟶ 0 ⟶ 𝒪_S ⟶ 𝒪_S ⟶ 0`, with base point the trivial extension `𝒪_X ⊕ 𝒢`. This file
ties `SquareZeroAlgebraExtension.isomorphismClassesEquivExt` to that description.

## Main definitions

* `SquareZeroAlgebraExtension.trivialExtension`: the extension `𝒪_X ⊕ 𝒢`.

## Main results

* `isomorphismClassesEquivExt_trivialExtension`: the bijection sends `𝒪_X ⊕ 𝒢` to `0`.
* `extClass_sub_extClass`: the difference of the classes of two extensions is the obstruction
  class of the pair (Step 1 of the proof of **Stacks 08U8**), the class of the difference of the
  two lifts of `ℰ = 𝒪'₁ ×_{𝒪_X} 𝒪'₂`; with `nonempty_iso_iff_obstruction_eq_zero` this is the
  torsor of **Stacks 08UC**.
* `isomorphismClassesEquivExt_mk_eq_obstruction`: the bijection is the obstruction class against
  the base point `𝒪_X ⊕ 𝒢`.
* `isomorphismClassesEquivExt_symm_apply`: the inverse is the pushout construction of the proof
  of **Stacks 08UC**.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf)
open _root_.PresheafOfModules (sqZeroExtMk sqZeroExtFst sqZeroExtSnd sqZeroExt_ext)
open _root_.Stacks.Sheaves.Differentials (sqZeroExtSheaf sqZeroExtSheafInl sqZeroExtSheafProj)

universe u

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

namespace AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-! ### The trivial extension `𝒪_X ⊕ 𝒢` -/

variable (G) in
/-- `𝒢`, as a module over the sheaf of rings underlying `𝒪_X`. -/
abbrev trivialModule : SheafOfModules.{u} (Stacks.Sheaves.Differentials.underlyingRingSheaf.{u}
    (X.sheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})) := G

variable (f G) in
/-- **The trivial extension** `0 ⟶ 𝒢 ⟶ 𝒪_X ⊕ 𝒢 ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras, with `𝒢` an
ideal of square zero. -/
@[ega "0 18.2.3" "partial"]
def trivialExtension : SquareZeroAlgebraExtension f G where
  sheaf := sqZeroExtSheaf.{u} _ (trivialModule G)
  base := structureRingMap f ≫ sqZeroExtSheafInl.{u} _ (trivialModule G)
  reduction := sqZeroExtSheafProj.{u} _ (trivialModule G)
  base_comp_reduction := (Category.assoc _ _ _).trans
    ((congrArg (structureRingMap f ≫ ·)
      (Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj.{u} _ _)).trans
        (Category.comp_id _))
  reduction_surjective := by
    refine Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (f₁ := (sqZeroExtSheafInl.{u} _ (trivialModule G)).hom) (f₃ := 𝟙 _) ?_
    exact congrArg (fun t ↦ t.hom)
      (Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj.{u} _
        (trivialModule G))
  ideal :=
    { app U :=
        { toFun := fun x ↦ sqZeroExtSnd x.1
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      app_smul U r x := by
        change sqZeroExtSnd (r * x.1) = sqZeroExtFst r • sqZeroExtSnd x.1
        exact (PresheafOfModules.sqZeroExtSnd_mul _ _).trans ((congrArg (_ + ·)
          ((congrArg (· • sqZeroExtSnd r) (x.2 : sqZeroExtFst x.1 = 0)).trans
            (zero_smul _ _))).trans (add_zero _))
      app_map i x := rfl }
  ideal_bijective U := by
    refine ⟨fun x y h ↦ Subtype.ext (sqZeroExt_ext ((x.2 : sqZeroExtFst x.1 = 0).trans
      (y.2 : sqZeroExtFst y.1 = 0).symm) h), fun m ↦ ⟨⟨sqZeroExtMk 0 m, rfl⟩, rfl⟩⟩

/-- The lift `𝒪_X ⟶ 𝒪_X ⊕ 𝒢`, `b ↦ (b, 0)`, of the canonical family of generators. -/
abbrev trivialGenerators : underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf ⟶
    (trivialExtension f G).generators :=
  Functor.whiskerRight (sqZeroExtSheafInl.{u} _ (trivialModule G)).hom (forget CommRingCat.{u})

/-- The lift `trivialGenerators` composed with the reduction `𝒪_X ⊕ 𝒢 ⟶ 𝒪_X` is the identity. -/
theorem trivialGenerators_comp :
    trivialGenerators (f := f) (G := G) ≫ (trivialExtension f G).generatorsMap = 𝟙 _ :=
  (Functor.whiskerRight_comp _ _ _).symm.trans ((congrArg (fun t ↦ Functor.whiskerRight
    (t : X.sheaf ⟶ X.sheaf).hom (forget CommRingCat.{u}))
      (Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj.{u} _
        (trivialModule G))).trans (Functor.whiskerRight_id' _))

/-- The presentation `f⁻¹𝒪_S[𝒪_X] ⟶ 𝒪_X` by the canonical family of generators is locally
surjective. -/
instance isLocallySurjective_canonicalPresentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f (underlyingPresheaf (Opens.grothendieckTopology X.carrier)
        X.sheaf) (𝟙 _)).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

/-- The trivial extension, presented by the canonical family of generators of `𝒪_X`. -/
abbrev presentedTrivial :
    PresentedSquareZeroExtension f G (underlyingPresheaf (Opens.grothendieckTopology X.carrier)
      X.sheaf) (𝟙 _) :=
  (trivialExtension f G).presented trivialGenerators trivialGenerators_comp

/-- The lift `f⁻¹𝒪_S[𝒪_X] ⟶ 𝒪_X ⊕ 𝒢` of `presentedTrivial` is the presentation followed by the
inclusion `b ↦ (b, 0)`. -/
theorem lift_presentedTrivial : (presentedTrivial (f := f) (G := G)).lift =
    generatorsPresentation f _ (𝟙 _) ≫ sqZeroExtSheafInl.{u} _ (trivialModule G) := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · refine (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ sqZeroExtSheafInl.{u} _ (trivialModule G))
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _).symm
  · have hw : Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
          CommRingCat.{u}).map (generatorsPresentation f _ (𝟙 _) ≫
            sqZeroExtSheafInl.{u} _ (trivialModule G))) (forget CommRingCat.{u}) =
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
          CommRingCat.{u}).map (generatorsPresentation f _ (𝟙 _))) (forget CommRingCat.{u}) ≫
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
          CommRingCat.{u}).map (sqZeroExtSheafInl.{u} _ (trivialModule G)))
            (forget CommRingCat.{u}) :=
      (congrArg (Functor.whiskerRight · (forget CommRingCat.{u})) (Functor.map_comp _ _ _)).trans
        (Functor.whiskerRight_comp _ _ _)
    refine (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (_ ≫ ·) hw).symm
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans (Category.id_comp _).symm (congrArg (· ≫ _) ?_)
    exact (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (structureRingMap f)
      (𝟙 _)).symm

/-- The homomorphism `𝒥/𝒥² ⟶ 𝒢` of the trivial extension, presented by the canonical family of
generators, vanishes: the lift `x ↦ (x̄, 0)` kills the kernel of the presentation. -/
theorem conormalToIdeal_presentedTrivial :
    (presentedTrivial (f := f) (G := G)).conormalToIdeal = 0 := by
  refine Stacks.Sites.Conormal.conormal_hom_ext.{u, u, u, u} _ G (fun U x ↦ ?_)
  refine (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule.{u, u, u, u} _ G _ U x).trans ?_
  refine Eq.trans ?_ (show (0 : G.val.obj U) = _ from rfl)
  rw [PresentedSquareZeroExtension.idealRestriction_app]
  change sqZeroExtSnd (((presentedTrivial (f := f) (G := G)).lift.hom.app U).hom x.1) = 0
  rw [lift_presentedTrivial]
  rfl

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The class of the trivial extension `𝒪_X ⊕ 𝒢` is zero.** -/
theorem extClass_trivialExtension : (trivialExtension f G).extClass = 0 := by
  refine (extClass_presented (trivialExtension f G) trivialGenerators
    trivialGenerators_comp).symm.trans ?_
  have hz : (PresentedSquareZeroExtension.twoTerm f (underlyingPresheaf
      (Opens.grothendieckTopology X.carrier) X.sheaf) (𝟙 _)).conormalExtClass G 0 = 0 := by
    rw [NaiveCotangentTwoTerm.conormalExtClass, Functor.map_zero, Functor.map_zero,
      Limits.comp_zero]
  exact (congrArg (fun t ↦ (PresentedSquareZeroExtension.naiveCotangentIso f _ _).inv ≫
    (PresentedSquareZeroExtension.twoTerm f _ _).conormalExtClass G t)
      conormalToIdeal_presentedTrivial).trans
    ((congrArg ((PresentedSquareZeroExtension.naiveCotangentIso f _ _).inv ≫ ·) hz).trans
      Limits.comp_zero)

/-- **The bijection of Stacks 0GPZ sends the trivial extension `𝒪_X ⊕ 𝒢` to `0`.** -/
theorem isomorphismClassesEquivExt_trivialExtension :
    isomorphismClassesEquivExt f G (Quotient.mk _ (trivialExtension f G)) = 0 :=
  extClass_trivialExtension

/-! ### The difference of two classes is the obstruction class of the pair -/

/-- **The difference of the classes of two extensions is the obstruction class of the pair**
(Step 1 of the proof of Stacks 08U8, as used for Stacks 08UC): present both extensions by
`ℰ = 𝒪'₁ ×_{𝒪_X} 𝒪'₂`; the classes differ by the class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` of the
difference `φ₁|_𝒥 - φ₂|_𝒥 : 𝒥/𝒥² ⟶ 𝒢` of the two lifts. -/
theorem extClass_sub_extClass (P Q : SquareZeroAlgebraExtension f G) :
    P.extClass - Q.extClass =
      (PresentedSquareZeroExtension.naiveCotangentIso f (pairGenerators P Q) (pairMap P Q)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (pairGenerators P Q) (pairMap P Q)).conormalExtClass
          G (PresentedSquareZeroExtension.obstruction (presentedFst P Q) (presentedSnd P Q)) := by
  rw [← extClass_presentedFst P Q, ← extClass_presentedSnd P Q]
  exact PresentedSquareZeroExtension.extClass_sub_extClass _ _

/-- **The bijection of Stacks 0GPZ is the one of the source's proof**: the torsor of
Stacks 08UC with base point the trivial extension `𝒪_X ⊕ 𝒢`. The class of an extension `𝒪'` is
the obstruction class of the pair `(𝒪', 𝒪_X ⊕ 𝒢)`: the class of the difference of the lifts of
`ℰ = 𝒪' ×_{𝒪_X} (𝒪_X ⊕ 𝒢)` into `𝒪'` and into `𝒪_X ⊕ 𝒢`, restricted to the kernel of
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`. -/
theorem isomorphismClassesEquivExt_mk_eq_obstruction (P : SquareZeroAlgebraExtension f G) :
    isomorphismClassesEquivExt f G (Quotient.mk _ P) =
      (PresentedSquareZeroExtension.naiveCotangentIso f (pairGenerators P (trivialExtension f G))
          (pairMap P (trivialExtension f G))).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (pairGenerators P (trivialExtension f G))
          (pairMap P (trivialExtension f G))).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (presentedFst P (trivialExtension f G))
            (presentedSnd P (trivialExtension f G))) := by
  rw [isomorphismClassesEquivExt_mk, ← extClass_sub_extClass, extClass_trivialExtension,
    sub_zero]

/-- Two extensions are isomorphic exactly when the obstruction class of the pair vanishes. -/
theorem nonempty_iso_iff_obstruction_eq_zero (P Q : SquareZeroAlgebraExtension f G) :
    Nonempty (P ≅ Q) ↔
      (PresentedSquareZeroExtension.naiveCotangentIso f (pairGenerators P Q) (pairMap P Q)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (pairGenerators P Q) (pairMap P Q)).conormalExtClass
          G (PresentedSquareZeroExtension.obstruction (presentedFst P Q) (presentedSnd P Q)) =
        0 := by
  rw [← extClass_sub_extClass]
  refine Iff.trans ?_ sub_eq_zero.symm
  constructor
  · rintro ⟨e⟩
    exact extClass_eq_of_hom e.hom
  · intro h
    obtain ⟨φ⟩ := nonempty_hom_of_extClass_eq h
    exact ⟨isoOfHom φ⟩

/-! ### The inverse is the pushout construction -/

/-- **The inverse of the bijection of Stacks 0GPZ is the pushout construction** of the proof of
Stacks 08UC at the base point `𝒪_X ⊕ 𝒢`: if `ξ` is, along the comparison `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of
a family of generators `α`, the class of `δ : 𝒥/𝒥² ⟶ 𝒢` (as Stacks 08UB provides), then `ξ`
corresponds to the pushout of `0 ⟶ 𝒥 ⟶ f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X ⟶ 0` along `𝒥 ⟶ 𝒥/𝒥² ⟶ 𝒢`. (For the base
point `𝒪_X ⊕ 𝒢` and the lift `e ↦ (α e, 0)` the restriction `φ|_𝒥` of the source vanishes, so
the source's `ψ = φ|_𝒥 + δ` is `δ`.) -/
theorem isomorphismClassesEquivExt_symm_apply (E : (Opens X.carrier)ᵒᵖ ⥤ Type u)
    (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f E α).hom]
    (δ : (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
      E α).X₁ ⟶ G) (ξ : extOneNaiveCotangent f G)
    (hξ : (PresentedSquareZeroExtension.naiveCotangentIso f E α).inv ≫
      (PresentedSquareZeroExtension.twoTerm f E α).conormalExtClass G δ = ξ) :
    (isomorphismClassesEquivExt f G).symm ξ = Quotient.mk _ (pushoutExtension E α δ) :=
  (Equiv.symm_apply_eq _).2 ((extClass_pushoutExtension E α δ).trans hξ).symm

end AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

end
