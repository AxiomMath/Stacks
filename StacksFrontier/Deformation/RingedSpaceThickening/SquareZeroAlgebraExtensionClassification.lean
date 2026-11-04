module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClassVanishing
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtensionSeparation
public import StacksFrontier.Deformation.ToposThickening.SolutionPushoutRealization
import StacksCore.Tactic.StacksAttribute

/-!
# Square-zero extensions of `f⁻¹𝒪_S`-algebras are classified by `Ext¹(𝖭𝖫_{X/S}, 𝒢)` (Stacks 0GPZ)

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module.
**Stacks 0GPZ** says that the set of isomorphism classes of extensions
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square zero is canonically
bijective to `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`. This file proves it, for the bijection that sends an
extension to its class (`SquareZeroAlgebraExtension.extClass`, the construction of
**Stacks 0GQ0**).

Injectivity is `SquareZeroAlgebraExtension.classMap_injective` of
`StacksFrontier/Deformation/RingedSpaceThickening/SquareZeroAlgebraExtensionSeparation.lean`.
Surjectivity is the construction of the proof of **Stacks 08UC**: by **Stacks 08UB** a class
`ξ` is, along the comparison `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of a suitable family of generators
`α : ℰ ⟶ 𝒪_X`, the class of a homomorphism `δ : 𝒥/𝒥² ⟶ 𝒢`, and the pushout of
`0 ⟶ 𝒥 ⟶ f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X ⟶ 0` along `𝒥 ⟶ 𝒥/𝒥² ⟶ 𝒢` is an extension whose homomorphism
`𝒥/𝒥² ⟶ 𝒢` is `δ`, so whose class is `ξ`. The existence of a solution needed for the torsor
of **Stacks 08UC** to carry a bijection is then not needed separately: the bijection is the
class map itself.

## Main definitions

* `SquareZeroAlgebraExtension.presented`: an extension presented by a lift of a family of
  generators; its class is the class of the extension (`extClass_presented`).
* `SquareZeroAlgebraExtension.pushoutExtension`: the pushout extension attached to a
  homomorphism `δ : 𝒥/𝒥² ⟶ 𝒢`, with `conormalToIdeal_presentedPushout` computing its
  homomorphism and `extClass_pushoutExtension` its class.
* `SquareZeroAlgebraExtension.isomorphismClassesEquivExt`: **Stacks 0GPZ**, the bijection.

## Main results

* `SquareZeroAlgebraExtension.classMap_surjective`: every class is the class of an extension.
* `SquareZeroAlgebraExtension.isomorphismClassesEquivExt_apply` and
  `isomorphismClassesEquivExt_mk`: the bijection is the class map, `[𝒪_{X'}] ↦ extClass 𝒪_{X'}`.

## Implementation notes

The sign: the class of `δ` given by **Stacks 08UB**, the chain map `𝖭𝖫(α) ⟶ 𝒢[1]` which is `δ`
in degree `-1`, is minus its class for the distinguished triangle of the two-term complex
(`Stacks.SheafOfModules.presentationConormalExtClass_eq_neg`), which is the one the class map
uses; hence the pushout is taken along `-δ`.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal conormalClass)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheafCoefficientMap)
open Stacks.Sites.SqZeroPushout
open _root_.PresheafOfModules (sqZeroExtMk)
open _root_.Stacks.Sheaves.Differentials (sqZeroExtSheafInl)

universe u

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

namespace AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-! ### The extension presented by a lift of a family of generators -/

section Presented

variable (P : SquareZeroAlgebraExtension f G) {E : (Opens X.carrier)ᵒᵖ ⥤ Type u}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  (ℓ : E ⟶ P.generators) (hℓ : ℓ ≫ P.generatorsMap = α)

/-- An extension, presented over a family of generators `α : ℰ ⟶ 𝒪_X` by a lift
`ℓ : ℰ ⟶ 𝒪_{X'}` of `α`. -/
def presented : PresentedSquareZeroExtension f G E α where
  sheaf := P.sheaf
  base := P.base
  reduction := P.reduction
  base_comp_reduction := P.base_comp_reduction
  liftGen := ℓ
  liftGen_comp := hℓ
  ideal := P.ideal

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The class of an extension does not depend on the family of generators** used to present
it. -/
theorem extClass_presented
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f E α).hom] :
    (P.presented ℓ hℓ).extClass = P.extClass :=
  PresentedSquareZeroExtension.extClass_eq_of_hom (P.presented ℓ hℓ) P.toPresented ℓ hℓ (𝟙 _)
    (Category.id_comp _) (Category.comp_id _) rfl (fun _ _ ↦ rfl)

end Presented

/-! ### The pushout extension of a conormal homomorphism -/

section Pushout

variable (E : (Opens X.carrier)ᵒᵖ ⥤ Type u)
  (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom]
  (δ : (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    E α).X₁ ⟶ G)

/-- The restriction datum `g ↦ δ[g]` of a homomorphism `δ : 𝒥/𝒥² ⟶ 𝒢` on the kernel `𝒥` of
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`. -/
def conormalRestriction : IdealRestriction (generatorsPresentation f E α) G where
  app U :=
    { toFun := fun g ↦ δ.val.app U (conormalClass.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
        (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E)
        X.sheaf (freeAlgebraSheafCoefficientMap _ (inverseImageBaseRing f) E)
        (generatorsPresentation f E α) U g)
      map_zero' := (congrArg (δ.val.app U).hom
        (Stacks.Sites.Conormal.conormalClass_zero.{u, u, u, u} _ _ _ _ _ _ U)).trans
          (map_zero _)
      map_add' := fun g g' ↦ (congrArg (δ.val.app U).hom
        (Stacks.Sites.Conormal.conormalClass_add.{u, u, u, u} _ _ _ _ _ _ U g g')).trans
          (map_add _ _ _) }
  app_smul U r g := (congrArg (δ.val.app U).hom
    (Stacks.Sites.Conormal.conormalClass_smul.{u, u, u, u} _ _ _ _ _ _ U r g)).trans
      ((δ.val.app U).hom.map_smul _ _)
  app_map {_ V} i g := (congrArg (δ.val.app V).hom
    (Stacks.Sites.Conormal.conormalClass_map.{u, u, u, u} _ _ _ _ _ _ i g _ rfl)).trans
      (PresheafOfModules.naturality_apply δ.val i _)

/-- `𝒢`, read over `f⁻¹𝒪_S[ℰ]` through the presentation. -/
abbrev pushoutModule :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.underlyingRingSheaf.{u}
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E)) :=
  (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X.carrier)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (generatorsPresentation f E α))).obj G

/-- The datum of the pushout of `0 ⟶ 𝒥 ⟶ f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X ⟶ 0` along `𝒥 ⟶ 𝒥/𝒥² ⟶ 𝒢`. -/
abbrev pushoutDatum : PushoutData.{u} (generatorsPresentation f E α) (pushoutModule (G := G) E α) :=
  IdealRestriction.toPushoutData.{u} _ (conormalRestriction E α δ)

/-- The pushout `𝒪_{X'_δ}` of `0 ⟶ 𝒥 ⟶ f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X ⟶ 0` along `𝒥 ⟶ 𝒥/𝒥² ⟶ 𝒢`. -/
abbrev pushoutRing : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  pushoutSheaf.{u} (generatorsPresentation f E α) (pushoutModule (G := G) E α) (pushoutDatum E α δ)

/-- The inclusion of `𝒢` into the pushout, on sections, as a map into the kernel of the
projection. -/
def pushoutIdealHom (U : (Opens X.carrier)ᵒᵖ) :
    G.val.obj U →+ kernelIdeal (pushoutProj.{u} _ _ (pushoutDatum E α δ)).hom U where
  toFun n := ⟨pushoutInr.{u} _ _ (pushoutDatum E α δ) U n,
    pushoutProj_pushoutInr.{u} _ _ (pushoutDatum E α δ) U n⟩
  map_zero' := Subtype.ext (pushoutInr_zero.{u} _ _ (pushoutDatum E α δ) U)
  map_add' n m := Subtype.ext (pushoutInr_add.{u} _ _ (pushoutDatum E α δ) U n m)

/-- The inclusion of `𝒢` into the pushout, on sections, onto the kernel of the projection. -/
def pushoutIdealEquiv (U : (Opens X.carrier)ᵒᵖ) :
    G.val.obj U ≃+ kernelIdeal (pushoutProj.{u} _ _ (pushoutDatum E α δ)).hom U :=
  AddEquiv.ofBijective (pushoutIdealHom E α δ U)
    ⟨fun n m h ↦ pushoutInr_injective.{u} _ _ (pushoutDatum E α δ) U (congrArg Subtype.val h),
      fun s ↦ by
        obtain ⟨n, hn⟩ := (pushoutProj_app_eq_zero_iff.{u} _ _ (pushoutDatum E α δ) U s.1).1 s.2
        exact ⟨n, Subtype.ext hn⟩⟩

/-- The image of a section `n` of `𝒢` in the pushout is `pushoutInr n`. -/
theorem pushoutIdealEquiv_apply (U : (Opens X.carrier)ᵒᵖ) (n : G.val.obj U) :
    (pushoutIdealEquiv E α δ U n).1 = pushoutInr.{u} _ _ (pushoutDatum E α δ) U n :=
  rfl

/-- The inverse of `pushoutIdealEquiv` commutes with restriction of sections. -/
theorem pushoutIdealEquiv_symm_map {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V)
    (s : kernelIdeal (pushoutProj.{u} _ _ (pushoutDatum E α δ)).hom U) :
    (pushoutIdealEquiv E α δ V).symm ⟨((pushoutRing E α δ).obj.map i).hom s.1,
      Stacks.Sites.Conormal.map_kernel _ i s.2⟩ =
      G.val.map i ((pushoutIdealEquiv E α δ U).symm s) := by
  obtain ⟨n, rfl⟩ := (pushoutIdealEquiv E α δ U).surjective s
  rw [AddEquiv.symm_apply_apply]
  exact (AddEquiv.symm_apply_eq _).2 (Subtype.ext (pushoutInr_map.{u} _ _ (pushoutDatum E α δ) i n))

/-- `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'_δ}`, `x ↦ [(x, 0)]`. -/
abbrev pushoutLift :
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ⟶
      pushoutRing E α δ :=
  sqZeroExtSheafInl _ (pushoutModule (G := G) E α) ≫ pushoutMk.{u} _ _ (pushoutDatum E α δ)

/-- The composite `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'_δ} ⟶ 𝒪_X` is the presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`. -/
theorem pushoutLift_comp_pushoutProj :
    pushoutLift E α δ ≫ pushoutProj.{u} _ _ (pushoutDatum E α δ) =
      generatorsPresentation f E α :=
  (Category.assoc _ _ _).trans ((congrArg (sqZeroExtSheafInl _ (pushoutModule (G := G) E α) ≫ ·)
    (pushoutMk_comp_pushoutProj.{u} _ _ (pushoutDatum E α δ))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ generatorsPresentation f E α)
        (Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj.{u} _ _)).trans
          (Category.id_comp _))))

/-- **The pushout extension** `0 ⟶ 𝒢 ⟶ 𝒪_{X'_δ} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras. -/
def pushoutExtension : SquareZeroAlgebraExtension f G where
  sheaf := pushoutRing E α δ
  base := freeAlgebraSheafCoefficientMap _ (inverseImageBaseRing f) E ≫ pushoutLift E α δ
  reduction := pushoutProj.{u} _ _ (pushoutDatum E α δ)
  base_comp_reduction := (Category.assoc _ _ _).trans
    ((congrArg (freeAlgebraSheafCoefficientMap _ (inverseImageBaseRing f) E ≫ ·)
      (pushoutLift_comp_pushoutProj E α δ)).trans
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc _ _ _ E _ _))
  reduction_surjective := isLocallySurjective_pushoutProj.{u} _ _ (pushoutDatum E α δ)
  ideal :=
    { app U := (pushoutIdealEquiv E α δ U).symm.toAddMonoidHom
      app_smul U r s := by
        change (pushoutIdealEquiv E α δ U).symm (r • s) =
          _ • (pushoutIdealEquiv E α δ U).symm s
        obtain ⟨n, rfl⟩ := (pushoutIdealEquiv E α δ U).surjective s
        rw [AddEquiv.symm_apply_apply]
        exact (AddEquiv.symm_apply_eq _).2
          (Subtype.ext (mul_pushoutInr.{u} _ (pushoutDatum E α δ) U r n))
      app_map := pushoutIdealEquiv_symm_map E α δ }
  ideal_bijective U := (pushoutIdealEquiv E α δ U).symm.bijective

/-- The lift `ℰ ⟶ 𝒪_{X'_δ}` of the generators: the variables, sent to the pushout. -/
abbrev pushoutGenerators : E ⟶ (pushoutExtension E α δ).generators :=
  freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ≫
    Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
      CommRingCat.{u}).map (pushoutLift E α δ)) (forget CommRingCat.{u})

/-- The lift `pushoutGenerators` of the generators lies over `α : ℰ ⟶ 𝒪_X`. -/
theorem pushoutGenerators_comp :
    pushoutGenerators E α δ ≫ (pushoutExtension E α δ).generatorsMap = α := by
  refine Eq.trans ?_ (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf E
    (structureRingMap f) α)
  refine (Category.assoc _ _ _).trans (congrArg (freeAlgebraSheafVariable
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ≫ ·) ?_)
  refine (Functor.whiskerRight_comp _ _ _).symm.trans ?_
  exact congrArg (fun t : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) E ⟶ X.sheaf ↦ Functor.whiskerRight t.hom (forget CommRingCat.{u}))
    (pushoutLift_comp_pushoutProj E α δ)

/-- The pushout extension, presented over `α : ℰ ⟶ 𝒪_X` by the variables. -/
abbrev presentedPushout : PresentedSquareZeroExtension f G E α :=
  (pushoutExtension E α δ).presented (pushoutGenerators E α δ) (pushoutGenerators_comp E α δ)

/-- The map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'_δ}` induced by the presentation `presentedPushout` is
`pushoutLift`, `x ↦ [(x, 0)]`. -/
theorem lift_presentedPushout : (presentedPushout E α δ).lift = pushoutLift E α δ := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext _ _ _ E ?_ ?_
  · exact Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc _ _ _ E _ _
  · exact Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc _ _ _ E _ _

/-- **The homomorphism `𝒥/𝒥² ⟶ 𝒢` of the pushout extension is `δ`**: on the kernel `𝒥` the
lift of the generators is `x ↦ [(x, 0)] = [(0, δ[x])]`. -/
theorem conormalToIdeal_presentedPushout : (presentedPushout E α δ).conormalToIdeal = δ := by
  refine Stacks.Sites.Conormal.conormal_hom_ext.{u, u, u, u} (generatorsPresentation f E α) G
    (fun U x ↦ ?_)
  refine (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule.{u, u, u, u} _ G _ U x).trans ?_
  rw [PresentedSquareZeroExtension.idealRestriction_app]
  have hL : ((presentedPushout E α δ).lift.hom.app U).hom x.1 =
      pushoutInr.{u} _ _ (pushoutDatum E α δ) U ((pushoutDatum E α δ).app U x) :=
    (congrArg (fun t : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) E ⟶ pushoutRing E α δ ↦ (t.hom.app U).hom x.1)
        (lift_presentedPushout E α δ)).trans
      (pushoutMk_inl.{u} _ _ (pushoutDatum E α δ) U x)
  refine (congrArg (pushoutIdealEquiv E α δ U).symm (Subtype.ext hL :
    (⟨_, _⟩ : kernelIdeal (pushoutProj.{u} _ _ (pushoutDatum E α δ)).hom U) =
      pushoutIdealEquiv E α δ U ((pushoutDatum E α δ).app U x))).trans ?_
  exact (AddEquiv.symm_apply_apply _ _)

attribute [local instance 10000] HasDerivedCategory.standard

/-- The class of the pushout extension of `δ` is the class of `δ` for the two-term complex,
transported along the comparison `𝖭𝖫(α) ≅ 𝖭𝖫_{X/S}`. -/
theorem extClass_pushoutExtension :
    (pushoutExtension E α δ).extClass =
      (PresentedSquareZeroExtension.naiveCotangentIso f E α).inv ≫
        (PresentedSquareZeroExtension.twoTerm f E α).conormalExtClass G δ := by
  refine (extClass_presented (pushoutExtension E α δ) (pushoutGenerators E α δ)
    (pushoutGenerators_comp E α δ)).symm.trans ?_
  exact congrArg (fun t ↦ (PresentedSquareZeroExtension.naiveCotangentIso f E α).inv ≫
    (PresentedSquareZeroExtension.twoTerm f E α).conormalExtClass G t)
      (conormalToIdeal_presentedPushout E α δ)

end Pushout

/-! ### Surjectivity, and the bijection -/

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Every class is the class of an extension.** By **Stacks 08UB** a class `ξ` becomes, along
the comparison `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of a suitable family of generators, the class of a homomorphism
`δ₀ : 𝒥/𝒥² ⟶ 𝒢`; the pushout extension of `-δ₀` (the sign being that between the two
descriptions of the class) has class `ξ`. -/
theorem exists_extClass_eq (ξ : extOneNaiveCotangent f G) :
    ∃ P : SquareZeroAlgebraExtension f G, P.extClass = ξ := by
  obtain ⟨E, α, hsurj, δ₀, hδ₀⟩ :=
    Stacks.SheafOfModules.exists_presentation_conormalExtClass
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
      (structureRingMap f) G ξ
  let := hsurj
  refine ⟨pushoutExtension E.obj α (-δ₀), ?_⟩
  have hneg : (PresentedSquareZeroExtension.twoTerm f E.obj α).conormalExtClass G (-δ₀) =
      -(PresentedSquareZeroExtension.twoTerm f E.obj α).conormalExtClass G δ₀ := by
    have h0 := AlgebraicGeometry.RingedSpaceThickening.conormalExtClass_sub
      (PresentedSquareZeroExtension.twoTerm f E.obj α) G 0 δ₀
    have hz : (PresentedSquareZeroExtension.twoTerm f E.obj α).conormalExtClass G 0 = 0 := by
      rw [NaiveCotangentTwoTerm.conormalExtClass, Functor.map_zero, Functor.map_zero,
        Limits.comp_zero]
    refine (congrArg ((PresentedSquareZeroExtension.twoTerm f E.obj α).conormalExtClass G)
      (zero_sub δ₀).symm).trans (h0.trans ?_)
    rw [hz, zero_sub]
  have h2 := hδ₀.trans (Stacks.SheafOfModules.presentationConormalExtClass_eq_neg _ _ _ _ _ _ G δ₀)
  refine (extClass_pushoutExtension E.obj α (-δ₀)).trans ?_
  refine (congrArg ((PresentedSquareZeroExtension.naiveCotangentIso f E.obj α).inv ≫ ·)
    (hneg.trans h2.symm)).trans ?_
  exact Iso.inv_hom_id_assoc (PresentedSquareZeroExtension.naiveCotangentIso f E.obj α) ξ

/-- **The class map of Stacks 0GPZ is surjective.** -/
theorem classMap_surjective : Function.Surjective (classMap f G) := fun ξ ↦
  (exists_extClass_eq ξ).elim fun P hP ↦ ⟨Quotient.mk _ P, hP⟩

variable (f G) in
/-- Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. The set
of isomorphism classes of extensions `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras with `𝒢` an
ideal of square zero is canonically bijective to `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.

The bijection is the class map of **Stacks 0GQ0**: an extension goes to the class of the
homomorphism `𝒥/𝒥² ⟶ 𝒢` of the presentation of `𝒪_X` by the sheaf of sets underlying
`𝒪_{X'}`, read through the quasi-isomorphism of **Stacks 08TL**
(`isomorphismClassesEquivExt_apply`). -/
@[stacks 0GPZ]
def isomorphismClassesEquivExt : IsomorphismClasses f G ≃ extOneNaiveCotangent f G :=
  Equiv.ofBijective (classMap f G) ⟨classMap_injective, classMap_surjective⟩

/-- The bijection of **Stacks 0GPZ** is the class map: it sends the isomorphism class of an
extension `𝒪_{X'}` to its class `SquareZeroAlgebraExtension.extClass`. -/
theorem isomorphismClassesEquivExt_apply (p : IsomorphismClasses f G) :
    isomorphismClassesEquivExt f G p = classMap f G p :=
  rfl

/-- The bijection `isomorphismClassesEquivExt` sends the isomorphism class of an extension
`𝒪_{X'}` to its class `SquareZeroAlgebraExtension.extClass`. -/
@[simp]
theorem isomorphismClassesEquivExt_mk (P : SquareZeroAlgebraExtension f G) :
    isomorphismClassesEquivExt f G (Quotient.mk _ P) = P.extClass :=
  rfl

end AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

end
