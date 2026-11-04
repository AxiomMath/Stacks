module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentation
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble

/-!
# The extension class of a square-zero extension, and the cocycle of two of them

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. Fix a
family of generators `α : ℰ ⟶ 𝒪_X` whose polynomial presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is
surjective, and write `𝒥` for its kernel, so that `𝖭𝖫(α) = (𝒥/𝒥² ⟶ Ω)`.

A `PresentedSquareZeroExtension` — a square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of
`f⁻¹𝒪_S`-algebras *together with a lift* `α' : ℰ ⟶ 𝒪_{X'}` of `α`, with its homomorphism
`𝒥/𝒥² ⟶ 𝒢` — determines a class in `Ext¹_{𝒪_X}(𝖭𝖫(α), 𝒢)`, hence, through the
quasi-isomorphism `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of Stacks 08TL, a class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.
For two extensions over the same presentation the difference of their classes is the class of
the difference of their homomorphisms `𝒥/𝒥² ⟶ 𝒢`, and these differences satisfy the cocycle
identity for three extensions.

## Main definitions

* `PresentedSquareZeroExtension.twoTerm`: the two-term complex `𝖭𝖫(α) = (𝒥/𝒥² ⟶ Ω)` of the
  prescribed presentation, with the distinguished triangle of its two-term structure.
* `PresentedSquareZeroExtension.presentedExtClass` and
  `PresentedSquareZeroExtension.extClass`: the class of the extension in
  `Ext¹_{𝒪_X}(𝖭𝖫(α), 𝒢)` and its transport to `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.
* `PresentedSquareZeroExtension.obstruction`: the difference homomorphism `𝒥/𝒥² ⟶ 𝒢` of two
  extensions over the one presentation.

## Main results

* `PresentedSquareZeroExtension.presentedExtClass_sub_presentedExtClass` and
  `PresentedSquareZeroExtension.extClass_sub_extClass`: the difference of the classes of two
  extensions over one presentation is the class of their difference homomorphism.
* `PresentedSquareZeroExtension.conormalExtClass_obstruction_add` and
  `PresentedSquareZeroExtension.extClass_obstruction_add`: the cocycle identity for three
  extensions over one presentation.
* `PresentedSquareZeroExtension.extClass_eq_extClass_iff`: two extensions over one presentation
  have the same class exactly when the obstruction class of their difference homomorphism
  vanishes.
* `Stacks.Sites.Conormal.conormalDesc_sub_eq`: the descent of a restriction datum to the
  conormal sheaf is additive.

## References

* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction conormalDesc conormalDifference conormalSheaf
  conormalPresheaf conormal_hom_ext conormalDesc_toAssociatedModule
  conormalDifference_add_conormalDifference kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheaf_hom_ext freeAlgebraSheafCoefficientMap_comp_desc
  freeAlgebraSheafVariable_comp_desc)

universe v u w z v' u'

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
  (G : SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
  [Presheaf.IsLocallySurjective J φ.hom]

/-- The descent of a restriction datum to the conormal sheaf is additive. -/
theorem conormalDesc_sub_eq (ρ σ : IdealRestriction φ G) :
    conormalDesc.{v, u, w, z} φ G (IdealRestriction.sub ρ σ) =
      conormalDesc.{v, u, w, z} φ G ρ - conormalDesc.{v, u, w, z} φ G σ := by
  refine conormal_hom_ext.{v, u, w, z} φ G (fun X x ↦ ?_)
  show ((conormalDesc.{v, u, w, z} φ G (IdealRestriction.sub ρ σ)).val.app X) _ =
    ((conormalDesc.{v, u, w, z} φ G ρ).val.app X) _ -
      ((conormalDesc.{v, u, w, z} φ G σ).val.app X) _
  rw [conormalDesc_toAssociatedModule, conormalDesc_toAssociatedModule,
    conormalDesc_toAssociatedModule, IdealRestriction.sub_app]

/-- The morphism attached to a pair of restriction data is the difference of the two
descents. -/
theorem conormalDifference_eq_sub (ρ σ : IdealRestriction φ G) :
    conormalDifference.{v, u, w, z} φ G ρ σ =
      conormalDesc.{v, u, w, z} φ G ρ - conormalDesc.{v, u, w, z} φ G σ :=
  conormalDesc_sub_eq.{v, u, w, z} φ G ρ σ

end Stacks.Sites.Conormal

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Subtraction of conormal Ext classes -/

section ExtSub

variable {M : Type u} [Category.{v} M] [Preadditive M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] {single : M ⥤ D} [single.Additive]

/-- The class in `Ext¹(NL(α), 𝒢)` of a homomorphism out of the conormal module is additive in
that homomorphism, in subtracted form. -/
theorem conormalExtClass_sub (P : NaiveCotangentTwoTerm single) (G : M)
    (f g : P.conormal ⟶ G) :
    P.conormalExtClass G (f - g) = P.conormalExtClass G f - P.conormalExtClass G g := by
  simp only [NaiveCotangentTwoTerm.conormalExtClass, single.map_sub,
    (shiftFunctor D (1 : ℤ)).map_sub, Preadditive.comp_sub]

end ExtSub

variable {X S : RingedSpace.{u, u}}

namespace PresentedSquareZeroExtension

variable {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {E : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  (P : PresentedSquareZeroExtension f G E α)

section Conormal

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
  (generatorsPresentation f E α).hom]

/-- The difference homomorphism `𝒥/𝒥² ⟶ 𝒢` of two square-zero extensions over the one
presentation: the descent of the difference of their restriction data. -/
def obstruction (P₁ P₂ : PresentedSquareZeroExtension f G E α) :
    conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E)
      X.sheaf (generatorsPresentation f E α) ⟶ G :=
  conormalDifference.{u, u, u, u} (generatorsPresentation f E α) G
    P₁.idealRestriction P₂.idealRestriction

/-- The difference homomorphism is the difference of the two homomorphisms. -/
theorem obstruction_eq_sub (P₁ P₂ : PresentedSquareZeroExtension f G E α) :
    obstruction P₁ P₂ = P₁.conormalToIdeal - P₂.conormalToIdeal :=
  Stacks.Sites.Conormal.conormalDesc_sub_eq.{u, u, u, u} (generatorsPresentation f E α) G
    P₁.idealRestriction P₂.idealRestriction

/-- The cocycle identity for the difference homomorphisms of three square-zero extensions over
the one presentation. -/
theorem obstruction_add_obstruction (P₁ P₂ P₃ : PresentedSquareZeroExtension f G E α) :
    obstruction P₁ P₂ + obstruction P₂ P₃ = obstruction P₁ P₃ :=
  conormalDifference_add_conormalDifference.{u, u, u, u} (generatorsPresentation f E α) G
    P₁.idealRestriction P₂.idealRestriction P₃.idealRestriction

end Conormal

/-! ### The classes in `Ext¹` -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (f) (E) (α) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
  (generatorsPresentation f E α).hom]

/-- `𝖭𝖫(α) = (𝒥/𝒥² ⟶ Ω)`, the two-term naive cotangent complex of the prescribed presentation,
with the distinguished triangle of its two-term structure. The underlying object is the image
in `D(𝒪_X)` of the complex `presentationComplex f E α` itself. -/
abbrev twoTerm :
    NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) 0) :=
  NaiveCotangentTwoTerm.ofDoubleNegOne
    (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
      (structureRingMap f) E α).f

/-- `𝒢⟦1⟧`, the target of a degree one Ext class with values in `𝒢`. -/
abbrev shiftedSingleObj (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)) :=
  ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)) 0).obj G)⟦(1 : ℤ)⟧

variable {f} {E} {α}

/-- The class in `Ext¹_{𝒪_X}(𝖭𝖫(α), 𝒢)` that `α'` determines: the class of the homomorphism
`𝒥/𝒥² ⟶ 𝒢`. -/
def presentedExtClass (P : PresentedSquareZeroExtension f G E α) :
    (twoTerm f E α).obj ⟶ shiftedSingleObj G :=
  (twoTerm f E α).conormalExtClass G P.conormalToIdeal

/-- The difference of the classes of two square-zero extensions over one presentation is the
class of their difference homomorphism. -/
theorem presentedExtClass_sub_presentedExtClass
    (P₁ P₂ : PresentedSquareZeroExtension f G E α) :
    P₁.presentedExtClass - P₂.presentedExtClass =
      (twoTerm f E α).conormalExtClass G (obstruction P₁ P₂) :=
  ((congrArg ((twoTerm f E α).conormalExtClass G) (obstruction_eq_sub P₁ P₂)).trans
    (conormalExtClass_sub (twoTerm f E α) G P₁.conormalToIdeal P₂.conormalToIdeal)).symm

/-- The cocycle identity at the level of `Ext¹` classes for three square-zero extensions over
one presentation. -/
theorem conormalExtClass_obstruction_add (P₁ P₂ P₃ : PresentedSquareZeroExtension f G E α) :
    (twoTerm f E α).conormalExtClass G (obstruction P₁ P₂) +
        (twoTerm f E α).conormalExtClass G (obstruction P₂ P₃) =
      (twoTerm f E α).conormalExtClass G (obstruction P₁ P₃) :=
  (congrArg₂ (· + ·) (presentedExtClass_sub_presentedExtClass P₁ P₂).symm
      (presentedExtClass_sub_presentedExtClass P₂ P₃).symm).trans
    ((sub_add_sub_cancel P₁.presentedExtClass P₂.presentedExtClass
      P₃.presentedExtClass).trans (presentedExtClass_sub_presentedExtClass P₁ P₃))

/-- The class of a square-zero extension in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`: the class of the
homomorphism `𝒥/𝒥² ⟶ 𝒢` determined by `α'`, read in the group of the naive cotangent complex
of `𝒪_X` over `f⁻¹𝒪_S` through the quasi-isomorphism of Stacks 08TL. -/
def extClass (P : PresentedSquareZeroExtension f G E α) :
    relativeObj f ⟶ shiftedSingleObj G :=
  (naiveCotangentIso f E α).inv ≫ P.presentedExtClass

/-- The difference of the classes in `Ext¹(𝖭𝖫_{X/S}, 𝒢)` of two square-zero extensions over
one presentation is the class of their difference homomorphism. -/
theorem extClass_sub_extClass (P₁ P₂ : PresentedSquareZeroExtension f G E α) :
    P₁.extClass - P₂.extClass =
      (naiveCotangentIso f E α).inv ≫
        (twoTerm f E α).conormalExtClass G (obstruction P₁ P₂) :=
  (Preadditive.comp_sub _ _ _).symm.trans
    ((naiveCotangentIso f E α).inv ≫= presentedExtClass_sub_presentedExtClass P₁ P₂)

/-- The cocycle identity in `Ext¹(𝖭𝖫_{X/S}, 𝒢)`: the transported classes of the difference
homomorphisms of three square-zero extensions over one presentation telescope. -/
theorem extClass_obstruction_add (P₁ P₂ P₃ : PresentedSquareZeroExtension f G E α) :
    ((naiveCotangentIso f E α).inv ≫
          (twoTerm f E α).conormalExtClass G (obstruction P₁ P₂)) +
        ((naiveCotangentIso f E α).inv ≫
          (twoTerm f E α).conormalExtClass G (obstruction P₂ P₃)) =
      (naiveCotangentIso f E α).inv ≫
        (twoTerm f E α).conormalExtClass G (obstruction P₁ P₃) :=
  (Preadditive.comp_add _ _ _ _ _ _).symm.trans
    ((naiveCotangentIso f E α).inv ≫= conormalExtClass_obstruction_add P₁ P₂ P₃)

/-- Two square-zero extensions over one presentation have the same class in
`Ext¹(𝖭𝖫_{X/S}, 𝒢)` exactly when the obstruction class of their difference homomorphism
vanishes. -/
theorem extClass_eq_extClass_iff (P₁ P₂ : PresentedSquareZeroExtension f G E α) :
    P₁.extClass = P₂.extClass ↔
      (twoTerm f E α).conormalExtClass G (obstruction P₁ P₂) = 0 :=
  ⟨fun h ↦ (cancel_epi (naiveCotangentIso f E α).inv).1
      ((extClass_sub_extClass P₁ P₂).symm.trans ((sub_eq_zero.2 h).trans comp_zero.symm)),
    fun h ↦ sub_eq_zero.1 ((extClass_sub_extClass P₁ P₂).trans
      (((naiveCotangentIso f E α).inv ≫= h).trans comp_zero))⟩

end Derived

end PresentedSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening

end
