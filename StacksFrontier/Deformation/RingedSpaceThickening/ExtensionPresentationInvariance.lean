module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentationClass
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentPresentationExtClass

/-!
# The class of a square-zero extension does not depend on the presentation

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, `𝒢` an `𝒪_X`-module, and let
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` be a square-zero extension of `f⁻¹𝒪_S`-algebras. A
`PresentedSquareZeroExtension` presents such an extension by a family of generators
`α : ℰ ⟶ 𝒪_X` together with a lift `α' : ℰ ⟶ 𝒪_{X'}`, and attaches to that datum a class
`PresentedSquareZeroExtension.extClass` in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.

This file proves that the class is unchanged when the presentation is refined: a morphism
`u : ℰ₁ ⟶ ℰ₂` of families of generators compatible with the lifts carries the class of the
second presentation to the class of the first. The target group does not mention `ℰ`, the naive
cotangent complex `𝖭𝖫_{X/S}` being independent of it, so this is an honest equation between two
elements of one group and not a compatibility up to an identification.

## Main results

* `Stacks.Sites.Conormal.conormalSheafMapOfFac_comp_conormalDesc`: a restriction datum which is
  the pullback of another along a factorisation of presentations has for descent the map of
  conormal sheaves followed by the other descent.
* `AlgebraicGeometry.RingedSpaceThickening.PresentedSquareZeroExtension.freeAlgebraMap_comp_lift`:
  compatibility of the lifts `α'` with `u` passes to the induced maps `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}`.
* `...PresentedSquareZeroExtension.idealRestriction_pullback`: the restriction datum of the
  second presentation, read through `u`, is the restriction datum of the first — which through
  `Stacks.Sites.Conormal.conormalSheafMapOfFac_comp_conormalDesc` says that the maps
  `𝒥/𝒥² ⟶ 𝒢` of the two presentations agree.
* `...PresentedSquareZeroExtension.presentedExtClass_eq`: the two classes in `Ext¹(𝖭𝖫(α), 𝒢)`
  agree through the chain map `𝖭𝖫(α₁) ⟶ 𝖭𝖫(α₂)` of the two presentations.
* `...PresentedSquareZeroExtension.extClass_eq_extClass`: **the class in `Ext¹(𝖭𝖫_{X/S}, 𝒢)`
  does not depend on the presentation.**
* `...PresentedSquareZeroExtension.extClass_sub_extClass_of_map` and
  `...PresentedSquareZeroExtension.extClass_eq_extClass_iff_of_map`: the difference and
  separation statements of
  `StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationClass.lean`, carried over
  to a pair of extensions that do not share a presentation.

## Implementation notes

The compatibility of two presentations of one extension is not packaged as a structure; it is
the four hypotheses of `PresentedSquareZeroExtension.extClass_eq_extClass`, namely that `u` is a
morphism of families of generators (`hu`), that the comparison `θ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of the
two extended structure sheaves lies over `𝒪_X` (`hred`), that it is compatible with the two maps
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` (`hlift`), and that it is compatible with the two identifications of the
square-zero ideal with `𝒢` (`hideal`). The three intended consumers — well-definedness of the
class of an extension, the cocycle identity across three presentations, and injectivity through
the presentation by the fibre product `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` — all take `θ` to be the
identity of one extended structure sheaf, for which the last three hypotheses are immediate;
`freeAlgebraMap_comp_lift` reduces `hlift` to compatibility of `α'` itself, which is the form
those consumers have.

The work splits in two. Below the derived category it is a computation on local sections of the
conormal sheaf, settled by `Stacks.Sites.Conormal.conormal_hom_ext`. Inside the derived category
it is `Stacks.SheafOfModules.presentationConormalExtClass_eq`, which this file instantiates: the
naturality of the class of a conormal homomorphism in the presentation. That statement is proved
at a general site rather than here, because over a ringed space the unifier does not get from
the `Stacks.Sites.Conormal.conormalSheaf` spelling of the conormal sheaf of a presentation to
the degree `-1` term of its conormal sequence within a two-million heartbeat budget, while at a
general site it does. Accordingly every statement here is phrased so that the only
identification it asks for is the one between `conormalSheaf` and the degree `-1` term of the
two-term structure, and the maps induced by `u` appear as
`Stacks.Sites.Conormal.conormalSheafMapOfFac` rather than as
`Stacks.SheafOfModules.presentationConormalMap`, the two being the same by definition but typed
at the two different spellings.

The identification of the two comparisons to `𝖭𝖫_{X/S}` is
`Stacks.SheafOfModules.naiveCotangentComplexComparison_naturality`, which is **Stacks 08TY**.

## References

* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction conormalDesc conormalSheaf conormalPresheaf
  conormal_hom_ext conormalDesc_toAssociatedModule conormalDesc_conormalClass
  conormalSheafMapOfFac conormalSheafMapOfFac_conormalClass kernelIdeal kernelIdeal_le_comap
  hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheaf_hom_ext freeAlgebraSheafCoefficientMap
  freeAlgebraSheafCoefficientMap_comp_desc freeAlgebraSheafVariable_comp_desc)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.SheafOfModules (freeAlgebraMap freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap
  freeAlgebraSheafVariable_comp_freeAlgebraMap freeAlgebraMap_comp_presentation
  presentationNaiveCotangentComplexMap presentationConormalExtClass_eq
  naiveCotangentComplexComparison naiveCotangentComplexComparison_naturality)

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A₁ A₂ B : Sheaf J CommRingCat.{w}} (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁)
  (G : SheafOfModules.{max w u v z} (ringSheaf B))
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

/-- **A restriction datum pulled back along a factorisation of presentations has the composite
descent.** If the restriction datum `ρ₁` of `φ₁` is the restriction datum `ρ₂` of `φ₂` read
through `ψ`, then the descent of `ρ₁` factors as the map of conormal sheaves induced by the
factorisation followed by the descent of `ρ₂`. Both sides agree on every conormal class, which
determines them. -/
theorem conormalSheafMapOfFac_comp_conormalDesc (ρ₁ : IdealRestriction φ₁ G)
    (ρ₂ : IdealRestriction φ₂ G)
    (hρ : ∀ (X : Cᵒᵖ) (x : ↥(kernelIdeal φ₁.hom X)),
      ρ₂.app X ⟨ψ.hom.app X x, kernelIdeal_le_comap φ₁.hom φ₂.hom ψ.hom
        (hom_of_comp_eq hψ) X x.2⟩ = ρ₁.app X x) :
    conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ ≫
        conormalDesc.{v, u, w, z} φ₂ G ρ₂ =
      conormalDesc.{v, u, w, z} φ₁ G ρ₁ := by
  refine conormal_hom_ext.{v, u, w, z} φ₁ G (fun X x ↦ ?_)
  refine Eq.trans (congrArg ((conormalDesc.{v, u, w, z} φ₂ G ρ₂).val.app X)
    (conormalSheafMapOfFac_conormalClass.{v, u, w, z} J A₁ B A₁ A₂ (𝟙 A₁) ψ φ₁ φ₂ ψ hψ X x)) ?_
  refine Eq.trans (conormalDesc_conormalClass.{v, u, w, z} φ₂ G A₁ ψ ρ₂ X _) ?_
  exact (hρ X x).trans (conormalDesc_toAssociatedModule.{v, u, w, z} φ₁ G ρ₁ X x).symm

end Stacks.Sites.Conormal

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}}

namespace PresentedSquareZeroExtension

variable {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {E₁ E₂ : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α₁ : E₁ ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  {α₂ : E₂ ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  (P₁ : PresentedSquareZeroExtension f G E₁ α₁)
  (P₂ : PresentedSquareZeroExtension f G E₂ α₂)
  (u : E₁ ⟶ E₂) (θ : P₁.sheaf ⟶ P₂.sheaf)

section Lift

variable {G' : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P₁ : PresentedSquareZeroExtension f G E₁ α₁)
  (P₂ : PresentedSquareZeroExtension f G' E₂ α₂)
  (u : E₁ ⟶ E₂) (θ : P₁.sheaf ⟶ P₂.sheaf)

/-- **Compatibility of the lifts passes to the maps out of the polynomial algebra.** If
`θ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` is a morphism of `f⁻¹𝒪_S`-algebras carrying `α'₁` to `α'₂ ∘ u`, then it
carries the map `f⁻¹𝒪_S[ℰ₁] ⟶ 𝒪_{X'₁}` to the one of `ℰ₂` precomposed with `u`. The two
presented extensions may be by different coefficient modules; the statement does not involve
them. -/
theorem freeAlgebraMap_comp_lift (hbase : P₁.base ≫ θ = P₂.base)
    (hliftGen : P₁.liftGen ≫ Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map θ)
      (forget CommRingCat.{u}) = u ≫ P₂.liftGen) :
    freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u ≫
        P₂.lift =
      P₁.lift ≫ θ := by
  refine freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) P₂.sheaf E₁ ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
      freeAlgebraSheafCoefficientMap_comp_desc, ← Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc, hbase]
  · simp only [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc]
    rw [Category.assoc, freeAlgebraSheafVariable_comp_desc, hliftGen]

end Lift

section Conormal

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₁ α₁).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₂ α₂).hom]

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₁ α₁).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₂ α₂).hom] in
/-- **The restriction datum of the second presentation, read through `u`, is the restriction
datum of the first.** On a local relation `h` of the first presentation both sides are
`α'₁(h)`, carried into `𝒪_{X'₂}` by `θ` and read in the square-zero ideal. -/
theorem idealRestriction_pullback (hu : u ≫ α₂ = α₁)
    (hred : θ ≫ P₂.reduction = P₁.reduction)
    (hlift : freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      E₁ E₂ u ≫ P₂.lift = P₁.lift ≫ θ)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
      P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y)
    (V : (Opens X.carrier)ᵒᵖ) (h : ↥(kernelIdeal (generatorsPresentation f E₁ α₁).hom V)) :
    P₂.idealRestriction.app V
        ⟨(freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
            E₁ E₂ u).hom.app V h,
          kernelIdeal_le_comap (generatorsPresentation f E₁ α₁).hom
            (generatorsPresentation f E₂ α₂).hom
            (freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
              E₁ E₂ u).hom
            (hom_of_comp_eq (freeAlgebraMap_comp_presentation
              (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u X.sheaf
              (structureRingMap f) α₁ α₂ hu)) V h.2⟩ =
      P₁.idealRestriction.app V h := by
  refine Eq.trans (P₂.idealRestriction_app V _) ?_
  refine Eq.trans (congrArg (P₂.ideal.app V) (Subtype.ext ?_))
    (hideal V ⟨(P₁.lift.hom.app V).hom h.1, P₁.lift_mem_kernelIdeal V h⟩)
  exact congrArg (fun t : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) E₁ ⟶ P₂.sheaf ↦ (t.hom.app V).hom h.1) hlift

end Conormal

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₁ α₁).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₂ α₂).hom]

/-- **The classes of two compatibly presented square-zero extensions agree through the chain map
of the two presentations.** This is `PresentedSquareZeroExtension.extClass_eq_extClass` before
the two presentations are identified with `𝖭𝖫_{X/S}`. -/
theorem presentedExtClass_eq (hu : u ≫ α₂ = α₁)
    (hred : θ ≫ P₂.reduction = P₁.reduction)
    (hlift : freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      E₁ E₂ u ≫ P₂.lift = P₁.lift ≫ θ)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
      P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y) :
    P₁.presentedExtClass =
      DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u X.sheaf
          (structureRingMap f) α₁ α₂ hu) ≫
        P₂.presentedExtClass :=
  presentationConormalExtClass_eq (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    E₁ E₂ α₁ α₂ G u hu P₁.conormalToIdeal P₂.conormalToIdeal
    (Stacks.Sites.Conormal.conormalSheafMapOfFac_comp_conormalDesc.{u, u, u, u}
      (generatorsPresentation f E₁ α₁) (generatorsPresentation f E₂ α₂)
      (freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u)
      (freeAlgebraMap_comp_presentation (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) E₁ E₂ u X.sheaf (structureRingMap f) α₁ α₂ hu)
      G P₁.idealRestriction P₂.idealRestriction
      (idealRestriction_pullback P₁ P₂ u θ hu hred hlift hideal))

/-- **Stacks Project, Tag 0GQ0: the class of a square-zero extension does not depend on the
presentation.** Let `u : ℰ₁ ⟶ ℰ₂` be a morphism of families of generators with `u ≫ α₂ = α₁`,
and let `θ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` be a morphism of the two extended structure sheaves over `𝒪_X`,
compatible with the two maps `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` and with the two identifications of the
square-zero ideal with `𝒢`. Then the two presentations attach one and the same class in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.

The two classes live in one group, `𝖭𝖫_{X/S}` not depending on `ℰ`, so this is an equality and
not a compatibility up to an identification. It is what makes `extClass` an invariant of the
extension rather than of the presentation, and it is what the comparison of two extensions over
the presentation by the fibre product `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` needs. -/
theorem extClass_eq_extClass (hu : u ≫ α₂ = α₁)
    (hred : θ ≫ P₂.reduction = P₁.reduction)
    (hlift : freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      E₁ E₂ u ≫ P₂.lift = P₁.lift ≫ θ)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
      P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y) :
    P₁.extClass = P₂.extClass := by
  have hcomp : DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u X.sheaf
          (structureRingMap f) α₁ α₂ hu) ≫ (naiveCotangentIso f E₂ α₂).hom =
      (naiveCotangentIso f E₁ α₁).hom :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
      (naiveCotangentComplexComparison_naturality.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
        (structureRingMap f) E₁ E₂ u α₁ α₂ hu))
  have hinv : (naiveCotangentIso f E₁ α₁).inv ≫
      DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u X.sheaf
        (structureRingMap f) α₁ α₂ hu) = (naiveCotangentIso f E₂ α₂).inv := by
    rw [← Category.comp_id ((naiveCotangentIso f E₁ α₁).inv ≫ _),
      ← (naiveCotangentIso f E₂ α₂).hom_inv_id, Category.assoc,
      ← Category.assoc _ _ (naiveCotangentIso f E₂ α₂).inv, hcomp,
      (naiveCotangentIso f E₁ α₁).inv_hom_id_assoc]
  rw [extClass, extClass, presentedExtClass_eq P₁ P₂ u θ hu hred hlift hideal]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ P₂.presentedExtClass) hinv)

/-- **The difference of the classes of two square-zero extensions is computed in any presentation
they are both refined to.** The obstruction cocycle of a pair of extensions over the presentation
`ℰ₂` computes the difference of the classes of a pair presented by `ℰ₁`, whenever each of the two
is carried to the corresponding one — this is the form the cocycle identity across three
presentations needs. -/
theorem extClass_sub_extClass_of_map (P₁' : PresentedSquareZeroExtension f G E₁ α₁)
    (P₂' : PresentedSquareZeroExtension f G E₂ α₂)
    (h : P₁.extClass = P₂.extClass) (h' : P₁'.extClass = P₂'.extClass) :
    P₁.extClass - P₁'.extClass =
      (naiveCotangentIso f E₂ α₂).inv ≫
        (twoTerm f E₂ α₂).conormalExtClass G (obstruction P₂ P₂') := by
  rw [h, h', extClass_sub_extClass P₂ P₂']

/-- **Two square-zero extensions presented by different families of generators have the same
class exactly when the obstruction class of their difference over a common refinement
vanishes.** This is `PresentedSquareZeroExtension.extClass_eq_extClass_iff` made available to a
pair of extensions that do not share a presentation, which is the shape the separation half of
**Stacks 0GPZ** needs — in the source the common refinement is the presentation by the fibre
product `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`. -/
theorem extClass_eq_extClass_iff_of_map (P₁' : PresentedSquareZeroExtension f G E₁ α₁)
    (P₂' : PresentedSquareZeroExtension f G E₂ α₂)
    (h : P₁.extClass = P₂.extClass) (h' : P₁'.extClass = P₂'.extClass) :
    P₁.extClass = P₁'.extClass ↔
      (twoTerm f E₂ α₂).conormalExtClass G (obstruction P₂ P₂') = 0 := by
  rw [h, h', extClass_eq_extClass_iff P₂ P₂']

end Derived

end PresentedSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening

end
