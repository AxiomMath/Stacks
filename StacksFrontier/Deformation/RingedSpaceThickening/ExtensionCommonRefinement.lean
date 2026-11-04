module

public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentationInvariance
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProductLocallySurjective

/-!
# The common refinement of two presentations of square-zero extensions

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. An
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension` is a square-zero extension
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras, and a
`PresentedSquareZeroExtension` is such an extension together with a lift `α' : ℰ ⟶ 𝒪_{X'}` of a
prescribed family of generators `α : ℰ ⟶ 𝒪_X`. The latter carries a class
`extClass` in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, and
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationInvariance.lean` proves that
class unchanged when the presentation is refined along a morphism `u : ℰ₁ ⟶ ℰ₂` of families of
generators compatible with the lifts.

Two extensions have no reason to share a presentation: the lift `α'` is part of the datum, and
an arbitrary extension admits no lift of an arbitrary family of generators. This file supplies
the missing family, by the construction of the source: the fibre product. Given a family of
generators `α : ℰ ⟶ 𝒪_X` which is surjective and an extension `𝒪_{X'}`, the fibre product
`ℰ ×_{𝒪_X} 𝒪_{X'}` is again a surjective family of generators, and it carries *both* a
refinement map to `ℰ` and a lift to `𝒪_{X'}`. Starting from the family underlying `𝒪_{X'₁}` and
adjoining `𝒪_{X'₂}` gives `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`, over which two arbitrary extensions are
presented at once; adjoining `𝒪_{X'₃}` as well does the same for three.

Consequently the difference formula, the cocycle identity and the separation statement of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationClass.lean` — which are
proved there for extensions sharing a presentation — hold for arbitrary extensions, with the
obstruction cocycle taken over the common refinement. That is the content of
`AlgebraicGeometry.RingedSpaceThickening.extClass_sub_extClass_pairRefinement`,
`...conormalExtClass_obstruction_add_tripleRefinement` and
`...extClass_eq_extClass_iff_pairRefinement`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.presentedBy`: an extension
  read as a presented extension for a prescribed family of generators and a prescribed lift.
* `AlgebraicGeometry.RingedSpaceThickening.commonRefinementGenerators` and
  `...commonRefinementMap`: the family of generators `ℰ ×_{𝒪_X} 𝒪_{X'}` and its map to `𝒪_X`,
  with `...commonRefinementProj` and `...commonRefinementProjExtension` its two projections.
* `...PresentedSquareZeroExtension.restrictToCommonRefinement` and
  `...adjoinToCommonRefinement`: a presented extension over `ℰ`, and the adjoined extension
  `𝒪_{X'}` itself, read over the common refinement.
* `...pairRefinementGenerators` and `...tripleRefinementGenerators`: the common refinement of
  two and of three extensions, with `...pairRefinementFst`, `...pairRefinementSnd` and
  `...tripleRefinementFst`, `...tripleRefinementSnd`, `...tripleRefinementThd` the extensions
  read over it.

## Main results

* `...AlgebraSquareZeroExtension.presentedBy_extClass`: **the class of a square-zero extension
  does not depend on the chosen presentation.**
* `...AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom`: **the class only depends on the
  extension up to isomorphism**; a morphism of extensions over `𝒪_X` compatible with the two
  identifications of the square-zero ideal already suffices.
* `...pairRefinementFst_extClass`, `...pairRefinementSnd_extClass` and their ternary
  counterparts: the extensions read over the common refinement carry the classes they came
  with.
* `...extClass_sub_extClass_pairRefinement`: **the difference of the classes of two arbitrary
  square-zero extensions is the obstruction class of their difference homomorphism over the
  common refinement.**
* `...conormalExtClass_obstruction_add_tripleRefinement` together with
  `...extClass_sub_extClass_tripleRefinement₁₂` and its two companions: **the cocycle identity
  for three arbitrary square-zero extensions**, all three obstruction cocycles being taken over
  the one common refinement.
* `...extClass_eq_extClass_iff_pairRefinement`: **two arbitrary square-zero extensions have the
  same class exactly when the obstruction class of their difference homomorphism over the common
  refinement vanishes**, which by clause (1) of **Stacks 08U8** is the existence of a morphism
  between them; `...extClass_eq_extClass_iff_tripleRefinement` is the same criterion read over a
  further refinement.

## Implementation notes

The fibre product used here is the one of presheaves of *sets*,
`CategoryTheory.Presheaf.fibreProduct`: a family of generators is a presheaf of sets and a lift
of it is a morphism of presheaves of sets, so nothing below needs a ring structure on
`𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`. Its sections are the same either way — the sections of the fibre
product of sheaves of commutative rings
`Stacks.Sites.SqZeroPullback.fibreSheaf` are, by
`Stacks.Sites.SqZeroPullback.mem_fibreSubring_iff`, exactly the pairs agreeing in `𝒪_X` — and
the polynomial algebra `f⁻¹𝒪_S[ℰ]` is built on `ℰ` as a presheaf of sets in any case, so
carrying the ring structure along would be carrying it unused.

Surjectivity of the common refinement is
`CategoryTheory.Presheaf.isLocallySurjective_fibreProductFst_comp`, and surjectivity of the
resulting polynomial presentation is
`Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_isLocallySurjective`; both are stated at a
general site and are instances, so the surjectivity hypothesis that
`PresentedSquareZeroExtension.extClass` carries is discharged by instance search at every
refinement. That hypothesis is why the refinement is stated for a *surjective* family of
generators and an extension, rather than for two families: the family underlying an extension is
surjective because its reduction is.

All four of the hypotheses `hu`, `hred`, `hlift` and `hideal` of
`PresentedSquareZeroExtension.extClass_eq_extClass` are discharged here with `θ` the identity of
one extended structure sheaf, for which the last three are immediate;
`PresentedSquareZeroExtension.freeAlgebraMap_comp_lift` reduces `hlift` to compatibility of the
lifts `α'`, which is what the projections of a fibre product give by construction. Nothing in
this file enters the derived category or mentions a conormal sheaf, so the identification of the
two spellings of the conormal sheaf of a presentation — the one the implementation notes of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationInvariance.lean` discuss —
is not asked for again.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open CategoryTheory.Presheaf (fibreProduct fibreProductFst fibreProductSnd
  isPullback_fibreProduct)
open Stacks.Sites.Conormal (IdealRestriction conormalSheaf kernelIdeal kernelIdeal_le_comap
  hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.SheafOfModules (freeAlgebraMap)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-! ### Well-definedness: the class does not depend on the presentation -/

namespace AlgebraSquareZeroExtension

/-- **The family of generators underlying an extension is surjective**, the reduction
`𝒪_{X'} ⟶ 𝒪_X` being so. This is what makes the extension available as one leg of a common
refinement. -/
instance isLocallySurjective_generatorsMap (P : AlgebraSquareZeroExtension f G) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) P.generatorsMap :=
  (Presheaf.isLocallySurjective_iff_whisker_forget (Opens.grothendieckTopology X.carrier)
    P.reduction.hom).mp P.reduction_surjective

variable (P : AlgebraSquareZeroExtension f G)
  {E : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}

/-- **An extension read as a presented extension** for a prescribed family of generators
`α : ℰ ⟶ 𝒪_X` and a prescribed lift `α' : ℰ ⟶ 𝒪_{X'}` of it. The extension's own presentation,
`AlgebraSquareZeroExtension.toPresented`, is the case of the family underlying `𝒪_{X'}` with
`α'` the identity. -/
def presentedBy (lift : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) P.sheaf)
    (hlift : lift ≫ Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map P.reduction)
      (forget CommRingCat.{u}) = α) :
    PresentedSquareZeroExtension f G E α where
  sheaf := P.sheaf
  base := P.base
  reduction := P.reduction
  base_comp_reduction := P.base_comp_reduction
  liftGen := lift
  liftGen_comp := hlift
  ideal := P.ideal

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
  (generatorsPresentation f E α).hom]

/-- **Stacks Project, Tag 0GQ0: the class of a square-zero extension does not depend on the
presentation.** Whatever surjective family of generators `α : ℰ ⟶ 𝒪_X` is prescribed and
whatever lift `α' : ℰ ⟶ 𝒪_{X'}` of it is chosen, the resulting class in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the one of the extension's own presentation. What is asked of `ℰ`
is that its *polynomial presentation* `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` be surjective, which is weaker than
surjectivity of `α` itself and is what **Stacks 08UB** produces.

No common refinement is needed for this: the chosen lift `α'` is itself a morphism of families
of generators from `ℰ` to the family underlying `𝒪_{X'}`, compatible with the lifts because the
latter family is lifted by the identity. -/
theorem presentedBy_extClass
    (lift : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) P.sheaf)
    (hlift : lift ≫ Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map P.reduction)
      (forget CommRingCat.{u}) = α) :
    (P.presentedBy lift hlift).extClass = P.toPresented.extClass :=
  PresentedSquareZeroExtension.extClass_eq_extClass (P.presentedBy lift hlift) P.toPresented
    lift (𝟙 P.sheaf) hlift (Category.id_comp _)
    (PresentedSquareZeroExtension.freeAlgebraMap_comp_lift (P.presentedBy lift hlift)
      P.toPresented lift (𝟙 P.sheaf) (Category.comp_id _) (by simp [presentedBy, toPresented]))
    (fun _ _ ↦ rfl)

/-- **The class of a square-zero extension depends only on its isomorphism class.** A morphism
`θ : 𝒪_{X'} ⟶ 𝒪_{X''}` of extensions over `𝒪_X` which is compatible with the two
identifications of the square-zero ideal with `𝒢` already forces the two classes to agree; by
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_hom` such a morphism is in any case
invertible. -/
theorem extClass_eq_extClass_of_hom (P' : AlgebraSquareZeroExtension f G)
    (θ : P.sheaf ⟶ P'.sheaf) (hbase : P.base ≫ θ = P'.base)
    (hred : θ ≫ P'.reduction = P.reduction)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P.reduction.hom V)),
      P'.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P.reduction.hom P'.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = P.ideal.app V y) :
    P.toPresented.extClass = P'.toPresented.extClass := by
  refine PresentedSquareZeroExtension.extClass_eq_extClass P.toPresented P'.toPresented
    (Functor.whiskerRight θ.hom (forget CommRingCat.{u})) θ ?_ hred ?_ hideal
  · rw [← Functor.whiskerRight_comp]
    exact congrArg
      (fun t : P.sheaf ⟶ X.sheaf ↦ Functor.whiskerRight t.hom (forget CommRingCat.{u})) hred
  · exact PresentedSquareZeroExtension.freeAlgebraMap_comp_lift P.toPresented P'.toPresented
      (Functor.whiskerRight θ.hom (forget CommRingCat.{u})) θ hbase
      (by simp [toPresented])

end Derived

end AlgebraSquareZeroExtension

/-! ### The common refinement of a family of generators and an extension -/

section CommonRefinement

variable (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
  (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
  (P : AlgebraSquareZeroExtension f G)

/-- **The common refinement `ℰ ×_{𝒪_X} 𝒪_{X'}` of a family of generators and an extension**: the
family of generators whose sections are the pairs of a section of `ℰ` and a section of `𝒪_{X'}`
with the same image in `𝒪_X`. -/
abbrev commonRefinementGenerators : Functor (Opens X.carrier)ᵒᵖ (Type u) :=
  fibreProduct α P.generatorsMap

/-- The map `ℰ ×_{𝒪_X} 𝒪_{X'} ⟶ 𝒪_X` of the common refinement: either projection followed by the
corresponding map, the two agreeing by construction. -/
abbrev commonRefinementMap :
    commonRefinementGenerators E α P ⟶
      underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf :=
  fibreProductFst α P.generatorsMap ≫ α

/-- The projection of the common refinement to the given family of generators, a morphism of
families of generators over `𝒪_X`. -/
abbrev commonRefinementProj : commonRefinementGenerators E α P ⟶ E :=
  fibreProductFst α P.generatorsMap

/-- The projection of the common refinement to the family underlying the adjoined extension,
which is at the same time a lift of the common refinement to that extension. -/
abbrev commonRefinementProjExtension : commonRefinementGenerators E α P ⟶ P.generators :=
  fibreProductSnd α P.generatorsMap

/-- The projection to the adjoined extension is a lift of the map to `𝒪_X`. -/
theorem commonRefinementProjExtension_comp :
    commonRefinementProjExtension E α P ≫ P.generatorsMap = commonRefinementMap E α P :=
  (isPullback_fibreProduct α P.generatorsMap).w.symm

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) α]

/-- **A presented extension over `ℰ`, read over the common refinement**: the same extension, with
the lift of the refined family obtained from the given one by projection. -/
def PresentedSquareZeroExtension.restrictToCommonRefinement
    (Q : PresentedSquareZeroExtension f G E α) :
    PresentedSquareZeroExtension f G (commonRefinementGenerators E α P)
      (commonRefinementMap E α P) where
  sheaf := Q.sheaf
  base := Q.base
  reduction := Q.reduction
  base_comp_reduction := Q.base_comp_reduction
  liftGen := commonRefinementProj E α P ≫ Q.liftGen
  liftGen_comp := by rw [Category.assoc, Q.liftGen_comp]
  ideal := Q.ideal

/-- **The adjoined extension, read over the common refinement**: the extension `𝒪_{X'}` with the
projection of the fibre product to it as the lift of the refined family. This is the half of the
construction that no morphism of the original families provides. -/
def adjoinToCommonRefinement :
    PresentedSquareZeroExtension f G (commonRefinementGenerators E α P)
      (commonRefinementMap E α P) where
  sheaf := P.sheaf
  base := P.base
  reduction := P.reduction
  base_comp_reduction := P.base_comp_reduction
  liftGen := commonRefinementProjExtension E α P
  liftGen_comp := commonRefinementProjExtension_comp E α P
  ideal := P.ideal

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Refining the presentation does not change the class**: the restriction of a presented
extension to the common refinement carries the class it came with. -/
theorem PresentedSquareZeroExtension.restrictToCommonRefinement_extClass
    (Q : PresentedSquareZeroExtension f G E α) :
    (PresentedSquareZeroExtension.restrictToCommonRefinement E α P Q).extClass = Q.extClass :=
  PresentedSquareZeroExtension.extClass_eq_extClass
    (PresentedSquareZeroExtension.restrictToCommonRefinement E α P Q) Q
    (commonRefinementProj E α P) (𝟙 Q.sheaf) rfl (Category.id_comp _)
    (PresentedSquareZeroExtension.freeAlgebraMap_comp_lift
      (PresentedSquareZeroExtension.restrictToCommonRefinement E α P Q) Q
      (commonRefinementProj E α P) (𝟙 Q.sheaf) (Category.comp_id _)
      (by simp [PresentedSquareZeroExtension.restrictToCommonRefinement]))
    (fun _ _ ↦ rfl)

/-- **The adjoined extension, read over the common refinement, carries its own class**: the
projection of the fibre product to `𝒪_{X'}` is a morphism of families of generators from the
common refinement to the family underlying `𝒪_{X'}`, compatible with the lifts. -/
theorem adjoinToCommonRefinement_extClass :
    (adjoinToCommonRefinement E α P).extClass = P.toPresented.extClass :=
  PresentedSquareZeroExtension.extClass_eq_extClass (adjoinToCommonRefinement E α P)
    P.toPresented (commonRefinementProjExtension E α P) (𝟙 P.sheaf)
    (commonRefinementProjExtension_comp E α P) (Category.id_comp _)
    (PresentedSquareZeroExtension.freeAlgebraMap_comp_lift (adjoinToCommonRefinement E α P)
      P.toPresented (commonRefinementProjExtension E α P) (𝟙 P.sheaf) (Category.comp_id _)
      (by simp [adjoinToCommonRefinement, AlgebraSquareZeroExtension.toPresented]))
    (fun _ _ ↦ rfl)

end Derived

end CommonRefinement

/-! ### Two extensions: the presentation by `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` -/

section Pair

variable (P₁ P₂ : AlgebraSquareZeroExtension f G)

/-- **The common refinement `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` of two square-zero extensions**, as a
family of generators of `𝒪_X`: the family underlying the first extension, refined by adjoining
the second. -/
abbrev pairRefinementGenerators : Functor (Opens X.carrier)ᵒᵖ (Type u) :=
  commonRefinementGenerators P₁.generators P₁.generatorsMap P₂

/-- The map `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂} ⟶ 𝒪_X` of the common refinement of two extensions. -/
abbrev pairRefinementMap :
    pairRefinementGenerators P₁ P₂ ⟶
      underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf :=
  commonRefinementMap P₁.generators P₁.generatorsMap P₂

/-- The first of two extensions, presented by their common refinement. -/
def pairRefinementFst :
    PresentedSquareZeroExtension f G (pairRefinementGenerators P₁ P₂)
      (pairRefinementMap P₁ P₂) :=
  PresentedSquareZeroExtension.restrictToCommonRefinement P₁.generators P₁.generatorsMap P₂
    P₁.toPresented

/-- The second of two extensions, presented by their common refinement. -/
def pairRefinementSnd :
    PresentedSquareZeroExtension f G (pairRefinementGenerators P₁ P₂)
      (pairRefinementMap P₁ P₂) :=
  adjoinToCommonRefinement P₁.generators P₁.generatorsMap P₂

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The first extension, read over the common refinement, carries its own class. -/
theorem pairRefinementFst_extClass :
    (pairRefinementFst P₁ P₂).extClass = P₁.toPresented.extClass :=
  PresentedSquareZeroExtension.restrictToCommonRefinement_extClass P₁.generators
    P₁.generatorsMap P₂ P₁.toPresented

/-- The second extension, read over the common refinement, carries its own class. -/
theorem pairRefinementSnd_extClass :
    (pairRefinementSnd P₁ P₂).extClass = P₂.toPresented.extClass :=
  adjoinToCommonRefinement_extClass P₁.generators P₁.generatorsMap P₂

/-- **The difference of the classes of two arbitrary square-zero extensions is the obstruction
class of their difference homomorphism over their common refinement.** This is the difference
formula of **Stacks 08U8** for a pair of extensions that share no presentation: they are brought
over one presentation by `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`, where the difference homomorphism
`𝒥/𝒥² ⟶ 𝒢` exists. -/
theorem extClass_sub_extClass_pairRefinement :
    P₁.toPresented.extClass - P₂.toPresented.extClass =
      (PresentedSquareZeroExtension.naiveCotangentIso f (pairRefinementGenerators P₁ P₂)
          (pairRefinementMap P₁ P₂)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
            (pairRefinementMap P₁ P₂)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
            (pairRefinementSnd P₁ P₂)) := by
  rw [← pairRefinementFst_extClass P₁ P₂, ← pairRefinementSnd_extClass P₁ P₂]
  exact PresentedSquareZeroExtension.extClass_sub_extClass (pairRefinementFst P₁ P₂)
    (pairRefinementSnd P₁ P₂)

/-- **Stacks Project, Tag 0GPZ, the separation statement: two arbitrary square-zero extensions
have the same class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` exactly when the obstruction class of their
difference homomorphism over the common refinement `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` vanishes.** By
clause (1) of **Stacks 08U8** that class vanishes exactly when a morphism from the one extension
to the other exists, and such a morphism is invertible by
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_hom`; so this is the injectivity half
of the bijection of **Stacks 0GPZ**, reduced to that clause and to nothing else. -/
theorem extClass_eq_extClass_iff_pairRefinement :
    P₁.toPresented.extClass = P₂.toPresented.extClass ↔
      (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
            (pairRefinementMap P₁ P₂)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
            (pairRefinementSnd P₁ P₂)) = 0 := by
  rw [← pairRefinementFst_extClass P₁ P₂, ← pairRefinementSnd_extClass P₁ P₂]
  exact PresentedSquareZeroExtension.extClass_eq_extClass_iff (pairRefinementFst P₁ P₂)
    (pairRefinementSnd P₁ P₂)

end Derived

end Pair

/-! ### Three extensions: the cocycle identity -/

section Triple

variable (P₁ P₂ P₃ : AlgebraSquareZeroExtension f G)

/-- **The common refinement of three square-zero extensions**, as a family of generators of
`𝒪_X`: the common refinement of the first two, refined again by adjoining the third. -/
abbrev tripleRefinementGenerators : Functor (Opens X.carrier)ᵒᵖ (Type u) :=
  commonRefinementGenerators (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂) P₃

/-- The map to `𝒪_X` of the common refinement of three extensions. -/
abbrev tripleRefinementMap :
    tripleRefinementGenerators P₁ P₂ P₃ ⟶
      underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf :=
  commonRefinementMap (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂) P₃

/-- The first of three extensions, presented by their common refinement. -/
def tripleRefinementFst :
    PresentedSquareZeroExtension f G (tripleRefinementGenerators P₁ P₂ P₃)
      (tripleRefinementMap P₁ P₂ P₃) :=
  PresentedSquareZeroExtension.restrictToCommonRefinement (pairRefinementGenerators P₁ P₂)
    (pairRefinementMap P₁ P₂) P₃ (pairRefinementFst P₁ P₂)

/-- The second of three extensions, presented by their common refinement. -/
def tripleRefinementSnd :
    PresentedSquareZeroExtension f G (tripleRefinementGenerators P₁ P₂ P₃)
      (tripleRefinementMap P₁ P₂ P₃) :=
  PresentedSquareZeroExtension.restrictToCommonRefinement (pairRefinementGenerators P₁ P₂)
    (pairRefinementMap P₁ P₂) P₃ (pairRefinementSnd P₁ P₂)

/-- The third of three extensions, presented by their common refinement. -/
def tripleRefinementThd :
    PresentedSquareZeroExtension f G (tripleRefinementGenerators P₁ P₂ P₃)
      (tripleRefinementMap P₁ P₂ P₃) :=
  adjoinToCommonRefinement (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂) P₃

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The first of three extensions, read over the common refinement, carries its own class. -/
theorem tripleRefinementFst_extClass :
    (tripleRefinementFst P₁ P₂ P₃).extClass = P₁.toPresented.extClass :=
  (PresentedSquareZeroExtension.restrictToCommonRefinement_extClass
    (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂) P₃
    (pairRefinementFst P₁ P₂)).trans (pairRefinementFst_extClass P₁ P₂)

/-- The second of three extensions, read over the common refinement, carries its own class. -/
theorem tripleRefinementSnd_extClass :
    (tripleRefinementSnd P₁ P₂ P₃).extClass = P₂.toPresented.extClass :=
  (PresentedSquareZeroExtension.restrictToCommonRefinement_extClass
    (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂) P₃
    (pairRefinementSnd P₁ P₂)).trans (pairRefinementSnd_extClass P₁ P₂)

/-- The third of three extensions, read over the common refinement, carries its own class. -/
theorem tripleRefinementThd_extClass :
    (tripleRefinementThd P₁ P₂ P₃).extClass = P₃.toPresented.extClass :=
  adjoinToCommonRefinement_extClass (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂) P₃

/-- The difference of the classes of the first two of three arbitrary square-zero extensions,
computed by the obstruction cocycle over the common refinement of all three.

This is where the common refinement supplies the hypotheses of
`PresentedSquareZeroExtension.extClass_sub_extClass_of_map`: that lemma asks for two extensions
over one family of generators, each carried to one over a second family, and the two refinements
of the pair `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` and `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂} ×_{𝒪_X} 𝒪_{X'₃}` are
exactly that, the two comparisons being `pairRefinementFst_extClass` and
`tripleRefinementFst_extClass` and their companions. The same statement follows directly from
`PresentedSquareZeroExtension.extClass_sub_extClass`, as the two companion lemmas below do. -/
theorem extClass_sub_extClass_tripleRefinement₁₂ :
    P₁.toPresented.extClass - P₂.toPresented.extClass =
      (PresentedSquareZeroExtension.naiveCotangentIso f (tripleRefinementGenerators P₁ P₂ P₃)
          (tripleRefinementMap P₁ P₂ P₃)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
            (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (tripleRefinementFst P₁ P₂ P₃)
            (tripleRefinementSnd P₁ P₂ P₃)) := by
  rw [← pairRefinementFst_extClass P₁ P₂, ← pairRefinementSnd_extClass P₁ P₂]
  exact PresentedSquareZeroExtension.extClass_sub_extClass_of_map (pairRefinementFst P₁ P₂)
    (tripleRefinementFst P₁ P₂ P₃) (pairRefinementSnd P₁ P₂) (tripleRefinementSnd P₁ P₂ P₃)
    ((pairRefinementFst_extClass P₁ P₂).trans (tripleRefinementFst_extClass P₁ P₂ P₃).symm)
    ((pairRefinementSnd_extClass P₁ P₂).trans (tripleRefinementSnd_extClass P₁ P₂ P₃).symm)

/-- The difference of the classes of the last two of three arbitrary square-zero extensions,
computed by the obstruction cocycle over the common refinement of all three. -/
theorem extClass_sub_extClass_tripleRefinement₂₃ :
    P₂.toPresented.extClass - P₃.toPresented.extClass =
      (PresentedSquareZeroExtension.naiveCotangentIso f (tripleRefinementGenerators P₁ P₂ P₃)
          (tripleRefinementMap P₁ P₂ P₃)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
            (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (tripleRefinementSnd P₁ P₂ P₃)
            (tripleRefinementThd P₁ P₂ P₃)) := by
  rw [← tripleRefinementSnd_extClass P₁ P₂ P₃, ← tripleRefinementThd_extClass P₁ P₂ P₃]
  exact PresentedSquareZeroExtension.extClass_sub_extClass (tripleRefinementSnd P₁ P₂ P₃)
    (tripleRefinementThd P₁ P₂ P₃)

/-- The difference of the classes of the outer two of three arbitrary square-zero extensions,
computed by the obstruction cocycle over the common refinement of all three. -/
theorem extClass_sub_extClass_tripleRefinement₁₃ :
    P₁.toPresented.extClass - P₃.toPresented.extClass =
      (PresentedSquareZeroExtension.naiveCotangentIso f (tripleRefinementGenerators P₁ P₂ P₃)
          (tripleRefinementMap P₁ P₂ P₃)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
            (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (tripleRefinementFst P₁ P₂ P₃)
            (tripleRefinementThd P₁ P₂ P₃)) := by
  rw [← tripleRefinementFst_extClass P₁ P₂ P₃, ← tripleRefinementThd_extClass P₁ P₂ P₃]
  exact PresentedSquareZeroExtension.extClass_sub_extClass (tripleRefinementFst P₁ P₂ P₃)
    (tripleRefinementThd P₁ P₂ P₃)

/-- **The cocycle identity for three arbitrary square-zero extensions.** The three obstruction
cocycles, all taken over the one common refinement of the three extensions, telescope; by the
three difference formulas above each of them computes the difference of the corresponding pair of
classes, so this is the cocycle identity of **Stacks 08U8** for three extensions sharing no
presentation. -/
theorem conormalExtClass_obstruction_add_tripleRefinement :
    (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
          (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
        (PresentedSquareZeroExtension.obstruction (tripleRefinementFst P₁ P₂ P₃)
          (tripleRefinementSnd P₁ P₂ P₃)) +
      (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
            (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (tripleRefinementSnd P₁ P₂ P₃)
            (tripleRefinementThd P₁ P₂ P₃)) =
    (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
          (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
        (PresentedSquareZeroExtension.obstruction (tripleRefinementFst P₁ P₂ P₃)
          (tripleRefinementThd P₁ P₂ P₃)) :=
  PresentedSquareZeroExtension.conormalExtClass_obstruction_add (tripleRefinementFst P₁ P₂ P₃)
    (tripleRefinementSnd P₁ P₂ P₃) (tripleRefinementThd P₁ P₂ P₃)

/-- **The separation criterion is insensitive to further refinement**: two arbitrary square-zero
extensions have the same class exactly when the obstruction class of their difference
homomorphism vanishes over the common refinement of the two *together with an arbitrary third
extension*. Taking `P₃` to be either of the two gives back
`extClass_eq_extClass_iff_pairRefinement`, so nothing is lost by refining further; this is
`PresentedSquareZeroExtension.extClass_eq_extClass_iff_of_map` fed by the common refinement. -/
theorem extClass_eq_extClass_iff_tripleRefinement :
    P₁.toPresented.extClass = P₂.toPresented.extClass ↔
      (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
            (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (tripleRefinementFst P₁ P₂ P₃)
            (tripleRefinementSnd P₁ P₂ P₃)) = 0 := by
  rw [← pairRefinementFst_extClass P₁ P₂, ← pairRefinementSnd_extClass P₁ P₂]
  exact PresentedSquareZeroExtension.extClass_eq_extClass_iff_of_map (pairRefinementFst P₁ P₂)
    (tripleRefinementFst P₁ P₂ P₃) (pairRefinementSnd P₁ P₂) (tripleRefinementSnd P₁ P₂ P₃)
    ((pairRefinementFst_extClass P₁ P₂).trans (tripleRefinementFst_extClass P₁ P₂ P₃).symm)
    ((pairRefinementSnd_extClass P₁ P₂).trans (tripleRefinementSnd_extClass P₁ P₂ P₃).symm)

end Derived

end Triple

end AlgebraicGeometry.RingedSpaceThickening

end
