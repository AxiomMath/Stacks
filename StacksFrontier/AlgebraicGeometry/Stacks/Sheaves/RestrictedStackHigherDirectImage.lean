module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictedHigherDirectImageDegreewise
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibredRingedToposModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The higher direct image of a module, restricted to the small étale site of a scheme

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, `y : V ⟶ 𝒴` a 1-morphism out of the
algebraic stack of a scheme `V` (an object of `𝒴` over `V`), and `U = V ×_𝒴 𝒳` the 2-fibre
product, with base change `f' : U ⟶ V`. When `f` is representable by algebraic spaces, `U` is
represented by an algebraic space (`exists_isAlgebraicSpace_equivalenceOver_twoFibreProduct`).
Stacks 0GQH asserts `(Rⁱf_*ℱ)|_{V_étale} = Rⁱf'_{small,*}(ℱ|_{U_étale})` for `ℱ` in
`LQCoh^{fbc}(𝒪_𝒳)`. This file proves the identity for **every** module `ℱ` on the étale site of
`𝒳`, with `Rⁱf_*` computed in the étale topology. By Stacks 0771 (4)(a), for `ℱ ∈ LQCoh^{fbc}`
this is the fppf higher direct image of the tag.

The proof is the source's:

1. **Stacks 075H** for modules,
   `AlgebraicGeometry.Stack.StackModuleDirectImage.higherDirectImageBaseChangeIso`:
   `y⁻¹Rⁱf_*ℱ ≅ Rⁱf'_*(y')⁻¹ℱ`, reducing to `𝒳` represented by `U` and `𝒴` by `V`;
2. **Stacks 075N (2) in degree `i`**,
   `AlgebraicGeometry.Space.restrictedHigherDirectImageIsoOfGrothendieck`, for `f'`.

The two steps are stated for different direct images: 075H for
`AlgebraicGeometry.Stack.stackModuleDirectImage`, 075N for the direct image of the morphism of
ringed topoi. `pushforwardModulesIsoStackModuleDirectImage` identifies them, because both are
right adjoint to the inverse image.

## Main results

* `AlgebraicGeometry.Space.smallEtaleHigherDirectImage`: the higher direct images `Rⁱf_{small,*}`
  of modules on the small étale sites of algebraic spaces.
* `AlgebraicGeometry.Stack.restrictedStackModuleHigherDirectImageIso`: the identity, for any
  presentations of `𝒱 = (Sch/V)` and of `U` by algebraic spaces.
* `AlgebraicGeometry.Stack.restrictedStackModuleHigherDirectImageIsoOfScheme`: the same, with
  `(Sch/V)` presented by `V`.
* `AlgebraicGeometry.Stack.restrictedStackModuleHigherDirectImageIsoOfRepresentable`: Stacks 075N
  (2) in degree `i` for a 1-morphism of algebraic stacks between stacks presented by algebraic
  spaces.

## Implementation notes

The categories `AlgebraicGeometry.Stack.StackModules` and the module categories of
`AlgebraicGeometry.FibredSite.associatedRingedTopos` are the same up to unfolding. Comparing right
derived functors across the two spellings is expensive, so each crossing is a separate
declaration: `stackModuleHigherDirectImageObjIso` and
`stackModuleToposHigherDirectImageObjIso`.

## References

* [Stacks Project, Tag 0GQH](https://stacks.math.columbia.edu/tag/0GQH)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u t

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- The sheaves of modules on the small étale site of an algebraic space form a Grothendieck
abelian category at the universe of the schemes. Stated for algebraic spaces written as
`⟨F, hF⟩`, as `AlgebraicGeometry.Space.additive_pushforwardModules_smallEtaleToposHom`. -/
instance Space.isGrothendieckAbelian_smallEtaleRingedTopos_modules (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} :
    IsGrothendieckAbelian.{u} (Space.smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- **The higher direct images `Rⁱf_{small,*}`** of sheaves of modules along a morphism of
algebraic spaces, on the small étale sites: the right derived functors of the direct image of the
morphism of small étale ringed topoi (Stacks 03G8). -/
abbrev Space.smallEtaleHigherDirectImage {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) (i : ℕ) :
    (Space.smallEtaleRingedTopos B S hS X).Modules ⥤
      (Space.smallEtaleRingedTopos B S hS Y).Modules :=
  have : IsGrothendieckAbelian.{u} (Space.smallEtaleRingedTopos B S hS X).Modules :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  (AlgebraicGeometry.RingedToposHom.pushforwardModules
    (Space.smallEtaleRingedToposHom B S hS g)).rightDerived i

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Instances

variable (τ : SiteKind) (𝒵 : AlgebraicStacks.{u, t} B S hS)

/-- The site of the ringed topos of an algebraic stack has sheafification of abelian groups at
the universe of the schemes: `AlgebraicGeometry.Stack.hasSheafify_stackModules`, at the spelling
of `AlgebraicGeometry.FibredSite.associatedRingedTopos`. -/
instance hasSheafify_associatedRingedTopos :
    HasSheafify (FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids
      τ).J AddCommGrpCat.{u} :=
  hasSheafify_stackModules B S hS τ 𝒵

/-- `AlgebraicGeometry.Stack.wEqualsLocallyBijective_stackModules`, at the spelling of
`AlgebraicGeometry.FibredSite.associatedRingedTopos`. -/
instance wEqualsLocallyBijective_associatedRingedTopos :
    (FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids
      τ).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_stackModules B S hS τ 𝒵

/-- The site of the ringed topos of an algebraic stack is essentially small. -/
instance essentiallySmall_associatedRingedTopos :
    EssentiallySmall.{u} (FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids τ).C :=
  essentiallySmall_obj_algebraicStack B S hS 𝒵

/-- The modules on the ringed topos of an algebraic stack form a Grothendieck abelian category at
the universe of the schemes. -/
instance isGrothendieckAbelian_associatedRingedTopos :
    IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids τ).Modules :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

end Instances

/-- The direct image of modules along the morphism of ringed topoi of a 1-morphism of algebraic
stacks, read as a functor between the categories `AlgebraicGeometry.Stack.StackModules`. -/
abbrev stackModuleToposDirectImage {𝒵 𝒲 : AlgebraicStacks.{u, t} B S hS} (g : 𝒵 ⟶ 𝒲)
    (τ : SiteKind) : StackModules B S hS τ 𝒵 ⥤ StackModules B S hS τ 𝒲 :=
  AlgebraicGeometry.RingedToposHom.pushforwardModules
    (X := FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids τ)
    (Y := FibredSite.associatedRingedTopos B S hS 𝒲.val.val.p 𝒲.val.isFiberedInGroupoids τ)
    (FibredSite.ringedToposMorphism B S hS 𝒵.val.val.p 𝒲.val.val.p 𝒵.val.isFiberedInGroupoids
      𝒲.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
      (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) τ)

/-- **The direct image of modules on the `τ`-sites along a 1-morphism of algebraic stacks is the
direct image along its morphism of ringed topoi**: both are right adjoint to the inverse image. -/
def pushforwardModulesIsoStackModuleDirectImage {𝒵 𝒲 : AlgebraicStacks.{u, t} B S hS}
    (g : 𝒵 ⟶ 𝒲) (τ : SiteKind) :
    AlgebraicGeometry.RingedToposHom.pushforwardModules
        (X := FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids τ)
        (Y := FibredSite.associatedRingedTopos B S hS 𝒲.val.val.p 𝒲.val.isFiberedInGroupoids τ)
        (FibredSite.ringedToposMorphism B S hS 𝒵.val.val.p
        𝒲.val.val.p 𝒵.val.isFiberedInGroupoids 𝒲.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor g.hom)
        (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
          (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) τ) ≅
      stackModuleDirectImage B S hS g τ :=
  have := hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS g (Type u)
  have := hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS g RingCat.{u}
  have := hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS g AddCommGrpCat.{u}
  have := hasSheafify_stackModules B S hS τ 𝒵
  have := wEqualsLocallyBijective_stackModules B S hS τ 𝒵
  have : HasSheafify (FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids τ).J AddCommGrpCat.{u} :=
    hasSheafify_stackModules B S hS τ 𝒵
  have : (FibredSite.associatedRingedTopos B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids τ).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    wEqualsLocallyBijective_stackModules B S hS τ 𝒵
  FibredSite.pushforwardModulesIsoModuleDirectImage B S hS 𝒵.val.val.p 𝒲.val.val.p
      𝒵.val.isFiberedInGroupoids 𝒲.val.isFiberedInGroupoids _
      (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) τ ≪≫
    (StackModuleDirectImage.pushforwardIsoModuleDirectImage B S hS g τ
      (stackModuleDirectImageData.{u, t} B S hS τ)).symm

variable {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) {V : BigFppfOver B S hS}
  (y : schemeStack.{u, t} B S hS V ⟶ 𝒴)

/-- The presentation of the algebraic stack of a scheme `V` by the algebraic space `V`, that is,
by the presheaf `yoneda.obj V`. -/
abbrev schemeStackEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, t} B S hS V).val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p :=
  PresheafOfCategories.sliceElementsEquivalenceOver V

/-- The second projection of a 2-fibre product of algebraic stacks is a 1-morphism over the
base. -/
theorem isFibredOneMorphism_twoFibreProduct_snd :
    (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p.IsFibredOneMorphism
      (schemeStack.{u, t} B S hS V).val.val.p
      (CatFiberedInGroupoids.homFunctor
        (twoFibreProductSquareAlgebraicStacks B S hS f y).snd.hom) :=
  (schemeStack.{u, t} B S hS V).val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p
      (twoFibreProductSquareAlgebraicStacks B S hS f y).snd.hom)

/-- The higher direct image of `AlgebraicGeometry.Stack.stackModuleHigherDirectImage`, read as the
right derived functor of `AlgebraicGeometry.Stack.stackModuleDirectImage` with the injective
resolutions of `AlgebraicGeometry.Stack.stackModuleDirectImageData`. -/
def stackModuleHigherDirectImageObjIso {𝒵 𝒲 : AlgebraicStacks.{u, t} B S hS} (g : 𝒵 ⟶ 𝒲)
    (i : ℕ) (M : StackModules B S hS .etale 𝒵) :
    (stackModuleHigherDirectImage B S hS g .etale i).obj M ≅
      (letI := (stackModuleDirectImageData.{u, t} B S hS .etale).enoughInjectives 𝒵
       ((stackModuleDirectImage B S hS g .etale).rightDerived i).obj M) :=
  Iso.refl _

/-- The right derived functors of `AlgebraicGeometry.Stack.stackModuleToposDirectImage`, computed
in `AlgebraicGeometry.Stack.StackModules` and in the modules of the ringed topoi, agree. -/
def stackModuleToposHigherDirectImageObjIso {𝒵 𝒲 : AlgebraicStacks.{u, t} B S hS}
    (g : 𝒵 ⟶ 𝒲) (i : ℕ) (M : StackModules B S hS .etale 𝒵) :
    (letI := (stackModuleDirectImageData.{u, t} B S hS .etale).enoughInjectives 𝒵
     letI := Functor.additive_of_iso
       (pushforwardModulesIsoStackModuleDirectImage B S hS g .etale).symm
     ((stackModuleToposDirectImage B S hS g .etale).rightDerived i).obj M) ≅
     ((AlgebraicGeometry.RingedToposHom.pushforwardModules
        (FibredSite.ringedToposMorphism B S hS 𝒵.val.val.p 𝒲.val.val.p 𝒵.val.isFiberedInGroupoids
          𝒲.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
          (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) .etale)).rightDerived i).obj M :=
  Iso.refl _

/-- **Stacks 075N (2) in degree `i`** for a 1-morphism `g : 𝒵 ⟶ 𝒲` of algebraic stacks whose source
and target are presented by algebraic spaces `U` and `G`, with `Rⁱg_*` computed from the direct
image of the morphism of ringed topoi of `g`. -/
def restrictedToposHigherDirectImageIsoOfRepresentable {𝒵 𝒲 : AlgebraicStacks.{u, t} B S hS}
    (g : 𝒵 ⟶ 𝒲) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (U ⋙ typeToCat)).p)
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p) (i : ℕ) (M : StackModules B S hS .etale 𝒵) :
    (AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS G
        𝒲.val.val.p 𝒲.val.isFiberedInGroupoids hG eG)).obj
      (((AlgebraicGeometry.RingedToposHom.pushforwardModules
        (FibredSite.ringedToposMorphism B S hS 𝒵.val.val.p 𝒲.val.val.p 𝒵.val.isFiberedInGroupoids
          𝒲.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
          (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) .etale)).rightDerived i).obj M) ≅
    ((AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.smallEtaleRingedToposHom B S hS
        (Space.inducedAlgebraicSpacesHom B S hS U G 𝒵.val.val.p 𝒲.val.val.p hU hG eU eG _
          (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom))))).rightDerived i).obj
      ((AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS U
        𝒵.val.val.p 𝒵.val.isFiberedInGroupoids hU eU)).obj M) :=
  have := hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS
    g (Type u)
  have := hasSheafify_stackModules B S hS .etale 𝒲
  have := wEqualsLocallyBijective_stackModules B S hS .etale 𝒲
  have : HasSheafify (FibredSite.associatedRingedTopos B S hS
      𝒲.val.val.p
      𝒲.val.isFiberedInGroupoids .etale).J AddCommGrpCat.{u} :=
    hasSheafify_stackModules B S hS .etale 𝒲
  have : (FibredSite.associatedRingedTopos B S hS
      𝒲.val.val.p
      𝒲.val.isFiberedInGroupoids .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    wEqualsLocallyBijective_stackModules B S hS .etale 𝒲
  have : IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS
      𝒲.val.val.p
      𝒲.val.isFiberedInGroupoids .etale).Modules :=
    isGrothendieckAbelian_associatedRingedTopos B S hS .etale 𝒲
  have e3 := Space.restrictedHigherDirectImageIsoOfGrothendieck B S hS U G
    𝒵.val.val.p
    𝒲.val.val.p
    𝒵.val.isFiberedInGroupoids
    𝒲.val.isFiberedInGroupoids hU hG eU eG _
    (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) i
  e3.app M

/-- **Stacks 075N (2) in degree `i` for a 1-morphism of algebraic stacks** `g : 𝒵 ⟶ 𝒲` whose
source and target are presented by algebraic spaces `U` and `G`:
`(Rⁱg_*ℳ)|_{G_étale} ≅ Rⁱg_{small,*}(ℳ|_{U_étale})`, where `Rⁱg_*` is the higher direct image of
modules on the étale sites of the stacks. -/
def restrictedStackModuleHigherDirectImageIsoOfRepresentable {𝒵 𝒲 : AlgebraicStacks.{u, t} B S hS}
    (g : 𝒵 ⟶ 𝒲) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (U ⋙ typeToCat)).p)
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p) (i : ℕ) (M : StackModules B S hS .etale 𝒵) :
    (AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS G
        𝒲.val.val.p
        𝒲.val.isFiberedInGroupoids hG eG)).obj
      ((stackModuleHigherDirectImage B S hS g
        .etale i).obj M) ≅
    ((AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.smallEtaleRingedToposHom B S hS
        (Space.inducedAlgebraicSpacesHom B S hS U G 𝒵.val.val.p 𝒲.val.val.p hU hG eU eG _
          (𝒲.val.isFiberedInGroupoids.isFibredOneMorphism
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom))))).rightDerived i).obj
      ((AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS U
        𝒵.val.val.p
        𝒵.val.isFiberedInGroupoids hU eU)).obj
        M) :=
  have := (stackModuleDirectImageData.{u, t} B S hS .etale).enoughInjectives 𝒵
  have e : stackModuleToposDirectImage B S hS g .etale ≅ stackModuleDirectImage B S hS g .etale :=
    pushforwardModulesIsoStackModuleDirectImage B S hS g .etale
  have := Functor.additive_of_iso e.symm
  (AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS G
      𝒲.val.val.p 𝒲.val.isFiberedInGroupoids hG eG)).mapIso
      (stackModuleHigherDirectImageObjIso B S hS g i M ≪≫
        ((Functor.rightDerivedIsoOfNatIso e i).app M).symm ≪≫
        stackModuleToposHigherDirectImageObjIso B S hS g i M) ≪≫
    restrictedToposHigherDirectImageIsoOfRepresentable B S hS g U hU eU G hG eG i M

/-- **The 2-fibre product `V ×_𝒴 𝒳` is represented by an algebraic space** when `f` is
representable by algebraic spaces (Stacks 0300, via
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`): this is the
algebraic space `U` of Stacks 0GQH, and the presentation `eU` below always exists. -/
theorem exists_isAlgebraicSpace_equivalenceOver_twoFibreProduct
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    ∃ U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS U ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
        (presheafOfCategories (U ⋙ typeToCat)).p) :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS 𝒳.val 𝒴.val
    (schemeStack.{u, t} B S hS V).val f.hom y.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom y.hom).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom y.hom))
    hf (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)

variable (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G)
  (eG : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, t} B S hS V).val.val.p
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (eU : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
    (presheafOfCategories (U ⋙ typeToCat)).p)

/-- The base change `f' : U ⟶ V` of `f` along `y : V ⟶ 𝒴`, as a morphism of algebraic spaces: the
morphism induced by the second projection of the 2-fibre product `U = V ×_𝒴 𝒳`, through the
presentation `eU` of the 2-fibre product by the algebraic space `U`. -/
abbrev baseChangeSpacesHom :
    (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩ :=
  Space.inducedAlgebraicSpacesHom B S hS U G
    (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
    (schemeStack.{u, t} B S hS V).val.val.p hU hG eU
    eG _ (isFibredOneMorphism_twoFibreProduct_snd B S hS f y)

/-- **Stacks 0GQH with `Rⁱf_*` computed in the étale topology, for every module.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, `y : V ⟶ 𝒴` an object of `𝒴` over a scheme
`V`, and `U = V ×_𝒴 𝒳` presented by an algebraic space `U` (`eU`). Let `G` present `(Sch/V)`
(`eG`), for instance `V` itself. Then for every sheaf of `𝒪_𝒳`-modules `ℱ` on `𝒳_étale` and
every `i`,

```text
(Rⁱf_*ℱ)|_{V_étale} ≅ Rⁱf'_{small,*}(ℱ|_{U_étale}),
```

where `(-)|_{V_étale}` is `y⁻¹` followed by the restriction `π_{V,*}` of Stacks 073M,
`(-)|_{U_étale}` is `(y')⁻¹` followed by `π_{U,*}`, and `f'_{small,*}` is the direct image of
the small étale sites of the algebraic spaces along the base change `f' : U ⟶ V`. -/
def restrictedStackModuleHigherDirectImageIso (i : ℕ) (F : StackModules B S hS .etale 𝒳) :
    (AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS G
        (schemeStack.{u, t} B S hS V).val.val.p
        (schemeStack.{u, t} B S hS V).val.isFiberedInGroupoids hG eG)).obj
      ((stackModuleInverseImage B S hS .etale y).obj
        ((stackModuleHigherDirectImage B S hS f .etale i).obj F)) ≅
    ((AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.smallEtaleRingedToposHom B S hS
        (baseChangeSpacesHom B S hS f y G hG eG U hU eU))).rightDerived i).obj
      ((AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS U
        (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
        (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.isFiberedInGroupoids hU eU)).obj
        ((stackModuleInverseImage B S hS .etale
          (twoFibreProductSquareAlgebraicStacks B S hS f y).fst).obj F)) := by
  have bc := StackModuleDirectImage.higherDirectImageBaseChangeIso B S hS f .etale
    (stackModuleDirectImageData.{u, t} B S hS .etale) y i F
  rw [stackModuleDirectImageData_higherDirectImage, stackModuleDirectImageData_higherDirectImage]
    at bc
  have e := restrictedStackModuleHigherDirectImageIsoOfRepresentable B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f y).snd U hU eU G hG eG i
      ((stackModuleInverseImage B S hS .etale
          (twoFibreProductSquareAlgebraicStacks B S hS f y).fst).obj F)
  exact (AlgebraicGeometry.RingedToposHom.pushforwardModules
      (Space.projectionRingedToposHom B S hS G (schemeStack.{u, t} B S hS V).val.val.p
      (schemeStack.{u, t} B S hS V).val.isFiberedInGroupoids hG eG)).mapIso bc ≪≫ e

/-- **Stacks 0GQH, étale reading, with `V` a scheme**: the case of
`AlgebraicGeometry.Stack.restrictedStackModuleHigherDirectImageIso` in which the algebraic stack of
the scheme `V` is presented by `V` itself. -/
def restrictedStackModuleHigherDirectImageIsoOfScheme (i : ℕ) (F : StackModules B S hS .etale 𝒳) :
    (AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS
        (yoneda.obj V) (schemeStack.{u, t} B S hS V).val.val.p
        (schemeStack.{u, t} B S hS V).val.isFiberedInGroupoids (isAlgebraicSpace_yoneda B S hS V)
        (schemeStackEquivalenceOver B S hS))).obj
      ((stackModuleInverseImage B S hS .etale y).obj
        ((stackModuleHigherDirectImage B S hS f .etale i).obj F)) ≅
    (Space.smallEtaleHigherDirectImage
        (baseChangeSpacesHom B S hS f y (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
          (schemeStackEquivalenceOver B S hS) U hU eU) i).obj
      ((AlgebraicGeometry.RingedToposHom.pushforwardModules (Space.projectionRingedToposHom B S hS U
        (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
        (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.isFiberedInGroupoids hU eU)).obj
        ((stackModuleInverseImage B S hS .etale
          (twoFibreProductSquareAlgebraicStacks B S hS f y).fst).obj F)) :=
  restrictedStackModuleHigherDirectImageIso B S hS f y (yoneda.obj V)
    (isAlgebraicSpace_yoneda B S hS V) (schemeStackEquivalenceOver B S hS) U hU eU i F

end Stack

end AlgebraicGeometry
