module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites

/-!
# Derived base change of sheaves of modules for the lisse-étale and flat-fppf sites

Let `f : 𝒳 ⟶ 𝒴` be a smooth (respectively flat) 1-morphism of algebraic stacks over a scheme
`S`. Write `𝒳_τ`, `𝒴_τ` for the big étale (respectively big fppf) sites of **Stacks 06TP** and
`𝒳'`, `𝒴'` for the lisse-étale (respectively flat-fppf) subsites of **Stacks 0787**, and let
`g : Sh(𝒳') ⟶ Sh(𝒳_τ)` and `g : Sh(𝒴') ⟶ Sh(𝒴_τ)` — here written `g'` over `𝒳` and `g` over
`𝒴` — be the morphisms of topoi of **Stacks 0788** attached to the inclusions of the subsites.
By **Stacks 07AT** the underlying functor of `f` restricts to a functor `f'` of the two
subsites, and the resulting square of ringed topoi
```
  (Sh(𝒳'), 𝒪_{𝒳'}) --g'--> (Sh(𝒳_τ), 𝒪_𝒳)
        |                        |
        f'                       f
        v                        v
  (Sh(𝒴'), 𝒪_{𝒴'}) --g-->  (Sh(𝒴_τ), 𝒪_𝒴)
```
commutes. The structure sheaf of a subsite *is* the restriction of the ambient one — that is the
content of **Stacks 0788** (f) — so `g^* = g^{-1}` and `(g')^* = (g')^{-1}` on sheaves of
modules are the inverse images `Stacks.SheafOfModules.inverseImage` of **Stacks 0797**, and they
are exact. **Stacks 07AV** asserts the two identities

`g^{-1} ∘ Rf_* = Rf'_* ∘ (g')^{-1}` and `L(g')_! ∘ (f')^{-1} = f^{-1} ∘ Lg_!`

on the unbounded derived categories, for sheaves of modules as well as for abelian sheaves. It is
proved with no hypothesis, for sheaves of modules in
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleModuleDerivedBaseChange.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfModuleDerivedBaseChange.lean`, and for abelian
sheaves in `StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleDerivedBaseChange.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedBaseChange.lean`. This file supplies the
ringed square those files use (the structure maps and the degreewise functors), together with an
earlier form of the module case, conditional on the inputs described below.

The sheaves of rings are the structure sheaves of **Stacks 06TV**, with sections in `Type u`,
and the sheaves of modules have sections in `Type (u + 1)`: the two sites have objects in
`Type (u + 1)` and morphisms in `Type u`, and the module universe has to dominate both for
`Mod(𝒪)` to be Grothendieck abelian, which is what makes K-injective resolutions — hence the
unbounded derived functors — available.

## Main definitions

* `AlgebraicGeometry.Stack.structureMapHomFunctor`: the structure map
  `f^♯ : 𝒪_𝒴 ⟶ f_* 𝒪_𝒳` of the morphism of ringed topoi attached to a 1-morphism, obtained from
  **Stacks 06TW** by transposition.
* `AlgebraicGeometry.Stack.restrictedStructureMap`: the structure map `(f')^♯` of the restricted
  column, forced by the square.
* `AlgebraicGeometry.Stack.FlatFppf.moduleInverseImage`,
  `AlgebraicGeometry.Stack.FlatFppf.modulePushforward`,
  `AlgebraicGeometry.Stack.FlatFppf.restrictedModulePushforward` and their lisse-étale
  counterparts: the three degreewise functors `g^*`, `f_*`, `f'_*` of the square on sheaves of
  modules.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.nonempty_moduleInverseImage_comp_derivedPushforward_iso` and
  `AlgebraicGeometry.Stack.LisseEtale.nonempty_moduleInverseImage_comp_derivedPushforward_iso`:
  a conditional form of the first identity of **Stacks 07AV**, for sheaves of modules on the
  flat-fppf and on the lisse-étale site.
* `AlgebraicGeometry.Stack.FlatFppf.nonempty_derivedLowerShriek_comp_moduleInverseImage_iso` and
  `AlgebraicGeometry.Stack.LisseEtale.nonempty_derivedLowerShriek_comp_moduleInverseImage_iso`:
  a conditional form of the second identity of **Stacks 07AV**, for sheaves of modules on the
  two sites.
* `AlgebraicGeometry.Stack.nonempty_subsiteInverseImage_comp_derivedPushforward_iso` and
  `AlgebraicGeometry.Stack.nonempty_derivedSubsiteLowerShriek_comp_inverseImage_iso`: the two
  identities for an arbitrary full subsite of the site of **Stacks 06TP**, of which the four
  conditional statements above are the instantiations.
* `AlgebraicGeometry.Stack.sheafPushforwardContinuous_ringStructureSheafCore`: **Stacks 06TW**
  for the underlying sheaves of rings, the input from which the structure map `f^♯` is built.

## What is carried as a hypothesis, and why

*An isomorphism, not an equality.* A right derived functor is determined only up to a canonical
isomorphism, so the conclusions are isomorphisms of functors, and `Rf_*`, `Rf'_*` are carried as
data together with their comparisons from the degreewise direct images and the
`IsRightDerivedFunctor` property, as in the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites`.
Nothing in the library names the unbounded total right derived functor of
`Stacks.SheafOfModules.pushforwardCocontinuous`.

*The degree-zero square.* The hypothesis `hzero` is the identification
`f'_* ∘ (g')^* ≅ g^* ∘ f_*` on sheaves of modules, which is **Stacks 07AT** (1), respectively
(2), read on modules. The general base-change theorem **Stacks 0FN3** produces it from a
cofinality condition on the comparison functors of the index categories of Section 00XF; that
condition is not available for these two squares, so the degree-zero identification is granted
instead. This is the same input that the abelian-sheaf file carries, there also under the name
`hzero`.

*Preservation of K-injectivity.* The hypothesis `hKinj` is that `(g')^*` carries K-injective
complexes of `𝒪_𝒳`-modules to K-injective complexes of `𝒪_{𝒳'}`-modules. This hypothesis is
false in general, and nothing in the source supplies it. By **Stacks 08BJ**,
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, it would follow from left exactness
of the module-level lower shriek `g'_!` of **Stacks 0797**. But neither **Stacks 0789** nor
**Stacks 07AS** asserts that exactness — 07AS gives only the existence of `Lg_!`, the adjunction
and `g^* Lg_! = id` — and it fails: for `𝒳 = 𝔸¹` the image under `g'_!` of the injective map
`t : 𝒪 ⟶ 𝒪` of the lisse-étale structure sheaf is multiplication by `t` on `𝒪_{𝒳_{étale}}`, which
is zero on the closed point. `StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleDerivedBaseChange.lean`
calls the assertion that `(g')^*` preserves K-injectivity false. The unconditional files named
above replace it with the true statement that restricted K-injective complexes compute `Rf'_*`.
That is why the conditional statements here are not registered under **Stacks 07AV**.

*The adjunctions of the second identity.* The second identity is the conjugate of the first
across two composed adjunctions, so it carries the derived lower shrieks `Lg_!`, `L(g')_!` and
the derived inverse images `f^*`, `(f')^*` as data, together with the adjunctions
`Lg_! ⊣ g^*`, `L(g')_! ⊣ (g')^*` — **Stacks 07AS** (2)/(4) on the derived categories, proved
with no hypothesis in `StacksFrontier/AlgebraicGeometry/Stacks/SubsiteModuleDerivedLowerShriek.lean`
but taken here as arbitrary inputs — and `f^* ⊣ Rf_*`, `(f')^* ⊣ Rf'_*`. Given those, the
identity is forced:
conjugation of a natural isomorphism across adjunctions is a bijection,
`CategoryTheory.conjugateIsoEquiv`.

## References

* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 0FN6](https://stacks.math.columbia.edu/tag/0FN6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

open Stacks.SheafOfModules

universe u w dC dC' dD dD'

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- Continuity of the underlying functor of a 1-morphism of algebraic stacks for the sites of
**Stacks 06TP**, as a local instance. -/
local instance instIsContinuousHomFunctor (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (τ : GrothendieckTopology B.Schemes)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    f.hom.hom.toFunctor.IsContinuous (associatedTopology B S hS 𝒳.val.val.p τ)
      (associatedTopology B S hS 𝒴.val.val.p τ) :=
  (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f τ).1

/-- Cocontinuity of the underlying functor of a 1-morphism of algebraic stacks for the sites of
**Stacks 06TP**, as a local instance. -/
local instance instIsCocontinuousHomFunctor (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (τ : GrothendieckTopology B.Schemes)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    f.hom.hom.toFunctor.IsCocontinuous (associatedTopology B S hS 𝒳.val.val.p τ)
      (associatedTopology B S hS 𝒴.val.val.p τ) :=
  (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f τ).2

/-- The right Kan extensions of presheaves of rings with sections in `Type u` along a functor of
sites whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u` exist, provided
both sites are essentially small in `Type u`: the comma categories indexing them are then
essentially small, so the limits computing them exist in rings. -/
local instance instHasPointwiseRightKanExtensionRingCat {X : Type (u + 1)} [Category.{u} X]
    {Y : Type (u + 1)} [Category.{u} Y] [EssentiallySmall.{u} X] [EssentiallySmall.{u} Y]
    (F : X ⥤ Y) (G : Xᵒᵖ ⥤ RingCat.{u}) : F.op.HasPointwiseRightKanExtension G := fun Z => by
  have := hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Z F.op) RingCat.{u}
  infer_instance

/-- The same for presheaves of abelian groups with sections in `Type (u + 1)`, the universe in
which the sheaves of modules below take their sections. -/
local instance instHasPointwiseRightKanExtensionAddCommGrpCat {X : Type (u + 1)} [Category.{u} X]
    {Y : Type (u + 1)} [Category.{u} Y] [EssentiallySmall.{u} X] [EssentiallySmall.{u} Y]
    (F : X ⥤ Y) (G : Xᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.op.HasPointwiseRightKanExtension G := fun Z => by
  have := hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Z F.op)
    AddCommGrpCat.{u + 1}
  infer_instance

section Subsite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **Stacks 06TW for the underlying sheaves of rings.** The restriction along a 1-morphism `f`
of the structure sheaf of `𝒴` is the structure sheaf of `𝒳`, as an equality of sheaves of rings:
both are the restriction of one and the same structure sheaf of the base, along `𝒴.p` preceded by
`f` on one side and along `𝒳.p = f ⋙ 𝒴.p` on the other, and the sheaf condition is a
proposition. -/
theorem sheafPushforwardContinuous_ringStructureSheafCore :
    (f.hom.hom.toFunctor.sheafPushforwardContinuous RingCat.{u}
          (associatedTopology B S hS 𝒳.val.val.p τ)
          (associatedTopology B S hS 𝒴.val.val.p τ)).obj
        (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ) =
      ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ :=
  ObjectProperty.FullSubcategory.ext (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p
    𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
    f.hom.hom.w τ hτ).symm

/-- The structure map `f^♯ : 𝒪_𝒴 ⟶ f_* 𝒪_𝒳` of sheaves of rings on the sites of **Stacks 06TP**:
the transpose, across the adjunction between restriction along `f` and the direct image of
**Stacks 00XO**, of the identification of **Stacks 06TW** that the restriction of `𝒪_𝒴` is
`𝒪_𝒳`. It is this map that makes the morphism of topoi attached to `f` a morphism of ringed
topoi, and hence gives the direct image of sheaves of modules along `f`. -/
def structureMapHomFunctor :
    ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ ⟶
      (f.hom.hom.toFunctor.sheafPushforwardCocontinuous RingCat.{u}
          (associatedTopology B S hS 𝒳.val.val.p τ)
          (associatedTopology B S hS 𝒴.val.val.p τ)).obj
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ) :=
  (f.hom.hom.toFunctor.sheafAdjunctionCocontinuous RingCat.{u}
      (associatedTopology B S hS 𝒳.val.val.p τ)
      (associatedTopology B S hS 𝒴.val.val.p τ)).homEquiv _ _
    (eqToHom (sheafPushforwardContinuous_ringStructureSheafCore B S hS τ hτ f))

variable (P : ObjectProperty 𝒳.val.val.obj) (Q : ObjectProperty 𝒴.val.val.obj)
  (J' : GrothendieckTopology P.FullSubcategory) (K' : GrothendieckTopology Q.FullSubcategory)
  (u' : P.FullSubcategory ⥤ Q.FullSubcategory) [u'.IsCocontinuous J' K']
  [P.ι.IsContinuous J' (associatedTopology B S hS 𝒳.val.val.p τ)]
  [P.ι.IsCocontinuous J' (associatedTopology B S hS 𝒳.val.val.p τ)]
  [Q.ι.IsContinuous K' (associatedTopology B S hS 𝒴.val.val.p τ)]
  [Q.ι.IsCocontinuous K' (associatedTopology B S hS 𝒴.val.val.p τ)]
  (hsq : u' ⋙ Q.ι = P.ι ⋙ f.hom.hom.toFunctor)

/-- The structure map `(f')^♯ : 𝒪_{𝒴'} ⟶ f'_* 𝒪_{𝒳'}` of the restricted column of the square:
the restriction along the inclusion of the subsite of `𝒴` of `f^♯`, followed by the base-change
comparison of **Stacks 0FN1** for sheaves of rings. This is the structure map the commutativity
of the square forces; nothing is chosen. -/
def restrictedStructureMap :
    inverseImageRing K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
        (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ) ⟶
      (u'.sheafPushforwardCocontinuous RingCat.{u} J' K').obj
        (inverseImageRing J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
          (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)) :=
  structureMapSquare (structureMapHomFunctor B S hS τ hτ f) hsq

variable
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{u + 1}
    (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ))]
  [HasDerivedCategory.{dC'} (_root_.SheafOfModules.{u + 1}
    (inverseImageRing J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{u + 1}
    (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ))]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{u + 1}
    (inverseImageRing K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
      (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ)))]
  (Rf : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ)))
  (Rf' : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (inverseImageRing J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ))) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1}
      (inverseImageRing K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
        (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ))))
  (αf : (pushforwardCocontinuous.{u + 1} f.hom.hom.toFunctor
        (structureMapHomFunctor B S hS τ hτ f)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  (αf' : (pushforwardCocontinuous.{u + 1} u'
        (restrictedStructureMap B S hS τ hτ f P Q J' K' u' hsq)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')

/-- **Base change of the total direct image of sheaves of modules across the square of a full
subsite.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, let `P` and `Q` cut out full
subsites of the sites of **Stacks 06TP** on `𝒳` and on `𝒴` whose inclusions are continuous as
well as cocontinuous, and let `u'` be a cocontinuous functor of the two subsites restricting `f`.
Take the structure sheaves of **Stacks 06TV** upstairs and their restrictions downstairs, so that
`g^* = g^{-1}` and `(g')^* = (g')^{-1}` are the exact inverse images of **Stacks 0797**. Granted
the degree-zero identification `hzero` and the preservation `hKinj` of K-injectivity by `(g')^*`,
the total right derived direct images satisfy `Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*`.

The content is `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIso`: both sides are right
derived functors of one and the same functor on homotopy categories, `(g')^*` preserving
K-injectivity, and right derived functors over a Grothendieck abelian category are absolute. -/
theorem nonempty_subsiteInverseImage_comp_derivedPushforward_iso
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ))
      (ComplexShape.up ℤ))]
    [Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
      (inverseImageRing J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)))
      (ComplexShape.up ℤ))]
    (hzero : inverseImage.{u + 1} J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
          (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ) ⋙
        pushforwardCocontinuous.{u + 1} u'
          (restrictedStructureMap B S hS τ hτ f P Q J' K' u' hsq) ≅
      pushforwardCocontinuous.{u + 1} f.hom.hom.toFunctor
          (structureMapHomFunctor B S hS τ hτ f) ⋙
        inverseImage.{u + 1} K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
          (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ))
    (hKinj : ∀ I : CochainComplex (_root_.SheafOfModules.{u + 1}
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        (((inverseImage.{u + 1} J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
          (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ
            hτ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    Nonempty ((inverseImage.{u + 1} J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
          (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ
            hτ)).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (inverseImage.{u + 1} K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
        (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ
          hτ)).mapDerivedCategory) :=
  ⟨Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIso _ _ _ _ Rf Rf' αf αf' hzero hKinj⟩

variable
  (fStar : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)))
  (f'Star : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (inverseImageRing K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
        (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ))) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1}
      (inverseImageRing J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ))))
  (Lg : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (inverseImageRing K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
        (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ))) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ)))
  (Lg' : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (inverseImageRing J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ))) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)))

/-- **The conjugate base change across the square of a full subsite.** In the situation of
`AlgebraicGeometry.Stack.nonempty_subsiteInverseImage_comp_derivedPushforward_iso`, suppose
moreover that the two derived inverse images `f^*`, `(f')^*` are left adjoint to `Rf_*`, `Rf'_*`
and that the two derived lower shrieks `Lg_!`, `L(g')_!` are left adjoint to `g^*`, `(g')^*` on
the derived categories. Then `f^* ∘ Lg_! ≅ L(g')_! ∘ (f')^*`.

Both sides are left adjoint to the two sides of the first identity — `(f')^* ⋙ L(g')_!` to
`(g')^* ⋙ Rf'_*` and `Lg_! ⋙ f^*` to `Rf_* ⋙ g^*`, by `CategoryTheory.Adjunction.comp` — so the
isomorphism is the conjugate of the first one under `CategoryTheory.conjugateIsoEquiv`. -/
theorem nonempty_derivedSubsiteLowerShriek_comp_inverseImage_iso
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ))
      (ComplexShape.up ℤ))]
    [Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
      (inverseImageRing J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)))
      (ComplexShape.up ℤ))]
    (adjf : fStar ⊣ Rf) (adjf' : f'Star ⊣ Rf')
    (adjg : Lg ⊣ (inverseImage.{u + 1} K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
      (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ
        hτ)).mapDerivedCategory)
    (adjg' : Lg' ⊣ (inverseImage.{u + 1} J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ
        hτ)).mapDerivedCategory)
    (hzero : inverseImage.{u + 1} J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
          (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ) ⋙
        pushforwardCocontinuous.{u + 1} u'
          (restrictedStructureMap B S hS τ hτ f P Q J' K' u' hsq) ≅
      pushforwardCocontinuous.{u + 1} f.hom.hom.toFunctor
          (structureMapHomFunctor B S hS τ hτ f) ⋙
        inverseImage.{u + 1} K' (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
          (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ))
    (hKinj : ∀ I : CochainComplex (_root_.SheafOfModules.{u + 1}
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        (((inverseImage.{u + 1} J' (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
          (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ
            hτ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    Nonempty (Lg ⋙ fStar ≅ f'Star ⋙ Lg') := by
  obtain ⟨σ⟩ := nonempty_subsiteInverseImage_comp_derivedPushforward_iso B S hS τ hτ f P Q J' K'
    u' hsq Rf Rf' αf αf' hzero hKinj
  exact ⟨(conjugateIsoEquiv (adjf'.comp adjg') (adjg.comp adjf)).symm σ⟩

end Subsite

namespace FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure sheaf of the fppf site of an algebraic stack as a sheaf of rings: the
`RingCat`-valued structure sheaf of **Stacks 06TV** at the fppf topology, which is the sheaf of
rings over which the sheaves of modules of **Stacks 07AV** are taken. -/
abbrev ambientRingStructureSheaf (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Sheaf (associatedTopology B S hS 𝒵.val.val.p B.topology) RingCat.{u} :=
  ringStructureSheafCore B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids B.topology le_rfl

/-- The structure sheaf of the flat-fppf site of an algebraic stack as a sheaf of rings: the
restriction of `AlgebraicGeometry.Stack.FlatFppf.ambientRingStructureSheaf` along the inclusion
of the flat objects. That this restriction *is* the structure sheaf of the subsite is
**Stacks 0788** (2)(f), and it holds here by construction, as for
`AlgebraicGeometry.Stack.FlatFppf.structureSheaf`. -/
abbrev subsiteRingStructureSheaf (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Sheaf (topology B S hS 𝒵) RingCat.{u} :=
  inverseImageRing (topology B S hS 𝒵) (associatedTopology B S hS 𝒵.val.val.p B.topology)
    (objectProperty B S hS 𝒵).ι (ambientRingStructureSheaf B S hS 𝒵)

/-- The inverse image `g^* = g^{-1}` of sheaves of modules along the morphism of ringed topoi of
**Stacks 0788** (2): restriction along the inclusion of the flat objects, the structure sheaf of
the flat-fppf site being the restriction of the fppf one. By **Stacks 07AS** (2) it is exact. -/
abbrev moduleInverseImage (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒵) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒵) :=
  inverseImage.{u + 1} (topology B S hS 𝒵) (associatedTopology B S hS 𝒵.val.val.p B.topology)
    (objectProperty B S hS 𝒵).ι (ambientRingStructureSheaf B S hS 𝒵)

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The direct image `f_*` of sheaves of modules along a 1-morphism of algebraic stacks, for the
fppf sites and the structure map `f^♯` of **Stacks 06TW**. -/
abbrev modulePushforward :
    _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴) :=
  pushforwardCocontinuous.{u + 1} f.hom.hom.toFunctor
    (structureMapHomFunctor B S hS B.topology le_rfl f)

variable (hf : AlgebraicStacks.IsFlat B S hS f)

/-- Cocontinuity of the restriction of a flat 1-morphism to the flat-fppf sites, **Stacks 07AT**
(2), as a local instance. -/
local instance instIsCocontinuousSiteFunctor :
    (siteFunctor B S hS f hf).1.IsCocontinuous (topology B S hS 𝒳) (topology B S hS 𝒴) :=
  siteFunctor_isCocontinuous B S hS f hf

/-- The direct image `f'_*` of sheaves of modules along the restriction `f'` of a flat
1-morphism to the flat-fppf sites, for the structure map that the square of **Stacks 07AT** (2)
forces. -/
abbrev restrictedModulePushforward :
    _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴) :=
  pushforwardCocontinuous.{u + 1} (siteFunctor B S hS f hf).1
    (restrictedStructureMap B S hS B.topology le_rfl f (objectProperty B S hS 𝒳)
      (objectProperty B S hS 𝒴) (topology B S hS 𝒳) (topology B S hS 𝒴)
      (siteFunctor B S hS f hf).1 (siteFunctor B S hS f hf).2)

variable
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{dC'} (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴))]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴))]
  (Rf : DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)))
  (Rf' : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)))
  (αf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  (αf' : (restrictedModulePushforward B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
    (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) (ComplexShape.up ℤ))]
  [Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
    (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) (ComplexShape.up ℤ))]

include αf αf'

/-- **A conditional form of Stacks 07AV for sheaves of modules on the flat-fppf site, first
identity.** Let
`f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, let `g` and `g'` be the inclusions of the
flat-fppf subsites of `𝒴` and of `𝒳`, and let `f'` be the restriction of `f` to those subsites,
**Stacks 07AT** (2). Suppose the degree-zero square `f'_* ∘ (g')^* ≅ g^* ∘ f_*` of sheaves of
modules holds, and that `(g')^*` carries K-injective complexes to K-injective complexes. Then

`Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*`

on the unbounded derived categories of sheaves of modules.

This is not the statement of Stacks 07AV, and it is not registered under that tag: the hypothesis
`hKinj` is false in general (see the module docstring), and `hzero` is assumed rather than proved.
The unconditional statement is
`AlgebraicGeometry.Stack.FlatFppf.moduleDerivedRestrictionBaseChangeIso`. -/
theorem nonempty_moduleInverseImage_comp_derivedPushforward_iso
    (hzero : moduleInverseImage B S hS 𝒳 ⋙ restrictedModulePushforward B S hS f hf ≅
      modulePushforward B S hS f ⋙ moduleInverseImage B S hS 𝒴)
    (hKinj : ∀ I : CochainComplex
        (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        (((moduleInverseImage B S hS 𝒳).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    Nonempty ((moduleInverseImage B S hS 𝒳).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (moduleInverseImage B S hS 𝒴).mapDerivedCategory) :=
  nonempty_subsiteInverseImage_comp_derivedPushforward_iso B S hS B.topology le_rfl f
    (objectProperty B S hS 𝒳) (objectProperty B S hS 𝒴) (topology B S hS 𝒳)
    (topology B S hS 𝒴) (siteFunctor B S hS f hf).1 (siteFunctor B S hS f hf).2 Rf Rf' αf αf'
    hzero hKinj

variable
  (fStar : DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
  (f'Star : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (subsiteRingStructureSheaf B S hS 𝒴)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)))
  (Lg : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)))
  (Lg' : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))

/-- **A conditional form of Stacks 07AV for sheaves of modules on the flat-fppf site, second
identity.** In the
situation of
`AlgebraicGeometry.Stack.FlatFppf.nonempty_moduleInverseImage_comp_derivedPushforward_iso`,
suppose moreover that `f^*` and `(f')^*` are left adjoint to `Rf_*` and `Rf'_*` and that `Lg_!`
and `L(g')_!` are left adjoint to `g^*` and `(g')^*` on the derived categories. Then

`f^* ∘ Lg_! ≅ L(g')_! ∘ (f')^*`

on the unbounded derived categories of sheaves of modules.

This is not the statement of Stacks 07AV, and it is not registered under that tag: besides the
hypotheses `hzero` and `hKinj` of the first identity (`hKinj` being false in general), the four
adjunctions are arbitrary inputs. The unconditional statement is
`AlgebraicGeometry.Stack.FlatFppf.moduleDerivedLowerShriekBaseChangeIso`. -/
theorem nonempty_derivedLowerShriek_comp_moduleInverseImage_iso
    (adjf : fStar ⊣ Rf) (adjf' : f'Star ⊣ Rf')
    (adjg : Lg ⊣ (moduleInverseImage B S hS 𝒴).mapDerivedCategory)
    (adjg' : Lg' ⊣ (moduleInverseImage B S hS 𝒳).mapDerivedCategory)
    (hzero : moduleInverseImage B S hS 𝒳 ⋙ restrictedModulePushforward B S hS f hf ≅
      modulePushforward B S hS f ⋙ moduleInverseImage B S hS 𝒴)
    (hKinj : ∀ I : CochainComplex
        (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        (((moduleInverseImage B S hS 𝒳).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    Nonempty (Lg ⋙ fStar ≅ f'Star ⋙ Lg') :=
  nonempty_derivedSubsiteLowerShriek_comp_inverseImage_iso B S hS B.topology le_rfl f
    (objectProperty B S hS 𝒳) (objectProperty B S hS 𝒴) (topology B S hS 𝒳)
    (topology B S hS 𝒴) (siteFunctor B S hS f hf).1 (siteFunctor B S hS f hf).2 Rf Rf' αf αf'
    fStar f'Star Lg Lg' adjf adjf' adjg adjg' hzero hKinj

end FlatFppf

namespace LisseEtale

attribute [local instance] isContinuous_inclusion_topology' isCocontinuous_inclusion_topology'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big étale site of an algebraic stack: the site of **Stacks 06TP** at the étale topology
of the base, the ambient site of the lisse-étale subsite. -/
abbrev ambientTopology (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    GrothendieckTopology 𝒵.val.val.obj :=
  associatedTopology B S hS 𝒵.val.val.p (etaleTopology B)

/-- The structure sheaf of the big étale site of an algebraic stack as a sheaf of rings, the
sheaf of rings over which the sheaves of modules of **Stacks 07AV** are taken. -/
abbrev ambientRingStructureSheaf (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Sheaf (ambientTopology B S hS 𝒵) RingCat.{u} :=
  ringStructureSheafCore B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B)

/-- The structure sheaf of the lisse-étale site of an algebraic stack as a sheaf of rings: the
restriction of `AlgebraicGeometry.Stack.LisseEtale.ambientRingStructureSheaf` along the inclusion
of the smooth objects. That this restriction *is* the structure sheaf of the subsite is
**Stacks 0788** (1)(f). -/
abbrev subsiteRingStructureSheaf (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Sheaf (topology.{u, w} B S hS 𝒵) RingCat.{u} :=
  inverseImageRing (topology.{u, w} B S hS 𝒵) (ambientTopology B S hS 𝒵)
    (smoothObject.{u, w} B S hS 𝒵).ι (ambientRingStructureSheaf B S hS 𝒵)

/-- The inverse image `g^* = g^{-1}` of sheaves of modules along the morphism of ringed topoi of
**Stacks 0788** (1): restriction along the inclusion of the smooth objects, the structure sheaf
of the lisse-étale site being the restriction of the étale one. By **Stacks 07AS** (1) it is
exact. -/
abbrev moduleInverseImage (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒵) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒵) :=
  inverseImage.{u + 1} (topology.{u, w} B S hS 𝒵) (ambientTopology B S hS 𝒵)
    (smoothObject.{u, w} B S hS 𝒵).ι (ambientRingStructureSheaf B S hS 𝒵)

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The direct image `f_*` of sheaves of modules along a 1-morphism of algebraic stacks, for the
big étale sites and the structure map `f^♯` of **Stacks 06TW**. -/
abbrev modulePushforward :
    _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴) :=
  pushforwardCocontinuous.{u + 1} f.hom.hom.toFunctor
    (structureMapHomFunctor B S hS (etaleTopology B) (etaleTopology_le_topology B) f)

variable (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- Cocontinuity of the restriction of a smooth 1-morphism to the lisse-étale sites,
**Stacks 07AT** (1), as a local instance. -/
local instance instIsCocontinuousSiteFunctor :
    (siteFunctor.{u, w} B S hS f hf).1.IsCocontinuous (topology.{u, w} B S hS 𝒳)
      (topology.{u, w} B S hS 𝒴) :=
  siteFunctor_isCocontinuous.{u, w} B S hS f hf

/-- The direct image `f'_*` of sheaves of modules along the restriction `f'` of a smooth
1-morphism to the lisse-étale sites, for the structure map that the square of **Stacks 07AT** (1)
forces. -/
abbrev restrictedModulePushforward :
    _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴) :=
  pushforwardCocontinuous.{u + 1} (siteFunctor.{u, w} B S hS f hf).1
    (restrictedStructureMap B S hS (etaleTopology B) (etaleTopology_le_topology B) f
      (smoothObject.{u, w} B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒴)
      (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)
      (siteFunctor.{u, w} B S hS f hf).1 (siteFunctor.{u, w} B S hS f hf).2)

variable
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{dC'} (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴))]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴))]
  (Rf : DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)))
  (Rf' : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)))
  (αf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  (αf' : (restrictedModulePushforward B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
    (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) (ComplexShape.up ℤ))]
  [Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
    (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) (ComplexShape.up ℤ))]

include αf αf'

/-- **A conditional form of Stacks 07AV for sheaves of modules on the lisse-étale site, first
identity.** Let
`f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks, let `g` and `g'` be the inclusions of
the lisse-étale subsites of `𝒴` and of `𝒳`, and let `f'` be the restriction of `f` to those
subsites, **Stacks 07AT** (1). Suppose the degree-zero square `f'_* ∘ (g')^* ≅ g^* ∘ f_*` of
sheaves of modules holds, and that `(g')^*` carries K-injective complexes to K-injective
complexes. Then

`Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*`

on the unbounded derived categories of sheaves of modules.

This is not the statement of Stacks 07AV, and it is not registered under that tag: the hypothesis
`hKinj` is false in general (see the module docstring), and `hzero` is assumed rather than proved.
The unconditional statement is
`AlgebraicGeometry.Stack.LisseEtale.moduleDerivedRestrictionBaseChangeIso`. -/
theorem nonempty_moduleInverseImage_comp_derivedPushforward_iso
    (hzero : moduleInverseImage B S hS 𝒳 ⋙ restrictedModulePushforward B S hS f hf ≅
      modulePushforward B S hS f ⋙ moduleInverseImage B S hS 𝒴)
    (hKinj : ∀ I : CochainComplex
        (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        (((moduleInverseImage B S hS 𝒳).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    Nonempty ((moduleInverseImage B S hS 𝒳).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (moduleInverseImage B S hS 𝒴).mapDerivedCategory) :=
  nonempty_subsiteInverseImage_comp_derivedPushforward_iso B S hS (etaleTopology B)
    (etaleTopology_le_topology B) f (smoothObject.{u, w} B S hS 𝒳)
    (smoothObject.{u, w} B S hS 𝒴) (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)
    (siteFunctor.{u, w} B S hS f hf).1 (siteFunctor.{u, w} B S hS f hf).2 Rf Rf' αf αf'
    hzero hKinj

variable
  (fStar : DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
  (f'Star : DerivedCategory (_root_.SheafOfModules.{u + 1}
      (subsiteRingStructureSheaf B S hS 𝒴)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)))
  (Lg : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)))
  (Lg' : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))

/-- **A conditional form of Stacks 07AV for sheaves of modules on the lisse-étale site, second
identity.** In the
situation of
`AlgebraicGeometry.Stack.LisseEtale.nonempty_moduleInverseImage_comp_derivedPushforward_iso`,
suppose moreover that `f^*` and `(f')^*` are left adjoint to `Rf_*` and `Rf'_*` and that `Lg_!`
and `L(g')_!` are left adjoint to `g^*` and `(g')^*` on the derived categories. Then

`f^* ∘ Lg_! ≅ L(g')_! ∘ (f')^*`

on the unbounded derived categories of sheaves of modules.

This is not the statement of Stacks 07AV, and it is not registered under that tag: besides the
hypotheses `hzero` and `hKinj` of the first identity (`hKinj` being false in general), the four
adjunctions are arbitrary inputs. The unconditional statement is
`AlgebraicGeometry.Stack.LisseEtale.moduleDerivedLowerShriekBaseChangeIso`. -/
theorem nonempty_derivedLowerShriek_comp_moduleInverseImage_iso
    (adjf : fStar ⊣ Rf) (adjf' : f'Star ⊣ Rf')
    (adjg : Lg ⊣ (moduleInverseImage B S hS 𝒴).mapDerivedCategory)
    (adjg' : Lg' ⊣ (moduleInverseImage B S hS 𝒳).mapDerivedCategory)
    (hzero : moduleInverseImage B S hS 𝒳 ⋙ restrictedModulePushforward B S hS f hf ≅
      modulePushforward B S hS f ⋙ moduleInverseImage B S hS 𝒴)
    (hKinj : ∀ I : CochainComplex
        (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        (((moduleInverseImage B S hS 𝒳).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    Nonempty (Lg ⋙ fStar ≅ f'Star ⋙ Lg') :=
  nonempty_derivedSubsiteLowerShriek_comp_inverseImage_iso B S hS (etaleTopology B)
    (etaleTopology_le_topology B) f (smoothObject.{u, w} B S hS 𝒳)
    (smoothObject.{u, w} B S hS 𝒴) (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)
    (siteFunctor.{u, w} B S hS f hf).1 (siteFunctor.{u, w} B S hS f hf).2 Rf Rf' αf αf'
    fStar f'Star Lg Lg' adjf adjf' adjg adjg' hzero hKinj

end LisseEtale

end AlgebraicGeometry.Stack

end
