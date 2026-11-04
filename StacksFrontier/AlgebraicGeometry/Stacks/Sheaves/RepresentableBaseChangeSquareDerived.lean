module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHigherDirectImagesQcqs
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictionTotalDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibredModulePushforwardCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictedHigherDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact

/-!
# Base change of derived direct images along a square with representable base (Stacks 075P)

Let `S` be a scheme in a big fppf site and let

```
𝒳' = 𝒴' ×_𝒴 𝒳 --g'--> 𝒳
        |               |
        f'              f
        v               v
        𝒴' ----g---->   𝒴
```

be the canonical 2-fibre product square of algebraic stacks over `S`, with `𝒴'` represented by an
algebraic space `G'`. If `f` is representable by algebraic spaces, the apex `𝒳'` is represented by
an algebraic space `F'` (Stacks 0300). Writing `f' : F' ⟶ G'` also for the induced morphism of
algebraic spaces, Stacks 075P asserts

`g⁻¹(Rf_*ℱ)|_{G'_étale} = Rf'_{small,*}((g')⁻¹ℱ|_{F'_étale})`

for `ℱ` an abelian sheaf on `𝒳_étale` or a sheaf of `𝒪_𝒳`-modules. This file proves both, as
isomorphisms of functors on the unbounded derived categories `D(𝒳_étale)` and `D(𝒪_𝒳)`.

The source combines Stacks 075H, `g⁻¹Rf_* = Rf'_*(g')⁻¹`, with Stacks 075N for `f'`. Here the two
steps are taken at once. The square is 2-cartesian and `𝒴'` is fibred in setoids, so `g` is
faithful, hence so is `g'`, and `𝒳'` has equalizers, being represented by an algebraic space; so
`(g')_!` is exact on abelian sheaves (Stacks 06X1) and on sheaves of modules (Stacks 06X2), and
`(g')⁻¹` preserves K-injective complexes (Stacks 08BJ). Both
`α = (-)|_{F'_étale} ∘ (g')⁻¹` and `β = (-)|_{G'_étale} ∘ g⁻¹` are exact, and the underived
identity `f'_{small,*} ∘ α ≅ β ∘ f_*` is the composite of the degree-zero base change of
Stacks 075B with the square of Stacks 073N for `f'`. The abstract base change for right derived
functors, `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit`, then gives
`D(α) ⋙ Rf'_{small,*} ≅ Rf_* ⋙ D(β)`, once the unit of `Rf'_{small,*}` is known to be invertible
at `α(I)` for `I` K-injective. At abelian coefficients `α(I)` is K-injective, the restriction
preserving K-injectives (Stacks 075L); at module coefficients the restriction need not, and the
unit condition is supplied by Stacks 0D6E for `f' ∘ π_{F'}`, as in the proof of Stacks 075N.

## Main definitions

* `AlgebraicGeometry.Stack.RepresentableBaseChangeSquare.restrictedDerivedBaseChangeIsoClauses`:
  Stacks 075P, both clauses, for any presentations of `𝒳'` and `𝒴'` by algebraic spaces.
* `AlgebraicGeometry.Stack.RepresentableBaseChangeSquare.derivedAbIso`,
  `AlgebraicGeometry.Stack.RepresentableBaseChangeSquare.derivedModIso`: the two clauses.

## Main results

* `AlgebraicGeometry.Stack.RepresentableBaseChangeSquare.exists_isAlgebraicSpace_apex`: the apex
  is represented by an algebraic space when `f` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.RepresentableBaseChangeSquare.isKInjective_fstInverseImageAb`,
  `AlgebraicGeometry.Stack.RepresentableBaseChangeSquare.isKInjective_fstInverseImageMod`:
  `(g')⁻¹` preserves K-injective complexes.

## Implementation notes

The square is the canonical 2-fibre product `CategoryTheory.TwoFibreProductOver` of Stacks 0040,
with first factor `𝒳`; a 2-fibre product square in the sense of the source is one whose apex is
equivalent to it over `𝒴'` and `𝒳`. The derived direct images are those of Stacks 075N,
`AlgebraicGeometry.Space.derivedAbelianDirectImageFibred`,
`AlgebraicGeometry.Space.derivedAbelianDirectImageSpace`,
`AlgebraicGeometry.Space.derivedDirectImageFibred` and
`AlgebraicGeometry.Space.derivedDirectImageSpace`, the total right derived functors of degreewise
direct image; they exist because all sites involved are essentially small (an algebraic stack by
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`, the apex by
`CategoryTheory.TwoFibreProductOver.essentiallySmall`). Every derived category is taken in an
arbitrary model, `[HasDerivedCategory C]`. The identity holds for every presentation
`(F', eF')` of the apex, so representability of `f` enters only through
`exists_isAlgebraicSpace_apex`.

## References

* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 06X1](https://stacks.math.columbia.edu/tag/06X1)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
* [Stacks Project, Tag 075L](https://stacks.math.columbia.edu/tag/075L)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w v' w' dX dY dY₂ dA dF dG mX mY mY₂ mA mF mG

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat


/-! ### Categories fibred in groupoids represented by an algebraic space -/

namespace StacksRepresentableCFG.EquivalenceOver

variable {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*} [Category 𝒳] {p : 𝒳 ⥤ 𝒞} {P : 𝒞ᵒᵖ ⥤ Type*}
  (e : EquivalenceOver p (presheafOfCategories (P ⋙ typeToCat)).p)

include e in
/-- A category over `𝒞` equivalent over `𝒞` to the category of elements of a presheaf of sets
is faithful over `𝒞`: a morphism of elements is determined by the morphism of `𝒞` under it. -/
theorem faithful_of_presheafOfCategories : p.Faithful := by
  have : (presheafOfCategories (P ⋙ typeToCat)).p.Faithful :=
    ⟨fun h => PresheafOfCategories.elements_hom_ext _ _ h⟩
  have : e.hom.functor.Faithful := e.toEquivalence.faithful_functor
  have h : (e.hom.functor ⋙ (presheafOfCategories (P ⋙ typeToCat)).p).Faithful :=
    inferInstance
  rwa [e.hom.w] at h

include e in
/-- A category over `𝒞` equivalent over `𝒞` to the category of elements of a presheaf of sets
has equalizers as soon as the category of elements does, read as the comma category
`CostructuredArrow yoneda P`. -/
theorem hasEqualizers_of_presheafOfCategories [HasEqualizers (CostructuredArrow yoneda P)] :
    HasEqualizers 𝒳 :=
  have : (e.toEquivalence.trans
      (PresheafOfCategories.costructuredArrowToElements P).asEquivalence.symm).functor
      |>.IsEquivalence := inferInstance
  Adjunction.hasLimitsOfShape_of_equivalence
    (e.toEquivalence.trans
      (PresheafOfCategories.costructuredArrowToElements P).asEquivalence.symm).functor

end StacksRepresentableCFG.EquivalenceOver


/-! ### The two spellings of the direct and inverse images of abelian sheaves -/

namespace AlgebraicGeometry.FibredSite

open Stacks.Topos.AbelianPushforward

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q F) (τ : SiteKind)
  [∀ P : 𝒳ᵒᵖ ⥤ Type u, F.op.HasPointwiseRightKanExtension P]
  [∀ P : 𝒳ᵒᵖ ⥤ Type u, F.op.HasLeftKanExtension P]
  [HasWeakSheafify (BigFppfOver.associatedTopology B S hS q τ) (Type u)]

/-- The inverse image of abelian sheaves along the morphism of topoi a 1-morphism `F` of
categories fibred in groupoids induces is restriction of abelian sheaves along `F`. -/
def abelianInverseImageRingedToposMorphismIso :
    letI := hp.isFibered
    letI := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).1
    Sites.abelianInverseImage (ringedToposMorphism B S hS p q hp hq F hF τ).toToposHom ≅
      F.sheafPushforwardContinuous AddCommGrpCat.{u}
        (BigFppfOver.associatedTopology B S hS p τ)
        (BigFppfOver.associatedTopology B S hS q τ) := by
  letI := hp.isFibered
  letI := hq.isFibered
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  let J := BigFppfOver.associatedTopology B S hS p τ
  let K := BigFppfOver.associatedTopology B S hS q τ
  letI : (F.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K).isRightAdjoint
  exact Sites.abelianInverseImageIsoSheafPushforwardContinuous F J K
    (ringedToposMorphism B S hS p q hp hq F hF τ).toToposHom (Iso.refl _)

/-- The direct image of abelian sheaves along the morphism of topoi a 1-morphism `F` of
categories fibred in groupoids induces is the direct image of abelian sheaves along the
cocontinuous functor `F`, the right Kan extension along `F.op`: both are right adjoint to
restriction of abelian sheaves along `F`. -/
def abelianPushforwardRingedToposMorphismIso
    [∀ P : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u}, F.op.HasPointwiseRightKanExtension P] :
    letI := hp.isFibered
    letI := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).1
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).2
    abelianPushforward (BigFppfOver.associatedTopology B S hS p τ)
        (ringedToposMorphism B S hS p q hp hq F hF τ).toToposHom ≅
      F.sheafPushforwardCocontinuous AddCommGrpCat.{u}
        (BigFppfOver.associatedTopology B S hS p τ)
        (BigFppfOver.associatedTopology B S hS q τ) := by
  letI := hp.isFibered
  letI := hq.isFibered
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).2
  exact (abelianInverseImageAdjPushforward (K := BigFppfOver.associatedTopology B S hS q τ)
      (BigFppfOver.associatedTopology B S hS p τ)
      (ringedToposMorphism B S hS p q hp hq F hF τ).toToposHom).rightAdjointUniq
    ((F.sheafAdjunctionCocontinuous AddCommGrpCat.{u} _ _).ofNatIsoLeft
      (abelianInverseImageRingedToposMorphismIso B S hS p q hp hq F hF τ).symm)

end AlgebraicGeometry.FibredSite

/-! ### The square -/

namespace AlgebraicGeometry.Stack.RepresentableBaseChangeSquare

open Stacks.Topos.AbelianPushforward Stacks.Cohomology.UnboundedComplexes

/-! Size instances. Every category below is essentially small at the universe `u` of the
schemes of the site, so Kan extensions, sheafification and the Grothendieck abelian structure
are available on it; these are recorded as local instances. -/

/- The instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its two companions are
stated for sheaves of modules in a universe of the shape `max u v r w`; at the module categories
of this file their universe unification problems get stuck, so they are switched off here. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

/- The instance `AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor` asks
for limits of size `HasLimitsOfSize.{w, max v w}`; against the coefficient categories of this file,
whose universe is only determined later, its universe unification problem gets stuck, and the Kan
extensions it would provide are already supplied by the essential smallness instances below. -/
attribute [-instance] AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

attribute [local instance]
  Functor.hasPointwiseRightKanExtension_of_essentiallySmall_of_locallySmall
  Functor.hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall

/-- Sheaves of sets on an essentially small site have a sheafification. -/
local instance hasSheafify_type_of_essentiallySmall_baseChangeSquare {A : Type v}
    [Category.{w} A] [EssentiallySmall.{u} A] (J : GrothendieckTopology A) :
    HasSheafify J (Type u) :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

/-- Abelian sheaves on an essentially small site have a sheafification. -/
local instance hasSheafify_addCommGrpCat_of_essentiallySmall_baseChangeSquare {A : Type v}
    [Category.{w} A] [EssentiallySmall.{u} A] (J : GrothendieckTopology A) :
    HasSheafify J AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} J

/-- The inverse image of abelian sheaves along a morphism of topoi preserves finite limits. -/
local instance preservesFiniteLimits_abelianInverseImage {C : Type v} [Category.{w} C]
    {D : Type v'} [Category.{w'} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) :
    PreservesFiniteLimits (Sites.abelianInverseImage f) :=
  ((exactFunctor_iff _).1 (Sites.abelianInverseImage_exact f)).1

/-- The inverse image of abelian sheaves along a morphism of topoi preserves finite colimits. -/
local instance preservesFiniteColimits_abelianInverseImage {C : Type v} [Category.{w} C]
    {D : Type v'} [Category.{w'} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) :
    PreservesFiniteColimits (Sites.abelianInverseImage f) :=
  ((exactFunctor_iff _).1 (Sites.abelianInverseImage_exact f)).2

/-- The underlying category of the ringed topos associated with a category fibred in groupoids
over `(Sch/S)_{fppf}` is essentially small when that category is. -/
local instance essentiallySmall_associatedRingedTopos (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : Type v} [Category.{w} X] [EssentiallySmall.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    EssentiallySmall.{u} (FibredSite.associatedRingedTopos B S hS p hp τ).C :=
  inferInstanceAs (EssentiallySmall.{u} X)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)

/-- The apex `𝒴' ×_𝒴 𝒳` of the canonical 2-fibre product square, as a category: the
2-fibre product of Stacks 0040, with first factor `𝒳`. -/
abbrev Apex : Type (u + 1) :=
  TwoFibreProductOver 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    g.hom.hom.toFunctor

/-- The structure functor of the apex. -/
abbrev apexP : Apex B S hS f g ⥤ BigFppfOver B S hS :=
  TwoFibreProductOver.structureFunctor 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor g.hom.hom.toFunctor

/-- The apex of the square is fibred in groupoids over `(Sch/S)_{fppf}`. -/
theorem apexP_isFiberedInGroupoids : (apexP B S hS f g).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ (𝒳.val.isFiberedInGroupoids)
    (𝒴'.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.w g.hom.hom.w

/-- The apex of the square is essentially small. -/
instance essentiallySmall_apex : EssentiallySmall.{u} (Apex B S hS f g) :=
  TwoFibreProductOver.essentiallySmall f.hom.hom.w g.hom.hom.w

/-- **The apex of the square is representable by an algebraic space**, when `f` is
representable by algebraic spaces and `𝒴'` is representable by an algebraic space. This is
Stacks 0300, `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`, for the
2-fibre product with the factors in the order of the source's square, read through the exchange
of the two factors `CategoryTheory.TwoFibreProductOver.swapEquivalenceOver`. -/
@[stacks 075P "The first assertion: the apex X' of the 2-fibre product square is representable \
  by an algebraic space F', given that f is representable by algebraic spaces and that Y' is \
  representable by an algebraic space."]
theorem exists_isAlgebraicSpace_apex (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h𝒴' : IsRepresentableByAlgebraicSpace B S hS 𝒴'.val) :
    ∃ F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F' ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver (apexP B S hS f g)
        (presheafOfCategories (F' ⋙ typeToCat)).p) := by
  obtain ⟨F', hF', ⟨e⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴.val 𝒴'.val
    𝒳.val g.hom.hom f.hom.hom hf h𝒴'
  exact ⟨F', hF', ⟨(TwoFibreProductOver.swapEquivalenceOver _ _ _ _ _).trans e⟩⟩

/-- The projection `g' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒳` is a 1-morphism of fibred categories. -/
theorem fst_isFibredOneMorphism :
    (apexP B S hS f g).IsFibredOneMorphism 𝒳.val.val.p
      (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor) :=
  (𝒳.val.isFiberedInGroupoids).isFibredOneMorphism TwoFibreProductOver.fst_comp_eq

/-- The projection `f' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒴'` is a 1-morphism of fibred categories. -/
theorem snd_isFibredOneMorphism :
    (apexP B S hS f g).IsFibredOneMorphism 𝒴'.val.val.p
      (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor) :=
  (𝒴'.val.isFiberedInGroupoids).isFibredOneMorphism TwoFibreProductOver.snd_comp_eq

/-- The direct image `f_*` of abelian sheaves on the étale sites along `f : 𝒳 ⟶ 𝒴`. -/
abbrev directImageAb :
    Sheaf (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
        (𝒴.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u} :=
  Space.abelianDirectImageFibred B S hS 𝒳.val.val.p 𝒴.val.val.p (𝒳.val.isFiberedInGroupoids)
    (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor
    ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w)

/-- The inverse image `g⁻¹` of abelian sheaves on the étale sites along `g : 𝒴' ⟶ 𝒴`. -/
abbrev inverseImageAb :
    Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
        (𝒴.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
        (𝒴'.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u} :=
  Sites.abelianInverseImage (FibredSite.ringedToposMorphism B S hS 𝒴'.val.val.p 𝒴.val.val.p
    (𝒴'.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) g.hom.hom.toFunctor
    ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism g.hom.hom.w) .etale).toToposHom

/-- The inverse image `(g')⁻¹` of abelian sheaves on the étale sites along the projection
`g' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒳`. -/
abbrev fstInverseImageAb :
    Sheaf (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
        (apexP_isFiberedInGroupoids B S hS f g) .etale).J AddCommGrpCat.{u} :=
  Sites.abelianInverseImage (FibredSite.ringedToposMorphism B S hS (apexP B S hS f g)
    𝒳.val.val.p (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
    (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (fst_isFibredOneMorphism B S hS f g) .etale).toToposHom

/-- The direct image `f'_*` of abelian sheaves on the étale sites along the projection
`f' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒴'`. -/
abbrev sndDirectImageAb :
    Sheaf (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
        (apexP_isFiberedInGroupoids B S hS f g) .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
        (𝒴'.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u} :=
  Space.abelianDirectImageFibred B S hS (apexP B S hS f g) 𝒴'.val.val.p
    (apexP_isFiberedInGroupoids B S hS f g) (𝒴'.val.isFiberedInGroupoids)
    (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (snd_isFibredOneMorphism B S hS f g)

/-- **Stacks 075B at abelian coefficients, for the étale sites, in the spelling of morphisms of
topoi**: `(g')⁻¹ ⋙ f'_* ≅ f_* ⋙ g⁻¹`. This is
`AlgebraicGeometry.Stack.abelianDirectImageBaseChangeIso` read through
`AlgebraicGeometry.FibredSite.abelianInverseImageRingedToposMorphismIso` and
`AlgebraicGeometry.FibredSite.abelianPushforwardRingedToposMorphismIso`. -/
def abelianBaseChangeIso :
    fstInverseImageAb B S hS f g ⋙ sndDirectImageAb B S hS f g ≅
      directImageAb B S hS f ⋙ inverseImageAb B S hS g := by
  letI := (𝒳.val.isFiberedInGroupoids).isFibered
  letI := (𝒴.val.isFiberedInGroupoids).isFibered
  letI := (𝒴'.val.isFiberedInGroupoids).isFibered
  letI := (apexP_isFiberedInGroupoids B S hS f g).isFibered
  let hf := (𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w
  let hg := (𝒴.val.isFiberedInGroupoids).isFibredOneMorphism g.hom.hom.w
  let eF := FibredSite.abelianPushforwardRingedToposMorphismIso B S hS 𝒳.val.val.p 𝒴.val.val.p
    (𝒳.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor hf .etale
  let eG := FibredSite.abelianInverseImageRingedToposMorphismIso B S hS 𝒴'.val.val.p
    𝒴.val.val.p (𝒴'.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids)
    g.hom.hom.toFunctor hg .etale
  let eFst := FibredSite.abelianInverseImageRingedToposMorphismIso B S hS (apexP B S hS f g)
    𝒳.val.val.p (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
    (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (fst_isFibredOneMorphism B S hS f g) .etale
  let eSnd := FibredSite.abelianPushforwardRingedToposMorphismIso B S hS (apexP B S hS f g)
    𝒴'.val.val.p (apexP_isFiberedInGroupoids B S hS f g) (𝒴'.val.isFiberedInGroupoids)
    (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (snd_isFibredOneMorphism B S hS f g) .etale
  let base := abelianDirectImageBaseChangeIso B S hS 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor g.hom.hom.toFunctor (B.baseTopology .etale)
    (𝒳.val.isFiberedInGroupoids) (𝒴'.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids)
    f.hom.hom.w g.hom.hom.w
  exact Functor.isoWhiskerRight eFst _ ≪≫ Functor.isoWhiskerLeft _ eSnd ≪≫ base.symm ≪≫
    Functor.isoWhiskerRight eF.symm _ ≪≫ Functor.isoWhiskerLeft _ eG.symm

variable (F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF' : IsAlgebraicSpace B S hS F')
  (hG' : IsAlgebraicSpace B S hS G')
  (eF' : StacksRepresentableCFG.EquivalenceOver (apexP B S hS f g)
    (presheafOfCategories (F' ⋙ typeToCat)).p)
  (eG' : StacksRepresentableCFG.EquivalenceOver 𝒴'.val.val.p
    (presheafOfCategories (G' ⋙ typeToCat)).p)

/-- The morphism of algebraic spaces `f' : F' ⟶ G'` induced by the projection
`𝒴' ×_𝒴 𝒳 ⟶ 𝒴'` through the two presentations. -/
abbrev inducedHom : (⟨F', hF'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G', hG'⟩ :=
  Space.inducedAlgebraicSpacesHom B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF' hG' eF' eG'
    (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (snd_isFibredOneMorphism B S hS f g)

/-- The restriction `(-)|_{G'_étale}` of abelian sheaves on `𝒴'_étale`. -/
abbrev restrictionG'Ab :
    Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
        (𝒴'.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).J AddCommGrpCat.{u} :=
  Space.abelianRestrictionFunctor B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG' eG'

/-- The restriction `(-)|_{F'_étale}` of abelian sheaves on `(𝒴' ×_𝒴 𝒳)_étale`. -/
abbrev restrictionF'Ab :
    Sheaf (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
        (apexP_isFiberedInGroupoids B S hS f g) .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).J AddCommGrpCat.{u} :=
  Space.abelianRestrictionFunctor B S hS F' (apexP B S hS f g)
    (apexP_isFiberedInGroupoids B S hS f g) hF' eF'

/-- The direct image `f'_{small,*}` of abelian sheaves along the induced morphism of algebraic
spaces `F' ⟶ G'`. -/
abbrev smallDirectImageAb :
    Sheaf (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).J AddCommGrpCat.{u} ⥤
      Sheaf (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).J AddCommGrpCat.{u} :=
  Space.abelianDirectImageSpace B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF' hG' eF' eG'
    (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (snd_isFibredOneMorphism B S hS f g)

/-- **Equation 075M for the projection `f' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒴'`, at abelian coefficients**:
`f'_* ⋙ (-)|_{G'_étale} ≅ (-)|_{F'_étale} ⋙ f'_{small,*}`. It is the isomorphism of composite
direct images the 2-isomorphism of Stacks 073N induces on abelian sheaves. -/
def restrictionSquareAbIso :
    sndDirectImageAb B S hS f g ⋙ restrictionG'Ab B S hS G' hG' eG' ≅
      restrictionF'Ab B S hS f g F' hF' eF' ⋙ smallDirectImageAb B S hS f g F' G' hF' hG' eF' eG' :=
  abelianPushforwardPairIso
    (FibredSite.ringedToposMorphism B S hS (apexP B S hS f g) 𝒴'.val.val.p
      (apexP_isFiberedInGroupoids B S hS f g) (𝒴'.val.isFiberedInGroupoids)
      (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
      (snd_isFibredOneMorphism B S hS f g) .etale).toToposHom
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG'
      eG').toToposHom
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF').toToposHom
    (Space.smallEtaleRingedToposHom B S hS (inducedHom B S hS f g F' G' hF' hG' eF' eG')).toToposHom
    (Space.restrictionRingedSquareInducedAlgebraicSpaces B S hS F' G' (apexP B S hS f g)
      𝒴'.val.val.p (apexP_isFiberedInGroupoids B S hS f g) (𝒴'.val.isFiberedInGroupoids) hF'
      hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
      (snd_isFibredOneMorphism B S hS f g)).e

/-- The underived base change of the two composites around the square, at abelian
coefficients: `((g')⁻¹ ⋙ (-)|_{F'}) ⋙ f'_{small,*} ≅ f_* ⋙ (g⁻¹ ⋙ (-)|_{G'})`. -/
def underivedAbIso :
    (fstInverseImageAb B S hS f g ⋙ restrictionF'Ab B S hS f g F' hF' eF') ⋙
        smallDirectImageAb B S hS f g F' G' hF' hG' eF' eG' ≅
      directImageAb B S hS f ⋙ (inverseImageAb B S hS g ⋙ restrictionG'Ab B S hS G' hG' eG') :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictionSquareAbIso B S hS f g F' G' hF' hG' eF' eG').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (abelianBaseChangeIso B S hS f g) _ ≪≫ Functor.associator _ _ _

/-- The projection `g' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒳` is faithful and its source has equalizers, given
presentations of the apex and of `𝒴'` by algebraic spaces. -/
private theorem faithful_fst_and_hasEqualizers_apex
    (eF' : StacksRepresentableCFG.EquivalenceOver (apexP B S hS f g)
      (presheafOfCategories (F' ⋙ typeToCat)).p)
    (eG' : StacksRepresentableCFG.EquivalenceOver 𝒴'.val.val.p
      (presheafOfCategories (G' ⋙ typeToCat)).p) :
    (TwoFibreProductOver.fst 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
      g.hom.hom.toFunctor).Faithful ∧ HasEqualizers (Apex B S hS f g) :=
  have := eG'.faithful_of_presheafOfCategories
  ⟨TwoFibreProductOver.faithful_fst_of_faithful_structureFunctor _ _ _ _ _,
    eF'.hasEqualizers_of_presheafOfCategories⟩

include hF' hG' eF' eG' in
/-- The inverse image of abelian sheaves along the projection `g' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒳` carries
K-injective complexes to K-injective complexes. The projection is faithful, because `𝒴'` is
faithful over the site, and its source has equalizers, because it is an algebraic space; so
`(g')_!` is exact by Stacks 06X1, and a right adjoint of an exact functor preserves
K-injectivity (Stacks 08BJ). -/
theorem isKInjective_fstInverseImageAb (I : CochainComplex
      (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((fstInverseImageAb B S hS f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let := (𝒳.val.isFiberedInGroupoids).isFibered
  let := (apexP_isFiberedInGroupoids B S hS f g).isFibered
  obtain ⟨_, _⟩ := faithful_fst_and_hasEqualizers_apex B S hS f g F' G' eF' eG'
  let fst := TwoFibreProductOver.fst 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    g.hom.hom.toFunctor
  let hfst := fst_isFibredOneMorphism B S hS f g
  let := (hfst.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS))).1
  let J := BigFppfOver.associatedTopology B S hS (apexP B S hS f g) .etale
  let K := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale
  have hex := Stack.exact_sheafPullback_of_faithful.{u, u + 1, u + 1, u, u, u} B S hS
    (apexP B S hS f g) 𝒳.val.val.p fst
    (B.baseTopology .etale) (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
    TwoFibreProductOver.fst_comp_eq
  have hl : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback fst
      AddCommGrpCat.{u} J K) := ((exactFunctor_iff _).1 hex).1
  have hc : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback fst
      AddCommGrpCat.{u} J K) := ((exactFunctor_iff _).1 hex).2
  let adj := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous fst AddCommGrpCat.{u} J
    K).ofNatIsoRight (FibredSite.abelianInverseImageRingedToposMorphismIso B S hS
      (apexP B S hS f g) 𝒳.val.val.p (apexP_isFiberedInGroupoids B S hS f g)
      (𝒳.val.isFiberedInGroupoids) fst hfst .etale).symm
  have hadd : (fstInverseImageAb B S hS f g).Additive := additive_abelianInverseImage _ _
  have hadd' :
      (Functor.sheafPullbackConstruction.sheafPullback fst AddCommGrpCat.{u} J K).Additive :=
    @Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _ adj hadd
  exact @CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ _ _ _ _ _ _ hadd hadd' adj
    hl hc I _

/-- The composite `(g')⁻¹ ⋙ (-)|_{F'_étale}` of abelian sheaves is additive. -/
theorem additive_fstInverseImageAb_comp :
    (fstInverseImageAb B S hS f g ⋙ restrictionF'Ab B S hS f g F' hF' eF').Additive :=
  Functor.instAdditiveComp _ _

/-- The composite `g⁻¹ ⋙ (-)|_{G'_étale}` of abelian sheaves is additive. -/
theorem additive_inverseImageAb_comp :
    (inverseImageAb B S hS g ⋙ restrictionG'Ab B S hS G' hG' eG').Additive :=
  Functor.instAdditiveComp _ _

/-- The composite `(g')⁻¹ ⋙ (-)|_{F'_étale}` of abelian sheaves preserves finite limits. -/
theorem preservesFiniteLimits_fstInverseImageAb_comp :
    PreservesFiniteLimits (fstInverseImageAb B S hS f g ⋙ restrictionF'Ab B S hS f g F' hF' eF') :=
  comp_preservesFiniteLimits _ _

/-- The composite `(g')⁻¹ ⋙ (-)|_{F'_étale}` of abelian sheaves preserves finite colimits. -/
theorem preservesFiniteColimits_fstInverseImageAb_comp :
    PreservesFiniteColimits
      (fstInverseImageAb B S hS f g ⋙ restrictionF'Ab B S hS f g F' hF' eF') :=
  comp_preservesFiniteColimits _ _

/-- The composite `g⁻¹ ⋙ (-)|_{G'_étale}` of abelian sheaves preserves finite limits. -/
theorem preservesFiniteLimits_inverseImageAb_comp :
    PreservesFiniteLimits (inverseImageAb B S hS g ⋙ restrictionG'Ab B S hS G' hG' eG') :=
  comp_preservesFiniteLimits _ _

/-- The composite `g⁻¹ ⋙ (-)|_{G'_étale}` of abelian sheaves preserves finite colimits. -/
theorem preservesFiniteColimits_inverseImageAb_comp :
    PreservesFiniteColimits (inverseImageAb B S hS g ⋙ restrictionG'Ab B S hS G' hG' eG') :=
  comp_preservesFiniteColimits _ _

include hG' eG' in
/-- The composite `(g')⁻¹ ⋙ (-)|_{F'_étale}` of abelian sheaves carries K-injective complexes to
K-injective complexes. -/
theorem isKInjective_fstInverseImageAb_comp (I : CochainComplex
      (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).J AddCommGrpCat.{u}) ℤ) (hI : I.IsKInjective) :
    letI := additive_fstInverseImageAb_comp B S hS f g F' hF' eF'
    CochainComplex.IsKInjective (((fstInverseImageAb B S hS f g ⋙
      restrictionF'Ab B S hS f g F' hF' eF').mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have h₁ := isKInjective_fstInverseImageAb B S hS f g F' G' hF' hG' eF' eG' I
  have h₂ := preservesKInjective_abelianPushforward _
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF').toToposHom _ h₁
  @CochainComplex.isKInjective_of_iso _ _ _ _ _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (fstInverseImageAb B S hS f g ⋙
      restrictionF'Ab B S hS f g F' hF' eF')) (ComplexShape.up ℤ)).app I) h₂

section DerivedAb

variable
  [HasDerivedCategory.{dX} (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
      (𝒳.val.isFiberedInGroupoids) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY} (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
      (𝒴.val.isFiberedInGroupoids) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY₂} (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
      (𝒴'.val.isFiberedInGroupoids) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dA} (Sheaf (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dF}
    (Sheaf (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dG}
    (Sheaf (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).J AddCommGrpCat.{u})]

/-- **Stacks 075P at abelian coefficients**:
`g⁻¹(Rf_*ℱ)|_{G'_étale} ≅ Rf'_{small,*}((g')⁻¹ℱ|_{F'_étale})` naturally in `ℱ ∈ D(𝒳_étale)`,
the inverse images and restrictions being exact and appearing underived. It is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIso` for the exact functors
`(g')⁻¹ ⋙ (-)|_{F'_étale}` and `g⁻¹ ⋙ (-)|_{G'_étale}`, the underived identity
`underivedAbIso`, and the K-injectivity statement `isKInjective_fstInverseImageAb_comp`. -/
def derivedAbIso :
    Space.derivedAbelianDirectImageFibred B S hS 𝒳.val.val.p 𝒴.val.val.p
        (𝒳.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor
        ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w) ⋙
        (inverseImageAb B S hS g).mapDerivedCategory ⋙
          (restrictionG'Ab B S hS G' hG' eG').mapDerivedCategory ≅
      (fstInverseImageAb B S hS f g).mapDerivedCategory ⋙
        (restrictionF'Ab B S hS f g F' hF' eF').mapDerivedCategory ⋙
          Space.derivedAbelianDirectImageSpace B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF'
            hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
            (snd_isFibredOneMorphism B S hS f g) := by
  let α := fstInverseImageAb B S hS f g ⋙ restrictionF'Ab B S hS f g F' hF' eF'
  let β := inverseImageAb B S hS g ⋙ restrictionG'Ab B S hS G' hG' eG'
  haveI : α.Additive := additive_fstInverseImageAb_comp B S hS f g F' hF' eF'
  haveI : β.Additive := additive_inverseImageAb_comp B S hS g G' hG' eG'
  haveI : PreservesFiniteLimits α :=
    preservesFiniteLimits_fstInverseImageAb_comp B S hS f g F' hF' eF'
  haveI : PreservesFiniteColimits α :=
    preservesFiniteColimits_fstInverseImageAb_comp B S hS f g F' hF' eF'
  haveI : PreservesFiniteLimits β := preservesFiniteLimits_inverseImageAb_comp B S hS g G' hG' eG'
  haveI : PreservesFiniteColimits β :=
    preservesFiniteColimits_inverseImageAb_comp B S hS g G' hG' eG'
  have hK := isKInjective_fstInverseImageAb_comp B S hS f g F' G' hF' hG' eF' eG'
  exact Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso (Iso.refl β)) ≪≫
    (derivedBaseChangeIso α β (directImageAb B S hS f)
      (smallDirectImageAb B S hS f g F' G' hF' hG' eF' eG') _ _
      (Space.derivedAbelianDirectImageFibredUnit _ _ _ _ _ _ _ _ _)
      (Space.derivedAbelianDirectImageSpaceUnit _ _ _ _ _ _ _ _ _ _ _ _ _)
      (underivedAbIso B S hS f g F' G' hF' hG' eF' eG') hK).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso (Iso.refl α)).symm _ ≪≫
    Functor.associator _ _ _

end DerivedAb

/-! ### Sheaves of modules -/

/-- The inverse image `(g')^*` of sheaves of modules on the étale sites along the projection
`g' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒳`: restriction along `g'`, the structure sheaf of the apex being the restriction
of that of `𝒳`. -/
abbrev fstInverseImageMod :
    (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).Modules ⥤
      (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
        (apexP_isFiberedInGroupoids B S hS f g) .etale).Modules :=
  Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS (apexP B S hS f g) 𝒳.val.val.p
    (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
    (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    TwoFibreProductOver.fst_comp_eq (B.baseTopology .etale) (B.baseTopology_le_topology .etale)

/-- The inverse image `g^*` of sheaves of modules on the étale sites along `g : 𝒴' ⟶ 𝒴`. -/
abbrev inverseImageMod :
    (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
        (𝒴.val.isFiberedInGroupoids) .etale).Modules ⥤
      (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
        (𝒴'.val.isFiberedInGroupoids) .etale).Modules :=
  Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒴'.val.val.p 𝒴.val.val.p
    (𝒴'.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) g.hom.hom.toFunctor g.hom.hom.w
    (B.baseTopology .etale) (B.baseTopology_le_topology .etale)

/-- The direct image `f_*` of sheaves of modules on the étale sites along `f : 𝒳 ⟶ 𝒴`. -/
abbrev directImageMod :
    (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).Modules ⥤
      (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
        (𝒴.val.isFiberedInGroupoids) .etale).Modules :=
  RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
    (FibredSite.ringedToposMorphism B S hS 𝒳.val.val.p
    𝒴.val.val.p (𝒳.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor
    ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w) .etale)

/-- The direct image `f'_*` of sheaves of modules on the étale sites along the projection
`f' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒴'`. -/
abbrev sndDirectImageMod :
    (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
        (apexP_isFiberedInGroupoids B S hS f g) .etale).Modules ⥤
      (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
        (𝒴'.val.isFiberedInGroupoids) .etale).Modules :=
  RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
    (FibredSite.ringedToposMorphism B S hS (apexP B S hS f g)
    𝒴'.val.val.p (apexP_isFiberedInGroupoids B S hS f g) (𝒴'.val.isFiberedInGroupoids)
    (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (snd_isFibredOneMorphism B S hS f g) .etale)

/-- **Stacks 075B for sheaves of modules on the étale sites**: `(g')^* ⋙ f'_* ≅ f_* ⋙ g^*`. This
is `AlgebraicGeometry.FibredSite.pushforwardModulesBaseChangeIso`. -/
def moduleBaseChangeIso :
    fstInverseImageMod B S hS f g ⋙ sndDirectImageMod B S hS f g ≅
      directImageMod B S hS f ⋙ inverseImageMod B S hS g :=
  FibredSite.pushforwardModulesBaseChangeIso B S hS 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor g.hom.hom.toFunctor (𝒳.val.isFiberedInGroupoids)
    (𝒴'.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.w g.hom.hom.w

/-- The restriction `(-)|_{G'_étale}` of sheaves of modules on `𝒴'_étale`. -/
abbrev restrictionG'Mod :
    (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
        (𝒴'.val.isFiberedInGroupoids) .etale).Modules ⥤
      (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).Modules :=
  RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG' eG')

/-- The restriction `(-)|_{F'_étale}` of sheaves of modules on `(𝒴' ×_𝒴 𝒳)_étale`. -/
abbrev restrictionF'Mod :
    (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
        (apexP_isFiberedInGroupoids B S hS f g) .etale).Modules ⥤
      (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).Modules :=
  RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF')

/-- The direct image `f'_{small,*}` of sheaves of modules along the induced morphism of algebraic
spaces `F' ⟶ G'`. -/
abbrev smallDirectImageMod :
    (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).Modules ⥤
      (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).Modules :=
  RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
    (Space.smallEtaleRingedToposHom B S hS (inducedHom B S hS f g F' G' hF' hG' eF' eG'))

/-- **Equation 075M for the projection `f'`, for sheaves of modules**:
`f'_* ⋙ (-)|_{G'_étale} ≅ (-)|_{F'_étale} ⋙ f'_{small,*}`, induced by the 2-isomorphism of
Stacks 073N. -/
def restrictionSquareModIso :
    sndDirectImageMod B S hS f g ⋙ restrictionG'Mod B S hS G' hG' eG' ≅
      restrictionF'Mod B S hS f g F' hF' eF' ⋙
        smallDirectImageMod B S hS f g F' G' hF' hG' eF' eG' :=
  (RingedToposHom.pushforwardModulesCompIso
      (FibredSite.ringedToposMorphism B S hS (apexP B S hS f g) 𝒴'.val.val.p
        (apexP_isFiberedInGroupoids B S hS f g) (𝒴'.val.isFiberedInGroupoids)
        (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
        (snd_isFibredOneMorphism B S hS f g) .etale)
      (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG'
        eG')).symm ≪≫
    (Space.restrictionRingedSquareInducedAlgebraicSpaces B S hS F' G' (apexP B S hS f g)
      𝒴'.val.val.p (apexP_isFiberedInGroupoids B S hS f g) (𝒴'.val.isFiberedInGroupoids) hF'
      hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
      (snd_isFibredOneMorphism B S hS f g)).pushforwardModulesIso ≪≫
    RingedToposHom.pushforwardModulesCompIso
      (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
        (apexP_isFiberedInGroupoids B S hS f g) hF' eF')
      (Space.smallEtaleRingedToposHom B S hS (inducedHom B S hS f g F' G' hF' hG' eF' eG'))

/-- The underived base change of the two composites around the square, for sheaves of modules:
`((g')^* ⋙ (-)|_{F'}) ⋙ f'_{small,*} ≅ f_* ⋙ (g^* ⋙ (-)|_{G'})`. -/
def underivedModIso :
    (fstInverseImageMod B S hS f g ⋙ restrictionF'Mod B S hS f g F' hF' eF') ⋙
        smallDirectImageMod B S hS f g F' G' hF' hG' eF' eG' ≅
      directImageMod B S hS f ⋙ (inverseImageMod B S hS g ⋙ restrictionG'Mod B S hS G' hG' eG') :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictionSquareModIso B S hS f g F' G' hF' hG' eF' eG').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleBaseChangeIso B S hS f g) _ ≪≫ Functor.associator _ _ _

/-- The inverse image `(g')^*` of sheaves of modules is additive. -/
instance additive_fstInverseImageMod : (fstInverseImageMod B S hS f g).Additive := by
  let := (𝒳.val.isFiberedInGroupoids).isFibered
  let := (apexP_isFiberedInGroupoids B S hS f g).isFibered
  let := (fst_isFibredOneMorphism B S hS f g).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS)) |>.1
  exact Stacks.SheafOfModules.PushforwardRightExact.additive_pushforward _ _

/-- The inverse image `g^*` of sheaves of modules is additive. -/
instance additive_inverseImageMod : (inverseImageMod B S hS g).Additive := by
  let := (𝒴.val.isFiberedInGroupoids).isFibered
  let := (𝒴'.val.isFiberedInGroupoids).isFibered
  let := ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism
    g.hom.hom.w).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS)) |>.1
  exact Stacks.SheafOfModules.PushforwardRightExact.additive_pushforward _ _

/-- The inverse image `(g')^*` of sheaves of modules preserves finite limits. -/
instance preservesFiniteLimits_fstInverseImageMod :
    PreservesFiniteLimits (fstInverseImageMod B S hS f g) :=
  Stack.preservesFiniteLimits_modulePullback' B S hS
    (apexP B S hS f g) 𝒳.val.val.p (apexP_isFiberedInGroupoids B S hS f g)
    (𝒳.val.isFiberedInGroupoids)
    (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    TwoFibreProductOver.fst_comp_eq (B.baseTopology .etale) (B.baseTopology_le_topology .etale)

/-- The inverse image `g^*` of sheaves of modules preserves finite limits. -/
instance preservesFiniteLimits_inverseImageMod :
    PreservesFiniteLimits (inverseImageMod B S hS g) :=
  Stack.preservesFiniteLimits_modulePullback' B S hS
    𝒴'.val.val.p 𝒴.val.val.p (𝒴'.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids)
    g.hom.hom.toFunctor g.hom.hom.w (B.baseTopology .etale) (B.baseTopology_le_topology .etale)

/-- The inverse image `(g')^*` of sheaves of modules preserves finite colimits. -/
instance preservesFiniteColimits_fstInverseImageMod :
    PreservesFiniteColimits (fstInverseImageMod B S hS f g) := by
  let := (𝒳.val.isFiberedInGroupoids).isFibered
  let := (apexP_isFiberedInGroupoids B S hS f g).isFibered
  let := (fst_isFibredOneMorphism B S hS f g).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS)) |>.1
  let := (fst_isFibredOneMorphism B S hS f g).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS)) |>.2
  have := Stack.wEqualsLocallyBijective_associatedTopology_of_essentiallySmall.{u, _, _, u} B S hS
    (apexP B S hS f g) (B.baseTopology .etale)
  have := Stack.wEqualsLocallyBijective_associatedTopology_of_essentiallySmall.{u, _, _, u} B S hS
    𝒳.val.val.p (B.baseTopology .etale)
  exact Stacks.SheafOfModules.PushforwardRightExact.preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
    _ _ (isAlmostCocontinuous_of_isCocontinuous _ _ _)

/-- The inverse image `g^*` of sheaves of modules preserves finite colimits. -/
instance preservesFiniteColimits_inverseImageMod :
    PreservesFiniteColimits (inverseImageMod B S hS g) := by
  let := (𝒴.val.isFiberedInGroupoids).isFibered
  let := (𝒴'.val.isFiberedInGroupoids).isFibered
  let := ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism
    g.hom.hom.w).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS)) |>.1
  let := ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism
    g.hom.hom.w).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS)) |>.2
  have := Stack.wEqualsLocallyBijective_associatedTopology_of_essentiallySmall.{u, _, _, u} B S hS
    𝒴'.val.val.p (B.baseTopology .etale)
  have := Stack.wEqualsLocallyBijective_associatedTopology_of_essentiallySmall.{u, _, _, u} B S hS
    𝒴.val.val.p (B.baseTopology .etale)
  exact Stacks.SheafOfModules.PushforwardRightExact.preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
    _ _ (isAlmostCocontinuous_of_isCocontinuous _ _ _)

include hF' hG' eF' eG' in
/-- The inverse image of sheaves of modules along the projection `g' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒳` carries
K-injective complexes to K-injective complexes: `g'` is faithful and its source has equalizers,
so `(g')_!` on sheaves of modules is exact by Stacks 06X2, and a right adjoint of an exact functor
preserves K-injectivity (Stacks 08BJ). -/
theorem isKInjective_fstInverseImageMod (I : CochainComplex
      (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).Modules ℤ) [I.IsKInjective] :
    letI := additive_fstInverseImageMod B S hS f g
    CochainComplex.IsKInjective
      (((fstInverseImageMod B S hS f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let := (𝒳.val.isFiberedInGroupoids).isFibered
  let := (apexP_isFiberedInGroupoids B S hS f g).isFibered
  obtain ⟨_, _⟩ := faithful_fst_and_hasEqualizers_apex B S hS f g F' G' eF' eG'
  let := (fst_isFibredOneMorphism B S hS f g).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS)) |>.1
  let φ := Stack.ringStructureSheafCoreHom B S hS (apexP B S hS f g)
    𝒳.val.val.p (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (B.baseTopology .etale) (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
    TwoFibreProductOver.fst_comp_eq (B.baseTopology_le_topology .etale)
  let := Stack.isRightAdjoint_sheafOfModules_pushforward.{u, _, _, _, _, u} B S hS
    (apexP B S hS f g) 𝒳.val.val.p
    (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (B.baseTopology .etale) (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
    TwoFibreProductOver.fst_comp_eq (B.baseTopology_le_topology .etale)
  have hex := Stack.exactFunctor_sheafOfModules_pullback.{u, _, _, _, _, u} B S hS
    (apexP B S hS f g) 𝒳.val.val.p
    (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (B.baseTopology .etale) (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
    TwoFibreProductOver.fst_comp_eq (B.baseTopology_le_topology .etale)
  have hl : PreservesFiniteLimits (SheafOfModules.pullback.{u} φ) := ((exactFunctor_iff _).1 hex).1
  have hc : PreservesFiniteColimits (SheafOfModules.pullback.{u} φ) :=
    ((exactFunctor_iff _).1 hex).2
  have hψ : φ = ⟨eqToHom (Stack.ringStructureSheafCore_obj_eq B S hS (apexP B S hS f g)
      𝒳.val.val.p (apexP_isFiberedInGroupoids B S hS f g) (𝒳.val.isFiberedInGroupoids)
      (TwoFibreProductOver.fst _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
      TwoFibreProductOver.fst_comp_eq (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale))⟩ := by
    apply Sheaf.hom_ext
    ext x : 2
    simp only [φ, Stack.ringStructureSheafCoreHom]
    rw [Sheaf.eqToHom_hom_app]
    exact (eqToHom_app _ x).symm
  have heq : fstInverseImageMod B S hS f g = SheafOfModules.pushforward.{u} φ :=
    (congrArg (fun ψ => SheafOfModules.pushforward.{u} ψ) hψ).symm
  let adj := (SheafOfModules.pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight (eqToIso heq.symm)
  have hadd : (fstInverseImageMod B S hS f g).Additive := additive_fstInverseImageMod B S hS f g
  have hadd' : (SheafOfModules.pullback.{u} φ).Additive :=
    @Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _ adj hadd
  exact @CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ _ _ _ _ _ _ hadd hadd' adj
    hl hc I _

/-- The restriction `(-)|_{F'_étale}` of sheaves of modules is additive. -/
instance additive_restrictionF'Mod : (restrictionF'Mod B S hS f g F' hF' eF').Additive :=
  RingedToposHom.pushforwardModules_additive
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF')

/-- The restriction `(-)|_{G'_étale}` of sheaves of modules is additive. -/
instance additive_restrictionG'Mod : (restrictionG'Mod B S hS G' hG' eG').Additive :=
  RingedToposHom.pushforwardModules_additive
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG' eG')

/-- The restriction `(-)|_{F'_étale}` of sheaves of modules preserves finite limits. -/
instance preservesFiniteLimits_restrictionF'Mod :
    PreservesFiniteLimits (restrictionF'Mod B S hS f g F' hF' eF') :=
  RingedToposHom.pushforwardModules_preservesFiniteLimits
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF')

/-- The restriction `(-)|_{G'_étale}` of sheaves of modules preserves finite limits. -/
instance preservesFiniteLimits_restrictionG'Mod :
    PreservesFiniteLimits (restrictionG'Mod B S hS G' hG' eG') :=
  RingedToposHom.pushforwardModules_preservesFiniteLimits
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG' eG')

/-- The direct image `f_*` of sheaves of modules is additive. -/
instance additive_directImageMod : (directImageMod B S hS f).Additive :=
  RingedToposHom.pushforwardModules_additive
    (FibredSite.ringedToposMorphism B S hS 𝒳.val.val.p 𝒴.val.val.p (𝒳.val.isFiberedInGroupoids)
      (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor
      ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w) .etale)

/-- The direct image `f'_{small,*}` of sheaves of modules is additive. -/
instance additive_smallDirectImageMod :
    (smallDirectImageMod B S hS f g F' G' hF' hG' eF' eG').Additive :=
  RingedToposHom.pushforwardModules_additive
    (Space.smallEtaleRingedToposHom B S hS (inducedHom B S hS f g F' G' hF' hG' eF' eG'))

section RestrictionDerived

variable
  [HasDerivedCategory.{mA} (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) .etale).Modules]
  [HasDerivedCategory.{mF} (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).Modules]
  [HasDerivedCategory.{mY₂} (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
      (𝒴'.val.isFiberedInGroupoids) .etale).Modules]
  [HasDerivedCategory.{mG} (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).Modules]

omit [HasDerivedCategory.{mY₂} (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
    (𝒴'.val.isFiberedInGroupoids) .etale).Modules] in
/-- The functor `D(𝒪_{𝒳'}) ⥤ D(𝒪_{F'})` the exact restriction `(-)|_{F'_étale}` induces is the one
of `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact`. -/
theorem derivedPushforwardOfExact_projectionF' :
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF').derivedPushforwardOfExact =
      (restrictionF'Mod B S hS f g F' hF' eF').mapDerivedCategory :=
  RingedToposHom.derivedPushforwardOfExact_eq
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF')

/-- The functor `D(𝒪_{𝒴'}) ⥤ D(𝒪_{G'})` the exact restriction `(-)|_{G'_étale}` induces is the one
of `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact`. -/
theorem derivedPushforwardOfExact_projectionG' :
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG'
      eG').derivedPushforwardOfExact = (restrictionG'Mod B S hS G' hG' eG').mapDerivedCategory :=
  RingedToposHom.derivedPushforwardOfExact_eq
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG' eG')

end RestrictionDerived

/-- The composite `(g')^* ⋙ (-)|_{F'_étale}` of sheaves of modules is additive. -/
theorem additive_fstInverseImageMod_comp :
    (fstInverseImageMod B S hS f g ⋙ restrictionF'Mod B S hS f g F' hF' eF').Additive :=
  have := RingedToposHom.pushforwardModules_additive
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF')
  Functor.instAdditiveComp _ _

/-- The composite `g^* ⋙ (-)|_{G'_étale}` of sheaves of modules is additive. -/
theorem additive_inverseImageMod_comp :
    (inverseImageMod B S hS g ⋙ restrictionG'Mod B S hS G' hG' eG').Additive :=
  have := RingedToposHom.pushforwardModules_additive
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG' eG')
  Functor.instAdditiveComp _ _

/-- The composite `(g')^* ⋙ (-)|_{F'_étale}` of sheaves of modules preserves finite limits. -/
theorem preservesFiniteLimits_fstInverseImageMod_comp :
    PreservesFiniteLimits
      (fstInverseImageMod B S hS f g ⋙ restrictionF'Mod B S hS f g F' hF' eF') :=
  have := RingedToposHom.pushforwardModules_preservesFiniteLimits
    (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) hF' eF')
  comp_preservesFiniteLimits _ _

/-- The composite `(g')^* ⋙ (-)|_{F'_étale}` of sheaves of modules preserves finite colimits. -/
theorem preservesFiniteColimits_fstInverseImageMod_comp :
    PreservesFiniteColimits
      (fstInverseImageMod B S hS f g ⋙ restrictionF'Mod B S hS f g F' hF' eF') :=
  comp_preservesFiniteColimits _ _

/-- The composite `g^* ⋙ (-)|_{G'_étale}` of sheaves of modules preserves finite limits. -/
theorem preservesFiniteLimits_inverseImageMod_comp :
    PreservesFiniteLimits (inverseImageMod B S hS g ⋙ restrictionG'Mod B S hS G' hG' eG') :=
  have := RingedToposHom.pushforwardModules_preservesFiniteLimits
    (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids) hG' eG')
  comp_preservesFiniteLimits _ _

/-- The composite `g^* ⋙ (-)|_{G'_étale}` of sheaves of modules preserves finite colimits. -/
theorem preservesFiniteColimits_inverseImageMod_comp :
    PreservesFiniteColimits (inverseImageMod B S hS g ⋙ restrictionG'Mod B S hS G' hG' eG') :=
  comp_preservesFiniteColimits _ _

section DerivedMod

variable
  [HasDerivedCategory.{mX} (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
      (𝒳.val.isFiberedInGroupoids) .etale).Modules]
  [HasDerivedCategory.{mY} (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
      (𝒴.val.isFiberedInGroupoids) .etale).Modules]
  [HasDerivedCategory.{mY₂} (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
      (𝒴'.val.isFiberedInGroupoids) .etale).Modules]
  [HasDerivedCategory.{mA} (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) .etale).Modules]
  [HasDerivedCategory.{mF} (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).Modules]
  [HasDerivedCategory.{mG} (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).Modules]

omit [HasDerivedCategory.{mX} (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
      (𝒳.val.isFiberedInGroupoids) .etale).Modules]
  [HasDerivedCategory.{mY} (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
      (𝒴.val.isFiberedInGroupoids) .etale).Modules]
  [HasDerivedCategory.{mY₂} (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
      (𝒴'.val.isFiberedInGroupoids) .etale).Modules] in
/-- The unit of `Rf'_{small,*}` is invertible at `(g')^*I|_{F'_étale}` for every K-injective
complex `I` of `𝒪_𝒳`-modules: `(g')^*I` is K-injective (`isKInjective_fstInverseImageMod`), and the
unit of `Rf'_{small,*}` is invertible at the restriction of any K-injective complex of
`𝒪_{𝒳'}`-modules (`AlgebraicGeometry.Space.pushforwardComputesDerived_smallEtaleRingedToposHom`,
from Stacks 0D6E). -/
theorem isIso_derivedDirectImageSpaceUnit_app (I : CochainComplex
      (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
        (𝒳.val.isFiberedInGroupoids) .etale).Modules ℤ) (hI : I.IsKInjective) :
    letI := additive_fstInverseImageMod_comp B S hS f g F' hF' eF'
    IsIso ((Space.derivedDirectImageSpaceUnit B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF'
        hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
        (snd_isFibredOneMorphism B S hS f g)).app
      (((fstInverseImageMod B S hS f g ⋙ restrictionF'Mod B S hS f g F' hF' eF').mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have h := Space.pushforwardComputesDerived_smallEtaleRingedToposHom B S hS F' G'
    (apexP B S hS f g) 𝒴'.val.val.p (apexP_isFiberedInGroupoids B S hS f g) hF' hG' eF' eG'
    (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
    (snd_isFibredOneMorphism B S hS f g) _
    (Space.derivedDirectImageSpaceUnit B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF'
        hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
        (snd_isFibredOneMorphism B S hS f g))
    (((fstInverseImageMod B S hS f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (isKInjective_fstInverseImageMod B S hS f g F' G' hF' hG' eF' eG' I)
  exact h

/-- **Stacks 075P for sheaves of modules**:
`g^*(Rf_*ℱ)|_{G'_étale} ≅ Rf'_{small,*}((g')^*ℱ|_{F'_étale})` naturally in `ℱ ∈ D(𝒪_𝒳)`, with
`g^*`, `(g')^*` the inverse images of Stacks 06WE and the restrictions of Stacks 075N, all exact
and appearing underived. It is `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit`
for the underived identity `underivedModIso`; the unit condition is
`isIso_derivedDirectImageSpaceUnit_app`. -/
def derivedModIso :
    Space.derivedDirectImageFibred B S hS 𝒳.val.val.p 𝒴.val.val.p
        (𝒳.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor
        ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w) ⋙
        (inverseImageMod B S hS g).mapDerivedCategory ⋙
          (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids)
            hG' eG').derivedPushforwardOfExact ≅
      (fstInverseImageMod B S hS f g).mapDerivedCategory ⋙
        (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
          (apexP_isFiberedInGroupoids B S hS f g) hF' eF').derivedPushforwardOfExact ⋙
          Space.derivedDirectImageSpace B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF'
            hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
            (snd_isFibredOneMorphism B S hS f g) := by
  let α := fstInverseImageMod B S hS f g ⋙ restrictionF'Mod B S hS f g F' hF' eF'
  let β := inverseImageMod B S hS g ⋙ restrictionG'Mod B S hS G' hG' eG'
  haveI : α.Additive := additive_fstInverseImageMod_comp B S hS f g F' hF' eF'
  haveI : β.Additive := additive_inverseImageMod_comp B S hS g G' hG' eG'
  haveI : PreservesFiniteLimits α :=
    preservesFiniteLimits_fstInverseImageMod_comp B S hS f g F' hF' eF'
  haveI : PreservesFiniteColimits α :=
    preservesFiniteColimits_fstInverseImageMod_comp B S hS f g F' hF' eF'
  haveI : PreservesFiniteLimits β := preservesFiniteLimits_inverseImageMod_comp B S hS g G' hG' eG'
  haveI : PreservesFiniteColimits β :=
    preservesFiniteColimits_inverseImageMod_comp B S hS g G' hG' eG'
  let base := derivedBaseChangeIsoOfUnit α β (directImageMod B S hS f)
      (smallDirectImageMod B S hS f g F' G' hF' hG' eF' eG') _ _
      (Space.derivedDirectImageFibredUnit _ _ _ _ _ _ _ _ _)
      (Space.derivedDirectImageSpaceUnit _ _ _ _ _ _ _ _ _ _ _ _ _)
      (underivedModIso B S hS f g F' G' hF' hG' eF' eG')
      (fun I hI => isIso_derivedDirectImageSpaceUnit_app B S hS f g F' G' hF' hG' eF' eG' I hI)
  have eqF := derivedPushforwardOfExact_projectionF' B S hS f g F' hF' eF'
  have eqG := derivedPushforwardOfExact_projectionG' B S hS G' hG' eG'
  refine Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (eqToIso eqG) ≪≫
    Functor.mapDerivedCategoryCompIso (Iso.refl β)) ≪≫ base.symm ≪≫ ?_
  refine Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso (Iso.refl α)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (eqToIso eqF).symm _)

section Clauses

variable
  [HasDerivedCategory.{dX} (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒳.val.val.p
      (𝒳.val.isFiberedInGroupoids) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY} (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴.val.val.p
      (𝒴.val.isFiberedInGroupoids) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY₂} (Sheaf (FibredSite.associatedRingedTopos B S hS 𝒴'.val.val.p
      (𝒴'.val.isFiberedInGroupoids) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dA} (Sheaf (FibredSite.associatedRingedTopos B S hS (apexP B S hS f g)
      (apexP_isFiberedInGroupoids B S hS f g) .etale).J
      AddCommGrpCat.{u})]
  [HasDerivedCategory.{dF}
    (Sheaf (Space.smallEtaleRingedTopos B S hS ⟨F', hF'⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dG}
    (Sheaf (Space.smallEtaleRingedTopos B S hS ⟨G', hG'⟩).J AddCommGrpCat.{u})]

/-- **Stacks 075P.** Let `S` be a scheme and let

```
𝒴' ×_𝒴 𝒳 --g'--> 𝒳
    |            |
    f'           f
    v            v
    𝒴' ---g--->  𝒴
```

be the 2-fibre product square of algebraic stacks over `S`. If `𝒴'` is represented by an
algebraic space `G'` and the apex by an algebraic space `F'` — which is the case as soon as `f`
is representable by algebraic spaces, by `exists_isAlgebraicSpace_apex` — and `f' : F' ⟶ G'` is
the induced morphism of algebraic spaces, then

`g⁻¹(Rf_*ℱ)|_{G'_étale} = Rf'_{small,*}((g')⁻¹ℱ|_{F'_étale})`

1. for `ℱ` in `D(𝒳_étale)`, in particular for an abelian sheaf on `𝒳_étale`, and
2. for `ℱ` in `D(𝒪_𝒳)`, in particular for a sheaf of `𝒪_𝒳`-modules,

as isomorphisms of functors. The derived direct images are the total right derived functors of
Stacks 075N, `AlgebraicGeometry.Space.derivedAbelianDirectImageFibred`,
`AlgebraicGeometry.Space.derivedAbelianDirectImageSpace`,
`AlgebraicGeometry.Space.derivedDirectImageFibred` and
`AlgebraicGeometry.Space.derivedDirectImageSpace`. -/
@[stacks 075P "The displayed identity, both clauses, as isomorphisms of functors on the unbounded \
  derived categories: (1) g^{-1}(Rf_*F)|_{G'_etale} = Rf'_{small,*}((g')^{-1}F|_{F'_etale}) for F in \
  D(X_etale), (2) the same identity for F in D(O_X), for any presentations of Y' and of the apex \
  X' by algebraic spaces G' and F'."]
def restrictedDerivedBaseChangeIsoClauses :
    (Space.derivedAbelianDirectImageFibred B S hS 𝒳.val.val.p 𝒴.val.val.p
        (𝒳.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor
        ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w) ⋙
        (inverseImageAb B S hS g).mapDerivedCategory ⋙
          (restrictionG'Ab B S hS G' hG' eG').mapDerivedCategory ≅
      (fstInverseImageAb B S hS f g).mapDerivedCategory ⋙
        (restrictionF'Ab B S hS f g F' hF' eF').mapDerivedCategory ⋙
          Space.derivedAbelianDirectImageSpace B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF'
            hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
            (snd_isFibredOneMorphism B S hS f g)) ×
    (Space.derivedDirectImageFibred B S hS 𝒳.val.val.p 𝒴.val.val.p
        (𝒳.val.isFiberedInGroupoids) (𝒴.val.isFiberedInGroupoids) f.hom.hom.toFunctor
        ((𝒴.val.isFiberedInGroupoids).isFibredOneMorphism f.hom.hom.w) ⋙
        (inverseImageMod B S hS g).mapDerivedCategory ⋙
          (Space.projectionRingedToposHom B S hS G' 𝒴'.val.val.p (𝒴'.val.isFiberedInGroupoids)
            hG' eG').derivedPushforwardOfExact ≅
      (fstInverseImageMod B S hS f g).mapDerivedCategory ⋙
        (Space.projectionRingedToposHom B S hS F' (apexP B S hS f g)
          (apexP_isFiberedInGroupoids B S hS f g) hF' eF').derivedPushforwardOfExact ⋙
          Space.derivedDirectImageSpace B S hS F' G' (apexP B S hS f g) 𝒴'.val.val.p hF'
            hG' eF' eG' (TwoFibreProductOver.snd _ _ _ f.hom.hom.toFunctor g.hom.hom.toFunctor)
            (snd_isFibredOneMorphism B S hS f g)) :=
  ⟨derivedAbIso B S hS f g F' G' hF' hG' eF' eG', derivedModIso B S hS f g F' G' hF' hG' eF' eG'⟩

end Clauses

end DerivedMod

end AlgebraicGeometry.Stack.RepresentableBaseChangeSquare

end
