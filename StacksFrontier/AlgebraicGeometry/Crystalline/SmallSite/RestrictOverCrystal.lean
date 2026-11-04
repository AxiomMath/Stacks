module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PresentedCrystal

/-!
# A presented module on a localised small crystalline site has invertible comparison maps

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` of a global
crystalline situation and let `B` be an object of that site.  This file runs the computation of
[Stacks, Tag 07IT] for the implication (1) ⇒ (2)(b) on the *localised* site `Cris(X/S)/B`:

> assume `F` restricted to `𝒞/(U, T, δ)` has a global presentation
> `⊕_J 𝒪_{X/S} → ⊕_I 𝒪_{X/S} → F → 0`. It is clear that this gives a presentation
> `⊕_J 𝒪_T → ⊕_I 𝒪_T → F_T → 0` ... Moreover, the presentation restricts to `T'` to give a
> similar presentation of `F_{T'}`, whence (b) holds.

The conclusion is that if the restriction of `F` to `Cris(X/S)/B` has a global presentation, then
the comparison map `c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules is an isomorphism for
*every* morphism `f` of `Cris(X/S)` whose target is `B`.  That is what the Zariski-local reduction
of the tag consumes: quasi-coherence supplies a presentation only on a covering of the target, and
each member of that covering is a localised site of this kind.

This is the small-site form of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverCrystal`, and it is not a
consequence of it: a sheaf of modules on `Cris(X/S)` is in general not the restriction of one on
`CRIS(X/S)`, so the computation is repeated here, as it is in
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PresentedCrystal` for a presentation on all
of `Cris(X/S)`.  The hypothesis used here is the weaker one, and it is the one quasi-coherence
actually provides.

## The restriction functor into a localised small crystalline site

Everything rests on the restrictions of an object `A` of `Cris(X/S)` to the opens of its ambient
scheme being a functor *into the localised site* `Cris(X/S)/B`, for any morphism `h : A ⟶ B`:
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.restrictOverFunctor`,
which sends an open `W` to the restriction `A|_W` equipped with the structure morphism
`A|_W ⟶ A ⟶ B`.  Composed with `CategoryTheory.Over.forget B` it is the restriction functor
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor` of
`A` itself, on the nose, so its continuity and cocontinuity follow from those of the latter by the
general criteria of `StacksFrontier.CategoryTheory.Sites.SlicePost.IntoSlice`.  Being continuous
*and* cocontinuous, restriction of sheaves of modules along it preserves colimits, which is what
carries a presentation on the localised site to the Zariski site of the ambient scheme.

The comparison of structure sheaves is the identity: the restriction of `𝒪_{X/S}` to the opens of
the ambient scheme of `A` *is* the restriction along `restrictOverFunctor h` of the localisation
of `𝒪_{X/S}` at `B`, because the two site functors agree.  As on the unlocalised small site, the
sheaf of rings that appears is the big site's
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` at the underlying object
of `CRIS(X/S)`: the structure sheaf of `Cris(X/S)` is the restriction along the inclusion of that
of `CRIS(X/S)`, and the restrictions of an object of `Cris(X/S)` to the opens of its ambient
scheme are those of the underlying object.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.restrictOverFunctor` —
  **the restrictions of an object to the opens of its ambient scheme, as a functor into a
  localised small crystalline site**, with its continuity and cocontinuity.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.moduleRestrictionSheafOverFunctor` — the restriction `F ↦ F_T` of [Stacks, Tag 07IQ] for a
  module on a localised small crystalline site.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.fmapCompOver` —
  composition with the `f`-map there, at an arbitrary module universe.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.bijective_fmapCompOver_over_iff` — the `f`-map composition of the restriction of a module to a
  localised site is bijective exactly when its `f`-map composition on `Cris(X/S)` is.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.bijective_fmapCompOverLift_of_hasGlobalPresentation` — the source's computation on the
  localised site.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target` — **a sheaf of
  `𝒪_{X/S}`-modules on `Cris(X/S)` whose restriction to `Cris(X/S)/B` has a global presentation
  has an invertible comparison map at every morphism with target `B`.**

## Implementation notes

The crystal condition is tested through
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
`.isIso_moduleComparisonSheaf_iff_bijective_fmapComp`, which names no pullback functor and
therefore survives the universe lift of the module sections at which a global presentation on a
crystalline site lives; the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.PresentedCrystal` explains that test.

The restriction to the ambient scheme of the restriction of a module to the localised site, and
its restriction to the ambient scheme taken directly, have the same sections over every open, but
the two iterated restrictions of scalars along identity morphisms of sheaves of rings are not
definitionally the same sheaf of modules; they are compared by
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
`.moduleRestrictionSheafOverIso`, an isomorphism which is the identity on sections, and
bijectivity of the `f`-map composition is transported along it.

The two abstract steps of the computation, `Stacks.PresentedBijectivity.bijective_of_cofan` and
`Stacks.PresentedBijectivity.bijective_of_cofork`, and the bijectivity of a universe lift of the
module sections, `Crystalline.GlobalCrystallineSituation.Thickening`
`.bijective_uliftForPresentationMap`, are site-independent and are reused from the big site; so is
`Crystalline.GlobalCrystallineSituation.Thickening.bijective_comp_left_of_iso`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe m u

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

attribute [local instance] CrystallineThickening.restrictOpenFunctor_isContinuous
  CrystallineThickening.restrictOpenFunctor_isCocontinuous

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The restrictions of an object into a localised small crystalline site -/

/-- **The restrictions of an object of `Cris(X/S)` to the opens of its ambient scheme, as a
functor into the localisation of `Cris(X/S)` at an object the given one maps to.** -/
noncomputable def restrictOverFunctor {A B : CrystallineThickening S} (h : A ⟶ B) :
    A.obj.thickening.target.scheme.Opens ⥤ Over B :=
  CrystallineThickening.restrictOpenOverFunctor A ⋙ Over.map h

/-- Forgetting the base of the localised site recovers the restriction functor of the object. -/
theorem restrictOverFunctor_comp_forget {A B : CrystallineThickening S} (h : A ⟶ B) :
    restrictOverFunctor h ⋙ Over.forget B = CrystallineThickening.restrictOpenFunctor A := rfl

/-- The restriction functor `restrictOverFunctor h` into the localised site is cocontinuous. -/
instance isCocontinuous_restrictOverFunctor {A B : CrystallineThickening S} (h : A ⟶ B) :
    (restrictOverFunctor h).IsCocontinuous
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((smallTopology S).over B) :=
  Functor.isCocontinuous_of_comp_overForget _ _ _
    (CrystallineThickening.restrictOpenFunctor_isCocontinuous A)

/-- The restriction functor `restrictOverFunctor h` into the localised site preserves pullbacks. -/
instance preservesLimitsOfShape_walkingCospan_restrictOverFunctor
    {A B : CrystallineThickening S} (h : A ⟶ B) :
    PreservesLimitsOfShape WalkingCospan (restrictOverFunctor h) :=
  have : PreservesLimitsOfShape WalkingCospan (restrictOverFunctor h ⋙ Over.forget B) :=
    CrystallineThickening.preservesLimitsOfShape_walkingCospan_restrictOpenFunctor A
  preservesLimitsOfShape_of_reflects_of_preserves (restrictOverFunctor h) (Over.forget B)

/-- The restriction functor `restrictOverFunctor h` into the localised site is continuous. -/
instance isContinuous_restrictOverFunctor {A B : CrystallineThickening S} (h : A ⟶ B) :
    (restrictOverFunctor h).IsContinuous
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((smallTopology S).over B) :=
  Functor.isContinuous_of_comp_overForget _ _ _
    (CrystallineThickening.coverPreserving_restrictOpenFunctor A)

/-- The restriction of the structure sheaf of a localised small crystalline site to the opens of
the ambient scheme of an object over the base *is* the restriction of `𝒪_{X/S}`. -/
theorem sheafPushforward_restrictOverFunctor_structure {A B : CrystallineThickening S}
    (h : A ⟶ B) :
    ((restrictOverFunctor h).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        ((smallTopology S).over B)).obj ((structureSheaf S).over B) =
      Thickening.ringRestrictionSheaf A.obj := rfl

/-- **The comparison of structure sheaves for the restriction to the ambient scheme of an object
of a localised small crystalline site is the identity.** -/
noncomputable def restrictOverStructureHom {A B : CrystallineThickening S} (h : A ⟶ B) :
    Thickening.ringRestrictionSheaf A.obj ⟶
      ((restrictOverFunctor h).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        ((smallTopology S).over B)).obj ((structureSheaf S).over B) :=
  𝟙 (Thickening.ringRestrictionSheaf A.obj)

/-- **The restriction `F ↦ F_T` of [Stacks, Tag 07IQ] for a sheaf of modules on a localised small
crystalline site**, at an arbitrary module universe. -/
noncomputable def moduleRestrictionSheafOverFunctor {A B : CrystallineThickening S} (h : A ⟶ B) :
    SheafOfModules.{m} ((structureSheaf S).over B) ⥤
      SheafOfModules.{m} (Thickening.ringRestrictionSheaf A.obj) :=
  SheafOfModules.pushforward.{m} (restrictOverStructureHom h)

/-- **The restriction to the ambient scheme of an object over the base of the restriction of a
module to a localised small crystalline site is its restriction to that ambient scheme.**  Both
have the sections of the module over the restrictions of the object as their sections, so the
comparison is the identity on sections. -/
noncomputable def moduleRestrictionSheafOverIso (M : SheafOfModules.{m} (structureSheaf S))
    {A B : CrystallineThickening S} (h : A ⟶ B) :
    (moduleRestrictionSheafOverFunctor.{m} h).obj (M.over B) ≅
      (moduleRestrictionSheafFunctor.{m} A).obj M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ by ext; rfl))

/-- The isomorphism `moduleRestrictionSheafOverIso M h` is the identity on sections over every
open. -/
@[simp]
theorem moduleRestrictionSheafOverIso_hom_val_app (M : SheafOfModules.{m} (structureSheaf S))
    {A B : CrystallineThickening S} (h : A ⟶ B)
    (W : (A.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    (moduleRestrictionSheafOverIso M h).hom.val.app W = 𝟙 _ := rfl

/-- The restriction of a morphism of a localised small crystalline site over an open of the
ambient scheme of its target is a morphism over the base. -/
theorem restrictOpenMap_comp_restrictOpenHom_comp {B : CrystallineThickening S}
    {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) (W : A₂.left.obj.thickening.target.scheme.Opens) :
    CrystallineThickening.restrictOpenMap g.left W ≫ (A₂.left.restrictOpenHom W ≫ A₂.hom) =
      A₁.left.restrictOpenHom (g.left.hom.targetHom.hom ⁻¹ᵁ W) ≫ A₁.hom := by
  rw [← Category.assoc, CrystallineThickening.restrictOpenMap_restrictOpenHom, Category.assoc,
    Over.w g]

/-- **The restrictions of a morphism of a localised small crystalline site over the opens of the
ambient schemes**, as a natural transformation of functors into the localised site. -/
noncomputable def restrictOverFunctorMap {B : CrystallineThickening S} {A₁ A₂ : Over B}
    (g : A₁ ⟶ A₂) :
    Opens.map g.left.hom.targetHom.hom.base ⋙ restrictOverFunctor A₁.hom ⟶
      restrictOverFunctor A₂.hom where
  app W := Over.homMk (CrystallineThickening.restrictOpenMap g.left W)
    (restrictOpenMap_comp_restrictOpenHom_comp g W)
  naturality _ _ i := by
    ext
    exact Thickening.restrictOpenLE_restrictOpenMap g.left.hom (leOfHom i)

/-- **The `f`-map of [Stacks, Tag 07IQ] for a sheaf of modules on a localised small crystalline
site**, at an arbitrary module universe. -/
noncomputable def moduleFMapSheafOver {B : CrystallineThickening S}
    (N : SheafOfModules.{m} ((structureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) :
    (moduleRestrictionSheafOverFunctor.{m} A₂.hom).obj N ⟶
      (SheafOfModules.pushforward.{m}
          (Thickening.ringRestrictionSheafFMap g.left.hom)).obj
        ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).obj N) :=
  ⟨PresheafOfModules.pushforwardOfNatTrans (restrictOverFunctorMap g)
    ((structureSheaf S).over B).obj N.val⟩

/-- **Composition with the `f`-map on a localised small crystalline site.** -/
noncomputable def fmapCompOver {B : CrystallineThickening S}
    (N : SheafOfModules.{m} ((structureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} (Thickening.ringRestrictionSheaf A₁.left.obj)) :
    ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).obj N ⟶ Z) →
      ((moduleRestrictionSheafOverFunctor.{m} A₂.hom).obj N ⟶
        (SheafOfModules.pushforward.{m}
          (Thickening.ringRestrictionSheafFMap g.left.hom)).obj Z) :=
  fun k ↦ moduleFMapSheafOver N g ≫
    (SheafOfModules.pushforward.{m} (Thickening.ringRestrictionSheafFMap g.left.hom)).map k

/-- **Composition with the `f`-map on a localised small crystalline site is natural in the
module**, contravariantly. -/
theorem fmapCompOver_naturality {B : CrystallineThickening S}
    {N₁ N₂ : SheafOfModules.{m} ((structureSheaf S).over B)} (ψ : N₁ ⟶ N₂)
    {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} (Thickening.ringRestrictionSheaf A₁.left.obj))
    (k : (moduleRestrictionSheafOverFunctor.{m} A₁.hom).obj N₂ ⟶ Z) :
    fmapCompOver N₁ g Z ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).map ψ ≫ k) =
      (moduleRestrictionSheafOverFunctor.{m} A₂.hom).map ψ ≫ fmapCompOver N₂ g Z k := by
  have h : (moduleRestrictionSheafOverFunctor.{m} A₂.hom).map ψ ≫ moduleFMapSheafOver N₂ g =
      moduleFMapSheafOver N₁ g ≫
        (SheafOfModules.pushforward.{m}
            (Thickening.ringRestrictionSheafFMap g.left.hom)).map
          ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).map ψ) := by
    apply SheafOfModules.Hom.ext
    ext W x
    exact (PresheafOfModules.naturality_apply ψ.val
      ((restrictOverFunctorMap g).app W.unop).op x).symm
  simp only [fmapCompOver, Functor.map_comp]
  rw [← Category.assoc, ← h, Category.assoc]

/-- **Composition with the `f`-map of an isomorphic module is bijective exactly when it is for the
given one.** -/
theorem bijective_fmapCompOver_congr {B : CrystallineThickening S}
    {N₁ N₂ : SheafOfModules.{m} ((structureSheaf S).over B)} (e : N₁ ≅ N₂)
    {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} (Thickening.ringRestrictionSheaf A₁.left.obj))
    (h : Function.Bijective (fmapCompOver N₂ g Z)) :
    Function.Bijective (fmapCompOver N₁ g Z) := by
  have h₁ := Thickening.bijective_comp_left_of_iso (Z := Z)
    ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).mapIso e)
  have h₂ := Thickening.bijective_comp_left_of_iso
    (Z := (SheafOfModules.pushforward.{m}
      (Thickening.ringRestrictionSheafFMap g.left.hom)).obj Z)
    ((moduleRestrictionSheafOverFunctor.{m} A₂.hom).mapIso e)
  have hsq : (fmapCompOver N₁ g Z) ∘
        (fun k : (moduleRestrictionSheafOverFunctor.{m} A₁.hom).obj N₂ ⟶ Z ↦
          ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).mapIso e).hom ≫ k) =
      (fun k ↦ ((moduleRestrictionSheafOverFunctor.{m} A₂.hom).mapIso e).hom ≫ k) ∘
        (fmapCompOver N₂ g Z) :=
    funext fun k ↦ fmapCompOver_naturality e.hom g Z k
  rw [← Function.Bijective.of_comp_iff _ h₁, hsq]
  exact h₂.comp h

/-- **Composition with the `f`-map of the restriction of a module to a localised small crystalline
site is composition with its `f`-map on `Cris(X/S)`**, read through the identification of the two
restrictions to the ambient schemes. -/
theorem fmapCompOver_over (M : SheafOfModules.{m} (structureSheaf S))
    {B : CrystallineThickening S} {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} (Thickening.ringRestrictionSheaf A₁.left.obj))
    (k : (moduleRestrictionSheafFunctor.{m} A₁.left).obj M ⟶ Z) :
    fmapCompOver (M.over B) g Z ((moduleRestrictionSheafOverIso M A₁.hom).hom ≫ k) =
      (moduleRestrictionSheafOverIso M A₂.hom).hom ≫ fmapComp.{m} M g.left Z k := by
  apply SheafOfModules.Hom.ext
  ext W x
  rfl

/-- **Composition with the `f`-map of the restriction of a module to a localised small crystalline
site is bijective exactly when composition with its `f`-map on `Cris(X/S)` is.** -/
theorem bijective_fmapCompOver_over_iff (M : SheafOfModules.{m} (structureSheaf S))
    {B : CrystallineThickening S} {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} (Thickening.ringRestrictionSheaf A₁.left.obj)) :
    Function.Bijective (fmapCompOver (M.over B) g Z) ↔
      Function.Bijective (fmapComp.{m} M g.left Z) := by
  have h₁ := Thickening.bijective_comp_left_of_iso (Z := Z)
    (moduleRestrictionSheafOverIso M A₁.hom)
  have h₂ := Thickening.bijective_comp_left_of_iso
    (Z := (SheafOfModules.pushforward.{m}
      (Thickening.ringRestrictionSheafFMap g.left.hom)).obj Z)
    (moduleRestrictionSheafOverIso M A₂.hom)
  have hsq : (fmapCompOver (M.over B) g Z) ∘
        (fun k : (moduleRestrictionSheafFunctor.{m} A₁.left).obj M ⟶ Z ↦
          (moduleRestrictionSheafOverIso M A₁.hom).hom ≫ k) =
      (fun k ↦ (moduleRestrictionSheafOverIso M A₂.hom).hom ≫ k) ∘
        (fmapComp.{m} M g.left Z) :=
    funext fun k ↦ fmapCompOver_over M g Z k
  rw [← Function.Bijective.of_comp_iff (fmapCompOver (M.over B) g Z) h₁, hsq,
    Function.Bijective.of_comp_iff' h₂]

/-- **The restriction of the structure sheaf of `Cris(X/S)` to a localised small crystalline site
is the structure sheaf of that site.** -/
noncomputable def unitOverIso (B : CrystallineThickening S) :
    (SheafOfModules.unit (structureSheaf S)).over B ≅
      SheafOfModules.unit ((structureSheaf S).over B) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ by ext; rfl))

/-- **Composition with the `f`-map is bijective at the structure sheaf of a localised small
crystalline site**: the comparison map of `𝒪_{X/S}` on `Cris(X/S)` is an isomorphism, the
structure sheaf of the small site being the restriction of that of `CRIS(X/S)`, which is a
crystal. -/
theorem bijective_fmapCompOver_unit {B : CrystallineThickening S} {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A₁.left.obj)) :
    Function.Bijective
      (fmapCompOver (SheafOfModules.unit ((structureSheaf S).over B)) g Z) :=
  bijective_fmapCompOver_congr (unitOverIso B).symm g Z
    ((bijective_fmapCompOver_over_iff _ g Z).2
      ((isIso_moduleComparisonSheaf_iff_bijective_fmapComp _ g.left).1
        (isSheafCrystal_restrictUnit S A₁.left A₂.left g.left) Z))

/-- **Restriction to the ambient scheme from a localised small crystalline site preserves colimits
of size `u + 1`**, the size in which a global presentation on that site is indexed. -/
theorem preservesColimitsOfSize_moduleRestrictionSheafOverFunctor
    {A B : CrystallineThickening S} (h : A ⟶ B) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf A.obj) from
        moduleRestrictionSheafOverFunctor.{u + 1} h) := by
  have _ : HasSheafify ((smallTopology S).over B) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((smallTopology S).over B).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    (restrictOverFunctor h) (restrictOverStructureHom h)

/-! ### The index universe of a global presentation -/

/-- **Composition with the `f`-map on a localised small crystalline site at the raised module
universe, read on the universe lifts of the modules at the module universe `u`.** -/
noncomputable def fmapCompOverLift {B : CrystallineThickening S}
    (N : SheafOfModules.{u} ((structureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A₁.left.obj)) :
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafOverFunctor.{u} A₁.hom).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z) →
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafOverFunctor.{u} A₂.hom).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((SheafOfModules.pushforward.{u}
            (Thickening.ringRestrictionSheafFMap g.left.hom)).obj Z)) :=
  fmapCompOver.{u + 1} (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)

/-- **Composition with the `f`-map on a localised small crystalline site commutes with a universe
lift of the module sections.** -/
theorem fmapCompOverLift_uliftForPresentationMap {B : CrystallineThickening S}
    (N : SheafOfModules.{u} ((structureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A₁.left.obj))
    (k : (moduleRestrictionSheafOverFunctor.{u} A₁.hom).obj N ⟶ Z) :
    fmapCompOverLift N g Z (SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) =
      SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} (fmapCompOver.{u} N g Z k) := by
  apply SheafOfModules.Hom.ext
  ext W x
  rfl

/-- **Composition with the `f`-map on a localised small crystalline site is bijective exactly when
its universe lift is.** -/
theorem bijective_fmapCompOverLift_iff {B : CrystallineThickening S}
    (N : SheafOfModules.{u} ((structureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A₁.left.obj)) :
    Function.Bijective (fmapCompOverLift N g Z) ↔
      Function.Bijective (fmapCompOver.{u} N g Z) := by
  have h₁ := Thickening.bijective_uliftForPresentationMap.{u, u, u}
    ((moduleRestrictionSheafOverFunctor.{u} A₁.hom).obj N) Z
  have h₂ := Thickening.bijective_uliftForPresentationMap.{u, u, u}
    ((moduleRestrictionSheafOverFunctor.{u} A₂.hom).obj N)
    ((SheafOfModules.pushforward.{u}
      (Thickening.ringRestrictionSheafFMap g.left.hom)).obj Z)
  have hsq : (fmapCompOverLift N g Z) ∘
        (fun k : (moduleRestrictionSheafOverFunctor.{u} A₁.hom).obj N ⟶ Z ↦
          SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) =
      (fun k ↦ SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) ∘
        (fmapCompOver.{u} N g Z) :=
    funext fun k ↦ fmapCompOverLift_uliftForPresentationMap N g Z k
  rw [← Function.Bijective.of_comp_iff (fmapCompOverLift N g Z) h₁, hsq,
    Function.Bijective.of_comp_iff' h₂]

/-- Composition with the `f`-map at the raised universe, in its own spelling and in the spelling
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.fmapCompOverLift` gives
it, are the same map. -/
theorem bijective_fmapCompOver_uliftForPresentation_iff {B : CrystallineThickening S}
    (N : SheafOfModules.{u} ((structureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A₁.left.obj)) :
    Function.Bijective (fmapCompOver.{u + 1}
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) ↔
      Function.Bijective (fmapCompOverLift N g Z) :=
  Iff.rfl

/-- **A globally presented sheaf of modules on a localised small crystalline site has bijective
`f`-map composition.**  This is the computation the source of [Stacks, Tag 07IT] performs for the
implication (1) ⇒ (2)(b), carried out on the localised site: restriction to the ambient scheme
preserves the coproducts and the cokernel of the presentation, being a pushforward along a
continuous *and cocontinuous* functor, and composition with the `f`-map is bijective at the
structure sheaf. -/
theorem bijective_fmapCompOverLift_of_hasGlobalPresentation {B : CrystallineThickening S}
    (N : SheafOfModules.{u} ((structureSheaf S).over B)) (hN : N.HasGlobalPresentation)
    {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A₁.left.obj)) :
    Function.Bijective (fmapCompOverLift N g Z) := by
  have hA := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} A₁.hom
  have hB := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} A₂.hom
  have hA' : PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf A₁.left.obj) from
          moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom) := preservesColimitsOfSize_shrink _
  have hB' : PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf A₂.left.obj) from
          moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom) := preservesColimitsOfSize_shrink _
  refine (bijective_fmapCompOver_uliftForPresentation_iff N g Z).1 ?_
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcoker⟩⟩ := hN
  have hθ : ∀ {N₁ N₂ : SheafOfModules.{u + 1} ((structureSheaf S).over B)} (ψ : N₁ ⟶ N₂)
      (k : (moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom).obj N₂ ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z),
      fmapCompOver.{u + 1} N₁ g (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)
          ((moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom).map ψ ≫ k) =
        (moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom).map ψ ≫
          fmapCompOver.{u + 1} N₂ g
            (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z) k :=
    fun ψ k ↦ fmapCompOver_naturality ψ g _ k
  have hunit : Function.Bijective (fmapCompOver.{u + 1}
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (SheafOfModules.unit ((structureSheaf S).over B))) g
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    (bijective_fmapCompOver_uliftForPresentation_iff _ g Z).2
      ((bijective_fmapCompOverLift_iff _ g Z).2 (bijective_fmapCompOver_unit g Z))
  have hPbij : Function.Bijective (fmapCompOver.{u + 1} P g
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    Stacks.PresentedBijectivity.bijective_of_cofan hθ ι
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom) _
        (Cofan.mk P ι)) (isColimitOfPreserves _ hP))
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom) _
        (Cofan.mk P ι)) (isColimitOfPreserves _ hP)) hunit
  have hQbij : Function.Bijective (fmapCompOver.{u + 1} Q g
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    Stacks.PresentedBijectivity.bijective_of_cofan hθ κ
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom) _
        (Cofan.mk Q κ)) (isColimitOfPreserves _ hQ))
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom) _
        (Cofan.mk Q κ)) (isColimitOfPreserves _ hQ)) hunit
  have hab' : a ≫ b = 0 ≫ b := by rw [hab, zero_comp]
  exact Stacks.PresentedBijectivity.bijective_of_cofork hθ
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom) hab'
      (isColimitOfPreserves _ hcoker))
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom) hab'
      (isColimitOfPreserves _ hcoker)) hPbij hQbij.1

/-! ### The crystal condition at a morphism over a base carrying a presentation -/

/-- **A sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` whose restriction to a localised small
crystalline site has a global presentation has invertible comparison maps at every morphism over
that base.** -/
theorem isIso_moduleComparisonSheaf_of_hasGlobalPresentation_over
    (M : SheafOfModules.{u} (structureSheaf S)) {B : CrystallineThickening S}
    (hM : (M.over B).HasGlobalPresentation) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) :
    IsIso (moduleComparisonSheaf M g.left) :=
  (isIso_moduleComparisonSheaf_iff_bijective_fmapComp M g.left).2 fun Z ↦
    (bijective_fmapCompOver_over_iff M g Z).1
      ((bijective_fmapCompOverLift_iff _ g Z).1
        (bijective_fmapCompOverLift_of_hasGlobalPresentation (M.over B) hM g Z))

/-- **A sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` whose restriction to the localisation of
`Cris(X/S)` at an object has a global presentation has an invertible comparison map at every
morphism into that object.** -/
theorem isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target
    (M : SheafOfModules.{u} (structureSheaf S)) {A B : CrystallineThickening S}
    (hM : (M.over B).HasGlobalPresentation) (r : A ⟶ B) :
    IsIso (moduleComparisonSheaf M r) :=
  isIso_moduleComparisonSheaf_of_hasGlobalPresentation_over M hM
    (Over.homMk r (Category.comp_id r) : Over.mk r ⟶ Over.mk (𝟙 B))

end Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

end
