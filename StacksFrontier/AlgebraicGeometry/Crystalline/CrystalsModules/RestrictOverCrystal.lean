module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.PresentedCrystal
public import StacksFrontier.CategoryTheory.Sites.SlicePost.IntoSlice

/-!
# A presented module on a localised crystalline site has invertible comparison maps

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation and let `B` be an object of that site.  This file runs the computation of
[Stacks, Tag 07IT] for the implication (1) ⇒ (2)(b) on the *localised* site `CRIS(X/S)/B`:

> assume `F` restricted to `𝒞/(U, T, δ)` has a global presentation
> `⊕_J 𝒪_{X/S} → ⊕_I 𝒪_{X/S} → F → 0`. It is clear that this gives a presentation
> `⊕_J 𝒪_T → ⊕_I 𝒪_T → F_T → 0` ... Moreover, the presentation restricts to `T'` to give a
> similar presentation of `F_{T'}`, whence (b) holds.

The conclusion is that if the restriction of `F` to `CRIS(X/S)/B` has a global presentation, then
the comparison map `c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules is an isomorphism for
*every* morphism `f` of `CRIS(X/S)` whose target is `B`.

`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.PresentedCrystal` is the same
computation with the presentation taken on all of `CRIS(X/S)`; the hypothesis here is weaker, and
it is the one quasi-coherence actually provides.

## The restriction functor into a localised site

Everything rests on the restrictions of an object `A` of `CRIS(X/S)` to the opens of its ambient
scheme being a functor *into the localised site* `CRIS(X/S)/B`, for any morphism `h : A ⟶ B`:
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOverFunctor`, which sends an open `W`
to the restriction `A|_W` equipped with the structure morphism `A|_W ⟶ A ⟶ B`.  Composed with
`CategoryTheory.Over.forget B` it is the restriction functor
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor` of `A` itself, on the
nose, so its continuity and cocontinuity follow from those of the latter by the general criteria
of `StacksFrontier.CategoryTheory.Sites.SlicePost.IntoSlice`.  Being continuous *and* cocontinuous,
restriction of sheaves of modules along it preserves colimits, which is what carries a
presentation on the localised site to the Zariski site of the ambient scheme.

The comparison of structure sheaves is the identity: the restriction of `𝒪_{X/S}` to the opens of
the ambient scheme of `A` *is* the restriction along `restrictOverFunctor h` of the localisation
of `𝒪_{X/S}` at `B`, because the two site functors agree.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOverFunctor` — **the restrictions of
  an object to the opens of its ambient scheme, as a functor into a localised crystalline site**,
  with its continuity and cocontinuity.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheafOverFunctor` — the
  restriction `F ↦ F_T` of [Stacks, Tag 07IQ] for a module on a localised crystalline site.
* `Crystalline.GlobalCrystallineSituation.Thickening.fmapCompOver` — composition with the `f`-map
  there, at an arbitrary module universe.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.bijective_fmapCompOver_over_iff` — the
  `f`-map composition of the restriction of a module to a localised site is bijective exactly when
  its `f`-map composition on `CRIS(X/S)` is.
* `bijective_fmapCompOverLift_of_hasGlobalPresentation` — a globally presented sheaf of modules on
  a localised crystalline site has bijective `f`-map composition.
* `isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target` — **a sheaf of
  `𝒪_{X/S}`-modules whose restriction to `CRIS(X/S)/B` has a global presentation has an invertible
  comparison map at every morphism with target `B`.**

## Implementation notes

The crystal condition is tested through `isIso_moduleComparisonSheaf_iff_bijective_fmapComp`, which
names no pullback functor and therefore survives the universe lift of the module sections at which
a global presentation on a crystalline site lives; the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.PresentedCrystal` explains that test.

The restriction to the ambient scheme of the restriction of a module to the localised site, and
its restriction to the ambient scheme taken directly, have the same sections over every open, but
the two iterated restrictions of scalars along identity morphisms of sheaves of rings are not
definitionally the same sheaf of modules; they are compared by
`Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheafOverIso`, an isomorphism
which is the identity on sections, and bijectivity of the `f`-map composition is transported along
it.

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

namespace Crystalline.GlobalCrystallineSituation.Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The restrictions of an object into a localised crystalline site -/

/-- **The restrictions of an object of `CRIS(X/S)` to the opens of its ambient scheme, as a
functor into the localisation of `CRIS(X/S)` at that object.** -/
noncomputable def selfOverFunctor (A : Thickening S) :
    A.thickening.target.scheme.Opens ⥤ Over A where
  obj W := Over.mk (A.restrictOpenHom W)
  map i := Over.homMk (A.restrictOpenLE i.le) (restrictOpenLE_restrictOpenHom A i.le)
  map_id _ := by ext; exact A.restrictOpenFunctor.map_id _
  map_comp i j := by ext; exact A.restrictOpenFunctor.map_comp i j

/-- **The restrictions of an object of `CRIS(X/S)` to the opens of its ambient scheme, as a
functor into the localisation of `CRIS(X/S)` at an object the given one maps to.** -/
noncomputable def restrictOverFunctor {A B : Thickening S} (h : A ⟶ B) :
    A.thickening.target.scheme.Opens ⥤ Over B :=
  selfOverFunctor A ⋙ Over.map h

/-- Forgetting the base of the localised site recovers the restriction functor of the object. -/
theorem restrictOverFunctor_comp_forget {A B : Thickening S} (h : A ⟶ B) :
    restrictOverFunctor h ⋙ Over.forget B = A.restrictOpenFunctor := rfl

/-- The restrictions of an object into a localised crystalline site form a cocontinuous functor
from the Zariski site of its ambient scheme. -/
instance isCocontinuous_restrictOverFunctor {A B : Thickening S} (h : A ⟶ B) :
    (restrictOverFunctor h).IsCocontinuous
      (Opens.grothendieckTopology ↥A.thickening.target.scheme) ((topology S).over B) :=
  Functor.isCocontinuous_of_comp_overForget _ _ _
    (by rw [restrictOverFunctor_comp_forget h]; exact restrictOpenFunctor_isCocontinuous A)

/-- The restrictions of an object into a localised crystalline site preserve pullbacks. -/
instance preservesLimitsOfShape_walkingCospan_restrictOverFunctor {A B : Thickening S}
    (h : A ⟶ B) : PreservesLimitsOfShape WalkingCospan (restrictOverFunctor h) :=
  have : PreservesLimitsOfShape WalkingCospan (restrictOverFunctor h ⋙ Over.forget B) := by
    rw [restrictOverFunctor_comp_forget h]
    exact preservesLimitsOfShape_walkingCospan_restrictOpenFunctor A
  preservesLimitsOfShape_of_reflects_of_preserves (restrictOverFunctor h) (Over.forget B)

/-- The restrictions of an object into a localised crystalline site form a continuous functor
from the Zariski site of its ambient scheme. -/
instance isContinuous_restrictOverFunctor {A B : Thickening S} (h : A ⟶ B) :
    (restrictOverFunctor h).IsContinuous
      (Opens.grothendieckTopology ↥A.thickening.target.scheme) ((topology S).over B) :=
  Functor.isContinuous_of_comp_overForget _ _ _
    (by rw [restrictOverFunctor_comp_forget h]; exact coverPreserving_restrictOpenFunctor A)

/-- The restriction of the structure sheaf of a localised crystalline site to the opens of the
ambient scheme of an object over the base *is* the restriction of `𝒪_{X/S}`. -/
theorem sheafPushforward_restrictOverFunctor_structure {A B : Thickening S} (h : A ⟶ B) :
    ((restrictOverFunctor h).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥A.thickening.target.scheme)
        ((topology S).over B)).obj ((crystallineStructureSheaf S).over B) =
      A.ringRestrictionSheaf := rfl

/-- **The comparison of structure sheaves for the restriction to the ambient scheme of an object
of a localised crystalline site is the identity.** -/
noncomputable def restrictOverStructureHom {A B : Thickening S} (h : A ⟶ B) :
    A.ringRestrictionSheaf ⟶
      ((restrictOverFunctor h).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥A.thickening.target.scheme)
        ((topology S).over B)).obj ((crystallineStructureSheaf S).over B) :=
  𝟙 A.ringRestrictionSheaf

/-- **The restriction `F ↦ F_T` of [Stacks, Tag 07IQ] for a sheaf of modules on a localised
crystalline site**, at an arbitrary module universe. -/
noncomputable def moduleRestrictionSheafOverFunctor {A B : Thickening S} (h : A ⟶ B) :
    SheafOfModules.{m} ((crystallineStructureSheaf S).over B) ⥤
      SheafOfModules.{m} A.ringRestrictionSheaf :=
  SheafOfModules.pushforward.{m} (restrictOverStructureHom h)

/-- **The restriction to the ambient scheme of an object over the base of the restriction of a
module to a localised crystalline site is its restriction to that ambient scheme.**  Both have the
sections of the module over the restrictions of the object as their sections, so the comparison is
the identity on sections. -/
noncomputable def moduleRestrictionSheafOverIso
    (M : SheafOfModules.{m} (crystallineStructureSheaf S)) {A B : Thickening S} (h : A ⟶ B) :
    (moduleRestrictionSheafOverFunctor.{m} h).obj (M.over B) ≅
      (moduleRestrictionSheafFunctor.{m} A).obj M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y f; ext x; rfl))

/-- The isomorphism `moduleRestrictionSheafOverIso` is the identity on sections over every open. -/
@[simp]
theorem moduleRestrictionSheafOverIso_hom_val_app
    (M : SheafOfModules.{m} (crystallineStructureSheaf S)) {A B : Thickening S} (h : A ⟶ B)
    (W : (A.thickening.target.scheme.Opens)ᵒᵖ) :
    (moduleRestrictionSheafOverIso M h).hom.val.app W = 𝟙 _ := rfl

/-- The restriction of a morphism of a localised crystalline site over an open of the ambient
scheme of its target is a morphism over the base. -/
theorem restrictOpenMap_comp_restrictOpenHom_comp {B : Thickening S} {A₁ A₂ : Over B}
    (g : A₁ ⟶ A₂) (W : A₂.left.thickening.target.scheme.Opens) :
    restrictOpenMap g.left W ≫ (A₂.left.restrictOpenHom W ≫ A₂.hom) =
      A₁.left.restrictOpenHom (g.left.targetHom.hom ⁻¹ᵁ W) ≫ A₁.hom := by
  rw [← Category.assoc, restrictOpenMap_restrictOpenHom, Category.assoc, Over.w g]

/-- **The restrictions of a morphism of a localised crystalline site over the opens of the ambient
schemes**, as a natural transformation of functors into the localised site. -/
noncomputable def restrictOverFunctorMap {B : Thickening S} {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) :
    Opens.map g.left.targetHom.hom.base ⋙ restrictOverFunctor A₁.hom ⟶
      restrictOverFunctor A₂.hom where
  app W := Over.homMk (restrictOpenMap g.left W) (restrictOpenMap_comp_restrictOpenHom_comp g W)
  naturality _ _ i := by ext; exact restrictOpenLE_restrictOpenMap g.left (leOfHom i)

/-- **The `f`-map of [Stacks, Tag 07IQ] for a sheaf of modules on a localised crystalline
site**, at an arbitrary module universe. -/
noncomputable def moduleFMapSheafOver {B : Thickening S}
    (N : SheafOfModules.{m} ((crystallineStructureSheaf S).over B)) {A₁ A₂ : Over B}
    (g : A₁ ⟶ A₂) :
    (moduleRestrictionSheafOverFunctor.{m} A₂.hom).obj N ⟶
      (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g.left)).obj
        ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).obj N) :=
  ⟨PresheafOfModules.pushforwardOfNatTrans (restrictOverFunctorMap g)
    ((crystallineStructureSheaf S).over B).obj N.val⟩

/-- **Composition with the `f`-map on a localised crystalline site.** -/
noncomputable def fmapCompOver {B : Thickening S}
    (N : SheafOfModules.{m} ((crystallineStructureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} A₁.left.ringRestrictionSheaf) :
    ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).obj N ⟶ Z) →
      ((moduleRestrictionSheafOverFunctor.{m} A₂.hom).obj N ⟶
        (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g.left)).obj Z) :=
  fun k ↦ moduleFMapSheafOver N g ≫
    (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g.left)).map k

/-- **Composition with the `f`-map on a localised crystalline site is natural in the module**,
contravariantly. -/
theorem fmapCompOver_naturality {B : Thickening S}
    {N₁ N₂ : SheafOfModules.{m} ((crystallineStructureSheaf S).over B)} (ψ : N₁ ⟶ N₂)
    {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) (Z : SheafOfModules.{m} A₁.left.ringRestrictionSheaf)
    (k : (moduleRestrictionSheafOverFunctor.{m} A₁.hom).obj N₂ ⟶ Z) :
    fmapCompOver N₁ g Z ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).map ψ ≫ k) =
      (moduleRestrictionSheafOverFunctor.{m} A₂.hom).map ψ ≫ fmapCompOver N₂ g Z k := by
  have h : (moduleRestrictionSheafOverFunctor.{m} A₂.hom).map ψ ≫ moduleFMapSheafOver N₂ g =
      moduleFMapSheafOver N₁ g ≫
        (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g.left)).map
          ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).map ψ) := by
    apply SheafOfModules.Hom.ext
    ext W x
    exact (PresheafOfModules.naturality_apply ψ.val
      ((restrictOverFunctorMap g).app W.unop).op x).symm
  simp only [fmapCompOver, Functor.map_comp]
  rw [← Category.assoc, ← h, Category.assoc]

/-- Precomposition with an isomorphism is bijective on morphisms. -/
theorem bijective_comp_left_of_iso {C₁ : Type*} [Category C₁] {X Y Z : C₁} (e : X ≅ Y) :
    Function.Bijective (fun k : Y ⟶ Z ↦ e.hom ≫ k) :=
  ⟨fun _ _ hab ↦ by simpa using congrArg (fun t ↦ e.inv ≫ t) hab,
    fun c ↦ ⟨e.inv ≫ c, by simp⟩⟩

/-- Bijectivity transfers along a commuting square whose two other sides are bijective. -/
private theorem bijective_iff_of_comp_eq {α β γ δ : Sort*} {f : α → β} {g : γ → δ} {u : γ → α}
    {v : δ → β} (hu : Function.Bijective u) (hv : Function.Bijective v) (h : f ∘ u = v ∘ g) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [← Function.Bijective.of_comp_iff _ hu, h, hv.of_comp_iff']

/-- **Composition with the `f`-map of an isomorphic module is bijective exactly when it is for the
given one.** -/
theorem bijective_fmapCompOver_congr {B : Thickening S}
    {N₁ N₂ : SheafOfModules.{m} ((crystallineStructureSheaf S).over B)} (e : N₁ ≅ N₂)
    {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) (Z : SheafOfModules.{m} A₁.left.ringRestrictionSheaf)
    (h : Function.Bijective (fmapCompOver N₂ g Z)) :
    Function.Bijective (fmapCompOver N₁ g Z) := by
  refine (bijective_iff_of_comp_eq
    (bijective_comp_left_of_iso (Z := Z) ((moduleRestrictionSheafOverFunctor.{m} A₁.hom).mapIso e))
    (bijective_comp_left_of_iso
      (Z := (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g.left)).obj Z)
      ((moduleRestrictionSheafOverFunctor.{m} A₂.hom).mapIso e))
    (by exact funext fun k ↦ fmapCompOver_naturality e.hom g Z k)).2 h

/-- **Composition with the `f`-map of the restriction of a module to a localised crystalline site
is composition with its `f`-map on the big crystalline site**, read through the identification of
the two restrictions to the ambient schemes. -/
theorem fmapCompOver_over (M : SheafOfModules.{m} (crystallineStructureSheaf S))
    {B : Thickening S} {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} A₁.left.ringRestrictionSheaf)
    (k : (moduleRestrictionSheafFunctor.{m} A₁.left).obj M ⟶ Z) :
    fmapCompOver (M.over B) g Z ((moduleRestrictionSheafOverIso M A₁.hom).hom ≫ k) =
      (moduleRestrictionSheafOverIso M A₂.hom).hom ≫ fmapComp.{m} M g.left Z k := by
  apply SheafOfModules.Hom.ext
  ext W x
  rfl

/-- **Composition with the `f`-map of the restriction of a module to a localised crystalline site
is bijective exactly when composition with its `f`-map on the big crystalline site is.** -/
theorem bijective_fmapCompOver_over_iff (M : SheafOfModules.{m} (crystallineStructureSheaf S))
    {B : Thickening S} {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{m} A₁.left.ringRestrictionSheaf) :
    Function.Bijective (fmapCompOver (M.over B) g Z) ↔
      Function.Bijective (fmapComp.{m} M g.left Z) := by
  exact bijective_iff_of_comp_eq
    (bijective_comp_left_of_iso (Z := Z) (moduleRestrictionSheafOverIso M A₁.hom))
    (bijective_comp_left_of_iso
      (Z := (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g.left)).obj Z)
      (moduleRestrictionSheafOverIso M A₂.hom))
    (funext fun k ↦ fmapCompOver_over M g Z k)

/-- **The restriction of the structure sheaf of `CRIS(X/S)` to a localised crystalline site is the
structure sheaf of that site.** -/
noncomputable def unitOverIso (B : Thickening S) :
    (SheafOfModules.unit (crystallineStructureSheaf S)).over B ≅
      SheafOfModules.unit ((crystallineStructureSheaf S).over B) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y f; ext; rfl))

/-- **Composition with the `f`-map is bijective at the structure sheaf of a localised crystalline
site**: the comparison map of `𝒪_{X/S}` on the big crystalline site is an isomorphism. -/
theorem bijective_fmapCompOver_unit {B : Thickening S} {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} A₁.left.ringRestrictionSheaf) :
    Function.Bijective
      (fmapCompOver (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) g Z) :=
  bijective_fmapCompOver_congr (unitOverIso B).symm g Z
    ((bijective_fmapCompOver_over_iff _ g Z).2
      ((isIso_moduleComparisonSheaf_iff_bijective_fmapComp _ g.left).1
        (isIso_moduleComparisonSheaf_unit g.left) Z))

/-- **Restriction to the ambient scheme from a localised crystalline site preserves colimits of
size `u + 1`**, the size in which a global presentation on that site is indexed. -/
theorem preservesColimitsOfSize_moduleRestrictionSheafOverFunctor {A B : Thickening S}
    (h : A ⟶ B) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} A.ringRestrictionSheaf from
        moduleRestrictionSheafOverFunctor.{u + 1} h) := by
  have _ : HasSheafify ((topology S).over B) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((topology S).over B).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    (restrictOverFunctor h) (restrictOverStructureHom h)

/-! ### The index universe of a global presentation -/

/-- **Composition with the `f`-map on a localised crystalline site at the raised module universe,
read on the universe lifts of the modules at the module universe `u`.** -/
noncomputable def fmapCompOverLift {B : Thickening S}
    (N : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} A₁.left.ringRestrictionSheaf) :
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafOverFunctor.{u} A₁.hom).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z) →
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafOverFunctor.{u} A₂.hom).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g.left)).obj Z)) :=
  fmapCompOver.{u + 1} (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)

/-- **Composition with the `f`-map on a localised crystalline site commutes with a universe lift
of the module sections.** -/
theorem fmapCompOverLift_uliftForPresentationMap {B : Thickening S}
    (N : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} A₁.left.ringRestrictionSheaf)
    (k : (moduleRestrictionSheafOverFunctor.{u} A₁.hom).obj N ⟶ Z) :
    fmapCompOverLift N g Z (SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) =
      SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} (fmapCompOver.{u} N g Z k) := by
  apply SheafOfModules.Hom.ext
  ext W x
  rfl

/-- **Composition with the `f`-map on a localised crystalline site is bijective exactly when its
universe lift is.** -/
theorem bijective_fmapCompOverLift_iff {B : Thickening S}
    (N : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} A₁.left.ringRestrictionSheaf) :
    Function.Bijective (fmapCompOverLift N g Z) ↔ Function.Bijective (fmapCompOver.{u} N g Z) := by
  exact bijective_iff_of_comp_eq
    (bijective_uliftForPresentationMap.{u, u, u}
      ((moduleRestrictionSheafOverFunctor.{u} A₁.hom).obj N) Z)
    (bijective_uliftForPresentationMap.{u, u, u}
      ((moduleRestrictionSheafOverFunctor.{u} A₂.hom).obj N)
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g.left)).obj Z))
    (funext fun k ↦ fmapCompOverLift_uliftForPresentationMap N g Z k)

/-- Composition with the `f`-map at the raised universe, in its own spelling and in the spelling
`Crystalline.GlobalCrystallineSituation.Thickening.fmapCompOverLift` gives it, are the same map. -/
theorem bijective_fmapCompOver_uliftForPresentation_iff {B : Thickening S}
    (N : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂)
    (Z : SheafOfModules.{u} A₁.left.ringRestrictionSheaf) :
    Function.Bijective (fmapCompOver.{u + 1}
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) ↔
      Function.Bijective (fmapCompOverLift N g Z) :=
  Iff.rfl

/-- **A globally presented sheaf of modules on a localised crystalline site has bijective `f`-map
composition.**  This is the computation the source of [Stacks, Tag 07IT] performs for the
implication (1) ⇒ (2)(b), carried out on the localised site: restriction to the ambient scheme
preserves the coproducts and the cokernel of the presentation, being a pushforward along a
continuous *and cocontinuous* functor, and composition with the `f`-map is bijective at the
structure sheaf. -/
theorem bijective_fmapCompOverLift_of_hasGlobalPresentation {B : Thickening S}
    (N : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)) (hN : N.HasGlobalPresentation)
    {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) (Z : SheafOfModules.{u} A₁.left.ringRestrictionSheaf) :
    Function.Bijective (fmapCompOverLift N g Z) := by
  have hA := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} A₁.hom
  have hB := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} A₂.hom
  have hA' : PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} A₁.left.ringRestrictionSheaf from
          moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom) := preservesColimitsOfSize_shrink _
  have hB' : PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} A₂.left.ringRestrictionSheaf from
          moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom) := preservesColimitsOfSize_shrink _
  refine (bijective_fmapCompOver_uliftForPresentation_iff N g Z).1 ?_
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcoker⟩⟩ := hN
  have hθ : ∀ {N₁ N₂ : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
      (ψ : N₁ ⟶ N₂)
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
        (SheafOfModules.unit ((crystallineStructureSheaf S).over B))) g
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    (bijective_fmapCompOver_uliftForPresentation_iff _ g Z).2
      ((bijective_fmapCompOverLift_iff _ g Z).2 (bijective_fmapCompOver_unit g Z))
  have hfree : ∀ {J : Type (u + 1)}
      {U X : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
      (c : J → (U ⟶ X)), IsColimit (Cofan.mk X c) →
      Function.Bijective (fmapCompOver.{u + 1} U g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) →
      Function.Bijective (fmapCompOver.{u + 1} X g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    fun c hc hU ↦ Stacks.PresentedBijectivity.bijective_of_cofan hθ c
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom) _
        _) (isColimitOfPreserves _ hc))
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom) _
        _) (isColimitOfPreserves _ hc)) hU
  have hPbij := hfree ι hP hunit
  have hQbij := hfree κ hQ hunit
  have hab' : a ≫ b = 0 ≫ b := by rw [hab, zero_comp]
  exact Stacks.PresentedBijectivity.bijective_of_cofork hθ
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₁.hom) hab'
      (isColimitOfPreserves _ hcoker))
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafOverFunctor.{u + 1} A₂.hom) hab'
      (isColimitOfPreserves _ hcoker)) hPbij hQbij.1

/-! ### The crystal condition at a morphism over a base carrying a presentation -/

/-- **A sheaf of `𝒪_{X/S}`-modules whose restriction to a localised crystalline site has a global
presentation has invertible comparison maps at every morphism over that base.** -/
theorem isIso_moduleComparisonSheaf_of_hasGlobalPresentation_over
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {B : Thickening S}
    (hM : (M.over B).HasGlobalPresentation) {A₁ A₂ : Over B} (g : A₁ ⟶ A₂) :
    IsIso (moduleComparisonSheaf M g.left) :=
  (isIso_moduleComparisonSheaf_iff_bijective_fmapComp M g.left).2 fun Z ↦
    (bijective_fmapCompOver_over_iff M g Z).1
      ((bijective_fmapCompOverLift_iff _ g Z).1
        (bijective_fmapCompOverLift_of_hasGlobalPresentation (M.over B) hM g Z))

/-- **A sheaf of `𝒪_{X/S}`-modules whose restriction to the localisation of `CRIS(X/S)` at an
object has a global presentation has an invertible comparison map at every morphism into that
object.** -/
theorem isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A B : Thickening S}
    (hM : (M.over B).HasGlobalPresentation) (r : A ⟶ B) :
    IsIso (moduleComparisonSheaf M r) :=
  isIso_moduleComparisonSheaf_of_hasGlobalPresentation_over M hM
    (Over.homMk r (Category.comp_id r) : Over.mk r ⟶ Over.mk (𝟙 B))

end Crystalline.GlobalCrystallineSituation.Thickening

end
