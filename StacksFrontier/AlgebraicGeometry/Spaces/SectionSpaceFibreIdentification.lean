module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceSeparated

/-!
# The fibres of a comparison of spaces of sections

Let `Z ⟶ U` be a morphism of the big fppf site of `U`, let `w₂ : W₂ ⟶ h_Z` be a morphism of
presheaves on that site, and let `g : W₁ ⟶ W₂` be a morphism over `h_Z`, so that `w₁ = g ≫ w₂`.
Postcomposition with `g` carries a section of `W₁_T ⟶ Z_T` to a section of `W₂_T ⟶ Z_T` and
therefore defines a morphism of the spaces of sections of Stacks 05XR,
`AlgebraicGeometry.Space.sectionSpaceMap`.

This file computes the fibres of that morphism. A section `σ` of `W₂_T ⟶ Z_T` over a test
object `T / U` is a morphism `Z_T = T × Z ⟶ W₂` over `h_Z`, so `g` may be base changed along
it: the projection `(T × Z) ×_{W₂} W₁ ⟶ T × Z` is a morphism to `Z_T`, and a section of it over
an object `x : T' ⟶ T` of the big fppf site over `T` is a morphism
`T' × Z ⟶ (T × Z) ×_{W₂} W₁` whose first component is the morphism `T' × Z ⟶ T × Z` induced
by `x`. Those are `AlgebraicGeometry.Space.BaseChangeSections`, and the identification is that
they are exactly the sections of `W₁_{T'} ⟶ Z_{T'}` whose postcomposition with `g` is the
restriction of `σ` along `x`: one direction composes with the second projection of the fibre
product, the other is the morphism into the fibre product determined by the section and by `x`.

Assembled into a presheaf on the big fppf site of `U` over `h_T`, these sections identify the
fibre: the square formed by that presheaf, its structure morphism to `h_T` and the section of
`w₁` underlying a section of the base change is cartesian over the point of the space of
sections of `w₂` named by `σ`. So the space of sections of the base change of `g` along `σ`,
over the base `T`, is the fibre of the comparison morphism at `σ`.

## Main definitions

* `AlgebraicGeometry.Space.SectionsOver.pushforward`: postcomposition of a section with a
  morphism over `h_Z`.
* `AlgebraicGeometry.Space.sectionSpaceMap`: the induced morphism of the spaces of sections.
* `AlgebraicGeometry.Space.BaseChangeSections`: a section, over an object of the big fppf site
  over `T`, of the base change of `g` along a section `σ` of `w₂` over `T`.
* `AlgebraicGeometry.Space.baseChangeSectionPresheaf`: those sections as a presheaf on the big
  fppf site of `U`, with its structure morphism
  `AlgebraicGeometry.Space.baseChangeSectionBase` to `h_T`, its morphism
  `AlgebraicGeometry.Space.baseChangeSectionToSectionSpace` to the space of sections of `w₁`,
  and the morphism `AlgebraicGeometry.Space.baseChangeSectionLift` into it determined by a
  compatible pair of morphisms.

## Main results

* `AlgebraicGeometry.Space.baseChangeSectionsEquiv`: **the fibre identification over a test
  object**: the sections over `x : T' ⟶ T` of the base change of `g` along `σ` are the sections
  of `W₁_{T'} ⟶ Z_{T'}` whose postcomposition with `g` is the restriction of `σ` along `x`.
* `AlgebraicGeometry.Space.isPullback_baseChangeSectionPresheaf`: **the fibre
  identification**: the presheaf of sections of the base change of `g` along `σ` is the fibre
  of `AlgebraicGeometry.Space.sectionSpaceMap` at `σ`.
* `AlgebraicGeometry.Space.isEtale_pullback_fst_sectionsOver` and
  `AlgebraicGeometry.Space.isSurjective_pullback_fst_sectionsOver`: the base change of an étale,
  respectively surjective, `g` along a section is étale, respectively surjective.

## Implementation notes

The space of sections of Stacks 05XR is only described through the identification
`AlgebraicGeometry.Space.sectionSpaceEquiv` of its values with
`AlgebraicGeometry.Space.SectionsOver`, so every morphism out of or into it is transported
through that identification rather than computed, and its restriction maps are read off
`AlgebraicGeometry.Space.sectionSpaceEquiv_restrict`.

The sections of the base change are indexed by a morphism `x : T' ⟶ T` carried as data, that
is, the presheaf of them is a presheaf over `h_T`. That is the shape in which a presheaf on the
big fppf site over the scheme underlying `T` appears on the site over `U`: by the presheaf-level
form of Stacks 00Y1, `CategoryTheory.OverShriek.presheafEquivalence`, presheaves over `h_T`
are presheaves on the slice of the big fppf category over `U` at `T`, and that slice is the big
fppf category over the scheme underlying `T` by
`CategoryTheory.Over.iteratedSliceEquiv`. What is *not* done here is to carry the base change of
`g` along `σ` across those equivalences together with its properties: the space of sections of
Stacks 05XR formed over `T` is an algebraic space étale over `T` by
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isSeparated` and
`AlgebraicGeometry.Space.isEtale_sectionSpace_of_isSeparated`, but those consume the base change
as a morphism of presheaves on the site over `T` which is étale and separated onto `Z_T`, with
`Z_T ⟶ T` finite, and the transport of `AlgebraicGeometry.IsAlgebraicSpace`, of étaleness and of
separatedness along the two equivalences above is not established. So the étaleness of the
comparison morphism, and with it the general case of the main assertion of Stacks 05XR, is not
proved in this file, and no statement here carries the tag of that source; the two permanence
results below record the étaleness and surjectivity of the base change on the site over `U`,
which is what such a transport would have to carry over.

No hypothesis is carried beyond `g` being a morphism over `h_Z`: the two permanence results at
the end take their algebraic-space inputs from unconditional results of the library.

## References

* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B U hU`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SectionSpaceFibreIdentification
    (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U) :
    HasPullbacks ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SectionSpaceFibreIdentification
    {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
    {X Y Z : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_SectionSpaceFibreIdentification B U hU).has_limit _

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
  {Z : BigFppfOver B U hU} {W₁ W₂ : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
  {w₁ : W₁ ⟶ yoneda.obj Z} {w₂ : W₂ ⟶ yoneda.obj Z}

/-- The morphism `T' × Z ⟶ T × Z` induced by a composite `T'' ⟶ T' ⟶ T` is the composite of
the induced morphisms. -/
private theorem prod_map_yoneda_comp {T T' T'' : BigFppfOver B U hU} (y : T'' ⟶ T')
    (x : T' ⟶ T) :
    prod.map (yoneda.map (y ≫ x)) (𝟙 (yoneda.obj Z)) =
      prod.map (yoneda.map y) (𝟙 (yoneda.obj Z)) ≫
        prod.map (yoneda.map x) (𝟙 (yoneda.obj Z)) := by
  rw [prod.map_map, Category.comp_id, Functor.map_comp]

/-- Applying a commuting square of morphisms of presheaves to a section gives equal values. -/
private theorem app_apply_eq_of_comp_eq {C : Type*} [Category C] {X F G H : Cᵒᵖ ⥤ Type u}
    {a : X ⟶ F} {b : X ⟶ G} {f : F ⟶ H} {g : G ⟶ H} (h : a ≫ f = b ≫ g) (T : Cᵒᵖ)
    (ξ : X.obj T) : f.app T (a.app T ξ) = g.app T (b.app T ξ) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h T) ξ

/-! ### Postcomposition of sections -/

/-- Postcomposition of a section of `W₁_T ⟶ Z_T` with a morphism `g : W₁ ⟶ W₂` over `h_Z`:
the composite is again a morphism `Z_T ⟶ W₂` over `h_Z`. -/
noncomputable def SectionsOver.pushforward {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₁ w₁) :
    SectionsOver B U hU Z T W₂ w₂ :=
  ⟨σ.1 ≫ g, by rw [Category.assoc, hg, σ.2]⟩

/-- The postcomposition of a section with `g` has underlying morphism `σ.1 ≫ g`. -/
@[simp]
theorem SectionsOver.pushforward_coe {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₁ w₁) :
    (SectionsOver.pushforward hg σ).1 = σ.1 ≫ g :=
  rfl

/-- Postcomposition commutes with restriction of sections. -/
theorem SectionsOver.restrict_pushforward {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} (f : T' ⟶ T) (σ : SectionsOver B U hU Z T W₁ w₁) :
    SectionsOver.restrict f (SectionsOver.pushforward hg σ) =
      SectionsOver.pushforward hg (SectionsOver.restrict f σ) :=
  Subtype.ext (Category.assoc _ _ _).symm

/-- **The comparison of the spaces of sections along a morphism `g : W₁ ⟶ W₂` over `h_Z`**: a
section of `W₁_T ⟶ Z_T` is sent to its postcomposition with `g`. -/
noncomputable def sectionSpaceMap {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁) :
    sectionSpace B U hU Z W₁ w₁ ⟶ sectionSpace B U hU Z W₂ w₂ where
  app T := ↾fun s => (sectionSpaceEquiv B U hU Z T.unop W₂ w₂).symm
    (SectionsOver.pushforward hg (sectionSpaceEquiv B U hU Z T.unop W₁ w₁ s))
  naturality := by
    rintro ⟨T⟩ ⟨T'⟩ f
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change (sectionSpaceEquiv B U hU Z T' W₂ w₂).symm (SectionsOver.pushforward hg
        (sectionSpaceEquiv B U hU Z T' W₁ w₁
          ((sectionSpace B U hU Z W₁ w₁).map f.unop.op s))) =
      (sectionSpace B U hU Z W₂ w₂).map f.unop.op
        ((sectionSpaceEquiv B U hU Z T W₂ w₂).symm
          (SectionsOver.pushforward hg (sectionSpaceEquiv B U hU Z T W₁ w₁ s)))
    apply (sectionSpaceEquiv B U hU Z T' W₂ w₂).injective
    rw [Equiv.apply_symm_apply, sectionSpaceEquiv_restrict w₁ f.unop s,
      sectionSpaceEquiv_restrict w₂ f.unop, Equiv.apply_symm_apply,
      SectionsOver.restrict_pushforward]

/-- The components of the comparison morphism: a section is sent to its postcomposition
with `g`. -/
theorem sectionSpaceEquiv_sectionSpaceMap {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    (T : BigFppfOver B U hU) (s : (sectionSpace B U hU Z W₁ w₁).obj (op T)) :
    sectionSpaceEquiv B U hU Z T W₂ w₂ ((sectionSpaceMap hg).app (op T) s) =
      SectionsOver.pushforward hg (sectionSpaceEquiv B U hU Z T W₁ w₁ s) :=
  Equiv.apply_symm_apply _ _

/-- The point of the space of sections of `w₂` named by a section `σ` over `T`, read off a
morphism `x : T' ⟶ T`, is the restriction of `σ` along `x`. -/
theorem sectionSpaceEquiv_yonedaEquiv_symm {T T' : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) (x : T' ⟶ T) :
    sectionSpaceEquiv B U hU Z T' W₂ w₂
        ((yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T W₂ w₂).symm σ)).app (op T') x) =
      SectionsOver.restrict x σ := by
  change sectionSpaceEquiv B U hU Z T' W₂ w₂ ((sectionSpace B U hU Z W₂ w₂).map x.op
      ((sectionSpaceEquiv B U hU Z T W₂ w₂).symm σ)) = _
  rw [sectionSpaceEquiv_restrict, Equiv.apply_symm_apply]

/-! ### Sections of the base change of `g` along a section of `w₂` -/

/-- **A section of the base change of `g` along a section `σ` of `w₂` over `T`**, over an
object of the big fppf site over `T`: a morphism `x : T' ⟶ T` of the site over `U` together
with a morphism `T' × Z ⟶ (T × Z) ×_{W₂} W₁` whose first component is the morphism
`T' × Z ⟶ T × Z` induced by `x`. -/
abbrev BaseChangeSections (g : W₁ ⟶ W₂) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) (T' : BigFppfOver B U hU) :=
  {p : (T' ⟶ T) × (yoneda.obj T' ⨯ yoneda.obj Z ⟶ pullback σ.1 g) //
    p.2 ≫ pullback.fst σ.1 g = prod.map (yoneda.map p.1) (𝟙 (yoneda.obj Z))}

/-- The sections of the base change over a fixed object form a small type: they are a subtype
of a product of a hom-set of the site with the morphisms out of `T' × Z`, and the latter are
small by `CategoryTheory.small_hom_prod_yoneda`. -/
instance small_baseChangeSections (g : W₁ ⟶ W₂) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) (T' : BigFppfOver B U hU) :
    Small.{u} (BaseChangeSections g σ T') := by
  have : HasBinaryProducts (BigFppfOver B U hU) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  have := CategoryTheory.small_hom_prod_yoneda T' Z (pullback σ.1 g)
  infer_instance

/-- Restriction of a section of the base change along a morphism of the site over `T`. -/
noncomputable def BaseChangeSections.restrict {g : W₁ ⟶ W₂} {T : BigFppfOver B U hU}
    {σ : SectionsOver B U hU Z T W₂ w₂} {T' T'' : BigFppfOver B U hU} (y : T'' ⟶ T')
    (p : BaseChangeSections g σ T') : BaseChangeSections g σ T'' :=
  ⟨⟨y ≫ p.1.1, prod.map (yoneda.map y) (𝟙 (yoneda.obj Z)) ≫ p.1.2⟩, by
    rw [Category.assoc, p.2, ← prod_map_yoneda_comp]⟩

/-- A section of the base change restricted along `y` lies over the composite with `y`. -/
@[simp]
theorem BaseChangeSections.restrict_base {g : W₁ ⟶ W₂} {T : BigFppfOver B U hU}
    {σ : SectionsOver B U hU Z T W₂ w₂} {T' T'' : BigFppfOver B U hU} (y : T'' ⟶ T')
    (p : BaseChangeSections g σ T') :
    (BaseChangeSections.restrict y p).1.1 = y ≫ p.1.1 :=
  rfl

/-- The morphism into the fibre product of a restricted section of the base change is the composite
with the morphism `T'' × Z ⟶ T' × Z` induced by `y`. -/
@[simp]
theorem BaseChangeSections.restrict_lift {g : W₁ ⟶ W₂} {T : BigFppfOver B U hU}
    {σ : SectionsOver B U hU Z T W₂ w₂} {T' T'' : BigFppfOver B U hU} (y : T'' ⟶ T')
    (p : BaseChangeSections g σ T') :
    (BaseChangeSections.restrict y p).1.2 =
      prod.map (yoneda.map y) (𝟙 (yoneda.obj Z)) ≫ p.1.2 :=
  rfl

/-- Restriction along the identity does nothing. -/
theorem BaseChangeSections.restrict_id {g : W₁ ⟶ W₂} {T : BigFppfOver B U hU}
    {σ : SectionsOver B U hU Z T W₂ w₂} {T' : BigFppfOver B U hU}
    (p : BaseChangeSections g σ T') : BaseChangeSections.restrict (𝟙 T') p = p :=
  Subtype.ext (by simp [Prod.ext_iff])

/-- Restriction along a composite is the composite of the restrictions. -/
theorem BaseChangeSections.restrict_comp {g : W₁ ⟶ W₂} {T : BigFppfOver B U hU}
    {σ : SectionsOver B U hU Z T W₂ w₂} {T' T'' T''' : BigFppfOver B U hU} (y : T'' ⟶ T')
    (y' : T''' ⟶ T'') (p : BaseChangeSections g σ T') :
    BaseChangeSections.restrict (y' ≫ y) p =
      BaseChangeSections.restrict y' (BaseChangeSections.restrict y p) :=
  Subtype.ext (Prod.ext (Category.assoc _ _ _) (by
    change prod.map (yoneda.map (y' ≫ y)) (𝟙 (yoneda.obj Z)) ≫ p.1.2 =
      prod.map (yoneda.map y') (𝟙 (yoneda.obj Z)) ≫
        prod.map (yoneda.map y) (𝟙 (yoneda.obj Z)) ≫ p.1.2
    rw [prod_map_yoneda_comp, Category.assoc]))

/-- The sections of the base change of `g` along `σ`, as a presheaf on the big fppf site
of `U`. -/
noncomputable def baseChangeSectionPresheaf (g : W₁ ⟶ W₂) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u where
  obj T' := Shrink (BaseChangeSections g σ T'.unop)
  map {X Y} f := ↾fun s => equivShrink (BaseChangeSections g σ Y.unop)
    (BaseChangeSections.restrict f.unop
      ((equivShrink (BaseChangeSections g σ X.unop)).symm s))
  map_id X := ConcreteCategory.hom_ext _ _ fun s => by
    change equivShrink (BaseChangeSections g σ X.unop)
        (BaseChangeSections.restrict (𝟙 X.unop)
          ((equivShrink (BaseChangeSections g σ X.unop)).symm s)) = s
    rw [BaseChangeSections.restrict_id, Equiv.apply_symm_apply]
  map_comp {X Y V} f h := ConcreteCategory.hom_ext _ _ fun s => by
    change equivShrink (BaseChangeSections g σ V.unop)
        (BaseChangeSections.restrict (h.unop ≫ f.unop)
          ((equivShrink (BaseChangeSections g σ X.unop)).symm s)) =
      equivShrink (BaseChangeSections g σ V.unop)
        (BaseChangeSections.restrict h.unop
          ((equivShrink (BaseChangeSections g σ Y.unop)).symm
            (equivShrink (BaseChangeSections g σ Y.unop)
              (BaseChangeSections.restrict f.unop
                ((equivShrink (BaseChangeSections g σ X.unop)).symm s)))))
    rw [Equiv.symm_apply_apply, BaseChangeSections.restrict_comp]

/-- The values of `AlgebraicGeometry.Space.baseChangeSectionPresheaf` are the sections of the
base change. -/
noncomputable def baseChangeSectionPresheafEquiv (g : W₁ ⟶ W₂) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) (T' : BigFppfOver B U hU) :
    (baseChangeSectionPresheaf g σ).obj (op T') ≃ BaseChangeSections g σ T' :=
  (equivShrink (BaseChangeSections g σ T')).symm

/-- Under `AlgebraicGeometry.Space.baseChangeSectionPresheafEquiv`, the restriction maps of
`AlgebraicGeometry.Space.baseChangeSectionPresheaf` are restriction of sections of the base
change. -/
theorem baseChangeSectionPresheafEquiv_map (g : W₁ ⟶ W₂) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) {T' T'' : BigFppfOver B U hU} (y : T'' ⟶ T')
    (s : (baseChangeSectionPresheaf g σ).obj (op T')) :
    baseChangeSectionPresheafEquiv g σ T'' ((baseChangeSectionPresheaf g σ).map y.op s) =
      BaseChangeSections.restrict y (baseChangeSectionPresheafEquiv g σ T' s) :=
  Equiv.symm_apply_apply _ _

/-! ### The two morphisms out of the presheaf of sections of the base change -/

/-- **The structure morphism of the presheaf of sections of the base change to `h_T`**: a
section of the base change over `x : T' ⟶ T` remembers `x`. -/
noncomputable def baseChangeSectionBase (g : W₁ ⟶ W₂) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) :
    baseChangeSectionPresheaf g σ ⟶ yoneda.obj T where
  app T' := ↾fun s => (baseChangeSectionPresheafEquiv g σ T'.unop s).1.1
  naturality := by
    rintro ⟨T'⟩ ⟨T''⟩ f
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change (baseChangeSectionPresheafEquiv g σ T''
        ((baseChangeSectionPresheaf g σ).map f.unop.op s)).1.1 =
      f.unop ≫ (baseChangeSectionPresheafEquiv g σ T' s).1.1
    rw [baseChangeSectionPresheafEquiv_map, BaseChangeSections.restrict_base]

/-- The structure morphism to `h_T` sends a section of the base change to the morphism to `T` it
lies over. -/
@[simp]
theorem baseChangeSectionBase_app (g : W₁ ⟶ W₂) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W₂ w₂) (T' : BigFppfOver B U hU)
    (s : (baseChangeSectionPresheaf g σ).obj (op T')) :
    (baseChangeSectionBase g σ).app (op T') s =
      (baseChangeSectionPresheafEquiv g σ T' s).1.1 :=
  rfl

/-- **The section of `w₁` underlying a section of the base change**: compose with the second
projection of the fibre product. -/
noncomputable def BaseChangeSections.toSectionsOver {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} {σ : SectionsOver B U hU Z T W₂ w₂}
    (p : BaseChangeSections g σ T') : SectionsOver B U hU Z T' W₁ w₁ :=
  ⟨p.1.2 ≫ pullback.snd σ.1 g, by
    calc (p.1.2 ≫ pullback.snd σ.1 g) ≫ w₁
        = (p.1.2 ≫ pullback.snd σ.1 g ≫ g) ≫ w₂ := by simp only [← hg, Category.assoc]
      _ = (prod.map (yoneda.map p.1.1) (𝟙 (yoneda.obj Z)) ≫ σ.1) ≫ w₂ := by
          rw [← pullback.condition, ← Category.assoc, p.2]
      _ = prod.snd := by rw [Category.assoc, σ.2, prod.map_snd, Category.comp_id]⟩

/-- The section of `w₁` underlying a section of the base change is its composite with the second
projection of the fibre product. -/
@[simp]
theorem BaseChangeSections.toSectionsOver_coe {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} {σ : SectionsOver B U hU Z T W₂ w₂}
    (p : BaseChangeSections g σ T') :
    (BaseChangeSections.toSectionsOver hg p).1 = p.1.2 ≫ pullback.snd σ.1 g :=
  rfl

/-- **The underlying section of `w₁` pushes forward to the restriction of `σ`.** -/
theorem BaseChangeSections.pushforward_toSectionsOver {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} {σ : SectionsOver B U hU Z T W₂ w₂}
    (p : BaseChangeSections g σ T') :
    SectionsOver.pushforward hg (BaseChangeSections.toSectionsOver hg p) =
      SectionsOver.restrict p.1.1 σ :=
  Subtype.ext (by
    rw [SectionsOver.pushforward_coe, BaseChangeSections.toSectionsOver_coe, Category.assoc,
      ← pullback.condition, ← Category.assoc, p.2, SectionsOver.restrict_coe])

/-- The underlying section of `w₁` commutes with restriction. -/
theorem BaseChangeSections.toSectionsOver_restrict {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' T'' : BigFppfOver B U hU} {σ : SectionsOver B U hU Z T W₂ w₂} (y : T'' ⟶ T')
    (p : BaseChangeSections g σ T') :
    BaseChangeSections.toSectionsOver hg (BaseChangeSections.restrict y p) =
      SectionsOver.restrict y (BaseChangeSections.toSectionsOver hg p) :=
  Subtype.ext (Category.assoc _ _ _)

/-- A section of `w₁` over `T'` whose postcomposition with `g` is the restriction of `σ` along
`x : T' ⟶ T` agrees over `W₂` with the morphism `T' × Z ⟶ T × Z` induced by `x`. -/
theorem SectionsOver.comp_eq_of_pushforward_eq {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} {σ : SectionsOver B U hU Z T W₂ w₂} {x : T' ⟶ T}
    {s : SectionsOver B U hU Z T' W₁ w₁}
    (hs : SectionsOver.pushforward hg s = SectionsOver.restrict x σ) :
    prod.map (yoneda.map x) (𝟙 (yoneda.obj Z)) ≫ σ.1 = s.1 ≫ g :=
  (congrArg Subtype.val hs).symm

/-- **A section of `w₁` over `T'` whose postcomposition with `g` is the restriction of `σ`
along `x : T' ⟶ T` is a section of the base change over `x`**: the section and the morphism
`T' × Z ⟶ T × Z` induced by `x` agree over `W₂`, hence define a morphism into the fibre
product. -/
noncomputable def BaseChangeSections.ofSectionsOver {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) (x : T' ⟶ T)
    (s : SectionsOver B U hU Z T' W₁ w₁)
    (hs : SectionsOver.pushforward hg s = SectionsOver.restrict x σ) :
    BaseChangeSections g σ T' :=
  ⟨⟨x, pullback.lift (prod.map (yoneda.map x) (𝟙 (yoneda.obj Z))) s.1
      (SectionsOver.comp_eq_of_pushforward_eq hg hs)⟩, pullback.lift_fst _ _ _⟩

/-- The section of the base change attached to a section of `w₁` over `x` lies over `x`. -/
@[simp]
theorem BaseChangeSections.ofSectionsOver_base {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) (x : T' ⟶ T)
    (s : SectionsOver B U hU Z T' W₁ w₁)
    (hs : SectionsOver.pushforward hg s = SectionsOver.restrict x σ) :
    (BaseChangeSections.ofSectionsOver hg σ x s hs).1.1 = x :=
  rfl

/-- The morphism into the fibre product of `BaseChangeSections.ofSectionsOver` is the one
determined by the section and by the morphism `T' × Z ⟶ T × Z` induced by `x`. -/
@[simp]
theorem BaseChangeSections.ofSectionsOver_lift {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) (x : T' ⟶ T)
    (s : SectionsOver B U hU Z T' W₁ w₁)
    (hs : SectionsOver.pushforward hg s = SectionsOver.restrict x σ) :
    (BaseChangeSections.ofSectionsOver hg σ x s hs).1.2 =
      pullback.lift (prod.map (yoneda.map x) (𝟙 (yoneda.obj Z))) s.1
        (SectionsOver.comp_eq_of_pushforward_eq hg hs) :=
  rfl

/-- The section of the base change attached to a section of `w₁` has that section underlying
it. -/
theorem BaseChangeSections.toSectionsOver_ofSectionsOver {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) (x : T' ⟶ T)
    (s : SectionsOver B U hU Z T' W₁ w₁)
    (hs : SectionsOver.pushforward hg s = SectionsOver.restrict x σ) :
    BaseChangeSections.toSectionsOver hg (BaseChangeSections.ofSectionsOver hg σ x s hs) = s :=
  Subtype.ext (pullback.lift_snd _ _ _)

/-- The section of the base change attached to a section of `w₁` depends only on the morphism
to `T` and on that section. -/
theorem BaseChangeSections.ofSectionsOver_congr {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) {x x' : T' ⟶ T}
    {s s' : SectionsOver B U hU Z T' W₁ w₁}
    (hs : SectionsOver.pushforward hg s = SectionsOver.restrict x σ)
    (hs' : SectionsOver.pushforward hg s' = SectionsOver.restrict x' σ) (hx : x = x')
    (hss : s = s') :
    BaseChangeSections.ofSectionsOver hg σ x s hs =
      BaseChangeSections.ofSectionsOver hg σ x' s' hs' := by
  subst hx
  subst hss
  rfl

/-- The section of the base change attached to a section of `w₁` commutes with restriction. -/
theorem BaseChangeSections.restrict_ofSectionsOver {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' T'' : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) (x : T' ⟶ T)
    (s : SectionsOver B U hU Z T' W₁ w₁)
    (hs : SectionsOver.pushforward hg s = SectionsOver.restrict x σ) (y : T'' ⟶ T')
    (hs' : SectionsOver.pushforward hg (SectionsOver.restrict y s) =
      SectionsOver.restrict (y ≫ x) σ) :
    BaseChangeSections.restrict y (BaseChangeSections.ofSectionsOver hg σ x s hs) =
      BaseChangeSections.ofSectionsOver hg σ (y ≫ x) (SectionsOver.restrict y s) hs' := by
  refine Subtype.ext (Prod.ext rfl ?_)
  change prod.map (yoneda.map y) (𝟙 (yoneda.obj Z)) ≫
      pullback.lift (prod.map (yoneda.map x) (𝟙 (yoneda.obj Z))) s.1
        (SectionsOver.comp_eq_of_pushforward_eq hg hs) =
    pullback.lift (prod.map (yoneda.map (y ≫ x)) (𝟙 (yoneda.obj Z)))
      (SectionsOver.restrict y s).1 (SectionsOver.comp_eq_of_pushforward_eq hg hs')
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← prod_map_yoneda_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, SectionsOver.restrict_coe]

/-! ### The fibre identification -/

/-- **The fibre identification, over a test object.** The sections over `x : T' ⟶ T` of the
base change of `g` along `σ` are exactly the sections of `W₁_{T'} ⟶ Z_{T'}` whose
postcomposition with `g` is the restriction of `σ` along `x`. -/
noncomputable def baseChangeSectionsEquiv {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T T' : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) (x : T' ⟶ T) :
    {u : yoneda.obj T' ⨯ yoneda.obj Z ⟶ pullback σ.1 g //
        u ≫ pullback.fst σ.1 g = prod.map (yoneda.map x) (𝟙 (yoneda.obj Z))} ≃
      {s : SectionsOver B U hU Z T' W₁ w₁ //
        SectionsOver.pushforward hg s = SectionsOver.restrict x σ} where
  toFun u := ⟨BaseChangeSections.toSectionsOver hg (⟨⟨x, u.1⟩, u.2⟩ : BaseChangeSections g σ T'),
    BaseChangeSections.pushforward_toSectionsOver hg (⟨⟨x, u.1⟩, u.2⟩ : BaseChangeSections g σ T')⟩
  invFun s := ⟨pullback.lift (prod.map (yoneda.map x) (𝟙 (yoneda.obj Z))) s.1.1
      (SectionsOver.comp_eq_of_pushforward_eq hg s.2), pullback.lift_fst _ _ _⟩
  left_inv u := Subtype.ext (by
    change pullback.lift (prod.map (yoneda.map x) (𝟙 (yoneda.obj Z)))
        (BaseChangeSections.toSectionsOver hg
          (⟨⟨x, u.1⟩, u.2⟩ : BaseChangeSections g σ T')).1 _ = u.1
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, u.2]
    · rw [pullback.lift_snd, BaseChangeSections.toSectionsOver_coe])
  right_inv s := Subtype.ext (Subtype.ext (by
    change pullback.lift (prod.map (yoneda.map x) (𝟙 (yoneda.obj Z))) s.1.1 _ ≫
        pullback.snd σ.1 g = s.1.1
    rw [pullback.lift_snd]))

/-- The morphism from the presheaf of sections of the base change to the space of sections
of `w₁`. -/
noncomputable def baseChangeSectionToSectionSpace {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) :
    baseChangeSectionPresheaf g σ ⟶ sectionSpace B U hU Z W₁ w₁ where
  app T' := ↾fun s => (sectionSpaceEquiv B U hU Z T'.unop W₁ w₁).symm
    (BaseChangeSections.toSectionsOver hg (baseChangeSectionPresheafEquiv g σ T'.unop s))
  naturality := by
    rintro ⟨T'⟩ ⟨T''⟩ f
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change (sectionSpaceEquiv B U hU Z T'' W₁ w₁).symm (BaseChangeSections.toSectionsOver hg
        (baseChangeSectionPresheafEquiv g σ T''
          ((baseChangeSectionPresheaf g σ).map f.unop.op s))) =
      (sectionSpace B U hU Z W₁ w₁).map f.unop.op
        ((sectionSpaceEquiv B U hU Z T' W₁ w₁).symm
          (BaseChangeSections.toSectionsOver hg (baseChangeSectionPresheafEquiv g σ T' s)))
    apply (sectionSpaceEquiv B U hU Z T'' W₁ w₁).injective
    rw [Equiv.apply_symm_apply, sectionSpaceEquiv_restrict w₁ f.unop, Equiv.apply_symm_apply,
      baseChangeSectionPresheafEquiv_map, BaseChangeSections.toSectionsOver_restrict]

/-- The components of that morphism: a section of the base change is sent to the section of
`w₁` underlying it. -/
theorem sectionSpaceEquiv_baseChangeSectionToSectionSpace {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) (T' : BigFppfOver B U hU)
    (s : (baseChangeSectionPresheaf g σ).obj (op T')) :
    sectionSpaceEquiv B U hU Z T' W₁ w₁ ((baseChangeSectionToSectionSpace hg σ).app (op T') s) =
      BaseChangeSections.toSectionsOver hg (baseChangeSectionPresheafEquiv g σ T' s) :=
  Equiv.apply_symm_apply _ _

/-- **The morphism into the presheaf of sections of the base change** determined by a morphism
to the space of sections of `w₁` and a morphism to `h_T` whose sections correspond under
postcomposition with `g` and restriction of `σ`. -/
noncomputable def baseChangeSectionLift {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂)
    {X : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (a : X ⟶ sectionSpace B U hU Z W₁ w₁)
    (b : X ⟶ yoneda.obj T)
    (hab : ∀ (T' : BigFppfOver B U hU) (ξ : X.obj (op T')),
      SectionsOver.pushforward hg (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) =
        SectionsOver.restrict (b.app (op T') ξ) σ) :
    X ⟶ baseChangeSectionPresheaf g σ where
  app T' := ↾fun ξ => (baseChangeSectionPresheafEquiv g σ T'.unop).symm
    (BaseChangeSections.ofSectionsOver hg σ (b.app T' ξ)
      (sectionSpaceEquiv B U hU Z T'.unop W₁ w₁ (a.app T' ξ)) (hab T'.unop ξ))
  naturality := by
    rintro ⟨T'⟩ ⟨T''⟩ f
    refine ConcreteCategory.hom_ext _ _ fun ξ => ?_
    have hb : b.app (op T'') (X.map f.unop.op ξ) = f.unop ≫ b.app (op T') ξ :=
      ConcreteCategory.congr_hom (b.naturality f.unop.op) ξ
    have ha : sectionSpaceEquiv B U hU Z T'' W₁ w₁ (a.app (op T'') (X.map f.unop.op ξ)) =
        SectionsOver.restrict f.unop
          (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) := by
      have hnat : a.app (op T'') (X.map f.unop.op ξ) =
          (sectionSpace B U hU Z W₁ w₁).map f.unop.op (a.app (op T') ξ) :=
        ConcreteCategory.congr_hom (a.naturality f.unop.op) ξ
      rw [hnat, sectionSpaceEquiv_restrict]
    change (baseChangeSectionPresheafEquiv g σ T'').symm
        (BaseChangeSections.ofSectionsOver hg σ (b.app (op T'') (X.map f.unop.op ξ))
          (sectionSpaceEquiv B U hU Z T'' W₁ w₁ (a.app (op T'') (X.map f.unop.op ξ)))
          (hab T'' (X.map f.unop.op ξ))) =
      (baseChangeSectionPresheaf g σ).map f.unop.op
        ((baseChangeSectionPresheafEquiv g σ T').symm
          (BaseChangeSections.ofSectionsOver hg σ (b.app (op T') ξ)
            (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) (hab T' ξ)))
    apply (baseChangeSectionPresheafEquiv g σ T'').injective
    rw [Equiv.apply_symm_apply, baseChangeSectionPresheafEquiv_map, Equiv.apply_symm_apply,
      BaseChangeSections.restrict_ofSectionsOver hg σ (b.app (op T') ξ)
        (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) (hab T' ξ) f.unop
        (by rw [← SectionsOver.restrict_pushforward, hab T' ξ, ← SectionsOver.restrict_comp])]
    exact BaseChangeSections.ofSectionsOver_congr hg σ _ _ hb ha

/-- The lift followed by the morphism to the space of sections of `w₁` is the given
morphism. -/
theorem baseChangeSectionLift_comp_toSectionSpace {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂)
    {X : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (a : X ⟶ sectionSpace B U hU Z W₁ w₁)
    (b : X ⟶ yoneda.obj T)
    (hab : ∀ (T' : BigFppfOver B U hU) (ξ : X.obj (op T')),
      SectionsOver.pushforward hg (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) =
        SectionsOver.restrict (b.app (op T') ξ) σ) :
    baseChangeSectionLift hg σ a b hab ≫ baseChangeSectionToSectionSpace hg σ = a := by
  refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun ξ => ?_)
  obtain ⟨T'⟩ := T₀
  apply (sectionSpaceEquiv B U hU Z T' W₁ w₁).injective
  change sectionSpaceEquiv B U hU Z T' W₁ w₁
      ((baseChangeSectionToSectionSpace hg σ).app (op T')
        ((baseChangeSectionLift hg σ a b hab).app (op T') ξ)) = _
  rw [sectionSpaceEquiv_baseChangeSectionToSectionSpace]
  change BaseChangeSections.toSectionsOver hg
      (baseChangeSectionPresheafEquiv g σ T' ((baseChangeSectionPresheafEquiv g σ T').symm
        (BaseChangeSections.ofSectionsOver hg σ (b.app (op T') ξ)
          (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) (hab T' ξ)))) = _
  rw [Equiv.apply_symm_apply, BaseChangeSections.toSectionsOver_ofSectionsOver]

/-- The lift followed by the structure morphism to `h_T` is the given morphism. -/
theorem baseChangeSectionLift_comp_base {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂)
    {X : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (a : X ⟶ sectionSpace B U hU Z W₁ w₁)
    (b : X ⟶ yoneda.obj T)
    (hab : ∀ (T' : BigFppfOver B U hU) (ξ : X.obj (op T')),
      SectionsOver.pushforward hg (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) =
        SectionsOver.restrict (b.app (op T') ξ) σ) :
    baseChangeSectionLift hg σ a b hab ≫ baseChangeSectionBase g σ = b := by
  refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun ξ => ?_)
  obtain ⟨T'⟩ := T₀
  change (baseChangeSectionPresheafEquiv g σ T' ((baseChangeSectionPresheafEquiv g σ T').symm
      (BaseChangeSections.ofSectionsOver hg σ (b.app (op T') ξ)
        (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) (hab T' ξ)))).1.1 = _
  rw [Equiv.apply_symm_apply, BaseChangeSections.ofSectionsOver_base]

/-- **The fibre identification.** Let `g : W₁ ⟶ W₂` be a morphism over `h_Z` and let `σ` be a
section of `W₂_T ⟶ Z_T`. Then the presheaf of sections of the base change of `g` along `σ`,
together with its structure morphism to `h_T` and the section of `w₁` underlying a section of
the base change, is the fibre product of the space of sections of `w₁` and of `h_T` over the
space of sections of `w₂`: the space of sections of the base change of `g` along `σ`, over the
base `T`, is the fibre of `AlgebraicGeometry.Space.sectionSpaceMap` at `σ`. -/
theorem isPullback_baseChangeSectionPresheaf {g : W₁ ⟶ W₂} (hg : g ≫ w₂ = w₁)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) :
    IsPullback (baseChangeSectionToSectionSpace hg σ) (baseChangeSectionBase g σ)
      (sectionSpaceMap hg)
      (yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T W₂ w₂).symm σ)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun s => ?_)
    obtain ⟨T'⟩ := T₀
    apply (sectionSpaceEquiv B U hU Z T' W₂ w₂).injective
    change sectionSpaceEquiv B U hU Z T' W₂ w₂ ((sectionSpaceMap hg).app (op T')
        ((baseChangeSectionToSectionSpace hg σ).app (op T') s)) =
      sectionSpaceEquiv B U hU Z T' W₂ w₂
        ((yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T W₂ w₂).symm σ)).app (op T')
          ((baseChangeSectionBase g σ).app (op T') s))
    rw [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_baseChangeSectionToSectionSpace,
      BaseChangeSections.pushforward_toSectionsOver, sectionSpaceEquiv_yonedaEquiv_symm,
      baseChangeSectionBase_app]
  · intro X φ φ' h₁ h₂
    refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun ξ => ?_)
    obtain ⟨T'⟩ := T₀
    apply (baseChangeSectionPresheafEquiv g σ T').injective
    have hbase : (baseChangeSectionPresheafEquiv g σ T' (φ.app (op T') ξ)).1.1 =
        (baseChangeSectionPresheafEquiv g σ T' (φ'.app (op T') ξ)).1.1 := by
      simpa only [baseChangeSectionBase_app] using app_apply_eq_of_comp_eq h₂ (op T') ξ
    have hsec : BaseChangeSections.toSectionsOver hg
          (baseChangeSectionPresheafEquiv g σ T' (φ.app (op T') ξ)) =
        BaseChangeSections.toSectionsOver hg
          (baseChangeSectionPresheafEquiv g σ T' (φ'.app (op T') ξ)) := by
      have h' := congrArg (sectionSpaceEquiv B U hU Z T' W₁ w₁)
        (app_apply_eq_of_comp_eq h₁ (op T') ξ)
      rwa [sectionSpaceEquiv_baseChangeSectionToSectionSpace,
        sectionSpaceEquiv_baseChangeSectionToSectionSpace] at h'
    refine Subtype.ext (Prod.ext hbase ?_)
    refine pullback.hom_ext ?_ ?_
    · rw [(baseChangeSectionPresheafEquiv g σ T' (φ.app (op T') ξ)).2,
        (baseChangeSectionPresheafEquiv g σ T' (φ'.app (op T') ξ)).2, hbase]
    · exact Subtype.ext_iff.mp hsec
  · intro X a b hab
    have key : ∀ (T' : BigFppfOver B U hU) (ξ : X.obj (op T')),
        SectionsOver.pushforward hg (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') ξ)) =
          SectionsOver.restrict (b.app (op T') ξ) σ := by
      intro T' ξ
      have h' := congrArg (sectionSpaceEquiv B U hU Z T' W₂ w₂)
        (app_apply_eq_of_comp_eq hab (op T') ξ)
      rwa [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_yonedaEquiv_symm] at h'
    exact ⟨baseChangeSectionLift hg σ a b key,
      baseChangeSectionLift_comp_toSectionSpace hg σ a b key,
      baseChangeSectionLift_comp_base hg σ a b key⟩

/-! ### The base change of the chart along a section -/

/-- **The base change of an étale `g` along a section `σ` of `w₂` over `T` is étale.** It is
the base change of `g` along the morphism `Z_T = T × Z ⟶ W₂` that `σ` is, and `T × Z` is an
algebraic space. -/
theorem isEtale_pullback_fst_sectionsOver (hW₁ : IsAlgebraicSpace B U hU W₁)
    (hW₂ : IsAlgebraicSpace B U hU W₂) {g : W₁ ⟶ W₂} (hg : IsEtale B U hU g)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) :
    IsEtale B U hU (pullback.fst σ.1 g) :=
  isEtale_pullback_fst B U hU (isAlgebraicSpace_yoneda_prod_yoneda T Z) hW₂ hW₁ σ.1 g hg

/-- **The base change of a surjective `g` along a section `σ` of `w₂` over `T` is
surjective.** -/
theorem isSurjective_pullback_fst_sectionsOver (hW₁ : IsAlgebraicSpace B U hU W₁)
    (hW₂ : IsAlgebraicSpace B U hU W₂) {g : W₁ ⟶ W₂} (hg : IsSurjective B U hU g)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W₂ w₂) :
    IsSurjective B U hU (pullback.fst σ.1 g) :=
  isSurjective_pullback_fst B U hU (isAlgebraicSpace_yoneda_prod_yoneda T Z) hW₂ hW₁ σ.1 g hg

end AlgebraicGeometry.Space

end
