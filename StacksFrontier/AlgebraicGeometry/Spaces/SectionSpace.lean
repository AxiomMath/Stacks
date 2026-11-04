module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.Logic.Small.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The space of sections of a morphism over a finite locally free scheme (Stacks 05XR)

Let `Z → U` be a morphism in the big fppf site of `U` and let `w : W ⟶ yoneda.obj Z` be a
morphism of presheaves on that site. Stacks 05XR studies the functor
`T / U ↦ {sections of W_T → Z_T}`, which it shows to be an algebraic space étale over `U`
when `Z → U` is finite locally free and `w` is an étale morphism of algebraic spaces.

This file constructs that functor, which is the first of the three assertions of the
source. Following the source's formulation, a section of `W_T → Z_T` is recorded as a
morphism `Z_T = T ×_U Z → W` over `Z`, that is, as an element of
`AlgebraicGeometry.Space.SectionsOver`.

The construction has one piece of mathematical content beyond bookkeeping: the functor must
be *small-valued*, while `SectionsOver` is a set of morphisms of presheaves and therefore a
priori one universe too large. Smallness holds because `yoneda.obj T ⨯ yoneda.obj Z` is
again representable: the big fppf category over `U` has fibre products
(`AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan` and the slice
construction), the Yoneda embedding preserves them, and so the Yoneda lemma identifies
`yoneda.obj T ⨯ yoneda.obj Z ⟶ W` with the value `W.obj (op (T ⨯ Z))`, which is small. That
is `CategoryTheory.small_hom_prod_yoneda`. With smallness in hand the functor is the
presheaf of sections transported into the ambient universe, and its values are identified
with `SectionsOver` on the nose.

## Main definitions

* `CategoryTheory.small_hom_prod_yoneda`: a morphism of presheaves out of a product of two
  representables is determined by a single element of the target, hence such morphisms form
  a small type.
* `AlgebraicGeometry.Space.SectionsOver`: a section of `W_T → Z_T`, as a morphism
  `T ×_U Z → W` over `Z`.
* `AlgebraicGeometry.Space.SectionsOver.restrict`: restriction of a section along a
  morphism of test objects, by base change.
* `AlgebraicGeometry.Space.sectionPresheaf`: the functor of sections.
* `AlgebraicGeometry.Space.sectionSpace`: the functor of sections, as produced by
  `AlgebraicGeometry.Space.exists_sectionSpace`.

## Main results

* `AlgebraicGeometry.Space.exists_sectionSpace`: the existence of the small-valued functor of
  sections of Stacks 05XR together with its natural description. That this functor is an
  algebraic space étale over `U` is
  `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_and_isEtale`.
* `AlgebraicGeometry.Space.sectionSpaceEquiv_map`: restriction in `sectionSpace` is base
  change of the corresponding morphism `Z_T → W`.

## References

* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u₁ u

namespace CategoryTheory

/-- A morphism of presheaves `yoneda.obj X ⨯ yoneda.obj Y ⟶ W` is the same thing as an
element of `W.obj (op (X ⨯ Y))`: the Yoneda embedding preserves the binary product, so the
source is representable and the Yoneda lemma applies. In particular such morphisms form a
small type, even though a general hom-set of presheaves does not. -/
theorem small_hom_prod_yoneda {C : Type u₁} [Category.{v, u₁} C] (X Y : C)
    [HasBinaryProduct X Y] (W : Cᵒᵖ ⥤ Type v) :
    Small.{v} (yoneda.obj X ⨯ yoneda.obj Y ⟶ W) :=
  Small.mk' ((Iso.homCongr (PreservesLimitPair.iso yoneda X Y) (Iso.refl W)).symm.trans
    yonedaEquiv)

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U)

/-- A section of `W_T → Z_T`, expressed as a morphism `Z_T → W` over `Z`. This form is
equivalent to a section of `W_T → Z_T` itself. -/
abbrev SectionsOver (Z T : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z) :=
  {σ : yoneda.obj T ⨯ yoneda.obj Z ⟶ W // σ ≫ w = prod.snd}

variable {B U hU}

/-- Restriction of a section of `W_T → Z_T` along a morphism `T' → T` of test objects: base
change of the corresponding morphism `Z_T → W` along `Z_{T'} → Z_T`. -/
noncomputable def SectionsOver.restrict {Z T T' : BigFppfOver B U hU}
    {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z} (f : T' ⟶ T)
    (σ : SectionsOver B U hU Z T W w) : SectionsOver B U hU Z T' W w :=
  ⟨prod.map (yoneda.map f) (𝟙 (yoneda.obj Z)) ≫ σ.1, by
    rw [Category.assoc, σ.2, prod.map_snd, Category.comp_id]⟩

/-- Restriction of a section is base change of the corresponding morphism `Z_T → W`. -/
@[simp]
theorem SectionsOver.restrict_coe {Z T T' : BigFppfOver B U hU}
    {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z} (f : T' ⟶ T)
    (σ : SectionsOver B U hU Z T W w) :
    (SectionsOver.restrict f σ).1 = prod.map (yoneda.map f) (𝟙 (yoneda.obj Z)) ≫ σ.1 :=
  rfl

/-- Restriction along the identity does nothing. -/
@[simp]
theorem SectionsOver.restrict_id {Z T : BigFppfOver B U hU}
    {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) : SectionsOver.restrict (𝟙 T) σ = σ := by
  ext
  simp

/-- Restriction along a composite is the composite of the restrictions. -/
theorem SectionsOver.restrict_comp {Z T T' T'' : BigFppfOver B U hU}
    {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z} (f : T' ⟶ T) (g : T'' ⟶ T')
    (σ : SectionsOver B U hU Z T W w) :
    SectionsOver.restrict (g ≫ f) σ
      = SectionsOver.restrict g (SectionsOver.restrict f σ) := by
  ext
  simp

variable (B U hU)

/-- The sections of `W_T → Z_T` form a small type: they are a subtype of the morphisms
`yoneda.obj T ⨯ yoneda.obj Z ⟶ W`, and the big fppf category over `U` has fibre products,
so `CategoryTheory.small_hom_prod_yoneda` applies. -/
instance small_sectionsOver (Z T : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z) :
    Small.{u} (SectionsOver B U hU Z T W w) := by
  have : HasBinaryProducts (BigFppfOver B U hU) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  have := CategoryTheory.small_hom_prod_yoneda T Z W
  infer_instance

/-- The functor assigning to `T / U` the sections of `W_T → Z_T`, with restriction given by
base change. -/
noncomputable def sectionPresheaf (Z : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z) :
    (BigFppfOver B U hU)ᵒᵖ ⥤ Type u where
  obj X := Shrink (SectionsOver B U hU Z X.unop W w)
  map {X Y} f := ↾fun s => equivShrink (SectionsOver B U hU Z Y.unop W w)
    (SectionsOver.restrict f.unop ((equivShrink (SectionsOver B U hU Z X.unop W w)).symm s))
  map_id X := by ext s; simp
  map_comp {X Y V} f g := by ext s; simp [SectionsOver.restrict_comp]

/-- The values of `AlgebraicGeometry.Space.sectionPresheaf` are the sections of
`W_T → Z_T`. -/
noncomputable def sectionPresheafEquiv (Z : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z)
    (X : (BigFppfOver B U hU)ᵒᵖ) :
    (sectionPresheaf B U hU Z W w).obj X ≃ SectionsOver B U hU Z X.unop W w :=
  (equivShrink (SectionsOver B U hU Z X.unop W w)).symm

/-- Under `AlgebraicGeometry.Space.sectionPresheafEquiv`, the restriction maps of
`AlgebraicGeometry.Space.sectionPresheaf` are restriction of sections. -/
theorem sectionPresheafEquiv_map (Z : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z)
    {X Y : (BigFppfOver B U hU)ᵒᵖ} (f : X ⟶ Y)
    (s : (sectionPresheaf B U hU Z W w).obj X) :
    sectionPresheafEquiv B U hU Z W w Y ((sectionPresheaf B U hU Z W w).map f s) =
      SectionsOver.restrict f.unop (sectionPresheafEquiv B U hU Z W w X s) :=
  Equiv.symm_apply_apply _ _

/-- The natural, small-valued functor of sections of `W → Z` of Stacks 05XR exists: there
is a presheaf on the big fppf site of `U` whose value at `T` is the set of sections of
`W_T → Z_T`, naturally in `T`, the restriction maps being base change. Stacks 05XR itself is
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_and_isEtale`. -/
@[stacks 05XR "the functor"]
theorem exists_sectionSpace (Z : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z) :
    ∃ F : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u,
      ∃ e : ∀ T : BigFppfOver B U hU, F.obj (Opposite.op T) ≃
          SectionsOver B U hU Z T W w,
        ∀ (T T' : BigFppfOver B U hU) (f : T' ⟶ T)
          (s : F.obj (Opposite.op T)),
          ((e T') (F.map f.op s)).1 =
            prod.map (yoneda.map f) (𝟙 (yoneda.obj Z)) ≫ ((e T) s).1 :=
  ⟨sectionPresheaf B U hU Z W w, fun T => sectionPresheafEquiv B U hU Z W w (op T),
    fun T T' f s => by rw [sectionPresheafEquiv_map]; simp⟩

/-- The functor assigning to `T / U` the sections of `W_T → Z_T`. -/
noncomputable def sectionSpace (Z : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z) :
    (BigFppfOver B U hU)ᵒᵖ ⥤ Type u :=
  Classical.choose (exists_sectionSpace B U hU Z W w)

/-- The canonical identification of the values of `AlgebraicGeometry.Space.sectionSpace`
with sections. -/
noncomputable def sectionSpaceEquiv (Z T : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z) :
    (sectionSpace B U hU Z W w).obj (Opposite.op T) ≃ SectionsOver B U hU Z T W w :=
  (Classical.choose (Classical.choose_spec (exists_sectionSpace B U hU Z W w))) T

/-- Restriction of a section along a morphism of test schemes is base change of the
corresponding morphism `Z_T → W`. -/
theorem sectionSpaceEquiv_map (Z T T' : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z) (f : T' ⟶ T)
    (s : (sectionSpace B U hU Z W w).obj (Opposite.op T)) :
    ((sectionSpaceEquiv B U hU Z T' W w)
      ((sectionSpace B U hU Z W w).map f.op s)).1 =
        prod.map (yoneda.map f) (𝟙 (yoneda.obj Z)) ≫
          ((sectionSpaceEquiv B U hU Z T W w) s).1 :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_sectionSpace B U hU Z W w))) T T' f s

end AlgebraicGeometry.Space

end
