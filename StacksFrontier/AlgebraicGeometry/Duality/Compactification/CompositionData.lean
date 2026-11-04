module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekIndependence
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.OverIntermediate
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The compactifications that compute `(g ∘ f)^!`, `f^!` and `g^!` together

In the situation of [Stacks, Tag 0F42] let `f : X ⟶ Y` and `g : Y ⟶ Z` be composable morphisms of
`AlgebraicGeometry.FTS S`. The proof of [Stacks, Tag 0ATX] chooses a compactification
`i : Y ⟶ Ȳ` of `Y` over `Z` and then a compactification `X ⟶ X̄` of `X` over `Ȳ`. These two
choices determine

* a compactification `X ⟶ X̄ ⟶ Z` of `X` over `Z`, which computes `(g ∘ f)^!`;
* the inverse image `U = X̄ ×_Ȳ Y` of `Y` in `X̄`, and the compactification `X ⟶ U ⟶ Y` of `X`
  over `Y`, which computes `f^!`;

and the base change square

```
U --fst--> X̄
|q          |p
Y ---i---> Ȳ
```

which is cartesian by construction. This file records the choice, `Stacks.Duality.CompositionData`,
the two derived compactifications, morphisms of choices, and the existence of a choice dominating
two given ones — the reduction step of the second half of the source's proof.

## Main definitions

All in the namespace `Stacks.Duality`.

* `AlgebraicGeometry.CompactificationOf.ofFactorization` — the compactification given by an open
  immersion followed by a proper morphism.
* `CompositionData f g` — a compactification of `Y` over `Z` and one of `X` over it.
* `CompositionData.outer`, `CompositionData.inner` — the compactifications of `f ≫ g` and of `f`
  that a choice determines.
* `CompositionData.Hom` — a morphism of choices: a morphism of the compactifications of `Y` and a
  compatible morphism of the ambient schemes of the compactifications of `X`.
* `CompositionData.Hom.outerHom`, `CompositionData.Hom.innerHom` — the morphisms of
  compactifications a morphism of choices induces.

## Main results

* `CompositionData.isPullback_innerFst` — the square `U ⟶ X̄`, `Y ⟶ Ȳ` is cartesian.
* `CompositionData.exists_dense_hom` — two choices are dominated by a third, through morphisms of
  choices out of a choice whose compactifications all have dense interior; this is the step of the
  source's proof that uses [Stacks, Tag 0ATU] and [Stacks, Tag 0ATV].

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 0ATV](https://stacks.math.columbia.edu/tag/0ATV)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

/-- **The compactification given by a factorization through a proper morphism**: an open
immersion `ι : X ⟶ P` followed by a proper morphism `π : P ⟶ B` whose composite is `h`. -/
@[sga "4 XVII 3.2.5"]
def ofFactorization {X B : Scheme.{u}} {h : X ⟶ B} (P : Scheme.{u}) (ι : X ⟶ P) (π : P ⟶ B)
    [IsOpenImmersion ι] [IsProper π] (w : ι ≫ π = h) : CompactificationOf (Over.mk h) :=
  ⟨StructuredArrow.mk (Y := Over.mk π) (Over.homMk ι w), ⟨inferInstanceAs (IsOpenImmersion ι),
    inferInstanceAs (IsProper π)⟩⟩

/-- A compactification factors its structure morphism. -/
theorem immersion_comp_toBase' {S : Scheme.{u}} {X : Over S} (j : CompactificationOf X) :
    j.immersion ≫ j.toBase = X.hom := by
  simp [CompactificationOf.immersion, CompactificationOf.toBase]

end AlgebraicGeometry.CompactificationOf

namespace Stacks.Duality

/-- A commuting triangle of schemes, read on points. -/
theorem apply_eq {A B C : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ C} {c : A ⟶ C} (e : a ≫ b = c)
    (x : A) : b (a x) = c x := by
  rw [← Scheme.Hom.comp_apply, e]

variable {S : Scheme.{u}} [IsNoetherian S] {X Y Z : FTS S} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The choices made in the proof of [Stacks, Tag 0ATX]**: a compactification `i : Y ⟶ Ȳ` of
`Y` over `Z`, and a compactification `X ⟶ X̄` of `X` over `Ȳ`, where `X` lies over `Ȳ` through
`f` followed by `i`. -/
structure CompositionData where
  /-- The compactification `Y ⟶ Ȳ ⟶ Z` of `g`. -/
  base : CompactificationOf (Over.mk g.left)
  /-- The compactification `X ⟶ X̄ ⟶ Ȳ` of `f ≫ i`. -/
  top : CompactificationOf (Over.mk (f.left ≫ base.immersion))

namespace CompositionData

variable {f g} (D : CompositionData f g)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The compactification of `X` over `Ȳ` factors `f ≫ i`. -/
theorem top_immersion_comp_toBase :
    D.top.immersion ≫ D.top.toBase = f.left ≫ D.base.immersion :=
  D.top.immersion_comp_toBase'

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The compactification of `Y` factors `g`. -/
theorem base_immersion_comp_toBase : D.base.immersion ≫ D.base.toBase = g.left :=
  D.base.immersion_comp_toBase'

/-- **The compactification `X ⟶ X̄ ⟶ Ȳ ⟶ Z` of `f ≫ g`** determined by a choice. -/
def outer : CompactificationOf (Over.mk (f ≫ g).left) :=
  CompactificationOf.ofFactorization D.top.space D.top.immersion
    (D.top.toBase ≫ D.base.toBase) (by
      rw [← Category.assoc, top_immersion_comp_toBase, Category.assoc,
        base_immersion_comp_toBase]
      rfl)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The ambient scheme of `D.outer` is `X̄`. -/
@[simp] theorem outer_space : D.outer.space = D.top.space := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The open immersion of `D.outer` is `X ⟶ X̄`. -/
@[simp] theorem outer_immersion : D.outer.immersion = D.top.immersion := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The proper morphism of `D.outer` is `X̄ ⟶ Ȳ ⟶ Z`. -/
@[simp] theorem outer_toBase : D.outer.toBase = D.top.toBase ≫ D.base.toBase := rfl

/-- The open immersion `i : Y ⟶ Ȳ`, with source `Y` itself. -/
def baseImm : Y.left ⟶ D.base.space := D.base.immersion

/-- The open immersion `X ⟶ X̄`, with source `X` itself. -/
def topImm : X.left ⟶ D.top.space := D.top.immersion

/-- `i : Y ⟶ Ȳ` is an open immersion. -/
instance : IsOpenImmersion D.baseImm := inferInstanceAs (IsOpenImmersion D.base.immersion)

/-- `X ⟶ X̄` is an open immersion. -/
instance : IsOpenImmersion D.topImm := inferInstanceAs (IsOpenImmersion D.top.immersion)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `X ⟶ X̄ ⟶ Ȳ` is `f` followed by `i`. -/
theorem topImm_comp_toBase : D.topImm ≫ D.top.toBase = f.left ≫ D.baseImm :=
  D.top_immersion_comp_toBase

/-- The inverse image `U = X̄ ×_Ȳ Y` of `Y` in `X̄`. -/
abbrev innerSpace : Scheme.{u} := pullback D.top.toBase D.baseImm

/-- The open immersion `U ⟶ X̄`. -/
abbrev innerFst : D.innerSpace ⟶ D.top.space := pullback.fst _ _

/-- The proper morphism `q : U ⟶ Y`. -/
abbrev innerSnd : D.innerSpace ⟶ Y.left := pullback.snd _ _

/-- The open immersion `X ⟶ U`. -/
def innerImmersion : X.left ⟶ D.innerSpace :=
  pullback.lift D.topImm f.left D.topImm_comp_toBase

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `X ⟶ U ⟶ X̄` is the open immersion of `X` into `X̄`. -/
@[reassoc (attr := simp)]
theorem innerImmersion_fst : D.innerImmersion ≫ D.innerFst = D.topImm :=
  pullback.lift_fst _ _ _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `X ⟶ U ⟶ Y` is `f`. -/
@[reassoc (attr := simp)]
theorem innerImmersion_snd : D.innerImmersion ≫ D.innerSnd = f.left :=
  pullback.lift_snd _ _ _

/-- `X ⟶ U` is an open immersion, since its composite with the open immersion `U ⟶ X̄` is. -/
instance : IsOpenImmersion D.innerImmersion := by
  have : IsOpenImmersion (D.innerImmersion ≫ D.innerFst) := by
    rw [innerImmersion_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ D.innerFst

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **The square `U ⟶ X̄` over `Y ⟶ Ȳ` is cartesian**, by construction. -/
theorem isPullback_innerFst :
    IsPullback D.innerFst D.innerSnd D.top.toBase D.baseImm :=
  IsPullback.of_hasPullback _ _

/-- **The compactification `X ⟶ U ⟶ Y` of `f`** determined by a choice. -/
def inner : CompactificationOf (Over.mk f.left) :=
  CompactificationOf.ofFactorization D.innerSpace D.innerImmersion D.innerSnd
    D.innerImmersion_snd

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The ambient scheme of `D.inner` is `U`. -/
@[simp] theorem inner_space : D.inner.space = D.innerSpace := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The open immersion of `D.inner` is `X ⟶ U`. -/
@[simp] theorem inner_immersion : D.inner.immersion = D.innerImmersion := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The proper morphism of `D.inner` is `q : U ⟶ Y`. -/
@[simp] theorem inner_toBase : D.inner.toBase = D.innerSnd := rfl

/-! ### Morphisms of choices -/

/-- **A morphism of choices**: a morphism of the compactifications of `Y` over `Z` and a morphism
of the ambient schemes of the compactifications of `X` which is compatible with the open
immersions of `X` and lies over the morphism of the compactifications of `Y`. -/
structure Hom (D₁ D₂ : CompositionData f g) where
  /-- The morphism `Ȳ₁ ⟶ Ȳ₂` of compactifications of `Y`. -/
  base : D₁.base ⟶ D₂.base
  /-- The morphism `X̄₁ ⟶ X̄₂`. -/
  top : D₁.top.space ⟶ D₂.top.space
  immersion_comp_top : D₁.top.immersion ≫ top = D₂.top.immersion
  top_comp_toBase : top ≫ D₂.top.toBase = D₁.top.toBase ≫ CompactificationOf.Hom.map base

namespace Hom

attribute [reassoc] immersion_comp_top top_comp_toBase

variable {D₁ D₂ : CompositionData f g} (φ : Hom D₁ D₂)

/-- The morphism `X̄₁ ⟶ X̄₂` as a morphism of the compactifications of `f ≫ g`. -/
def outerHom : D₁.outer ⟶ D₂.outer :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk φ.top (by
      change φ.top ≫ D₂.top.toBase ≫ D₂.base.toBase = D₁.top.toBase ≫ D₁.base.toBase
      rw [φ.top_comp_toBase_assoc, CompactificationOf.homMap_comp_toBase]))
    (Over.OverMorphism.ext φ.immersion_comp_top))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The underlying morphism of `φ.outerHom` is `X̄₁ ⟶ X̄₂`. -/
@[simp] theorem outerHom_map : CompactificationOf.Hom.map φ.outerHom = φ.top := rfl

/-- The morphism `U₁ ⟶ U₂` induced on the inverse images of `Y`. -/
def innerMap : D₁.innerSpace ⟶ D₂.innerSpace :=
  pullback.map _ _ _ _ φ.top (𝟙 Y.left) (CompactificationOf.Hom.map φ.base)
    φ.top_comp_toBase.symm
    (by simp [baseImm, CompactificationOf.immersion_comp_homMap])

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `U₁ ⟶ U₂` lies over `X̄₁ ⟶ X̄₂`. -/
@[reassoc (attr := simp)]
theorem innerMap_fst : φ.innerMap ≫ D₂.innerFst = D₁.innerFst ≫ φ.top :=
  pullback.lift_fst _ _ _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `U₁ ⟶ U₂` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem innerMap_snd : φ.innerMap ≫ D₂.innerSnd = D₁.innerSnd :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `U₁ ⟶ U₂` is compatible with the open immersions of `X`. -/
@[reassoc (attr := simp)]
theorem innerImmersion_innerMap : D₁.innerImmersion ≫ φ.innerMap = D₂.innerImmersion := by
  apply pullback.hom_ext
  · simp [topImm, immersion_comp_top]
  · simp

/-- The morphism `U₁ ⟶ U₂` as a morphism of the compactifications of `f`. -/
def innerHom : D₁.inner ⟶ D₂.inner :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk φ.innerMap φ.innerMap_snd) (Over.OverMorphism.ext φ.innerImmersion_innerMap))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The underlying morphism of `φ.innerHom` is `U₁ ⟶ U₂`. -/
@[simp] theorem innerHom_map : CompactificationOf.Hom.map φ.innerHom = φ.innerMap := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **The square of the morphisms `U₁ ⟶ U₂` and `X̄₁ ⟶ X̄₂` is cartesian** when the morphism of
compactifications of `Y` preserves the interior: `U₁` is the inverse image of `Y` in `X̄₁`, and
the inverse image of `Y` under `Ȳ₁ ⟶ Ȳ₂` is `Y`. -/
theorem isPullback_innerMap (hb : CompactificationOf.PreservesInterior φ.base) :
    IsPullback φ.innerMap D₁.innerFst D₂.innerFst φ.top := by
  refine IsOpenImmersion.isPullback φ.innerMap D₁.innerFst D₂.innerFst φ.top
    φ.innerMap_fst.symm ?_
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_preimage]
  rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, ← Set.preimage_comp]
  have h : (D₂.top.toBase ∘ φ.top : D₁.top.space → _) =
      CompactificationOf.Hom.map φ.base ∘ D₁.top.toBase := by
    funext x
    exact (apply_eq φ.top_comp_toBase x).trans (apply_eq rfl x).symm
  rw [h, Set.preimage_comp]
  congr 1

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **A morphism of choices whose morphism of ambient schemes of `X` preserves the interior
induces an interior-preserving morphism on the inverse images of `Y`.** -/
theorem preservesInterior_innerHom
    (ho : CompactificationOf.PreservesInterior φ.outerHom) :
    CompactificationOf.PreservesInterior φ.innerHom := by
  unfold CompactificationOf.PreservesInterior at ho ⊢
  simp only [outerHom_map, outer_immersion] at ho
  show (φ.innerMap : D₁.innerSpace → D₂.innerSpace) ⁻¹' Set.range D₂.innerImmersion =
    Set.range D₁.innerImmersion
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz⟩
    have h1 : D₁.innerFst x ∈ (φ.top ⁻¹' Set.range D₂.topImm) := by
      refine ⟨z, ?_⟩
      rw [← apply_eq D₂.innerImmersion_fst z, hz, apply_eq φ.innerMap_fst x]
      exact (apply_eq rfl x)
    obtain ⟨y, hy⟩ : D₁.innerFst x ∈ Set.range D₁.topImm := ho ▸ h1
    refine ⟨y, D₁.innerFst.isOpenEmbedding.injective ?_⟩
    rw [apply_eq D₁.innerImmersion_fst y, hy]
  · rintro x ⟨y, rfl⟩
    exact ⟨y, (apply_eq φ.innerImmersion_innerMap y).symm⟩

/-- **A morphism of choices preserves the interiors** when the morphism of compactifications of `Y`
does and the morphism of ambient schemes of `X`, as a morphism of compactifications of `f ≫ g`,
does. The morphism on the inverse images of `Y` then preserves the interior too,
`Stacks.Duality.CompositionData.Hom.preservesInterior_innerHom`. -/
def PreservesInterior : Prop :=
  CompactificationOf.PreservesInterior φ.base ∧ CompactificationOf.PreservesInterior φ.outerHom

end Hom

/-! ### A choice dominating two given ones -/

section Dominate

variable (D₁ D₂ : CompositionData f g)

/-- The common refinement with dense interior of the two compactifications of `Y`. -/
abbrev domBase : CompactificationOf (Over.mk g.left) :=
  CategoryOfCompactifications.commonRefinement (compactificationSituation g D₁.base) D₁.base
    D₂.base

/-- Its projection to the first compactification of `Y`. -/
abbrev domBaseFst : domBase D₁ D₂ ⟶ D₁.base :=
  CategoryOfCompactifications.commonRefinementFst (compactificationSituation g D₁.base) D₁.base
    D₂.base

/-- Its projection to the second compactification of `Y`. -/
abbrev domBaseSnd : domBase D₁ D₂ ⟶ D₂.base :=
  CategoryOfCompactifications.commonRefinementSnd (compactificationSituation g D₁.base) D₁.base
    D₂.base

/-- The base change of the first compactification of `X` to the common refinement. -/
abbrev domP₁ : Scheme.{u} :=
  pullback D₁.top.toBase (CompactificationOf.Hom.map (domBaseFst D₁ D₂))

/-- The base change of the second compactification of `X` to the common refinement. -/
abbrev domP₂ : Scheme.{u} :=
  pullback D₂.top.toBase (CompactificationOf.Hom.map (domBaseSnd D₁ D₂))

/-- The fibre product of the two base changes over the common refinement; it is proper over it. -/
abbrev domP : Scheme.{u} :=
  pullback (pullback.snd D₁.top.toBase (CompactificationOf.Hom.map (domBaseFst D₁ D₂)))
    (pullback.snd D₂.top.toBase (CompactificationOf.Hom.map (domBaseSnd D₁ D₂)))

/-- The structure morphism of `domP` to the common refinement. -/
abbrev domProj : domP D₁ D₂ ⟶ (domBase D₁ D₂).space :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The morphism from `X` into `domP`. -/
def domMap : X.left ⟶ domP D₁ D₂ :=
  pullback.lift
    (pullback.lift D₁.top.immersion (f.left ≫ (domBase D₁ D₂).immersion) (by
      rw [top_immersion_comp_toBase, Category.assoc, CompactificationOf.immersion_comp_homMap]))
    (pullback.lift D₂.top.immersion (f.left ≫ (domBase D₁ D₂).immersion) (by
      rw [top_immersion_comp_toBase, Category.assoc, CompactificationOf.immersion_comp_homMap]))
    ((pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)

/-- The first component of `X ⟶ domP` is the first compactification of `X`. -/
@[reassoc (attr := simp)]
theorem domMap_fst_fst : domMap D₁ D₂ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = D₁.top.immersion := by
  rw [domMap, pullback.lift_fst_assoc, pullback.lift_fst]

/-- The second component of `X ⟶ domP` is the second compactification of `X`. -/
@[reassoc (attr := simp)]
theorem domMap_snd_fst : domMap D₁ D₂ ≫ pullback.snd _ _ ≫ pullback.fst _ _ = D₂.top.immersion := by
  rw [domMap, pullback.lift_snd_assoc, pullback.lift_fst]

/-- `X ⟶ domP ⟶ Ȳ` is `f` followed by the open immersion of `Y`. -/
@[reassoc (attr := simp)]
theorem domMap_proj : domMap D₁ D₂ ≫ domProj D₁ D₂ = f.left ≫ (domBase D₁ D₂).immersion := by
  rw [domProj, domMap, pullback.lift_fst_assoc, pullback.lift_snd]

/-- `X ⟶ domP` is an immersion, its first component being one. -/
instance : IsImmersion (domMap D₁ D₂) := by
  have : IsImmersion (domMap D₁ D₂ ≫ pullback.fst _ _ ≫ pullback.fst _ _) := by
    rw [domMap_fst_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst _ _ ≫ pullback.fst _ _)

/-- `domP` is quasi-separated, being proper over a Noetherian scheme. -/
instance : QuasiSeparatedSpace (domP D₁ D₂) :=
  quasiSeparatedSpace_of_quasiSeparated (domProj D₁ D₂ ≫ (domBase D₁ D₂).toBase)

/-- `X ⟶ domP` is quasi-compact, `X` being Noetherian. -/
instance : QuasiCompact (domMap D₁ D₂) := quasiCompact_of_compactSpace _

/-- `X` is open in its scheme-theoretic closure in `domP`. -/
instance : IsOpenImmersion (domMap D₁ D₂).toImage :=
  isOpenImmersion_toImage _ (Or.inl inferInstance)

/-- **The dominating compactification of `X` over the common refinement**: the scheme-theoretic
closure of `X` in `domP`. -/
def domTop : CompactificationOf (Over.mk (f.left ≫ (domBase D₁ D₂).immersion)) :=
  CompactificationOf.ofFactorization (domMap D₁ D₂).image (domMap D₁ D₂).toImage
    ((domMap D₁ D₂).imageι ≫ domProj D₁ D₂) (by
      rw [← Category.assoc, Scheme.Hom.toImage_imageι, domMap_proj])

/-- **A choice dominating two given ones.** -/
def dom : CompositionData f g := ⟨domBase D₁ D₂, domTop D₁ D₂⟩

/-- The morphism from the dominating choice to the first one. -/
def domFst : Hom (dom D₁ D₂) D₁ where
  base := domBaseFst D₁ D₂
  top := (domMap D₁ D₂).imageι ≫ pullback.fst _ _ ≫ pullback.fst _ _
  immersion_comp_top := by
    have h : (domMap D₁ D₂).toImage ≫ (domMap D₁ D₂).imageι ≫ pullback.fst _ _ ≫
        pullback.fst _ _ = D₁.top.immersion := by
      rw [Scheme.Hom.toImage_imageι_assoc, domMap_fst_fst]
    exact h
  top_comp_toBase := by
    have h : ((domMap D₁ D₂).imageι ≫ pullback.fst _ _ ≫ pullback.fst _ _) ≫ D₁.top.toBase =
        ((domMap D₁ D₂).imageι ≫ domProj D₁ D₂) ≫
          CompactificationOf.Hom.map (domBaseFst D₁ D₂) := by
      simp only [domProj, Category.assoc]
      rw [pullback.condition (f := D₁.top.toBase)]
    exact h

/-- The morphism from the dominating choice to the second one. -/
def domSnd : Hom (dom D₁ D₂) D₂ where
  base := domBaseSnd D₁ D₂
  top := (domMap D₁ D₂).imageι ≫ pullback.snd _ _ ≫ pullback.fst _ _
  immersion_comp_top := by
    have h : (domMap D₁ D₂).toImage ≫ (domMap D₁ D₂).imageι ≫ pullback.snd _ _ ≫
        pullback.fst _ _ = D₂.top.immersion := by
      rw [Scheme.Hom.toImage_imageι_assoc, domMap_snd_fst]
    exact h
  top_comp_toBase := by
    have h : ((domMap D₁ D₂).imageι ≫ pullback.snd _ _ ≫ pullback.fst _ _) ≫ D₂.top.toBase =
        ((domMap D₁ D₂).imageι ≫ domProj D₁ D₂) ≫
          CompactificationOf.Hom.map (domBaseSnd D₁ D₂) := by
      simp only [domProj, Category.assoc, pullback.condition]
    exact h

/-- The compactification of `X` in the dominating choice has dense interior. -/
theorem denseRange_dom : DenseRange (dom D₁ D₂).top.immersion.base :=
  (isDominant_toImage (domMap D₁ D₂) (Or.inl inferInstance)).denseRange

/-- The compactification of `Y` in the dominating choice has dense interior. -/
theorem hasDenseInterior_dom : HasDenseInterior (Over.mk g.left) (dom D₁ D₂).base :=
  CategoryOfCompactifications.hasDenseInterior_commonRefinement _ _ _

/-- A morphism out of the dominating choice preserves the interiors. -/
theorem Hom.preservesInterior_of_dom {D : CompositionData f g} (φ : Hom (dom D₁ D₂) D) :
    φ.PreservesInterior :=
  ⟨preservesInterior_of_dense g (hasDenseInterior_dom D₁ D₂) _,
    CompactificationOf.preservesInterior_of_denseRange _ (denseRange_dom D₁ D₂)⟩

/-- **Two choices are dominated by a third**, through interior-preserving morphisms of choices
out of a choice whose compactifications have dense interior. This is the reduction step of the
source's proof, which uses [Stacks, Tag 0ATU] for the compactifications of `Y` and the
scheme-theoretic closure of `X` in the fibre product of the two base changes for those of `X`. -/
theorem exists_hom_hom :
    ∃ (D : CompositionData f g) (φ₁ : Hom D D₁) (φ₂ : Hom D D₂),
      φ₁.PreservesInterior ∧ φ₂.PreservesInterior :=
  ⟨dom D₁ D₂, domFst D₁ D₂, domSnd D₁ D₂, Hom.preservesInterior_of_dom D₁ D₂ _,
    Hom.preservesInterior_of_dom D₁ D₂ _⟩

end Dominate

/-! ### A choice through given compactifications of `f ≫ g` and of `g` -/

section OfCompactifications

variable (jfg : CompactificationOf (Over.mk (f ≫ g).left))
  (jg : CompactificationOf (Over.mk g.left))

include jfg in
/-- **A compactification of `X` over the compactification `Ȳ` of `Y`**, given compactifications of
`f ≫ g` and of `g`: [Stacks, Tag 0A9Z], applied to `X ⟶ Ȳ ⟶ Z` with `X` compactifiable over `Z`
through the given compactification of `f ≫ g`. -/
theorem exists_top : Nonempty (CompactificationOf (Over.mk (f.left ≫ jg.immersion))) := by
  obtain ⟨j, -⟩ := exists_quasiCompact_compactification_over (f.left ≫ jg.immersion) jg.toBase
    ⟨CompactificationOf.ofFactorization jfg.space jfg.immersion jfg.toBase (by
        rw [jfg.immersion_comp_toBase', Category.assoc, jg.immersion_comp_toBase']
        rfl),
      inferInstance⟩
  exact ⟨j⟩

/-- **A choice of compactifications whose compactification of `Y` is the given one**, the
compactification of `X` over it being given by [Stacks, Tag 0A9Z]. -/
noncomputable def ofCompactifications : CompositionData f g :=
  ⟨jg, Classical.choice (exists_top jfg jg)⟩

/-- The compactification of `Y` in `ofCompactifications jfg jg` is `jg`. -/
@[simp] theorem ofCompactifications_base : (ofCompactifications jfg jg).base = jg := rfl

end OfCompactifications

end CompositionData

end Stacks.Duality

end
