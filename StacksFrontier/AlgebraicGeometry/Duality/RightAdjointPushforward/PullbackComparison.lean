module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic

/-!
# The two-variable comparison map of the right adjoint of pushforward

Let `f : X ⟶ Y` be a morphism of schemes and let `a` be a right adjoint of the restricted derived
direct image `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `K, L ∈ D_QCoh(𝒪_Y)` there is a canonical
map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`,

which is the two-variable form of Equation 48.8.0.1 of [Stacks, Tag 0A9S]. It is the map adjoint
to

  `Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} a(L)) = K ⊗ᴸ_{𝒪_Y} Rf_*(a(L)) ⟶ K ⊗ᴸ_{𝒪_Y} L`,

where the first step is the projection formula of [Stacks, Tag 08EU] and the second is the
identity of `K` tensored with the trace map `Rf_*(a(L)) ⟶ L`, that is, with the counit of the
adjunction `Rf_* ⊣ a`.

The projection-formula map itself is *constructed* here, not assumed: it is the adjoint transpose,
for the adjunction `Lf^* ⊣ Rf_*` of `Stacks.Duality.quasiCoherentDerivedAdjunction`, of the oplax
monoidality of `Lf^*` followed by the counit of that adjunction in the pushforward factor. This
is the abstract construction of `CategoryTheory.adjunctionTensorMap`, instantiated
at the derived tensor products of [Stacks, Tag 08DX].

## Main definitions

All in the namespace `Stacks.Duality`.

* `quasiCoherentDerivedTensorSwap` — the derived tensor product of `D_QCoh(𝒪_Z)` as a functor on
  the product category with its two arguments interchanged, `(K₁, K₂) ↦ K₂ ⊗ᴸ_{𝒪_Z} K₁`.
* `projectionFormulaMap` — the canonical map `K ⊗ᴸ_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} E)`, whose
  invertibility is [Stacks, Tag 08EU].
* `compareWithPullbackTensor` — the comparison map `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)` of
  [Stacks, Tag 0A9S].
* `twistedInverseImageCompareWithPullbackTensor` — the same map for the twisted inverse image
  `f^×` of `Stacks.Duality.twistedInverseImage` and its own adjunction.

## Main results

* `projectionFormulaMap_naturality` — the projection-formula map is natural in both arguments.
* `homEquiv_symm_compareWithPullbackTensor` and
  `projectionFormulaMap_comp_map_compareWithPullbackTensor_comp_counit` — the adjunction
  characterization which pins the comparison map uniquely: its adjoint transpose is the inverse
  projection formula followed by the identity of `K` tensored with the trace map, equivalently
  the projection formula followed by `Rf_*` of the comparison map and the trace map is the
  identity of `K` tensored with the trace map.
* `compareWithPullbackTensor_naturality_left`, `compareWithPullbackTensor_naturality_right` and
  `compareWithPullbackTensor_naturality` — naturality of the comparison map in `K`, in `L`, and
  in both.

## Implementation notes

*Which inputs are hypotheses, and why.* The source cites two results at exactly the two points
where this file takes a hypothesis.

* The **oplax monoidality** `α` of derived pullback, read on the interchanged bifunctors: at
  `(K₁, K₂)` it is the map `Lf^*(K₂ ⊗ᴸ_{𝒪_Y} K₁) ⟶ Lf^*K₂ ⊗ᴸ_{𝒪_X} Lf^*K₁`, natural in both
  arguments. It is the bifunctorial content of [Stacks, Tag 079U] used in the proof of
  [Stacks, Tag 08EU], and the interchange of its two arguments is only a renaming. It is not
  available in this repository: what is available is
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIsoOfKFlat`, the source's
  isomorphism on K-flat representatives, whose own docstring records that "the passage from
  K-flat representatives to arbitrary objects of `D(𝒪_Y)`, which is what makes the source's
  statement bifunctorial" is not there. So `α` is a hypothesis, and it is the *only* datum the
  construction below depends on.
* The **invertibility** of `projectionFormulaMap` is [Stacks, Tag 08EU], the projection formula
  for a quasi-compact quasi-separated morphism. It is hypothesised as an `IsIso` instance, a
  `Prop`, so no further datum enters: the comparison map is canonical in `α` alone.

The specialization at `L = 𝒪_Y`, which is the displayed equation of [Stacks, Tag 0A9S], is in
`PullbackComparisonStructureSheaf.lean` of this directory; it needs a right unitor for the
derived tensor product, which this file deliberately does not.

This mirrors `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward`, which carries the
geometric inputs of [Stacks, Tag 0A9E] as hypotheses in the same way.

*The right adjoint is a hypothesis too.* `Functor.IsLeftAdjoint` is a `Prop` and
`Functor.rightAdjoint` is fed by choice, so a construction that obtained `a` from an existence
statement would depend on an arbitrary choice. The functor `a` and the adjunction
`Rf_* ⊣ a` are therefore explicit arguments, which is also the shape in which a consumer has
them. `twistedInverseImageCompareWithPullbackTensor` specializes to the repository's own right
adjoint, `Stacks.Duality.twistedInverseImage`.

*The order of the tensor factors.* The two bifunctors fed to
`CategoryTheory.adjunctionTensorMap` are the derived tensor products with their
arguments interchanged. This is what makes the projection-formula map come out as
`K ⊗ᴸ Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ E)`, the order in which the source writes it; with the
un-interchanged bifunctors it would come out as `Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)`, and converting
between the two would need a symmetry of the derived tensor product, which this repository does
not have.

*The quasi-coherence hypothesis.* `hpush` is the standard input that lets derived direct image
be restricted to the complexes with quasi-coherent cohomology; it holds for `f` quasi-compact
and quasi-separated by `AlgebraicGeometry.isQuasicoherent_derivedPushforward`, which is
[Stacks, Tag 08D5]. Its derived-pullback counterpart is *not* assumed: it holds for every
morphism of schemes by `Stacks.Duality.isQuasicoherent_homology_derivedPullback'`, which is
[Stacks, Tag 08DW] part (1), so the statements are written with the unconditional
`Stacks.Duality.quasiCoherentDerivedPullback'` and the adjunction
`Stacks.Duality.quasiCoherentDerivedAdjunction` is given that proof directly.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`, no
declaration here carries a `[HasDerivedCategory.{w}]` binder: the quasi-coherent derived tensor
product and derived pullback are available only at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and a free binder would put the statements
at a model at which those are not.

*Compatibility with the shift and with distinguished triangles* is not stated. It would ask for
`Functor.CommShift` structures on the derived tensor product in each variable, and those are not
available in this repository for `Stacks.Duality.quasiCoherentDerivedTensor`; assuming them would
add hypotheses of a different kind than the two the source cites.

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality

/-! ### The derived tensor product with its arguments interchanged -/

/-- The derived tensor product on `D_QCoh(𝒪_Z)`, as a functor on the product category with its
two arguments interchanged: it sends `(K₁, K₂)` to `K₂ ⊗ᴸ_{𝒪_Z} K₁`. -/
abbrev quasiCoherentDerivedTensorSwap (Z : Scheme.{u}) :
    quasiCoherentDerivedCategory Z × quasiCoherentDerivedCategory Z ⥤
      quasiCoherentDerivedCategory Z :=
  CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (quasiCoherentDerivedTensor Z)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (α : quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ⟶
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X)

/-! ### The projection-formula map -/

/-- **The projection-formula map** `K ⊗ᴸ_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} E)`: the adjoint
transpose, for the adjunction `Lf^* ⊣ Rf_*` on the quasi-coherent derived categories, of the
oplax monoidality of `Lf^*` followed by the counit of that adjunction in the pushforward factor.
Its invertibility is [Stacks, Tag 08EU]. -/
@[stacks 0B53 "the map"]
def projectionFormulaMap (E : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor Y).obj K).obj
        ((quasiCoherentDerivedPushforward f hpush).obj E) ⟶
      (quasiCoherentDerivedPushforward f hpush).obj
        (((quasiCoherentDerivedTensor X).obj
          ((quasiCoherentDerivedPullback' f).obj K)).obj E) :=
  CategoryTheory.adjunctionTensorMap
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
    (quasiCoherentDerivedTensorSwap Y) (quasiCoherentDerivedTensorSwap X) α E K

/-- The projection-formula map is natural in both arguments. -/
@[stacks 0B53 "naturality"]
theorem projectionFormulaMap_naturality {E E' : quasiCoherentDerivedCategory X}
    {K K' : quasiCoherentDerivedCategory Y} (φ : E ⟶ E') (h : K ⟶ K') :
    (((quasiCoherentDerivedTensor Y).map h).app
          ((quasiCoherentDerivedPushforward f hpush).obj E) ≫
        ((quasiCoherentDerivedTensor Y).obj K').map
          ((quasiCoherentDerivedPushforward f hpush).map φ)) ≫
      projectionFormulaMap f hpush α E' K' =
    projectionFormulaMap f hpush α E K ≫
      (quasiCoherentDerivedPushforward f hpush).map
        (((quasiCoherentDerivedTensor X).map
            ((quasiCoherentDerivedPullback' f).map h)).app E ≫
          ((quasiCoherentDerivedTensor X).obj
            ((quasiCoherentDerivedPullback' f).obj K')).map φ) :=
  CategoryTheory.adjunctionTensorMap_natural
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
    (quasiCoherentDerivedTensorSwap Y) (quasiCoherentDerivedTensorSwap X) α φ h

/-- Naturality of the projection-formula map in the pulled-back argument. -/
theorem projectionFormulaMap_naturality_left (E : quasiCoherentDerivedCategory X)
    {K K' : quasiCoherentDerivedCategory Y} (h : K ⟶ K') :
    ((quasiCoherentDerivedTensor Y).map h).app
        ((quasiCoherentDerivedPushforward f hpush).obj E) ≫
      projectionFormulaMap f hpush α E K' =
    projectionFormulaMap f hpush α E K ≫
      (quasiCoherentDerivedPushforward f hpush).map
        (((quasiCoherentDerivedTensor X).map
          ((quasiCoherentDerivedPullback' f).map h)).app E) := by
  simpa using projectionFormulaMap_naturality f hpush α (𝟙 E) h

/-- Naturality of the projection-formula map in the pushed-forward argument. -/
theorem projectionFormulaMap_naturality_right {E E' : quasiCoherentDerivedCategory X}
    (φ : E ⟶ E') (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor Y).obj K).map
        ((quasiCoherentDerivedPushforward f hpush).map φ) ≫
      projectionFormulaMap f hpush α E' K =
    projectionFormulaMap f hpush α E K ≫
      (quasiCoherentDerivedPushforward f hpush).map
        (((quasiCoherentDerivedTensor X).obj
          ((quasiCoherentDerivedPullback' f).obj K)).map φ) := by
  simpa using projectionFormulaMap_naturality f hpush α φ (𝟙 K)

/-! ### The comparison map of Equation 48.8.0.1 -/

section Comparison

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-- **The two-variable comparison map of Equation 48.8.0.1 of [Stacks, Tag 0A9S]**:
`Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`, for a right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. It is the map adjoint to the inverse of the projection
formula `Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} a(L)) ≅ K ⊗ᴸ_{𝒪_Y} Rf_*(a(L))` followed by the identity of `K`
tensored with the trace map `adj.counit.app L : Rf_*(a(L)) ⟶ L`. -/
@[stacks 0A9S "variant: the two-variable map for an arbitrary cotensorator α and right adjoint a; \
  the tag is Stacks.Duality.qcqsCompareWithPullback"]
def compareWithPullbackTensor (K L : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj K)).obj (a.obj L) ⟶
      a.obj (((quasiCoherentDerivedTensor Y).obj K).obj L) :=
  adj.homEquiv _ _ (inv (projectionFormulaMap f hpush α (a.obj L) K) ≫
    ((quasiCoherentDerivedTensor Y).obj K).map (adj.counit.app L))

/-- **The adjunction characterization of the comparison map.** Its adjoint transpose is the
inverse projection formula followed by the identity of `K` tensored with the trace map; this
determines the comparison map uniquely. -/
@[stacks 0A9S "variant: the adjunction characterization of the two-variable map for an arbitrary \
  α and a; the tag is Stacks.Duality.qcqsCompareWithPullback"]
theorem homEquiv_symm_compareWithPullbackTensor (K L : quasiCoherentDerivedCategory Y) :
    (adj.homEquiv _ _).symm (compareWithPullbackTensor f hpush α adj K L) =
      inv (projectionFormulaMap f hpush α (a.obj L) K) ≫
        ((quasiCoherentDerivedTensor Y).obj K).map (adj.counit.app L) :=
  (adj.homEquiv _ _).symm_apply_apply _

/-- The adjunction characterization in the form a consumer rewrites with: `Rf_*` of the
comparison map followed by the trace map is the inverse projection formula followed by the
identity of `K` tensored with the trace map. -/
theorem map_compareWithPullbackTensor_comp_counit (K L : quasiCoherentDerivedCategory Y) :
    (quasiCoherentDerivedPushforward f hpush).map
          (compareWithPullbackTensor f hpush α adj K L) ≫
        adj.counit.app (((quasiCoherentDerivedTensor Y).obj K).obj L) =
      inv (projectionFormulaMap f hpush α (a.obj L) K) ≫
        ((quasiCoherentDerivedTensor Y).obj K).map (adj.counit.app L) :=
  homEquiv_symm_compareWithPullbackTensor f hpush α adj K L

/-- **Equation 48.8.0.1 as the source states it**: the projection formula, followed by `Rf_*` of
the comparison map and the trace map, is the identity of `K` tensored with the trace map. This is
the characterization with no inverse in it. -/
@[stacks 0A9S "variant: the characterization without the inverse for an arbitrary α and a; the \
  tag is Stacks.Duality.qcqsCompareWithPullback"]
theorem projectionFormulaMap_comp_map_compareWithPullbackTensor_comp_counit
    (K L : quasiCoherentDerivedCategory Y) :
    projectionFormulaMap f hpush α (a.obj L) K ≫
        (quasiCoherentDerivedPushforward f hpush).map
            (compareWithPullbackTensor f hpush α adj K L) ≫
          adj.counit.app (((quasiCoherentDerivedTensor Y).obj K).obj L) =
      ((quasiCoherentDerivedTensor Y).obj K).map (adj.counit.app L) := by
  rw [map_compareWithPullbackTensor_comp_counit, IsIso.hom_inv_id_assoc]

/-- Inverting the isomorphisms in a commuting square of morphisms. -/
private theorem comp_inv_eq_inv_comp {C : Type*} [Category C] {A B A' B' : C} {p : A ⟶ B}
    {p' : A' ⟶ B'} [IsIso p] [IsIso p'] {u : A ⟶ A'} {v : B ⟶ B'} (h : u ≫ p' = p ≫ v) :
    v ≫ inv p' = inv p ≫ u := by
  rw [IsIso.comp_inv_eq, Category.assoc, h, IsIso.inv_hom_id_assoc]

/-- A square of morphisms into the comparison maps commutes once it does after transposing. -/
private theorem comp_compareWithPullbackTensor_eq {K K' L L' : quasiCoherentDerivedCategory Y}
    (u : ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj K)).obj (a.obj L) ⟶
      ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj K')).obj (a.obj L'))
    (v : ((quasiCoherentDerivedTensor Y).obj K).obj L ⟶
      ((quasiCoherentDerivedTensor Y).obj K').obj L')
    (h : (quasiCoherentDerivedPushforward f hpush).map u ≫
        inv (projectionFormulaMap f hpush α (a.obj L') K') ≫
          ((quasiCoherentDerivedTensor Y).obj K').map (adj.counit.app L') =
      inv (projectionFormulaMap f hpush α (a.obj L) K) ≫
        ((quasiCoherentDerivedTensor Y).obj K).map (adj.counit.app L) ≫ v) :
    u ≫ compareWithPullbackTensor f hpush α adj K' L' =
      compareWithPullbackTensor f hpush α adj K L ≫ a.map v := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_compareWithPullbackTensor, homEquiv_symm_compareWithPullbackTensor]
  simpa using h

/-- The comparison map is natural in `K`. -/
theorem compareWithPullbackTensor_naturality_left {K K' : quasiCoherentDerivedCategory Y}
    (h : K ⟶ K') (L : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor X).map
          ((quasiCoherentDerivedPullback' f).map h)).app (a.obj L) ≫
        compareWithPullbackTensor f hpush α adj K' L =
      compareWithPullbackTensor f hpush α adj K L ≫
        a.map (((quasiCoherentDerivedTensor Y).map h).app L) := by
  apply comp_compareWithPullbackTensor_eq
  rw [← Category.assoc,
    comp_inv_eq_inv_comp (projectionFormulaMap_naturality_left f hpush α (a.obj L) h),
    Category.assoc]
  exact congrArg (_ ≫ ·) (((quasiCoherentDerivedTensor Y).map h).naturality _).symm

/-- The comparison map is natural in `L`. -/
theorem compareWithPullbackTensor_naturality_right (K : quasiCoherentDerivedCategory Y)
    {L L' : quasiCoherentDerivedCategory Y} (g : L ⟶ L') :
    ((quasiCoherentDerivedTensor X).obj
          ((quasiCoherentDerivedPullback' f).obj K)).map (a.map g) ≫
        compareWithPullbackTensor f hpush α adj K L' =
      compareWithPullbackTensor f hpush α adj K L ≫
        a.map (((quasiCoherentDerivedTensor Y).obj K).map g) := by
  apply comp_compareWithPullbackTensor_eq
  rw [← Category.assoc,
    comp_inv_eq_inv_comp (projectionFormulaMap_naturality_right f hpush α (a.map g) K),
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (_ ≫ ·) (congrArg _ (adj.counit_naturality g))

/-- The comparison map is natural in `K` and `L` jointly. -/
@[stacks 0A9S "variant: naturality of the two-variable map for an arbitrary α and a; the tag is \
  Stacks.Duality.qcqsCompareWithPullback"]
theorem compareWithPullbackTensor_naturality {K K' L L' : quasiCoherentDerivedCategory Y}
    (h : K ⟶ K') (g : L ⟶ L') :
    ((quasiCoherentDerivedTensor X).map
          ((quasiCoherentDerivedPullback' f).map h)).app (a.obj L) ≫
        ((quasiCoherentDerivedTensor X).obj
            ((quasiCoherentDerivedPullback' f).obj K')).map (a.map g) ≫
          compareWithPullbackTensor f hpush α adj K' L' =
      compareWithPullbackTensor f hpush α adj K L ≫
        a.map (((quasiCoherentDerivedTensor Y).map h).app L ≫
          ((quasiCoherentDerivedTensor Y).obj K').map g) := by
  rw [compareWithPullbackTensor_naturality_right, ← Category.assoc,
    compareWithPullbackTensor_naturality_left, Category.assoc, ← Functor.map_comp]

end Comparison

/-! ### The comparison map for the twisted inverse image -/

section TwistedInverseImage

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]
  [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]

/-- **Equation 48.8.0.1 for the twisted inverse image `f^×`** of
`Stacks.Duality.twistedInverseImage`: the comparison map
`Lf^*K ⊗ᴸ_{𝒪_X} f^×L ⟶ f^×(K ⊗ᴸ_{𝒪_Y} L)`, obtained from `compareWithPullbackTensor` at the
adjunction `Rf_* ⊣ f^×`. -/
@[stacks 0A9S "variant: the two-variable map at a = f^× for an arbitrary α; the tag is \
  Stacks.Duality.qcqsCompareWithPullback"]
def twistedInverseImageCompareWithPullbackTensor (K L : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj K)).obj
        ((twistedInverseImage f hpush).obj L) ⟶
      (twistedInverseImage f hpush).obj (((quasiCoherentDerivedTensor Y).obj K).obj L) :=
  compareWithPullbackTensor f hpush α (twistedInverseImageAdjunction f hpush) K L

end TwistedInverseImage

end Stacks.Duality

end
