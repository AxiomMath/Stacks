module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic

/-!
# Covering families of algebraic spaces, and locality on the base

Let `S` be a scheme contained in a big fppf site `B`. A family `fᵢ : Xᵢ ⟶ Y` of morphisms of
algebraic spaces over `S` is a *syntomic*, *smooth* or *étale* covering (Stacks 041A, 041C,
041E) when every `fᵢ` has the corresponding property and the maps on points are jointly
surjective, and an *fppf covering* (Stacks 03Y8) when every `fᵢ` is flat and locally of finite
presentation and the maps on points are jointly surjective. It is an *fpqc covering*
(Stacks 03MQ) when every `fᵢ` is flat and every affine scheme-valued point of `Y` admits a
finite affine fpqc covering through which the pulled-back family factors.

These five notions are the ones for which Stacks 03YH considers a property of morphisms of
algebraic spaces to be *local on the base*: the property holds of a morphism exactly when it
holds of its pullback to every member of every covering family. Presented as a precoverage on
the category of algebraic spaces over `S`, that is Mathlib's
`CategoryTheory.MorphismProperty.IsLocalAtTarget`.

The same five notions are the ones for which Stacks 06EP considers a property to be *local on
the source*: the property holds of a morphism exactly when it holds of its composite with
every member of every covering family of its source. For the same precoverage that is Mathlib's
`CategoryTheory.MorphismProperty.IsLocalAtSource`, whose `comp` and `of_forall_comp` fields are
the two directions of the covering-family criterion and whose `RespectsIso` parent is the
invariance under isomorphisms of arrows that Stacks 06EP also demands.

## Main definitions

* `AlgebraicGeometry.Space.IsJointlySurjective` is the joint-surjectivity condition
  `|Y| = ⋃ᵢ |fᵢ|(|Xᵢ|)` shared by four of the five notions.
* `AlgebraicGeometry.Space.IsFpqcCovering`: **Stacks 03MQ**.
* `AlgebraicGeometry.Space.IsFppfCovering`: **Stacks 03Y8**.
* `AlgebraicGeometry.Space.IsSyntomicCovering`: **Stacks 041A**.
* `AlgebraicGeometry.Space.IsSmoothCovering`: **Stacks 041C**.
* `AlgebraicGeometry.Space.IsEtaleCovering`: **Stacks 041E**.
* `AlgebraicGeometry.Space.Topology`, `AlgebraicGeometry.Space.Topology.IsCovering` and
  `AlgebraicGeometry.Space.Topology.precoverage`: **Stacks 03YH**, the five topologies, their
  covering families, and those families as a precoverage on the algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isJointlySurjective_iff` and
  `AlgebraicGeometry.Space.isJointlySurjective_const_iff` unfold joint surjectivity, the
  second identifying a one-member family with `AlgebraicGeometry.Space.IsSurjective`.
* `AlgebraicGeometry.Space.isJointlySurjective_reindex`,
  `AlgebraicGeometry.Space.isFpqcCovering_reindex` and the `reindex` lemmas of the four
  structures: all five notions are stable under precomposing the index type with a
  surjection, so in particular under reindexing by an equivalence.
* `AlgebraicGeometry.Space.isSyntomicCovering_iff`: **Stacks 041A**, the structure unfolded to
  a conjunction.
* `AlgebraicGeometry.Space.IsSmoothCovering.isFppfCovering` and
  `AlgebraicGeometry.Space.IsSyntomicCovering.isFppfCovering`: two steps of the chain of
  implications of Tag 0DFQ.

## Implementation notes

Morphisms of algebraic spaces over `S` are natural transformations of presheaves on the big
fppf site of `S`, as in `AlgebraicGeometry.Spaces.Morphisms`. The four pointwise covering
conditions are structures, so that a client may name their clauses, and they record
algebraicity of the source and target as fields, matching the source definitions, which speak
of families of morphisms *of algebraic spaces*; the fpqc condition is an abbreviation of a
conjunction, since its second clause is itself existential and nothing is gained by splitting
it, and it records no algebraicity, because its refinement condition is meaningful and used for
an arbitrary family of morphisms of presheaves. Users who need algebraicity alongside the fpqc
condition should impose `AlgebraicGeometry.IsAlgebraicSpace` separately;
`Topology.IsCovering` records it uniformly for all five cases, which is what makes the fpqc
case fit the same shape as the other four.

The properties of morphisms of algebraic spaces appearing in the three middle notions are the
every-chart conditions of Tag 03MJ applied to the corresponding properties of morphisms of
schemes: `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` (Tag 03XP),
`AlgebraicGeometry.Space.IsSyntomic` (Tag 03Z7) and `AlgebraicGeometry.Space.IsSmooth`
(Tag 03ZC), each of which is an abbreviation for
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` at the corresponding scheme-level property, so
the chart API applies to the fields of the structures below directly. Flatness and étaleness
have library forms and are used: `AlgebraicGeometry.Space.IsFlat` (03ML) and
`AlgebraicGeometry.Space.IsEtale` (03FR). Note that étaleness of a morphism of algebraic spaces
is *not* the every-chart condition for `AlgebraicGeometry.Etale` but the stability condition of
Tag 03FR, which is why the étale covering notion is not formally a special case of the other
three.

Monotonicity of the every-chart condition in the tested property of scheme morphisms is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_mono` of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeProperties.lean`; that file is downstream of
this one, so the two implications of Tag 0DFQ proved here unfold the chart condition directly
instead.

`Topology.precoverage` is a precoverage on `AlgebraicGeometry.AlgebraicSpaces`, whose objects
are presheaves bundled with their algebraicity, while the covering predicates are stated for
bare presheaves; a covering family of the precoverage is therefore a presieve of the form
`CategoryTheory.Presieve.ofArrows` whose underlying family of presheaf morphisms is a covering
in the above sense. A property of morphisms of algebraic spaces is local on the base for a
topology `τ` exactly when `CategoryTheory.MorphismProperty.IsLocalAtTarget` holds of it for
`τ.precoverage`; stating locality this way gives a client Mathlib's pullback API and invariance
under isomorphism for free.

The index type `I` of a covering family lives in its own universe `v`, independent of the
universe `u` of the schemes; in the five predicates and in `Topology.IsCovering` it is pinned
by the explicit family argument, so no instantiation is hidden from a consumer, while
`Topology.precoverage` quantifies over it existentially, so a covering of the precoverage may
be indexed by any type. The index type of the *refining* family in the fpqc condition is
existentially quantified and is therefore pinned, to `u + 1`, matching
`AlgebraicGeometry.BigFppfSite.precoverage` and `AlgebraicGeometry.BigAffineFppf.precoverage`;
since that family is required to be finite this is no restriction.

## References

* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041A](https://stacks.math.columbia.edu/tag/041A)
* [Stacks Project, Tag 041C](https://stacks.math.columbia.edu/tag/041C)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 06EP](https://stacks.math.columbia.edu/tag/06EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Joint surjectivity on points -/

/-- A family of morphisms of presheaves on the big fppf site of `S` is *jointly
surjective* when the images of the induced maps on points cover the points of the common
target, that is `|Y| = ⋃ᵢ |fᵢ|(|Xᵢ|)`. -/
abbrev IsJointlySurjective {I : Type v} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ Y) : Prop :=
  (⋃ i, Set.range (pointsMap B S hS (X i) (f i))) = Set.univ

/-- A family is jointly surjective exactly when every point of the target is in the image
of some member. -/
theorem isJointlySurjective_iff {I : Type v} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ Y) :
    IsJointlySurjective B S hS X f ↔
      ∀ y : points B S hS Y, ∃ i, ∃ x : points B S hS (X i),
        pointsMap B S hS (X i) (f i) x = y := by
  rw [IsJointlySurjective, Set.iUnion_eq_univ_iff]
  simp only [Set.mem_range]

/-- A one-member family is jointly surjective exactly when its member is surjective. -/
theorem isJointlySurjective_const_iff {I : Type v} [Nonempty I]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsJointlySurjective B S hS (fun _ : I ↦ X) (fun _ ↦ f) ↔ IsSurjective B S hS f := by
  rw [IsJointlySurjective, Set.iUnion_const, Set.range_eq_univ]

/-- Joint surjectivity is preserved by precomposing the index type with a surjection. -/
theorem isJointlySurjective_reindex {I : Type v} {J : Type w}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ Y} (h : IsJointlySurjective B S hS X f) {σ : J → I}
    (hσ : Function.Surjective σ) :
    IsJointlySurjective B S hS (fun j ↦ X (σ j)) (fun j ↦ f (σ j)) :=
  (hσ.iUnion_comp fun i ↦ Set.range (pointsMap B S hS (X i) (f i))).trans h

/-! ### Fpqc coverings -/

/-- **Stacks 03MQ.** A family of flat morphisms of algebraic spaces over `S` with common
target `Y` is an *fpqc covering* when, for every affine object `T` of the big fppf site of
`S` and every morphism `h : T ⟶ Y`, there is a finite family of affine objects over `T`
which is an fpqc covering of `T` and refines the family pulled back along `h`. -/
@[stacks 03MQ]
abbrev IsFpqcCovering {I : Type v} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ Y) : Prop :=
  (∀ i, IsFlat B S hS (f i)) ∧ ∀ (T : BigAffineFppf B S hS)
      (h : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
      ∃ U : PreZeroHypercover.{u + 1} T, Finite U.I₀ ∧
        Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ ∈
          Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T) ∧
        ∀ j : U.I₀, ∃ i : I, ∃ a : yoneda.obj
            ((BigAffineFppf.inclusion B S hS).obj (U.X j)) ⟶ X i, a ≫ f i =
              yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)) ≫ h

/-- Every member of an fpqc covering is flat. -/
theorem isFpqcCovering_flat {I : Type v} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ Y}
    (h : IsFpqcCovering B S hS f) (i : I) : IsFlat B S hS (f i) := h.1 i

/-- The fpqc condition is preserved by precomposing the index type with a surjection. -/
theorem isFpqcCovering_reindex {I : Type v} {J : Type w}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ Y} (h : IsFpqcCovering B S hS f) {σ : J → I}
    (hσ : Function.Surjective σ) : IsFpqcCovering B S hS (fun j ↦ f (σ j)) := by
  refine ⟨fun j ↦ h.1 (σ j), fun T g ↦ ?_⟩
  obtain ⟨U, hfin, hmem, hrefine⟩ := h.2 T g
  refine ⟨U, hfin, hmem, fun k ↦ ?_⟩
  obtain ⟨i, a, ha⟩ := hrefine k
  obtain ⟨j, rfl⟩ := hσ i
  exact ⟨j, a, ha⟩

/-! ### Fppf coverings -/

/-- **Stacks 03Y8.** A family of morphisms of algebraic spaces over `S` with common target
is an *fppf covering* when every member is flat and locally of finite presentation and the
family is jointly surjective on points. -/
@[stacks 03Y8]
structure IsFppfCovering {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F) : Prop where
  /-- The target is an algebraic space. -/
  target_isAlgebraicSpace : IsAlgebraicSpace B S hS F
  /-- Every source is an algebraic space. -/
  source_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (X i)
  /-- Every member of the family is flat. -/
  flat : ∀ i, IsFlat B S hS (f i)
  /-- Every member of the family is locally of finite presentation. -/
  locallyOfFinitePresentation : ∀ i, IsLocallyOfFinitePresentation B S hS (f i)
  /-- The images of the members cover the set of points of the target. -/
  jointly_surjective : (⋃ i, Set.range (pointsMap B S hS (X i) (f i))) = Set.univ

/-- The fppf condition is preserved by precomposing the index type with a surjection. -/
theorem IsFppfCovering.reindex {I : Type v} {J : Type w}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (h : IsFppfCovering B S hS X f) {σ : J → I}
    (hσ : Function.Surjective σ) :
    IsFppfCovering B S hS (fun j ↦ X (σ j)) (fun j ↦ f (σ j)) where
  target_isAlgebraicSpace := h.target_isAlgebraicSpace
  source_isAlgebraicSpace j := h.source_isAlgebraicSpace (σ j)
  flat j := h.flat (σ j)
  locallyOfFinitePresentation j := h.locallyOfFinitePresentation (σ j)
  jointly_surjective := isJointlySurjective_reindex B S hS h.jointly_surjective hσ

/-! ### Syntomic coverings -/

/-- **Stacks 041A.** A family of morphisms of algebraic spaces over `S` with common target
is a *syntomic covering* when every member is syntomic and the family is jointly
surjective on points. -/
@[stacks_fixed 041A]
structure IsSyntomicCovering {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F) : Prop where
  /-- The target is an algebraic space. -/
  target_isAlgebraicSpace : IsAlgebraicSpace B S hS F
  /-- Every source is an algebraic space. -/
  source_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (X i)
  /-- Every member of the family is syntomic. -/
  syntomic : ∀ i, IsSyntomic B S hS (f i)
  /-- The images of the members cover the set of points of the target. -/
  jointly_surjective : (⋃ i, Set.range (pointsMap B S hS (X i) (f i))) = Set.univ

/-- **Stacks 041A.** Being a syntomic covering is exactly: the target and all the sources are
algebraic spaces, every member of the family is syntomic, and the images of the maps on points
exhaust the points of the target. -/
@[stacks 041A "the condition unfolded"]
theorem isSyntomicCovering_iff {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F) :
    IsSyntomicCovering B S hS X f ↔
      (IsAlgebraicSpace B S hS F ∧ (∀ i, IsAlgebraicSpace B S hS (X i)) ∧
        (∀ i, IsSyntomic B S hS (f i)) ∧
        Set.univ = ⋃ i, Set.range (pointsMap B S hS (X i) (f i))) :=
  ⟨fun h => ⟨h.target_isAlgebraicSpace, h.source_isAlgebraicSpace, h.syntomic,
      h.jointly_surjective.symm⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄.symm⟩⟩

/-- The syntomic condition is preserved by precomposing the index type with a
surjection. -/
theorem IsSyntomicCovering.reindex {I : Type v} {J : Type w}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (h : IsSyntomicCovering B S hS X f) {σ : J → I}
    (hσ : Function.Surjective σ) :
    IsSyntomicCovering B S hS (fun j ↦ X (σ j)) (fun j ↦ f (σ j)) where
  target_isAlgebraicSpace := h.target_isAlgebraicSpace
  source_isAlgebraicSpace j := h.source_isAlgebraicSpace (σ j)
  syntomic j := h.syntomic (σ j)
  jointly_surjective := isJointlySurjective_reindex B S hS h.jointly_surjective hσ

/-- **Stacks 0DFQ**, one step. A syntomic covering is an fppf covering, because a syntomic
morphism of schemes is flat and locally of finite presentation. -/
theorem IsSyntomicCovering.isFppfCovering {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hc : IsSyntomicCovering B S hS X f) :
    IsFppfCovering B S hS X f where
  target_isAlgebraicSpace := hc.target_isAlgebraicSpace
  source_isAlgebraicSpace := hc.source_isAlgebraicSpace
  flat i := fun U V a b h ha hb hcomm ↦
    _root_.AlgebraicGeometry.flat (hc.syntomic i U V a b h ha hb hcomm)
  locallyOfFinitePresentation i := fun U V a b h ha hb hcomm ↦
    _root_.AlgebraicGeometry.locallyOfFinitePresentation
      (hc.syntomic i U V a b h ha hb hcomm)
  jointly_surjective := hc.jointly_surjective

/-! ### Smooth coverings -/

/-- **Stacks 041C.** A family of morphisms of algebraic spaces over `S` with common target
is a *smooth covering* when every member is smooth and the family is jointly surjective on
points. -/
@[stacks 041C]
structure IsSmoothCovering {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F) : Prop where
  /-- The target is an algebraic space. -/
  target_isAlgebraicSpace : IsAlgebraicSpace B S hS F
  /-- Every source is an algebraic space. -/
  source_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (X i)
  /-- Every member of the family is smooth. -/
  smooth : ∀ i, IsSmooth B S hS (f i)
  /-- The images of the members cover the set of points of the target. -/
  jointly_surjective : (⋃ i, Set.range (pointsMap B S hS (X i) (f i))) = Set.univ

/-- The smooth condition is preserved by precomposing the index type with a surjection. -/
theorem IsSmoothCovering.reindex {I : Type v} {J : Type w}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (h : IsSmoothCovering B S hS X f) {σ : J → I}
    (hσ : Function.Surjective σ) :
    IsSmoothCovering B S hS (fun j ↦ X (σ j)) (fun j ↦ f (σ j)) where
  target_isAlgebraicSpace := h.target_isAlgebraicSpace
  source_isAlgebraicSpace j := h.source_isAlgebraicSpace (σ j)
  smooth j := h.smooth (σ j)
  jointly_surjective := isJointlySurjective_reindex B S hS h.jointly_surjective hσ

/-- **Stacks 0DFQ**, one step. A smooth covering is an fppf covering, because a smooth
morphism of schemes is flat and locally of finite presentation. -/
theorem IsSmoothCovering.isFppfCovering {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hc : IsSmoothCovering B S hS X f) :
    IsFppfCovering B S hS X f where
  target_isAlgebraicSpace := hc.target_isAlgebraicSpace
  source_isAlgebraicSpace := hc.source_isAlgebraicSpace
  flat i := fun U V a b h ha hb hcomm ↦ by
    have := hc.smooth i U V a b h ha hb hcomm
    infer_instance
  locallyOfFinitePresentation i := fun U V a b h ha hb hcomm ↦ by
    have := hc.smooth i U V a b h ha hb hcomm
    infer_instance
  jointly_surjective := hc.jointly_surjective

/-! ### Étale coverings -/

/-- **Stacks 041E.** A family of morphisms of algebraic spaces over `S` with common target
is an *étale covering* when every member is étale and the family is jointly surjective on
points. -/
@[stacks 041E]
structure IsEtaleCovering {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F) : Prop where
  /-- The target is an algebraic space. -/
  target_isAlgebraicSpace : IsAlgebraicSpace B S hS F
  /-- Every source is an algebraic space. -/
  source_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (X i)
  /-- Every member of the family is étale. -/
  etale : ∀ i, IsEtale B S hS (f i)
  /-- The images of the members cover the set of points of the target. -/
  jointly_surjective : (⋃ i, Set.range (pointsMap B S hS (X i) (f i))) = Set.univ

/-- The étale condition is preserved by precomposing the index type with a surjection. -/
theorem IsEtaleCovering.reindex {I : Type v} {J : Type w}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (h : IsEtaleCovering B S hS X f) {σ : J → I}
    (hσ : Function.Surjective σ) :
    IsEtaleCovering B S hS (fun j ↦ X (σ j)) (fun j ↦ f (σ j)) where
  target_isAlgebraicSpace := h.target_isAlgebraicSpace
  source_isAlgebraicSpace j := h.source_isAlgebraicSpace (σ j)
  etale j := h.etale (σ j)
  jointly_surjective := isJointlySurjective_reindex B S hS h.jointly_surjective hσ

/-! ### Properties of morphisms local on the base -/

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

/-- **Stacks 03YH.** The topologies for which locality on the base of a property of morphisms
of algebraic spaces is considered. -/
@[stacks_fixed 03YH "the five topologies"]
inductive Topology where
  /-- The fpqc topology. -/
  | fpqc
  /-- The fppf topology. -/
  | fppf
  /-- The syntomic topology. -/
  | syntomic
  /-- The smooth topology. -/
  | smooth
  /-- The étale topology. -/
  | etale
  deriving DecidableEq

/-- **Stacks 03YH.** A family of morphisms of algebraic spaces over `S` with common target is
a covering family for the topology `τ` when its source and target presheaves are algebraic
spaces and it satisfies the covering condition of `τ`. -/
@[stacks 03YH "covering families"]
abbrev Topology.IsCovering (τ : Topology)
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Yi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : ∀ i, Yi i ⟶ Y) : Prop :=
  IsAlgebraicSpace B S hS Y ∧
    (∀ i, IsAlgebraicSpace B S hS (Yi i)) ∧
      match τ with
      | .fpqc => IsFpqcCovering B S hS g
      | .fppf => IsFppfCovering B S hS Yi g
      | .syntomic => IsSyntomicCovering B S hS Yi g
      | .smooth => IsSmoothCovering B S hS Yi g
      | .etale => IsEtaleCovering B S hS Yi g

/-- **Stacks 03YH.** The precoverage on the category of algebraic spaces over `S` presented by
the `τ`-covering families. A property `P` of morphisms of algebraic spaces is local on the
base for `τ` exactly when
`CategoryTheory.MorphismProperty.IsLocalAtTarget P (τ.precoverage B S hS)`. -/
@[stacks 03YH "the precoverage"]
def Topology.precoverage (τ : Topology)
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Precoverage (AlgebraicSpaces B S hS) where
  coverings Y := {R | ∃ (I : Type v)
      (Yi : I → AlgebraicSpaces B S hS) (g : ∀ i, Yi i ⟶ Y),
      R = Presieve.ofArrows Yi g ∧
        τ.IsCovering B S hS (fun i => (Yi i).obj) (fun i => (g i).hom)}

add_to_stacks 03YH "locality on the base" CategoryTheory.MorphismProperty.IsLocalAtTarget

add_to_stacks 06EP CategoryTheory.MorphismProperty.IsLocalAtSource

end AlgebraicGeometry.Space

end
