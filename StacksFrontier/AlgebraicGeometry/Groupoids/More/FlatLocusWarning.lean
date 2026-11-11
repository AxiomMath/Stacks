module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.MaximalLocus
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PointwiseBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The largest flat open of a morphism of schemes

Stacks Tag 04LI warns about how Stacks Tag 04LH reads at `P =` flat, `Q =` every morphism (the
empty condition) and `R =` flat and locally of finite presentation.  The lemma applies there:
every morphism of schemes has a largest open of its source on which it is flat, namely the
interior of its pointwise flat locus, and that open commutes with base change along a morphism
which is flat and locally of finite presentation, because such a base change has an open
projection to the source.  But the largest flat open need not be the pointwise flat locus.

## Main definitions

* `AlgebraicGeometry.maximalFlatOpen`: the largest open of the source on which a morphism of
  schemes is flat.

## Main results

* `AlgebraicGeometry.isGreatest_maximalFlatOpen`: `maximalFlatOpen` is the largest flat open.
* `AlgebraicGeometry.isGreatest_preimage_of_isPullback`: the largest flat open commutes with base
  change along a morphism which is flat and locally of finite presentation.
* `AlgebraicGeometry.flat_maximal_locus_warning` is Stacks Tag 04LI: the four hypotheses of
  Stacks Tag 04LH hold for this triple, and the largest flat open need not be the flat locus.
* `AlgebraicGeometry.exists_open_with_preimage_maximalFlatOpen` is Stacks Tag 04LH at this
  triple.

## Implementation notes

The base change compatibility uses that a flat morphism locally of finite presentation is
universally open (Mathlib's `AlgebraicGeometry.UniversallyOpen.of_flat`, Stacks Tag 01UA), so
the inverse image of the interior of the flat locus is the interior of its inverse image, and
that flatness at a point is preserved and reflected by flat base change
(`AlgebraicGeometry.isFlatAt_iff_of_isPullback`).  The counterexample is
`AlgebraicGeometry.exists_flat_locus_not_open`.

## References

* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 04LH](https://stacks.math.columbia.edu/tag/04LH)
* [Stacks Project, Tag 04LI](https://stacks.math.columbia.edu/tag/04LI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### The triple `P =` flat, `Q =` every morphism, `R =` flat and locally of finite
presentation -/

/-- The largest open of the source on which a morphism of schemes is flat: the interior of the
set of points at which it is flat. -/
def maximalFlatOpen {X Y : Scheme.{u}} (f : X ⟶ Y) : X.Opens :=
  ⟨interior {x : X | IsFlatAt f.toLRSHom.toShHom x}, isOpen_interior⟩

/-- Every morphism of schemes has a largest open of its source on which it is flat, namely
`AlgebraicGeometry.maximalFlatOpen`. -/
public theorem isGreatest_maximalFlatOpen {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsGreatest {W : X.Opens | Flat (W.ι ≫ f)} (maximalFlatOpen f) :=
  ⟨flat_of_subset_setOf_isFlatAt f _ interior_subset, fun W hW =>
    interior_maximal (fun _ hx => isFlatAt_of_flat_comp_ι f hW hx) W.isOpen⟩

/-- A largest flat open of the source is contained in the pointwise flat locus and contains
the interior of that locus. -/
private theorem interior_subset_and_subset_of_isGreatest {X Y : Scheme.{u}} {f : X ⟶ Y}
    {V : X.Opens} (hV : IsGreatest {W : X.Opens | Flat (W.ι ≫ f)} V) :
    interior {x : X | IsFlatAt f.toLRSHom.toShHom x} ⊆ V ∧
      (V : Set X) ⊆ {x : X | IsFlatAt f.toLRSHom.toShHom x} :=
  ⟨hV.2 (isGreatest_maximalFlatOpen f).1, fun _ hx => isFlatAt_of_flat_comp_ι f hV.1 hx⟩

/-- The largest flat open of the source commutes with base change along a morphism which is flat
and locally of finite presentation: for a cartesian square with such a base morphism `q`, the
inverse image of the largest flat open of `f` is the largest flat open of the base change
`f'`. -/
public theorem isGreatest_preimage_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y} [Flat q] [LocallyOfFinitePresentation q]
    (hp : IsPullback p f' f q) {V : X.Opens}
    (hV : IsGreatest {W : X.Opens | Flat (W.ι ≫ f)} V) :
    IsGreatest {W' : X'.Opens | Flat (W'.ι ≫ f')} (p ⁻¹ᵁ V) := by
  have : Flat p := MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip inferInstance
  have : LocallyOfFinitePresentation p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip inferInstance
  have hlocus : {x' : X' | IsFlatAt f'.toLRSHom.toShHom x'} =
      p ⁻¹' {x : X | IsFlatAt f.toLRSHom.toShHom x} :=
    Set.ext fun x' => isFlatAt_iff_of_isPullback hp x'
  obtain ⟨hint, hsub⟩ := interior_subset_and_subset_of_isGreatest hV
  refine ⟨flat_of_subset_setOf_isFlatAt f' _ ?_, fun W' hW' => ?_⟩
  · rw [hlocus]
    exact Set.preimage_mono hsub
  · have hW'sub : (W' : Set X') ⊆ interior {x' : X' | IsFlatAt f'.toLRSHom.toShHom x'} :=
      interior_maximal (fun _ hx => isFlatAt_of_flat_comp_ι f' hW' hx) W'.isOpen
    rw [hlocus, ← p.isOpenMap.preimage_interior_eq_interior_preimage p.continuous] at hW'sub
    exact hW'sub.trans (Set.preimage_mono hint)

/-- The trivial property of morphisms of schemes is stable under base change. -/
private theorem top_isStableUnderBaseChange :
    (⊤ : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
  ⟨fun _ _ => trivial⟩

/-- **Stacks Project, Tag 04LI.** Stacks Tag 04LH applies to `P =` flat, `Q =` every morphism
(the empty condition) and `R =` flat and locally of finite presentation: `R` implies `Q`, `Q` is
stable under composition and base change, every morphism of schemes has a largest open of its
source on which it is flat, and that open commutes with base change along a morphism which is
flat and locally of finite presentation. But this largest flat open is not the set of points at
which the morphism is flat: for some morphism of schemes it is strictly smaller.

The largest flat open is `AlgebraicGeometry.maximalFlatOpen`, the interior of the pointwise flat
locus. The counterexample is `AlgebraicGeometry.exists_flat_locus_not_open`; openness of the
universally open map `p` (Mathlib's `AlgebraicGeometry.UniversallyOpen.of_flat`, Stacks 01UA)
gives the base change compatibility. -/
@[stacks 04LI "hypotheses (1)-(4) of 04LH for P = flat, Q = empty, R = flat and locally of \
  finite presentation, and a morphism whose largest flat open is not its flat locus; the base \
  change hypothesis uses Mathlib's UniversallyOpen.of_flat (01UA)"]
public theorem flat_maximal_locus_warning :
    ((fun _ _ q => Flat q ∧ LocallyOfFinitePresentation q : MorphismProperty Scheme.{u}) ≤ ⊤) ∧
    (⊤ : MorphismProperty Scheme.{u}).IsStableUnderComposition ∧
    (⊤ : MorphismProperty Scheme.{u}).IsStableUnderBaseChange ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), ∃ V : X.Opens,
      IsGreatest {W : X.Opens | Flat (W.ι ≫ f)} V) ∧
    (∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y},
      Flat q → LocallyOfFinitePresentation q → IsPullback p f' f q → ∀ {V : X.Opens},
        IsGreatest {W : X.Opens | Flat (W.ι ≫ f)} V →
          IsGreatest {W' : X'.Opens | Flat (W'.ι ≫ f')} (p ⁻¹ᵁ V)) ∧
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (W : X.Opens),
      IsGreatest {V : X.Opens | Flat (V.ι ≫ f)} W ∧
        (W.1 : Set X) ⊂ {x : X | IsFlatAt f.toLRSHom.toShHom x} :=
  ⟨fun _ _ _ _ => trivial, inferInstance, top_isStableUnderBaseChange,
    fun f => ⟨_, isGreatest_maximalFlatOpen f⟩,
    fun _ _ hp _ hV => isGreatest_preimage_of_isPullback hp hV, exists_flat_locus_not_open⟩

/-- Stacks Tag 04LH applied to the triple of Stacks Tag 04LI: for a groupoid scheme whose source
and target are flat and locally of finite presentation, and any morphism `g : U' ⟶ U`, the
largest open of `U' ×_{g, U, t} R` on which `h = s ∘ pr₁` is flat is the inverse image of an open
of `U'`. -/
public theorem exists_open_with_preimage_maximalFlatOpen {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left] :
    ∃ W : U'.Opens,
      IsGreatest
        {V : (Limits.pullback g G.target.left).Opens |
          Flat (V.ι ≫ Limits.pullback.snd g G.target.left ≫ G.source.left)}
        ((Limits.pullback.fst g G.target.left) ⁻¹ᵁ W) := by
  have := top_isStableUnderBaseChange.{u}
  exact exists_open_with_preimage_maximal_locus (@Flat.{u}) ⊤
    (fun _ _ q => Flat q ∧ LocallyOfFinitePresentation q) (fun _ _ _ _ => trivial)
    (fun f _ => ⟨_, isGreatest_maximalFlatOpen f⟩)
    (fun _ ⟨_, _⟩ hp _ hV => isGreatest_preimage_of_isPullback hp hV)
    G g ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩ trivial

end AlgebraicGeometry
