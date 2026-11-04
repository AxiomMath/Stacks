module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.WeightedFibreSum
public import StacksCore.Tactic.StacksAttribute

/-!
# Weightings of locally quasi-finite morphisms

An integer-valued function on the source of a locally quasi-finite morphism is a weighting if,
on every finite open piece after an étale base change, its separable-degree weighted fibre sum
is locally constant. A weighting restricts to a weighting on every open subscheme of its source.

## Main definitions

* `AlgebraicGeometry.IsWeighting` says that an integer-valued function is a weighting of a
  scheme morphism.

## Main results

* `AlgebraicGeometry.isWeighting_iff` is the defining characterization of a weighting.
* `AlgebraicGeometry.IsWeighting.isLocallyConstant` applies a weighting to a finite open piece
  of an étale base change.
* `AlgebraicGeometry.IsWeighting.comp_isOpenImmersion` shows that precomposing a morphism and
  its weighting with an open immersion preserves the weighting property.

## Implementation notes

The condition that `U` is an open subscheme of `X ×_Y V` is expressed invariantly by requiring
the morphism induced by the commutative square to be an open immersion. The fibre integral is
`AlgebraicGeometry.separableDegreeWeightedFiberSum`. The predicate itself does not need the
ambient local quasi-finiteness assumption on `f`; results about weightings impose that
assumption as in the source. For the same reason the restriction statement holds for an
arbitrary morphism, an open subscheme being represented invariantly by an open immersion into
the source.

## References

* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 0GK8](https://stacks.math.columbia.edu/tag/0GK8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An integer-valued function `w` on `X` is a weighting of `f : X ⟶ Y` if its
separable-degree weighted fibre sum is locally constant on every finite open
piece of every étale base change of `f`. -/
@[stacks 0F3A, sga "4 XVII 6.2.4" "condition (*)"]
def IsWeighting {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) : Prop :=
  ∀ {U V : Scheme.{u}} (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g),
    Etale g → IsOpenImmersion (pullback.lift h π comm) → IsFinite π →
      IsLocallyConstant (separableDegreeWeightedFiberSum π (w ∘ h))

/-- The defining characterization of a weighting in terms of finite open
pieces after étale base change. -/
theorem isWeighting_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) :
    IsWeighting f w ↔
      ∀ {U V : Scheme.{u}} (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g),
        Etale g → IsOpenImmersion (pullback.lift h π comm) → IsFinite π →
          IsLocallyConstant (separableDegreeWeightedFiberSum π (w ∘ h)) := Iff.rfl

/-- A weighting has locally constant weighted fibre sum on each finite open
piece after an étale base change. -/
theorem IsWeighting.isLocallyConstant {X Y U V : Scheme.{u}} {f : X ⟶ Y} {w : X → ℤ}
    (hw : IsWeighting f w) (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g)
    (hg : Etale g) (hU : IsOpenImmersion (pullback.lift h π comm)) (hπ : IsFinite π) :
    IsLocallyConstant (separableDegreeWeightedFiberSum π (w ∘ h)) := hw h π g comm hg hU hπ

/-- The restriction of a weighting to an open subscheme of the source is a
weighting of the restricted morphism. -/
@[stacks 0GK8]
theorem IsWeighting.comp_isOpenImmersion {X' X Y : Scheme.{u}}
    (j : X' ⟶ X) [IsOpenImmersion j] {f : X ⟶ Y} {w : X → ℤ}
    (hw : IsWeighting f w) : IsWeighting (j ≫ f) (w ∘ j) := by
    intro U V h π g comm hg hU hπ
    let i := Limits.pullback.map (j ≫ f) g f g j (𝟙 _) (𝟙 _) (by simp) (by simp)
    have comm' : (h ≫ j) ≫ f = π ≫ g := by simpa [Category.assoc] using comm
    have heq : Limits.pullback.lift h π comm ≫ i =
        Limits.pullback.lift (h ≫ j) π comm' := by
      apply Limits.pullback.hom_ext <;>
        simp only [i, Limits.pullback.map, Category.assoc, Limits.pullback.lift_fst_assoc,
          Limits.pullback.lift_fst, Limits.pullback.lift_snd, Category.comp_id]
    simpa [Category.assoc, Function.comp_def] using
      (hw (h ≫ j) π g comm' hg (by rw [← heq]; infer_instance) hπ)

end AlgebraicGeometry
