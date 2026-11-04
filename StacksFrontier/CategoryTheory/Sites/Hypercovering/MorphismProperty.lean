module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal.Existence

/-!
# Hypercoverings for a property of morphisms

Let `P` be a property of morphisms of a category `C` with fibre products. A `P`-*hypercovering* is
an augmented simplicial object `U ⟶ X` of `C` whose augmentation in degree zero, whose canonical
degree-one morphism `U₁ ⟶ U₀ ×_X U₀`, and whose higher matching morphisms
`U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` all belong to `P`.

## Main definitions

* `SimplicialObject.Augmented.over`: an augmented simplicial object, regarded as a simplicial
  object of the slice category over the point of its augmentation.
* `SimplicialObject.Augmented.firstMatchingArrow`: the canonical morphism `U₁ ⟶ U₀ ×_X U₀`.
* `SimplicialObject.Augmented.matchingArrow`: the canonical morphism from level `n + 1` to the
  degree-`n + 1` term of the `n`-th relative coskeleton.
* `MorphismProperty.IsHypercovering`: the predicate that those three families of morphisms belong
  to `P` (Tag 0DER).

## Main results

The `simp` API of `firstMatchingArrow` identifies its domain and codomain and its composites with
the two pullback projections; the fields of `MorphismProperty.IsHypercovering` expose the three
defining conditions.

## Implementation notes

The coskeleton is computed in the slice category over the point of the augmentation, exactly as in
the source, and the resulting morphism is then forgotten down to `C`; both `firstMatchingArrow`
and `matchingArrow` are packaged as objects of `Arrow C` so that their domain and codomain are
available to a client without naming the coskeleton. The degree-one condition is stated directly
in terms of the chosen fibre product `U₀ ×_X U₀`, with
`firstMatchingArrow_hom_fst` and `firstMatchingArrow_hom_snd` recording that the components of
`firstMatchingArrow` are the two face maps. The coskeleton clause is restricted to `n ≥ 1`, as in
the source, the cases `n = 0` and `n = 1` being covered by the first two clauses.

No stability, composition or isomorphism hypothesis on `P` is needed to state the predicate;
those are hypotheses of the subsequent properties of hypercoverings, not of the definition.

## References

* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory

namespace SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- An augmented simplicial object, regarded as a simplicial object of the slice category over
the point of its augmentation. -/
@[implicit_reducible]
noncomputable def over (A : SimplicialObject.Augmented C) : SimplicialObject (Over A.right) :=
  A.left.toOver A.right (fun n ↦ A.hom.app n) (fun g ↦ by simp)

variable [HasPullbacks C]

/-- The canonical morphism `U₁ ⟶ U₀ ×_X U₀` of an augmented simplicial object, whose components
are its two face maps, presented as an object of `Arrow C`. -/
@[implicit_reducible, sga "4 V 7.3.1.1"]
noncomputable def firstMatchingArrow (A : SimplicialObject.Augmented C) : Arrow C :=
  Arrow.mk (pullback.lift (f := A.hom.app (op (SimplexCategory.mk 0)))
    (g := A.hom.app (op (SimplexCategory.mk 0)))
    (A.left.δ 1) (A.left.δ 0) (by simp [SimplicialObject.δ]))

/-- The domain of `firstMatchingArrow` is the degree-one term. -/
@[simp]
lemma firstMatchingArrow_left (A : SimplicialObject.Augmented C) :
    (firstMatchingArrow A).left = A.left.obj (op (SimplexCategory.mk 1)) :=
  rfl

/-- The codomain of `firstMatchingArrow` is the fibre product `U₀ ×_X U₀`. -/
@[simp]
lemma firstMatchingArrow_right (A : SimplicialObject.Augmented C) :
    (firstMatchingArrow A).right =
      pullback (A.hom.app (op (SimplexCategory.mk 0)))
        (A.hom.app (op (SimplexCategory.mk 0))) :=
  rfl

/-- The first component of `firstMatchingArrow` is the face map `δ 1`. -/
@[reassoc (attr := simp)]
lemma firstMatchingArrow_hom_fst (A : SimplicialObject.Augmented C) :
    (firstMatchingArrow A).hom ≫
        pullback.fst (A.hom.app (op (SimplexCategory.mk 0)))
          (A.hom.app (op (SimplexCategory.mk 0))) = A.left.δ 1 :=
  pullback.lift_fst _ _ _

/-- The second component of `firstMatchingArrow` is the face map `δ 0`. -/
@[reassoc (attr := simp)]
lemma firstMatchingArrow_hom_snd (A : SimplicialObject.Augmented C) :
    (firstMatchingArrow A).hom ≫
        pullback.snd (A.hom.app (op (SimplexCategory.mk 0)))
          (A.hom.app (op (SimplexCategory.mk 0))) = A.left.δ 0 :=
  pullback.lift_snd _ _ _

/-- The canonical matching morphism `U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` of an augmented simplicial
object, presented as an object of `Arrow C`. The coskeleton is formed in the slice category over
the point of the augmentation, and the resulting morphism is then forgotten down to `C`. -/
@[sga "4 V 7.3.1.1", sga "4 V 7.3.3" "special case"]
noncomputable def matchingArrow (A : SimplicialObject.Augmented C) (n : ℕ) : Arrow C := by
  letI : HasFiniteLimits (Over A.right) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : ∀ F : SimplicialObject.Truncated (Over A.right) n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F := by
    intro F
    rcases n with _ | n
    · exact (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
        (C := Over A.right)).1 inferInstance F
    · exact (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
        (C := Over A.right)).2 (fun _ ↦ inferInstance) (n + 1) (by omega) F
  exact Arrow.mk ((Over.forget A.right).map
    (((SimplicialObject.coskAdj n).unit.app (over A)).app (op ⦋n + 1⦌)))

/-- The domain of the `n`-th matching morphism is the degree-`n + 1` term. -/
@[simp]
lemma matchingArrow_left (A : SimplicialObject.Augmented C) (n : ℕ) :
    (matchingArrow A n).left = A.left.obj (op ⦋n + 1⦌) :=
  rfl

end SimplicialObject.Augmented

/-- **Stacks Project, Tag 0DER.** An augmented simplicial object is a `P`-hypercovering when its
degree-zero augmentation, its canonical degree-one morphism to `U₀ ×_X U₀`, and all of its higher
matching morphisms belong to `P`. -/
@[stacks 0DER "p_hypercovering"]
structure MorphismProperty.IsHypercovering {C : Type u} [Category.{v} C] [HasPullbacks C]
    (P : MorphismProperty C) (A : SimplicialObject.Augmented C) : Prop where
  /-- The augmentation `U₀ ⟶ X` belongs to `P`. -/
  map_zero : P (A.hom.app (Opposite.op ⦋0⦌))
  /-- The canonical morphism `U₁ ⟶ U₀ ×_X U₀` belongs to `P`. -/
  map_one : P (SimplicialObject.Augmented.firstMatchingArrow A).hom
  /-- For every `n ≥ 1`, the matching morphism `U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` belongs
  to `P`. -/
  matching : ∀ n : ℕ, 1 ≤ n → P (SimplicialObject.Augmented.matchingArrow A n).hom

end CategoryTheory

end
