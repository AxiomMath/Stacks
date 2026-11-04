module

public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.MinimalVersal
public import StacksFrontier.Deformation.PredeformationTangent.DerivationAction
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Schlessinger.VersalImpliesS1
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential
public import StacksFrontier.Deformation.TangentSpace.SquareZero

/-!
# Bijectivity of the differential on derivation orbits (Stacks 06T6)

A formal object `ξ` of a predeformation category `p` over `R = ξ.base` has a differential
`dξ : Der_Λ(R, k) → T p`, obtained by sending a derivation to the class of the associated
morphism evaluated at the dual numbers.  Condition 06T6 asks that this map be bijective
*after* dividing both sides by the action of `Der_Λ(k, k)`: on the source that action adds
`δ ∘ q`, where `q : R → k` is the residue map, and on the target it is the action of
Stacks 06SW by the twisting automorphisms of the dual numbers.

The differential is presented as a *graph* rather than as a function, so that no choice of
pushforwards has to be fixed in order to state the condition: `derivationDifferentialGraph`
quantifies over such a choice, and the first clause of 06T6 is exactly the assertion that
the graph is single-valued, i.e. that the differential is a well-defined map independent of
the choice.  The remaining clauses are surjectivity, equivariance, and the identification of
target orbits with source orbits — note that the last clause compares *orbits*, not
individual fibres of the differential.

What is defined here only *names* the condition. That it holds is proved elsewhere, under each of
the two hypotheses under which the source asserts it:
`Deformation.minimalVersal_hasBijectiveDifferentialOnDerivationOrbits`, Stacks 06T8, establishes
all four clauses for a minimal versal formal object of a predeformation category satisfying (S2),
and `Deformation.hasBijectiveDifferentialOnDerivationOrbits_of_hasBijectiveDifferential`
establishes them for a formal object whose differential is bijective.

The same section of the source states Theorem 06IX, whose part (1) asks for a minimal versal
formal object with bijective differential. The implication (1) ⟹ (3a) is stated here under that
hypothesis; its content is the already-available Stacks 06SY, that a predeformation category with
a versal formal object satisfies Schlessinger's condition (S1).

## Main definitions

* `Deformation.HasBijectiveDifferentialOnDerivationOrbits`: **Stacks 06T6**, the condition
  itself, as a predicate on formal objects.

## Main results

* `Deformation.schlessingerConditionS1_of_minimalVersal_hasBijectiveDifferential`:
  **Stacks 06IX**, the implication (1) ⟹ (3a).

## References

* [Stacks Project, Tag 06T6](https://stacks.math.columbia.edu/tag/06T6)
* [Stacks Project, Tag 06IX](https://stacks.math.columbia.edu/tag/06IX)
-/

@[expose] public section

namespace Deformation

section

open CategoryTheory

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- The graph of the differential of a formal object, as a relation between derivations of
its underlying complete local algebra and tangent vectors of the predeformation category.
A derivation `D` is related to `y` when some choice of pushforwards and some square-zero
point `α` of `ξ.base` with square-zero component `D` has associated class `y`. -/
public noncomputable def derivationDifferentialGraph
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p)
    (D : Derivations ξ.base k)
    (y : predeformationTangentSpace.{u, v, w} p hp) : Prop :=
  let source := isomorphismClasses
    (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda ξ.base)))
    (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base))
  let dual := artinianDualNumbers.{u, w, v} Λ k
  ∃ (P : ChosenPushforwards p) (α : (restrictedCoyoneda ξ.base).obj dual),
    (∀ r : ξ.base, (α.hom r).snd.down = D r) ∧
      mapIsomorphismClasses
        (categoryOfElements_projection_isCofibered
          (restrictedCoyoneda ξ.base)) hp.cofibered
        (associatedMorphism hp.cofibered ξ P).toBasedFunctor dual
        (classOf
          (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda ξ.base)))
          (categoryOfElements_projection_isCofibered
            (restrictedCoyoneda ξ.base))
          ⟨⟨dual, α⟩, rfl⟩ : source.obj dual) = y

/-- **Stacks Project, Tag 06T6,** the condition itself. The differential of a formal object is a
well-defined, equivariant map from derivations of its underlying algebra to the tangent space,
surjective on tangent vectors, and bijective after passing to `Der_Λ(k, k)`-orbits on both
sides. That this holds for a minimal versal formal object is Stacks 06T8,
`Deformation.minimalVersal_hasBijectiveDifferentialOnDerivationOrbits`. -/
@[stacks 06T6 "the condition, as a predicate on formal objects"]
public noncomputable def HasBijectiveDifferentialOnDerivationOrbits
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p) : Prop :=
  let graph := derivationDifferentialGraph.{u, v, w} p hp ξ
  let action := (derivationAction.{u, v, w} p hp).action
  let q := residueHom ξ.base
  (∀ D : Derivations ξ.base k, ∃! y, graph D y) ∧
    (∀ y, ∃ D : Derivations ξ.base k, graph D y) ∧
    (∀ (D : Derivations ξ.base k) (δ : Derivation Λ k k) y,
      graph D y →
        ∃ E : Derivations ξ.base k,
          (∀ r : ξ.base, E r = D r + δ (q r)) ∧ graph E (action (δ, y))) ∧
    (∀ (D E : Derivations ξ.base k) y z,
      graph D y → graph E z →
        ((∃ δ : Derivation Λ k k, z = action (δ, y)) ↔
          (∃ δ : Derivation Λ k k, ∀ r : ξ.base, E r = D r + δ (q r))))

/-- **Stacks Project, Tag 06IX,** the implication (1) ⟹ (3a). Condition (1) of that theorem is
that the predeformation category have a minimal versal formal object whose differential is
bijective, Stacks 06IM; condition (3a) is Schlessinger's condition (S1). Neither the minimality
nor the bijectivity of the differential is used: versality alone gives (S1), by Stacks 06SY. -/
@[stacks 06IX "(1) implies (3a)"]
public theorem schlessingerConditionS1_of_minimalVersal_hasBijectiveDifferential
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (hξ : ∃ ξ : FormalObject p,
      IsMinimalVersal hp.cofibered ξ ∧ HasBijectiveDifferential hp.cofibered ξ) :
    SchlessingerConditionS1 p := by
  obtain ⟨ξ, ⟨hversal, -⟩, -⟩ := hξ
  exact schlessingerConditionS1_of_versal p hp ξ hversal

end

-- The content of the implication (1) ⟹ (3a) of Stacks 06IX -- a predeformation category
-- carrying a versal formal object satisfies Schlessinger's condition (S1) -- is the stronger
-- Stacks 06SY, which therefore carries the part key as well.
add_to_stacks 06IX "(1) implies (3a)" Deformation.schlessingerConditionS1_of_versal

end Deformation

end
