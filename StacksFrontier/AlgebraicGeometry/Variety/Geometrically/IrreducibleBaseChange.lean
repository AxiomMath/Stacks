module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometric irreducibility after a field extension

Geometric irreducibility of a scheme over a field can be checked after extending the base
field.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_iff_baseChange_fieldExtension`: a scheme over a
  field is geometrically irreducible if and only if its base change to any field extension is
  geometrically irreducible.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`. Its base change
along `k → k'` is represented by the canonical pullback projection to `Spec k'`.

## References

* [Stacks Project, Tag 054P](https://stacks.math.columbia.edu/tag/054P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open CommRingCat

universe u

/-- **Stacks Project, Tag 054P.** A scheme over a field is geometrically irreducible if and only
if its base change along any field extension is geometrically irreducible. -/
@[stacks 054P]
public theorem geometricallyIrreducible_iff_baseChange_fieldExtension
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (of k)) :
    GeometricallyIrreducible f ↔
      GeometricallyIrreducible
        (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) := by
  refine ⟨fun _ => inferInstance, fun h => ?_⟩
  rw [GeometricallyIrreducible.eq_geometrically] at h ⊢
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  obtain ⟨M, _, _, _, _, _, _⟩ := exists_common_extension k k' K
  let φ := Spec.map (ofHom (algebraMap k k'))
  let θ := Spec.map (ofHom (algebraMap k' M))
  let A : Scheme.{u} := pullback (pullback.snd f φ) θ
  have : IrreducibleSpace A :=
    (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mp h) M
  let χ : Spec (of M) ⟶ Spec (of K) := Spec.map (ofHom (algebraMap K M))
  let ψ : Spec (of K) ⟶ Spec (of k) := Spec.map (ofHom (algebraMap k K))
  let μ : Spec (of M) ⟶ Spec (of k) := Spec.map (ofHom (algebraMap k M))
  obtain ⟨hcomp, hcomp'⟩ : χ ≫ ψ = μ ∧ θ ≫ φ = μ := by
    constructor <;> dsimp only [χ, ψ, θ, φ, μ] <;>
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let e₁ := pullbackRightPullbackFstIso φ f θ ≪≫ pullback.congrHom hcomp' rfl
  let e₂ := pullbackRightPullbackFstIso ψ f χ ≪≫ pullback.congrHom hcomp rfl
  let q : A ⟶ pullback θ (pullback.fst φ f) :=
    (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) (pullbackSymmetry _ _).hom (𝟙 _) (by simp) (by simp)
  let r := q ≫ e₁.hom ≫ e₂.inv ≫ pullback.snd χ (pullback.fst ψ f) ≫
    (pullbackSymmetry ψ f).hom
  exact r.surjective.irreducibleSpace r.continuous

end AlgebraicGeometry
