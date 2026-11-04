module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAlgebra
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage

/-!
# Localising property (B) on the base

Property (B) for a morphism `f : X ⟶ Y` is reduced by
`Stacks.EtaleCohomology.hasPropertyB_of_etaleNeighborhood_decomposition` to the production of a
single decomposition over an étale neighbourhood of each point of each étale base `V ⟶ Y`. This
file names that remaining task — `Stacks.EtaleCohomology.HasLocalDecompositionAt` — and shows
that it may be checked after an arbitrary étale base change of `V`.

Taking the base change to be the inclusion of an affine open neighbourhood of the point is the
first step of the proof of the finite case [Stacks, Tag 04DQ]: over an affine `V₀` the fibre
product `X ×ₗᵧ V₀` is itself affine, because it is finite over `V₀`, and the whole question
becomes one about rings. The ring-theoretic steps are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAlgebra`.

## Main definitions

* `Stacks.EtaleCohomology.HasLocalDecompositionAt` is the decomposition over one étale
  neighbourhood of one point that property (B) is reduced to.

## Main results

* `Stacks.EtaleCohomology.hasPropertyB_of_hasLocalDecompositionAt` restates
  `hasPropertyB_of_etaleNeighborhood_decomposition` in terms of `HasLocalDecompositionAt`.
* `Stacks.EtaleCohomology.HasLocalDecompositionAt.of_etale` localises the question on the base:
  it suffices to answer it after any étale base change of `V` which hits the given point.
* `Stacks.EtaleCohomology.HasLocalDecompositionAt.of_refinement` relaxes
  `HasLocalDecompositionAt` using
  `Stacks.EtaleCohomology.exists_subordinate_decomposition_of_refinement`: the decomposition may be
  produced with an arbitrary index type together with a map to the index type of the covering.

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- The local form of property (B) at a point: over some étale neighbourhood `N` of `v` the fibre
product `X ×ₗᵧ V` breaks up as a disjoint union of pieces indexed by the given covering `U`, the
piece with index `i` mapping to `U.X i` over `X ×ₗᵧ V`. The comparison morphism `q` between the
two fibre products is carried together with its two defining equations, which pin it down.

This is exactly the hypothesis of `hasPropertyB_of_etaleNeighborhood_decomposition`, whose content
is that property (B) follows from it. -/
def HasLocalDecompositionAt {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Scheme.{u}} (g : V ⟶ Y)
    (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V) : Prop :=
  ∃ (N : EtaleNeighborhood V v) (q : pullback f (N.toBase ≫ g) ⟶ pullback f g),
    q ≫ pullback.fst f g = pullback.fst f (N.toBase ≫ g) ∧
    q ≫ pullback.snd f g = pullback.snd f (N.toBase ≫ g) ≫ N.toBase ∧
    ∃ (W : U.I₀ → Scheme.{u}) (e : (∐ W) ≅ pullback f (N.toBase ≫ g)) (a : ∀ i, W i ⟶ U.X i),
      ∀ i, a i ≫ U.f i = Sigma.ι W i ≫ e.hom ≫ q

/-- Property (B) holds as soon as the local decomposition exists at every point of every étale
base. This is `hasPropertyB_of_etaleNeighborhood_decomposition` phrased with
`HasLocalDecompositionAt`. -/
theorem hasPropertyB_of_hasLocalDecompositionAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ {V : Scheme.{u}} (g : V ⟶ Y) [Etale g]
      (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V),
      HasLocalDecompositionAt f g U v) :
    HasPropertyB f := by
  refine hasPropertyB_of_etaleNeighborhood_decomposition f ?_
  intro V g hg U v
  exact h g U v

/-- Étale morphisms preserve joint surjectivity under base change. -/
instance etale_isJointlySurjectivePreserving :
    Scheme.IsJointlySurjectivePreserving @Etale :=
  Scheme.isJointlySurjectivePreserving @Etale

/-- **The local form of property (B) may be checked after an étale base change of the base.** Let
`n : V' ⟶ V` be étale and let `v'` be a point of `V'` over `v`. If the local decomposition exists
at `v'` for the base `n ≫ g` and the covering obtained from `U` by base change along the
comparison morphism `m : X ×ₗᵧ V' ⟶ X ×ₗᵧ V`, then it exists at `v` for `g` and `U`.

An étale neighbourhood of `v'` in `V'` is one of `v` in `V`, and the two fibre products over it
agree; the pieces of the decomposition are reused unchanged, their maps to the members of the
pulled-back covering being composed with the projections of that base change.

The comparison morphism is carried with its two defining equations, which pin it down; the
canonical choice is `pullbackBaseChangeMap f g n` together with `pullbackBaseChangeMap_fst` and
`pullbackBaseChangeMap_snd`.

Taking `n` to be the inclusion of an affine open neighbourhood of `v` is how the finite case of
property (B), [Stacks, Tag 04DQ], reduces to a statement about rings. -/
theorem HasLocalDecompositionAt.of_etale {X Y V V' : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y)
    [Etale g] (n : V' ⟶ V) [Etale n] (m : pullback f (n ≫ g) ⟶ pullback f g)
    (hm₁ : m ≫ pullback.fst f g = pullback.fst f (n ≫ g))
    (hm₂ : m ≫ pullback.snd f g = pullback.snd f (n ≫ g) ≫ n)
    (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V) (v' : V') (hv : n v' = v)
    (h : HasLocalDecompositionAt f (n ≫ g) (U.pullback₁ m) v') :
    HasLocalDecompositionAt f g U v := by
  obtain ⟨N, q, hq₁, hq₂, W, e, a, ha⟩ := h
  let N₂ : EtaleNeighborhood V v :=
    { scheme := N.scheme
      point := N.point
      toBase := N.toBase ≫ n
      map_point := by
        calc (N.toBase ≫ n) N.point = n (N.toBase N.point) := rfl
          _ = n v' := by rw [N.map_point]
          _ = v := hv }
  let q₂ : pullback f (N₂.toBase ≫ g) ⟶ pullback f (n ≫ g) := q
  let e₂ : (∐ W) ≅ pullback f (N₂.toBase ≫ g) := e
  have hq₁' : q₂ ≫ pullback.fst f (n ≫ g) = pullback.fst f (N₂.toBase ≫ g) := hq₁
  have hq₂' : q₂ ≫ pullback.snd f (n ≫ g) = pullback.snd f (N₂.toBase ≫ g) ≫ N.toBase := hq₂
  have ha' : ∀ i, a i ≫ pullback.fst m (U.f i) = Sigma.ι W i ≫ e₂.hom ≫ q₂ := ha
  refine ⟨N₂, q₂ ≫ m, by rw [Category.assoc q₂, hm₁, hq₁'], by
    rw [Category.assoc q₂, hm₂, reassoc_of% hq₂'], W, e₂, fun i => a i ≫ pullback.snd m (U.f i),
    fun i => ?_⟩
  exact ((Category.assoc _ _ _).trans (congrArg (a i ≫ ·) pullback.condition.symm)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m) (ha' i)).trans (Category.assoc _ _ _)))

section Regrouping

/-- **The local decomposition may be produced with any index type refining the covering.** To
verify `HasLocalDecompositionAt` it suffices to produce, over some étale neighbourhood `N` of the
point, a decomposition of the fibre product indexed by an arbitrary type `L` together with a map
`idx : L → U.I₀` saying which member of the covering each piece maps to; the pieces are then
regrouped under the indices of `U` by `exists_subordinate_decomposition_of_refinement`.

This is the form in which the finite case of property (B), [Stacks, Tag 04DQ], produces its
decomposition: the pieces come from a finite affine refinement of the given covering and are
therefore indexed by the refinement, not by the covering. -/
theorem HasLocalDecompositionAt.of_refinement {X Y V : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y)
    (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V)
    (N : EtaleNeighborhood V v) (q : pullback f (N.toBase ≫ g) ⟶ pullback f g)
    (hq₁ : q ≫ pullback.fst f g = pullback.fst f (N.toBase ≫ g))
    (hq₂ : q ≫ pullback.snd f g = pullback.snd f (N.toBase ≫ g) ≫ N.toBase)
    {L : Type u} (T : L → Scheme.{u}) (idx : L → U.I₀)
    (ε : (∐ T) ≅ pullback f (N.toBase ≫ g)) (α : ∀ l, T l ⟶ U.X (idx l))
    (hα : ∀ l, α l ≫ U.f (idx l) = Sigma.ι T l ≫ ε.hom ≫ q) :
    HasLocalDecompositionAt f g U v := by
  obtain ⟨A, e', b, hb⟩ := exists_subordinate_decomposition_of_refinement idx T U.X
    (pullback f (N.toBase ≫ g)) (pullback f g) ε α U.f q hα
  exact ⟨N, q, hq₁, hq₂, A, e', b, hb⟩

end Regrouping

end Stacks.EtaleCohomology

end
