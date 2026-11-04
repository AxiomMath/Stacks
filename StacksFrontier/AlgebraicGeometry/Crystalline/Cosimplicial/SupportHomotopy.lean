module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Cosimplicial

/-!
# Cosimplicial objects with support projections are homotopic to zero

Let `K` be a cosimplicial object of a preadditive category.  A *family of support projections* on
`K` assigns to every subset `Z ⊆ [n]` of the vertices of `Δ[n]` an endomorphism `Q_Z` of `K_n`
("the part of `K_n` supported on `Z`") such that `Q_{[n]} = 1`, `Q_∅ = 0` and, for every
`f : [n] → [m]`, `K(f) ∘ Q_{f⁻¹ Z} = Q_Z ∘ K(f)`.

The basic example is a module decomposed along the vertices,
`K_n = ⊕_{e ∈ [n]} K_{n,e}` with `K(f)` carrying the summand `e` into the summand `f(e)`, where
`Q_Z` is the projection onto `⊕_{e ∈ Z} K_{n,e}` ([Stacks, Example 60.20.2, Tag 07L7]); and,
for every `a > 0`, the `a`-th exterior power of such a module (possibly tensored with an
arbitrary cosimplicial module), where `Q_Z = ⋀^a` of that projection, which vanishes at `Z = ∅`
precisely because `a > 0`.  This is the shape of the vanishing of the higher columns of the
Čech–de Rham double complex of a crystal ([Stacks, Lemma 60.21.2, Tag 07LA]).

The contracting homotopy is `h_α = Q_{α⁻¹(0)}` at the simplex `α : [n] → [1]`.

## Main definitions

* `Crystalline.SupportProjections` — a family of support projections.
* `Crystalline.SupportProjections.homotopyApp` — the components of the contracting homotopy.

## Main results

* `Crystalline.SupportProjections.homotopic_alternatingCofaceMapComplex` — the identity of the
  Moore complex of `K` is chain homotopic to zero.
* `Crystalline.SupportProjections.isZero_homology` — the Moore complex of `K` is acyclic in
  every degree.

## References

* [Stacks Project, Example 60.20.2, Tag 07L7](https://stacks.math.columbia.edu/tag/07L7)
* [Stacks Project, Lemma 60.21.2, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 01A0](https://stacks.math.columbia.edu/tag/01A0)
-/

@[expose] public noncomputable section

namespace Crystalline

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **A family of support projections** on a cosimplicial object `K`: for every subset `Z` of the
vertices of `Δ[n]` an endomorphism `Q_Z` of `K_n`, with `Q_{[n]} = 1`, `Q_∅ = 0`, and
`K(f) ∘ Q_{f⁻¹ Z} = Q_Z ∘ K(f)` for every `f : [n] → [m]`. -/
structure SupportProjections (K : CosimplicialObject C) where
  /-- The part of `K_n` supported on a set of vertices. -/
  proj (n : SimplexCategory) (Z : Set (Fin (n.len + 1))) : K.obj n ⟶ K.obj n
  /-- Everything is supported on the set of all vertices. -/
  proj_univ (n : SimplexCategory) : proj n Set.univ = 𝟙 _
  /-- Nothing is supported on the empty set of vertices. -/
  proj_empty (n : SimplexCategory) : proj n ∅ = 0
  /-- The structure maps carry the part supported on `f⁻¹ Z` to the part supported on `Z`. -/
  map_proj {n m : SimplexCategory} (f : n ⟶ m) (Z : Set (Fin (m.len + 1))) :
    K.map f ≫ proj m Z = proj n (f.toOrderHom ⁻¹' Z) ≫ K.map f

namespace SupportProjections

variable {K : CosimplicialObject C} (Q : SupportProjections K)

/-- The set of vertices of `[n]` at which a simplex `α : [n] → [1]` of `Δ[1]` vanishes. -/
def zeroSet (n : SimplexCategory) (α : (Δ[1] : SSet.{0}).obj (op n)) : Set (Fin (n.len + 1)) :=
  {e | (SSet.stdSimplex.objEquiv.{0} α).toOrderHom e = 0}

/-- **The component of the contracting homotopy at the simplex `α`**: the part supported on the
vertices at which `α` vanishes. -/
def homotopyApp (n : SimplexCategory) (α : (Δ[1] : SSet.{0}).obj (op n)) :
    K.obj n ⟶ K.obj n :=
  Q.proj n (zeroSet n α)

/-- The zero set of a reindexed simplex is the preimage of the zero set. -/
theorem zeroSet_map {n m : SimplexCategory} (g : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)) :
    zeroSet n ((Δ[1] : SSet.{0}).map g.op α) = g.toOrderHom ⁻¹' zeroSet m α := rfl

/-- The constant simplex at `0` vanishes everywhere. -/
theorem zeroSet_const_zero (n : SimplexCategory) :
    zeroSet n (SSet.stdSimplex.const.{0} 1 0 (op n)) = Set.univ := by
  ext e
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rfl

/-- The constant simplex at `1` vanishes nowhere. -/
theorem zeroSet_const_one (n : SimplexCategory) :
    zeroSet n (SSet.stdSimplex.const.{0} 1 1 (op n)) = ∅ := by
  ext e
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  change (OrderHom.const _ (1 : Fin 2)) e ≠ 0
  simp

include Q in
/-- **The Moore complex of a cosimplicial object with support projections is chain homotopic to
zero**: the identity and the zero endomorphism of `K` are homotopic through
`h_α = Q_{α⁻¹(0)}` ([Stacks, Tag 07L7]), and the Moore complex carries homotopic morphisms to
homotopic maps ([Stacks, Tag 01A0]). -/
theorem homotopic_alternatingCofaceMapComplex :
    homotopic C (ComplexShape.up ℕ) ((alternatingCofaceMapComplex C).map (𝟙 K))
      ((alternatingCofaceMapComplex C).map (0 : K ⟶ K)) := by
  refine AlgebraicTopology.homotopic_alternatingCofaceMapComplex_map
    (Relation.EqvGen.rel _ _ ⟨Q.homotopyApp, fun n m g α => ?_, fun n => ?_, fun n => ?_⟩)
  · rw [homotopyApp, homotopyApp, zeroSet_map]
    exact Q.map_proj g (zeroSet m α)
  · rw [homotopyApp, zeroSet_const_zero, Q.proj_univ]
    rfl
  · rw [homotopyApp, zeroSet_const_one, Q.proj_empty]
    rfl

include Q in
/-- **A cosimplicial object with support projections has acyclic Moore complex**, in every
degree. -/
theorem isZero_homology [CategoryWithHomology C] (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex C).obj K).homology j) := by
  obtain ⟨ho⟩ := Q.homotopic_alternatingCofaceMapComplex
  have hid := ho.homologyMap_eq j
  have h0 : (alternatingCofaceMapComplex C).map (0 : K ⟶ K) = 0 := by
    ext n
    rfl
  rw [(alternatingCofaceMapComplex C).map_id, h0, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at hid
  exact (IsZero.iff_id_eq_zero _).2 hid

end SupportProjections

end Crystalline
