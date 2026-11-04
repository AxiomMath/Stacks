module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Acyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedForms

/-!
# Cosimplicial modules split along the vertices of the simplex are homotopic to zero

Let `K` be a cosimplicial module over a cosimplicial ring `R`.  A *slot decomposition* of `K` is a
family of `R_n`-linear projections `π_e : K_n → K_n`, one for each vertex `e ∈ [n]`, which are
orthogonal idempotents summing to the identity and which are carried to each other by the
cosimplicial structure maps: `K(f) ∘ π_e = π_{f(e)} ∘ K(f)` for `f : [n] → [m]`.  In other words
`K_n = ⊕_{e ∈ [n]} K_{n,e}` and `K(f)` maps the summand of index `e` into the summand of index
`f(e)`.

The cosimplicial module of [Stacks, Example 60.20.2, Tag 07L7], `M_n = ⊕_{e ∈ [n]} A_n e_e`, is the
basic example, and the contracting homotopy of that example works verbatim for every slot
decomposition: at the simplex `α : [n] → [1]` it is the sum of the projections `π_e` over the
vertices with `α(e) = 0`.  This is the input of the vanishing of the higher columns of the
Čech–de Rham double complex of a crystal, [Stacks, Lemma 60.21.1, Tag 07L9] and
[Stacks, Lemma 60.21.2, Tag 07LA], for a covering by several smooth lifts: the module of divided
power differentials of the divided power envelope of `U_s` in `Y_{s₀} ×_S ⋯ ×_S Y_{s_n}` is the
direct sum over the slots `e ∈ [n]` of the base changes of `Ω_{Y_{s_e}/S}`, and a map of finite
ordinals `f` sends the slot `e` to the slot `f(e)`.

## Main definitions

* `Crystalline.SlotDecomposition` — a slot decomposition of a cosimplicial module.
* `Crystalline.SlotDecomposition.homotopy` — the contracting homotopy from the identity to zero.

## Main results

* `Crystalline.SlotDecomposition.homotopic_id_zero` — a cosimplicial module with a slot
  decomposition is homotopic to zero.
* `Crystalline.SlotDecomposition.homotopic_id_tensor_exteriorPower_zero` — for every cosimplicial
  module `M` and every `a > 0`, `M ⊗ ⋀^a K` is homotopic to zero ([Stacks, Tag 07LA] in the
  uncompleted form).
* `Crystalline.SlotDecomposition.isZero_homology_tensor_exteriorPower` — so its Moore complex is
  acyclic.

## References

* [Stacks Project, Example 60.20.2, Tag 07L7](https://stacks.math.columbia.edu/tag/07L7)
* [Stacks Project, Lemma 60.21.1, Tag 07L9](https://stacks.math.columbia.edu/tag/07L9)
* [Stacks Project, Lemma 60.21.2, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public noncomputable section

namespace Crystalline

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite Simplicial
  AlgebraicTopology

universe u

variable {A : CosimplicialObject CommRingCat.{u}}

/-- The structure map of a cosimplicial module along `f : n ⟶ m`, as an additive map between the
underlying groups. -/
def cosimplicialModuleMapAdd (K : CosimplicialModule A) {n m : SimplexCategory} (f : n ⟶ m) :
    K.obj (op (op n)) →+ K.obj (op (op m)) :=
  (K.map f.op.op).hom.toAddMonoidHom

/-- `cosimplicialModuleMapAdd` is the structure map. -/
theorem cosimplicialModuleMapAdd_apply (K : CosimplicialModule A) {n m : SimplexCategory}
    (f : n ⟶ m) (x : K.obj (op (op n))) : cosimplicialModuleMapAdd K f x = K.map f.op.op x := rfl

/-- A **slot decomposition** of a cosimplicial module `K`: orthogonal idempotent `A_n`-linear
projections `π_e` of `K_n`, indexed by the vertices `e ∈ [n]` and summing to the identity, which
the cosimplicial structure map of `f : [n] → [m]` carries from the slot `e` to the slot `f(e)`. -/
structure SlotDecomposition (K : CosimplicialModule A) where
  /-- The projection onto the slot of the vertex `e ∈ [n]`. -/
  proj (n : SimplexCategory) (e : Fin (n.len + 1)) : K.obj (op (op n)) ⟶ K.obj (op (op n))
  /-- The projections sum to the identity. -/
  sum_proj (n : SimplexCategory) (x : K.obj (op (op n))) : ∑ e, proj n e x = x
  /-- The projections are orthogonal idempotents. -/
  proj_proj (n : SimplexCategory) (e e' : Fin (n.len + 1)) (x : K.obj (op (op n))) :
    proj n e' (proj n e x) = if e = e' then proj n e x else 0
  /-- The structure map of `f` carries the slot `e` to the slot `f(e)`. -/
  map_proj {n m : SimplexCategory} (f : n ⟶ m) (e : Fin (n.len + 1)) (x : K.obj (op (op n))) :
    cosimplicialModuleMapAdd K f (proj n e x) =
      proj m (f.toOrderHom e) (cosimplicialModuleMapAdd K f x)

namespace SlotDecomposition

variable {K : CosimplicialModule A} (D : SlotDecomposition K)

/-- The set of vertices of `[n]` at which a simplex `α : [n] → [1]` of `Δ[1]` vanishes. -/
def zeroSet (n : SimplexCategory) (α : (Δ[1] : SSet.{0}).obj (op n)) :
    Finset (Fin (n.len + 1)) :=
  Finset.univ.filter fun e => (SSet.stdSimplex.objEquiv.{0} α).toOrderHom e = 0

/-- The component of the contracting homotopy at the simplex `α`: the sum of the projections onto
the slots of the vertices at which `α` vanishes. -/
def homotopyApp (n : SimplexCategory) (α : (Δ[1] : SSet.{0}).obj (op n)) :
    K.obj (op (op n)) ⟶ K.obj (op (op n)) :=
  ∑ e ∈ zeroSet n α, D.proj n e

/-- The component of the homotopy on an element. -/
theorem homotopyApp_apply (n : SimplexCategory) (α : (Δ[1] : SSet.{0}).obj (op n))
    (x : K.obj (op (op n))) : D.homotopyApp n α x = ∑ e ∈ zeroSet n α, D.proj n e x := by
  simp only [homotopyApp, ModuleCat.hom_sum, LinearMap.sum_apply]

/-- The projection onto the slot `e'` of the image of `x` under a structure map is the sum of
the images of the slots of `x` lying over `e'`. -/
theorem proj_map (D : SlotDecomposition K) {n m : SimplexCategory} (f : n ⟶ m)
    (e' : Fin (m.len + 1)) (x : K.obj (op (op n))) :
    D.proj m e' (cosimplicialModuleMapAdd K f x) =
      ∑ e, (if f.toOrderHom e = e' then D.proj m (f.toOrderHom e) (cosimplicialModuleMapAdd K f x)
        else 0 : K.obj (op (op m))) := by
  conv_lhs => rw [← D.sum_proj n x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [D.map_proj, D.proj_proj]

/-- **The contracting homotopy of a slot decomposition**, from the identity to zero
([Stacks, Tag 07L7]). -/
def homotopy : Homotopy (𝟙 K) (0 : K ⟶ K) where
  app := D.homotopyApp
  naturality {n m} f α := by
    ext x
    change D.homotopyApp m α (cosimplicialModuleMapAdd K f x) =
      cosimplicialModuleMapAdd K f (D.homotopyApp n ((Δ[1] : SSet.{0}).map f.op α) x)
    rw [D.homotopyApp_apply, D.homotopyApp_apply, map_sum]
    rw [Finset.sum_congr rfl fun e' _ => D.proj_map f e' x, Finset.sum_comm]
    simp only [zeroSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_eq_single (f.toOrderHom e) (fun b _ hb => by simp [Ne.symm hb])
      (by simp), D.map_proj]
    have hc : (SSet.stdSimplex.objEquiv.{0} ((Δ[1] : SSet.{0}).map f.op α)).toOrderHom e =
        (SSet.stdSimplex.objEquiv.{0} α).toOrderHom (f.toOrderHom e) := rfl
    rw [hc]
    simp only [if_true]
  app_zero n := by
    ext x
    change D.homotopyApp n _ x = x
    rw [D.homotopyApp_apply]
    have : zeroSet n (SSet.stdSimplex.const.{0} 1 0 (op n)) = Finset.univ := by
      ext e; simp [zeroSet]; rfl
    rw [this, D.sum_proj]
  app_one n := by
    ext x
    change D.homotopyApp n _ x = 0
    rw [D.homotopyApp_apply]
    have : zeroSet n (SSet.stdSimplex.const.{0} 1 1 (op n)) = ∅ := by
      ext e
      simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      change (OrderHom.const _ (1 : Fin 2)) e ≠ 0
      simp
    rw [this, Finset.sum_empty]

include D in
/-- **A cosimplicial module with a slot decomposition is homotopic to zero**
([Stacks, Tag 07L7]). -/
theorem homotopic_id_zero : Homotopic (𝟙 K) 0 :=
  Relation.EqvGen.rel _ _ ⟨D.homotopy⟩

include D in
/-- **[Stacks, Tag 07LA], uncompleted, for a slot-decomposed module of differentials**: for every
cosimplicial module `M` and every `a > 0`, the cosimplicial module `M ⊗ ⋀^a K` is homotopic to
zero. -/
theorem homotopic_id_tensor_exteriorPower_zero (M : CosimplicialModule A) {a : ℕ} (ha : 0 < a) :
    Homotopic (𝟙 (M ⊗ (exteriorPowerFunctor A a).functor.obj K)) 0 :=
  homotopic_id_tensor_zero (homotopic_id_exteriorPower_zero ha D.homotopic_id_zero) M

include D in
/-- **The Moore complex of `M ⊗ ⋀^a K` is acyclic** for `a > 0`. -/
theorem isZero_homology_tensor_exteriorPower (M : CosimplicialModule A) {a : ℕ} (ha : 0 < a)
    (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
      ((cosimplicialModuleForget A).obj
        (M ⊗ (exteriorPowerFunctor A a).functor.obj K))).homology j) :=
  isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero
    (D.homotopic_id_tensor_exteriorPower_zero M ha) j

end SlotDecomposition

end Crystalline
