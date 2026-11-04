module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnections
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamZigzag07Q9

/-!
# Base change of a cosimplicial module along a morphism of cosimplicial divided power algebras

Let `g : E ⟶ E'` be a morphism of cosimplicial divided power algebras, with completed rings
`D(b)` and `D'(b)`, and let `M(•)` be a cosimplicial module over `D(•)`.  This file builds the
cosimplicial module `M'(•)` over `D'(•)` with

`M'(b) = (D'(b) ⊗_{D(b)} M(b))^∧`,

the completed base change of `M(b)` along the component `g_b : D(b) → D'(b)`, its transition
maps being the completions of `D'(φ) ⊗ M(φ)`, together with the semilinear maps
`M(b) → M'(b)`, `m ↦ 1 ⊗ m`, which commute with the transitions.  This is the comparison of the
cosimplicial modules of a crystal over two cosimplicial envelopes used in the proof of
[Stacks, Lemma 60.22.4, Tag 07Q9].

## Main definitions

* `Crystalline.CosimplicialDPAlgebra.Hom.completedAlgebra07Q9` — `D'(b)` as a `D(b)`-algebra
  along `g_b`.
* `Crystalline.CosimplicialCompletedModule.pullback07Q9` — **the base change `M'(•)`**.
* `Crystalline.CosimplicialCompletedModule.pullbackApp07Q9` — the maps `M(b) → M'(b)`.

## Main results

* `Crystalline.CosimplicialDPAlgebra.Hom.completedRingMap_naturality07Q9` — the components of
  `g` on the completed rings commute with the transitions.
* `Crystalline.CosimplicialCompletedModule.pullbackApp07Q9_naturality` — the maps `M(b) → M'(b)`
  commute with the transitions.
* `Crystalline.CosimplicialCompletedModule.comparisonValues_tensorMap07Q9` — so do the maps they
  induce on `M(b) ⊗̂ Ω^a_{D(b)} → M'(b) ⊗̂ Ω^a_{D'(b)}`
  (in `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/PairBaseChangeConnection07Q9.lean`).
* `Crystalline.CosimplicialCompletedModule.pullback07Q9_isAdicComplete` — the modules `M'(b)` are
  `p`-adically complete.

## References

* [Stacks Project, Lemma 60.22.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Simplicial
open scoped TensorProduct

namespace Crystalline

namespace CosimplicialDPAlgebra.Hom

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} (g : E.Hom E')
  (p : ℕ)

/-- **`D'(b)` as a `D(b)`-algebra along the component `g_b` of a morphism of cosimplicial divided
power algebras.** -/
abbrev completedAlgebra07Q9 (b : ℕ) : Algebra (E.completedRing p b) (E'.completedRing p b) :=
  (g.completedRingMap p b).toAlgebra

/-- **The components of a morphism of cosimplicial divided power algebras on the completed rings
commute with the transitions**: `D'(φ) ∘ g_m = g_n ∘ D(φ)`. -/
theorem completedRingMap_naturality07Q9 {m n : SimplexCategory} (φ : m ⟶ n)
    (x : E.completedRing p m.len) :
    E'.completedRingMap p φ (g.completedRingMap p m.len x) =
      g.completedRingMap p n.len (E.completedRingMap p φ x) :=
  (adicCompletionMapₛₗ_comp_apply (ringHomₛₗ (g.app m.len).toRingHom)
      (ringHomₛₗ (E'.map φ).toRingHom) (ringHomₛₗ ((E'.map φ).comp (g.app m.len)).toRingHom)
      _ _ (map_pAdicIdeal_le p _) (fun _ => rfl) x).symm.trans
    (adicCompletionMapₛₗ_comp_apply (ringHomₛₗ (E.map φ).toRingHom)
      (ringHomₛₗ (g.app n.len).toRingHom)
      (ringHomₛₗ ((E'.map φ).comp (g.app m.len)).toRingHom) _ _ (map_pAdicIdeal_le p _)
      (fun y => (DFunLike.congr_fun (g.naturality φ) y).symm) x)

end CosimplicialDPAlgebra.Hom

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, u, u} E p) (g : E.Hom E')

/-- The transition `D'(m) → D'(n)` of the target scalars, semilinear over the transition
`D(m) → D(n)` for the module structures along `g`. -/
def pullbackScalarMap07Q9 {m n : SimplexCategory} (φ : m ⟶ n) :
    letI := g.completedAlgebra07Q9 p m.len
    letI := g.completedAlgebra07Q9 p n.len
    E'.completedRing p m.len →ₛₗ[E.completedRingMap p φ] E'.completedRing p n.len :=
  letI := g.completedAlgebra07Q9 p m.len
  letI := g.completedAlgebra07Q9 p n.len
  { toFun := E'.completedRingMap p φ
    map_add' := map_add _
    map_smul' := fun c x => by
      change E'.completedRingMap p φ (g.completedRingMap p m.len c * x) =
        g.completedRingMap p n.len (E.completedRingMap p φ c) * E'.completedRingMap p φ x
      rw [map_mul, g.completedRingMap_naturality07Q9] }

/-- The uncompleted transition `D'(m) ⊗_{D(m)} M(m) → D'(n) ⊗_{D(n)} M(n)`, the tensor product
of the transitions of the scalars and of the modules, semilinear over `D'(φ)`. -/
def pullbackTensorMap07Q9 {m n : SimplexCategory} (φ : m ⟶ n) :
    letI := g.completedAlgebra07Q9 p m.len
    letI := g.completedAlgebra07Q9 p n.len
    (E'.completedRing p m.len ⊗[E.completedRing p m.len] V.carrier m.len) →ₛₗ[
      E'.completedRingMap p φ]
      (E'.completedRing p n.len ⊗[E.completedRing p n.len] V.carrier n.len) :=
  letI := g.completedAlgebra07Q9 p m.len
  letI := g.completedAlgebra07Q9 p n.len
  { toFun := TensorProduct.map (pullbackScalarMap07Q9 g φ) (V.map φ)
    map_add' := map_add _
    map_smul' := fun c y => by
      induction y using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul x v =>
        rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
          TensorProduct.smul_tmul']
        change E'.completedRingMap p φ (c * x) ⊗ₜ[E.completedRing p n.len] V.map φ v =
          (E'.completedRingMap p φ c * E'.completedRingMap p φ x) ⊗ₜ[E.completedRing p n.len]
            V.map φ v
        rw [map_mul]
      | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add] }

/-- The uncompleted transition on a pure tensor. -/
theorem pullbackTensorMap07Q9_tmul {m n : SimplexCategory} (φ : m ⟶ n)
    (c : E'.completedRing p m.len) (x : V.carrier m.len) :
    letI := g.completedAlgebra07Q9 p m.len
    letI := g.completedAlgebra07Q9 p n.len
    V.pullbackTensorMap07Q9 g φ (c ⊗ₜ[E.completedRing p m.len] x) =
      E'.completedRingMap p φ c ⊗ₜ[E.completedRing p n.len] V.map φ x :=
  rfl

/-- **The base change `M'(•)` of a cosimplicial module `M(•)` along a morphism `g : E ⟶ E'` of
cosimplicial divided power algebras**: in degree `b` the completed base change
`(D'(b) ⊗_{D(b)} M(b))^∧` along `g_b`, with the completions of `D'(φ) ⊗ M(φ)` as transitions. -/
def pullback07Q9 : CosimplicialCompletedModule.{u, u, u} E' p where
  carrier b := letI := g.completedAlgebra07Q9 p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p b) (E'.completedRing p b)
      (V.carrier b)
  addCommGroup b := by
    letI := g.completedAlgebra07Q9 p b
    infer_instance
  module b := by
    letI := g.completedAlgebra07Q9 p b
    infer_instance
  map φ := adicCompletionMapₛₗ (V.pullbackTensorMap07Q9 g φ) (map_pAdicIdeal_le p _)
  map_id_apply n x := by
    let := g.completedAlgebra07Q9 p n.len
    refine adicCompletionMapₛₗ_id_apply _ _ (fun y => ?_) x
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul c v =>
      rw [pullbackTensorMap07Q9_tmul, V.map_id_apply]
      exact congrArg (fun z => z ⊗ₜ[E.completedRing p n.len] v)
        (E'.completedRingMap_id p n c)
    | add y z hy hz => rw [map_add, hy, hz]
  map_comp_apply {m n k} φ ψ x := by
    let := g.completedAlgebra07Q9 p m.len
    let := g.completedAlgebra07Q9 p n.len
    let := g.completedAlgebra07Q9 p k.len
    refine adicCompletionMapₛₗ_comp_apply _ _ _ _ _ _ (fun y => ?_) x
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul c v =>
      rw [pullbackTensorMap07Q9_tmul, pullbackTensorMap07Q9_tmul, pullbackTensorMap07Q9_tmul,
        V.map_comp_apply]
      exact congrArg (fun z => z ⊗ₜ[E.completedRing p k.len] V.map ψ (V.map φ v))
        (E'.completedRingMap_comp p φ ψ c)
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

/-- The module of the base change in degree `b` is the completed base change of `M(b)`. -/
theorem pullback07Q9_carrier (b : ℕ) :
    (V.pullback07Q9 g).carrier b = letI := g.completedAlgebra07Q9 p b
      CompletedConnection.baseChangeCarrier p (E.completedRing p b) (E'.completedRing p b)
        (V.carrier b) :=
  rfl

/-- The transition of the base change on the image of an uncompleted pure tensor. -/
theorem pullback07Q9_map_of {m n : SimplexCategory} (φ : m ⟶ n) (c : E'.completedRing p m.len)
    (x : V.carrier m.len) :
    letI := g.completedAlgebra07Q9 p m.len
    letI := g.completedAlgebra07Q9 p n.len
    (V.pullback07Q9 g).map φ (AdicCompletion.of (DividedPowers.pAdicIdeal p)
        (E'.completedRing p m.len ⊗[E.completedRing p m.len] V.carrier m.len)
        (c ⊗ₜ[E.completedRing p m.len] x)) =
      AdicCompletion.of (DividedPowers.pAdicIdeal p)
        (E'.completedRing p n.len ⊗[E.completedRing p n.len] V.carrier n.len)
        (E'.completedRingMap p φ c ⊗ₜ[E.completedRing p n.len] V.map φ x) :=
  adicCompletionMapₛₗ_of _ _ _

/-- **The map `M(b) → M'(b)`, `m ↦ 1 ⊗ m`**, semilinear over `g_b`. -/
def pullbackApp07Q9 (b : ℕ) :
    V.carrier b →ₛₗ[g.completedRingMap p b] (V.pullback07Q9 g).carrier b :=
  letI := g.completedAlgebra07Q9 p b
  CompletedConnection.baseChangeInclusion p (E.completedRing p b) (E'.completedRing p b)
    (V.carrier b)

/-- The map `M(b) → M'(b)` as a formula. -/
theorem pullbackApp07Q9_apply (b : ℕ) (x : V.carrier b) :
    letI := g.completedAlgebra07Q9 p b
    V.pullbackApp07Q9 g b x =
      AdicCompletion.of (DividedPowers.pAdicIdeal p)
        (E'.completedRing p b ⊗[E.completedRing p b] V.carrier b)
        ((1 : E'.completedRing p b) ⊗ₜ[E.completedRing p b] x) :=
  rfl

/-- **The maps `M(b) → M'(b)` commute with the transitions.** -/
theorem pullbackApp07Q9_naturality {m n : SimplexCategory} (φ : m ⟶ n) (x : V.carrier m.len) :
    V.pullbackApp07Q9 g n.len (V.map φ x) =
      (V.pullback07Q9 g).map φ (V.pullbackApp07Q9 g m.len x) := by
  let := g.completedAlgebra07Q9 p m.len
  let := g.completedAlgebra07Q9 p n.len
  rw [pullbackApp07Q9_apply, pullbackApp07Q9_apply, pullback07Q9_map_of, map_one]

/-- **The modules of the base change are `p`-adically complete**, being adic completions along
the finitely generated ideal `(p)`. -/
instance pullback07Q9_isAdicComplete (b : ℕ) :
    IsAdicComplete (DividedPowers.pAdicIdeal (A := E'.completedRing p b) p)
      ((V.pullback07Q9 g).carrier b) := by
  let := g.completedAlgebra07Q9 p b
  exact CompletedConnection.isPAdicallyComplete_baseChangeCarrier p (E.completedRing p b)
    (E'.completedRing p b) (V.carrier b)

end CosimplicialCompletedModule

end Crystalline

end
