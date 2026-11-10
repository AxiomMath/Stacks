module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.OpenSubgroups
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.ChangeBasePoint

/-!
# The character of `π₁` attached to a torsor cover

Let `Y` be a finite étale cover of a connected scheme `X`, and let an abelian group `K` act on `Y`
by automorphisms over `X` so that on every geometric fibre the action is simply transitive: `Y` is
a `K`-torsor (a Galois cover with group `K`), like the Artin–Schreier cover `t^q - t = g` with
`K = 𝔽_q`.  Then `π₁(X, x̄)` acts on the fibre at `x̄` commuting with `K`, so each `σ` moves every
point of the fibre by the same element `χ(σ) ∈ K`.  This is a continuous homomorphism
`χ : π₁(X, x̄) → K`, and it is compatible with change of base point.

## Main definitions

* `AlgebraicGeometry.TorsorCover`: the data of the cover and the simply transitive action.
* `AlgebraicGeometry.TorsorCover.fiberDiff`: the element of `K` carrying one point of a fibre to
  another.
* `AlgebraicGeometry.TorsorCover.character`: `χ : π₁(X, x̄) →* Multiplicative K`.

## Main results

* `AlgebraicGeometry.TorsorCover.smul_eq_character`: `σ • p = τ_{χ(σ)} p` for every `p`.
* `AlgebraicGeometry.TorsorCover.continuous_character`: `χ` is continuous for the discrete
  topology on `K`.
* `AlgebraicGeometry.TorsorCover.character_etaleFundamentalGroupMulEquiv`: `χ` is invariant under
  transport along a path.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- A finite étale cover `Y → X` with an action of an abelian group `K` by automorphisms over `X`
which is simply transitive on every geometric fibre. -/
public structure TorsorCover (X : Scheme.{u}) (K : Type*) [AddCommGroup K] where
  /-- The cover. -/
  cover : FiniteEtaleOver X
  /-- The action of `K` by endomorphisms over `X`. -/
  τ : K → (cover ⟶ cover)
  τ_zero : τ 0 = 𝟙 cover
  τ_add : ∀ a b, τ (a + b) = τ a ≫ τ b
  /-- The action on each geometric fibre is simply transitive. -/
  existsUnique : ∀ (s : GeometricPoint X) (p q : (finiteEtaleFiberFunctor s).obj cover),
    ∃! a : K, (finiteEtaleFiberFunctor s).map (τ a) p = q

namespace TorsorCover

variable {K : Type*} [AddCommGroup K] (T : TorsorCover X K)

/-- The element of `K` carrying `p` to `q` in a geometric fibre. -/
public def fiberDiff {s : GeometricPoint X} (p q : (finiteEtaleFiberFunctor s).obj T.cover) : K :=
  (T.existsUnique s p q).exists.choose

omit [ConnectedSpace X] in
/-- `fiberDiff p q` carries `p` to `q`. -/
public theorem map_τ_fiberDiff {s : GeometricPoint X}
    (p q : (finiteEtaleFiberFunctor s).obj T.cover) :
    (finiteEtaleFiberFunctor s).map (T.τ (T.fiberDiff p q)) p = q :=
  (T.existsUnique s p q).exists.choose_spec

omit [ConnectedSpace X] in
/-- `fiberDiff p q` is the only element of `K` carrying `p` to `q`. -/
public theorem fiberDiff_eq {s : GeometricPoint X}
    {p q : (finiteEtaleFiberFunctor s).obj T.cover} {a : K}
    (h : (finiteEtaleFiberFunctor s).map (T.τ a) p = q) : T.fiberDiff p q = a :=
  (T.existsUnique s p q).unique (T.map_τ_fiberDiff p q) h

omit [ConnectedSpace X] in
/-- On a geometric fibre, `τ (a + b)` acts as `τ a` followed by `τ b`. -/
public theorem map_τ_add {s : GeometricPoint X} (a b : K)
    (p : (finiteEtaleFiberFunctor s).obj T.cover) :
    (finiteEtaleFiberFunctor s).map (T.τ (a + b)) p =
      (finiteEtaleFiberFunctor s).map (T.τ b) ((finiteEtaleFiberFunctor s).map (T.τ a) p) := by
  rw [T.τ_add, Functor.map_comp]
  rfl

/-- The action of `π₁` on a fibre commutes with the action of `K`. -/
public theorem smul_map_τ {s : GeometricPoint X} (σ : EtaleFundamentalGroup X s) (a : K)
    (p : (finiteEtaleFiberFunctor s).obj T.cover) :
    σ • (finiteEtaleFiberFunctor s).map (T.τ a) p =
      (finiteEtaleFiberFunctor s).map (T.τ a) (σ • p) :=
  ConcreteCategory.congr_hom (σ.asIso.hom.naturality (T.τ a)) p

/-- The difference `fiberDiff p (σ • p)` does not depend on `p`. -/
public theorem fiberDiff_smul_eq {s : GeometricPoint X} (σ : EtaleFundamentalGroup X s)
    (p q : (finiteEtaleFiberFunctor s).obj T.cover) :
    T.fiberDiff p (σ • p) = T.fiberDiff q (σ • q) := by
  symm
  apply T.fiberDiff_eq
  have hq : (finiteEtaleFiberFunctor s).map (T.τ (T.fiberDiff p q)) p = q := T.map_τ_fiberDiff p q
  rw [← hq, smul_map_τ, ← map_τ_add, add_comm, map_τ_add, T.map_τ_fiberDiff]

/-- **The character `χ : π₁(X, x̄) → K` of a torsor cover**, read off at a point `p₀` of the
fibre at `x̄` (it does not depend on `p₀`, `fiberDiff_smul_eq`): `σ • p₀ = τ_{χ(σ)} p₀`. -/
public def character (x : GeometricPoint X) (p₀ : (finiteEtaleFiberFunctor x).obj T.cover) :
    EtaleFundamentalGroup X x →* Multiplicative K where
  toFun σ := Multiplicative.ofAdd (T.fiberDiff p₀ (σ • p₀))
  map_one' := by
    rw [ofAdd_eq_one]
    apply T.fiberDiff_eq
    rw [T.τ_zero, CategoryTheory.Functor.map_id, one_smul]
    rfl
  map_mul' σ σ' := by
    rw [← ofAdd_add]
    congr 1
    apply T.fiberDiff_eq
    rw [map_τ_add, T.map_τ_fiberDiff, ← smul_map_τ, T.map_τ_fiberDiff, mul_smul]

/-- The additive value of `χ(σ)` is `fiberDiff p₀ (σ • p₀)`. -/
public theorem toAdd_character (x : GeometricPoint X) (p₀ : (finiteEtaleFiberFunctor x).obj T.cover)
    (σ : EtaleFundamentalGroup X x) :
    Multiplicative.toAdd (T.character x p₀ σ) = T.fiberDiff p₀ (σ • p₀) :=
  rfl

/-- **`σ ∈ π₁(X, x̄)` moves every point of the fibre at `x̄` by `χ(σ)`.** -/
public theorem smul_eq_character (x : GeometricPoint X)
    (p₀ : (finiteEtaleFiberFunctor x).obj T.cover)
    (σ : EtaleFundamentalGroup X x) (p : (finiteEtaleFiberFunctor x).obj T.cover) :
    σ • p =
      (finiteEtaleFiberFunctor x).map (T.τ (Multiplicative.toAdd (T.character x p₀ σ))) p := by
  rw [toAdd_character, T.fiberDiff_smul_eq σ p₀ p, T.map_τ_fiberDiff]

/-- The character is determined by the action on any single point of the fibre. -/
public theorem character_eq_of_smul (x : GeometricPoint X)
    (p₀ : (finiteEtaleFiberFunctor x).obj T.cover)
    (σ : EtaleFundamentalGroup X x) (p : (finiteEtaleFiberFunctor x).obj T.cover) {a : K}
    (h : σ • p = (finiteEtaleFiberFunctor x).map (T.τ a) p) :
    Multiplicative.toAdd (T.character x p₀ σ) = a := by
  rw [toAdd_character, T.fiberDiff_smul_eq σ p₀ p]
  exact T.fiberDiff_eq h.symm

/-- **The character is invariant under transport along a path** `t` from `s̄` to `x̄`. -/
public theorem character_etaleFundamentalGroupMulEquiv {s x : GeometricPoint X}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (p₀ : (finiteEtaleFiberFunctor s).obj T.cover) (q₀ : (finiteEtaleFiberFunctor x).obj T.cover)
    (σ : EtaleFundamentalGroup X s) :
    T.character x q₀ (etaleFundamentalGroupMulEquiv t σ) = T.character s p₀ σ := by
  apply Multiplicative.toAdd.injective
  refine T.character_eq_of_smul x q₀ _ (t.hom.app T.cover p₀) ?_
  have h1 := T.smul_eq_character s p₀ σ p₀
  change (t.hom.app T.cover)
    ((σ.asIso.hom.app T.cover) ((t.inv.app T.cover) ((t.hom.app T.cover) p₀))) = _
  rw [show (t.inv.app T.cover) ((t.hom.app T.cover) p₀) = p₀ from
    ConcreteCategory.congr_hom (t.hom_inv_id_app T.cover) p₀]
  change (t.hom.app T.cover) (σ • p₀) = _
  rw [h1]
  exact ConcreteCategory.congr_hom (t.hom.naturality _) p₀

/-- Evaluation at a point of a fibre is continuous for the discrete topology on the fibre. -/
public theorem isOpen_setOf_smul_eq (x : GeometricPoint X) (Y : FiniteEtaleOver X)
    (y z : (finiteEtaleFiberFunctor x).obj Y) :
    IsOpen {σ : EtaleFundamentalGroup X x | σ • y = z} := by
  let (Z : FiniteEtaleOver X) : TopologicalSpace ((finiteEtaleFiberFunctor x).obj Z) := ⊥
  let (Z : FiniteEtaleOver X) : DiscreteTopology ((finiteEtaleFiberFunctor x).obj Z) := ⟨rfl⟩
  have h1 : Continuous fun σ : EtaleFundamentalGroup X x ↦
      Stacks.FundamentalGroup.componentEmbedding (finiteEtaleFiberFunctor x) σ :=
    continuous_induced_dom
  have h2 : Continuous fun σ : EtaleFundamentalGroup X x ↦
      Stacks.FundamentalGroup.componentEmbedding (finiteEtaleFiberFunctor x) σ Y :=
    (continuous_apply Y).comp h1
  have h3 : Continuous fun σ : EtaleFundamentalGroup X x ↦
      ((Stacks.FundamentalGroup.componentEmbedding (finiteEtaleFiberFunctor x) σ Y :
        Equiv.Perm ((finiteEtaleFiberFunctor x).obj Y)) :
        (finiteEtaleFiberFunctor x).obj Y → (finiteEtaleFiberFunctor x).obj Y) :=
    continuous_induced_dom.comp h2
  have hcont : Continuous fun σ : EtaleFundamentalGroup X x ↦ (σ.asIso.app Y).hom y :=
    (continuous_apply y).comp h3
  exact hcont.isOpen_preimage {z} (isOpen_discrete _)

/-- **The character is continuous** for the discrete topology on `K`: the fibre of `a` is the set
of `σ` moving `p₀` to `τ_a p₀`, which is open. -/
public theorem continuous_character [TopologicalSpace (Multiplicative K)]
    [DiscreteTopology (Multiplicative K)] (x : GeometricPoint X)
    (p₀ : (finiteEtaleFiberFunctor x).obj T.cover) :
    Continuous (T.character x p₀) := by
  refine continuous_def.2 fun S _ => ?_
  have : T.character x p₀ ⁻¹' S = ⋃ a ∈ S, {σ : EtaleFundamentalGroup X x |
      σ • p₀ = (finiteEtaleFiberFunctor x).map (T.τ (Multiplicative.toAdd a)) p₀} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun h ↦ ⟨_, h, T.smul_eq_character x p₀ σ p₀⟩, fun ⟨a, ha, h⟩ ↦
      Multiplicative.toAdd.injective (T.character_eq_of_smul x p₀ σ p₀ h) ▸ ha⟩
  rw [this]
  exact isOpen_biUnion fun a _ => isOpen_setOf_smul_eq x T.cover p₀ _

end TorsorCover

end AlgebraicGeometry
