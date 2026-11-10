module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.RestrictScalars
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Tactic.Group

/-!
# The coefficient-ring trace of a twisted endomorphism of a group-ring module

Let `Λ` be a ring, `G` a finite group, `P` a finite projective `Λ[G]`-module and `f` a
`Λ[G]`-linear endomorphism of `P`. For `g ∈ G` the map `g⁻¹ ∘ f` is `Λ`-linear, and its trace over
`Λ` is determined by the trace of `f` over `Λ[G]`:

`Tr_Λ(g⁻¹ ∘ f | P) = κ_g(Tr_{Λ[G]}(f | P))`,  `κ_g(x) = ∑_{k ∈ G} x(k⁻¹ g k)`.

The functional `κ_g` is the sum of the coefficients of `x` over the conjugates of `g`, each
counted `#Z_G(g)` times. This is the instance of the functoriality of
`StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace` for the restriction of
scalars `Λ[G] → Λ`, twisted by the action of `g⁻¹`, and it holds verbatim for endomorphisms of
perfect complexes of `Λ[G]`-modules. It is the identity

`#Z_g · Tr^{Z_g}_Λ((g, π) | K) = Tr_Λ((g, π) | K)`

used in Step 8 of the proof of [Stacks, Tag 03UG] (with [Stacks, Tag 03UB]), in the form needed
there: it computes the trace of `(g⁻¹π)^*` on `RΓ_c(V_k̄, A)` from the trace of `π^*` on
`RΓ_c(U_k̄, f_* A)` over `A[G]`.

## Main definitions

* `Stacks.Trace.groupAlgebraRestriction`: restriction of scalars along `Λ → Λ[G]`.
* `Stacks.Trace.groupElementAction`: the action of `g⁻¹`, a natural endomorphism of it.
* `Stacks.Trace.conjugacyTrace`: the induced map `κ_g : Λ[G]^♮ → Λ^♮`.

## Main results

* `Stacks.Trace.conjugacyTrace_mk`: `κ_g(x) = ∑_{k ∈ G} x(k⁻¹ g k)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.FilteredDerived
open scoped MonoidAlgebra BigOperators

universe u v w

namespace Stacks.Trace

variable (Λ : Type u) [Ring Λ] (G : Type v) [Group G]

/-- Restriction of scalars along `Λ → Λ[G]`, in the module universe `max u v w`. -/
abbrev groupAlgebraRestriction : ModuleCat.{max u v w} Λ[G] ⥤ ModuleCat.{max u v w} Λ :=
  ModuleCat.restrictScalars (MonoidAlgebra.singleOneRingHom (R := Λ) (M := G))

/-- The action of `g⁻¹ ∈ G` on a `Λ[G]`-module, as a natural endomorphism of the underlying
`Λ`-module. -/
def groupElementAction (g : G) : groupAlgebraRestriction.{u, v, w} Λ G ⟶
    groupAlgebraRestriction.{u, v, w} Λ G where
  app M :=
    let φ : (groupAlgebraRestriction.{u, v, w} Λ G).obj M →ₗ[Λ]
        (groupAlgebraRestriction.{u, v, w} Λ G).obj M :=
      { toFun := fun (m : M) => (MonoidAlgebra.single g⁻¹ (1 : Λ) • m : M)
        map_add' := fun a b => smul_add _ (a : M) (b : M)
        map_smul' := fun r m => by
          change MonoidAlgebra.single g⁻¹ (1 : Λ) •
              (MonoidAlgebra.singleOneRingHom (R := Λ) (M := G) r • (m : M)) =
            MonoidAlgebra.singleOneRingHom (R := Λ) (M := G) r •
              (MonoidAlgebra.single g⁻¹ (1 : Λ) • (m : M))
          rw [smul_smul, smul_smul]
          congr 1
          simp [MonoidAlgebra.singleOneRingHom, MonoidAlgebra.single_mul_single] }
    ModuleCat.ofHom (X := (groupAlgebraRestriction.{u, v, w} Λ G).obj M)
      (Y := (groupAlgebraRestriction.{u, v, w} Λ G).obj M) φ
  naturality M N f := by
    ext m
    exact (f.hom.map_smul _ m).symm

variable [Finite G]

/-- Restriction of scalars along `Λ → Λ[G]` preserves finite projective modules. -/
theorem preservesFiniteProjective_groupAlgebraRestriction :
    PreservesFiniteProjective.{max u v, w} (groupAlgebraRestriction.{u, v, w} Λ G) :=
  fun P _ _ => ⟨finite_restrictScalars_groupAlgebra Λ G P,
    projective_restrictScalars_groupAlgebra Λ G P⟩

/-- **The conjugacy trace `κ_g : Λ[G]^♮ → Λ^♮`**, the map induced on additive commutator quotients
by restriction of scalars along `Λ → Λ[G]` twisted by the action of `g⁻¹`. -/
def conjugacyTrace (g : G) :
    AdditiveCommutatorQuotient Λ[G] →+ AdditiveCommutatorQuotient Λ :=
  functorTraceMap.{max u v, w} (groupAlgebraRestriction.{u, v, w} Λ G)
    (groupElementAction.{u, v, w} Λ G g) (preservesFiniteProjective_groupAlgebraRestriction Λ G)

/-- The `Λ`-linear identification of the restricted regular module with `G → Λ`. -/
def regularRestrictionEquiv [Fintype G] :
    (groupAlgebraRestriction.{u, v, w} Λ G).obj (regularModule.{max u v, w} Λ[G]) ≃ₗ[Λ]
      (G → Λ) where
  toFun m k := (m : ULift.{max u v w} Λ[G]).down.coeff k
  map_add' a b := by
    funext k
    change ((a : ULift.{max u v w} Λ[G]).down + (b : ULift.{max u v w} Λ[G]).down).coeff k = _
    rw [MonoidAlgebra.coeff_add]
    rfl
  map_smul' r m := by
    funext k
    change (MonoidAlgebra.single 1 r * (m : ULift.{max u v w} Λ[G]).down).coeff k = _
    rw [MonoidAlgebra.coeff_single_one_mul]
    rfl
  invFun f := (⟨∑ k, MonoidAlgebra.single k (f k)⟩ : ULift.{max u v w} Λ[G])
  left_inv m := by
    apply ULift.ext
    change ∑ k, MonoidAlgebra.single k ((m : ULift.{max u v w} Λ[G]).down.coeff k) = _
    ext h
    classical
    simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]
  right_inv f := by
    funext h
    classical
    change (∑ k, MonoidAlgebra.single k (f k)).coeff h = f h
    simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- **The conjugacy trace on a class**: `κ_g(x) = ∑_{k ∈ G} x(k⁻¹ g k)`. -/
theorem conjugacyTrace_mk [Fintype G] (g : G) (x : Λ[G]) :
    conjugacyTrace.{u, v, w} Λ G g (additiveCommutatorQuotientMk Λ[G] x) =
      additiveCommutatorQuotientMk Λ (∑ k : G, x.coeff (k⁻¹ * g * k)) := by
  classical
  rw [conjugacyTrace, functorTraceMap_mk]
  simp only [functorTraceRaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  unfold functorTrace
  have h := preservesFiniteProjective_groupAlgebraRestriction.{u, v, w} Λ G
    (regularModule.{max u v, w} Λ[G]) inferInstance inferInstance
  let := h.1
  let := h.2
  let e := regularRestrictionEquiv.{u, v, w} Λ G
  rw [projectiveModuleTrace_eq_of_split Λ _ _ e.symm.toLinearMap e.toLinearMap
    (by ext m; simp), freeModuleTrace_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  change (MonoidAlgebra.single g⁻¹ (1 : Λ) *
    (∑ j, MonoidAlgebra.single j (standardBasisVector Λ G k j)) * x).coeff k = _
  have hs : (∑ j, MonoidAlgebra.single j (standardBasisVector Λ G k j)) =
      MonoidAlgebra.single k (1 : Λ) := by
    rw [Finset.sum_eq_single k]
    · simp [standardBasisVector]
    · intro j _ hj
      simp [standardBasisVector, hj]
    · simp
  rw [hs, MonoidAlgebra.single_mul_single, mul_one, MonoidAlgebra.coeff_single_mul_apply,
    one_mul]
  congr 1
  group

end Stacks.Trace
