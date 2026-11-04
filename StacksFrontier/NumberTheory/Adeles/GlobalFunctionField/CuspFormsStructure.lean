module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeStability

/-!
# Finiteness and base change of `C(Λ)` (Stacks 03VW)

Let `k` be a finite field of characteristic `p`, `K` a function field over `k`, and `Λ` a ring in
which `p` is invertible. We prove Stacks Proposition 03VW: `C(Λ)` is a finitely generated
`Λ`-module when `Λ` is Noetherian, and for a field `Λ` with prime subfield `F` the natural map
`Λ ⊗_F C(F) → C(Λ)`, `c ⊗ f ↦ c · f`, is an isomorphism intertwining `id ⊗ T_v` and `T_v`.

The proofs are in
* `StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsFinite` (finite generation, by
  reduction theory: the elements of `C(Λ)` are determined by their values on a finite set);
* `StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsBaseChange` (base change: when
  `p` is invertible the conditions cutting out `C(Λ)` are linear with coefficients in `F`);
* `StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeStability` (the Hecke operators
  preserve `C(Λ)`).

## References

* [Stacks Project, Tag 03VW](https://stacks.math.columbia.edu/tag/03VW)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u w

namespace Stacks.Adeles.GlobalFunctionField

variable (k : Type u) [Field k] [Finite k] (K : Type u) [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- **Stacks 03VW.** Let `k` be a finite field of characteristic `p` and `K` a function field
over `k` (a finite extension of `k(x)`; this includes `K = k(X)` for every geometrically
irreducible smooth projective curve `X` over `k`, whose places are the closed points of `X`). Let
`Λ` be a ring in which `p` is invertible.

1. If `Λ` is Noetherian, then `C(Λ)` is a finitely generated `Λ`-module.
2. If `Λ` is a field with prime subfield `F` (the bottom subfield `⊥`), then
   `C(Λ) = C(F) ⊗_F Λ` compatibly with `T_v` acting: there is a `Λ`-linear isomorphism
   `e : Λ ⊗_F C(F) ≃ C(Λ)` given by `c ⊗ f ↦ c · (ι ∘ f)` (`ι : F → Λ` the inclusion), and for
   every place `v` and every choice of the data `π, λ, g₀, g` of the formula for `T_v`
   (`Stacks.Adeles.IsHeckeDataAt`), `T_v` restricts to linear endomorphisms `T_F` of `C(F)` and
   `T_Λ` of `C(Λ)` with `e ∘ (id ⊗ T_F) = T_Λ ∘ e`.

`C(Λ)` is `Stacks.Adeles.cuspFormsCentralChar`: the unramified cusp forms (Tag 03VS) with
`U_v f = φ_v⁻¹ f` for all `v`, where the source's undefined `φ_v` is read as `q_v`, as in that
definition's docstring. The characteristic `p` of `k` is `ringChar k`. The tensor product is
written `Λ ⊗_F C(F)`, with `Λ` on the left so that it carries its `Λ`-module structure; it is
`C(F) ⊗_F Λ` of the source up to the swap of factors. -/
@[stacks 03VW]
public theorem cuspFormsCentralChar_fg_and_baseChange :
    (∀ (Λ : Type w) [CommRing Λ] [IsNoetherianRing Λ], IsUnit (ringChar k : Λ) →
      (cuspFormsCentralChar K Λ).FG) ∧
    ∀ (Λ : Type w) [Field Λ], IsUnit (ringChar k : Λ) →
      ∃ e : Λ ⊗[↥(⊥ : Subfield Λ)] cuspFormsCentralChar K ↥(⊥ : Subfield Λ) ≃ₗ[Λ]
          cuspFormsCentralChar K Λ,
        (∀ (c : Λ) (f : cuspFormsCentralChar K ↥(⊥ : Subfield Λ)),
          ((e (c ⊗ₜ f) : cuspFormsCentralChar K Λ) : GL (Fin 2) (AdeleRing K) → Λ) =
            c • mapCoeffs (algebraMap ↥(⊥ : Subfield Λ) Λ) f) ∧
        ∀ {v : Place K} {q : ℕ} (π : v.integers) (lam : Fin q → v.integers)
          (g₀ : GL (Fin 2) (AdeleRing K)) (g : Fin q → GL (Fin 2) (AdeleRing K)),
          IsHeckeDataAt v π lam g₀ g →
            ∃ (TF : cuspFormsCentralChar K ↥(⊥ : Subfield Λ) →ₗ[↥(⊥ : Subfield Λ)]
                cuspFormsCentralChar K ↥(⊥ : Subfield Λ))
              (TΛ : cuspFormsCentralChar K Λ →ₗ[Λ] cuspFormsCentralChar K Λ),
              (∀ f, (TF f : GL (Fin 2) (AdeleRing K) → ↥(⊥ : Subfield Λ)) =
                heckeOperator g₀ g f) ∧
              (∀ f, (TΛ f : GL (Fin 2) (AdeleRing K) → Λ) = heckeOperator g₀ g f) ∧
              e.toLinearMap ∘ₗ LinearMap.baseChange Λ TF = TΛ ∘ₗ e.toLinearMap := by
  refine ⟨fun Λ _ _ hp => cuspFormsCentralChar_fg k Λ hp, fun Λ _ hp => ?_⟩
  refine ⟨cuspFormsBaseChangeEquiv k hp, fun c f => cuspFormsBaseChangeEquiv_tmul k hp c f,
    fun π lam g₀ g hd => ?_⟩
  refine ⟨cuspFormsHecke k _ (isUnit_ringChar_of_algebra k hp) hd, cuspFormsHecke k Λ hp hd,
    fun f => rfl, fun f => rfl, ?_⟩
  rw [cuspFormsBaseChangeEquiv_toLinearMap]
  exact cuspFormsBaseChange_comp_baseChange_hecke k hp hd

end Stacks.Adeles.GlobalFunctionField

end
