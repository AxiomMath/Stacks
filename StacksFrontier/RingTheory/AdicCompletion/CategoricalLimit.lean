module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# The adic completion as a categorical inverse limit

Let `R` be a commutative ring, `I` an ideal of `R` and `M` an `R`-module. The adic quotients
`M ⧸ I ^ n • M` form an inverse system indexed by `ℕᵒᵖ`, and the adic completion
`AdicCompletion I M` is its limit. This file proves that statement for an inverse system presented
*abstractly*, as a functor `S : ℕᵒᵖ ⥤ ModuleCat R` together with linear equivalences
`e n : M ⧸ I ^ (n + 1) • M ≃ₗ[R] S.obj (op n)` intertwining the transition maps of `S` with
`Submodule.factorPow`, and the indexing is shifted by one, so that `S.obj (op n)` is the quotient
at level `n + 1`.

## Main definitions

* `AdicCompletion.quotientSystemCone`: the cone over `S` with vertex `AdicCompletion I M`,
  whose leg at `op n` is `e n` composed with the evaluation `AdicCompletion.eval I M (n + 1)`.
* `AdicCompletion.quotientSystemConeIsLimit`: that cone is a limit cone.
* `AdicCompletion.quotientSystemLimitEquiv`: the comparison isomorphism
  `AdicCompletion I M ≃ₗ[R] limit S` it induces.

## Main results

* `AdicCompletion.quotientSystemCone_π` computes the legs of the cone.
* `AdicCompletion.limit_π_quotientSystemLimitEquiv` and
  `AdicCompletion.limit_π_quotientSystemLimitEquiv_of` read off the components of the
  comparison isomorphism, on a general element of the completion and on the image of an
  element of `M`.

## Implementation notes

Because `S` starts at level `1`, the universal map into the completion has to supply a
component at level `0` as well.  There is no choice to make: `I ^ 0 • ⊤ = ⊤`, so
`M ⧸ I ^ 0 • M` is a subsingleton and the level-`0` component is the zero map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    (S : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (e : ∀ n : ℕ, (M ⧸ I ^ (n + 1) • (⊤ : Submodule R M)) ≃ₗ[R] S.obj (op n))
    (he : ∀ {m n : ℕ} (h : m ≤ n) x,
      S.map (homOfLE h).op (e n x) =
        e m (Submodule.factorPow I M (Nat.add_le_add_right h 1) x))

/-- The level-`0` adic quotient of a module is a subsingleton, since `I ^ 0 • ⊤ = ⊤`. -/
public theorem subsingleton_quotient_pow_zero_smul_top :
    Subsingleton (M ⧸ I ^ 0 • (⊤ : Submodule R M)) := by
  simpa only [pow_zero, one_smul] using
    (inferInstance : Subsingleton (M ⧸ (⊤ : Submodule R M)))

/-- The cone over a shifted system `S` of adic quotients of `M` with vertex the adic
completion `AdicCompletion I M`: the leg at `op n` evaluates an element of the completion at
level `n + 1` and transports it along `e n`. -/
public def quotientSystemCone : Cone S where
  pt := ModuleCat.of R (AdicCompletion I M)
  π :=
    { app n := ModuleCat.ofHom ((e n.unop).toLinearMap.comp (eval I M (n.unop + 1)))
      naturality m n a := by
        ext x
        change e n.unop (eval I M (n.unop + 1) x) =
          S.map a (e m.unop (eval I M (m.unop + 1) x))
        have ha : a = (homOfLE (leOfHom a.unop)).op := Subsingleton.elim _ _
        rw [ha, he]
        exact congrArg (e n.unop)
          (transitionMap_comp_eval_apply I M (Nat.add_le_add_right (leOfHom a.unop) 1) x).symm }

/-- The legs of `AdicCompletion.quotientSystemCone`. -/
public theorem quotientSystemCone_π (n : ℕ) (x : AdicCompletion I M) :
    (quotientSystemCone I M S e he).π.app (op n) x = e n (eval I M (n + 1) x) :=
  rfl

/-- The universal map from the vertex of a cone `c` over `S` to the adic completion: its
level-`n + 1` component is the leg of `c` at `op n` read through `e n`, and its level-`0`
component is zero, the level-`0` adic quotient being a subsingleton. -/
public def quotientSystemConeLift (c : Cone S) : c.pt →ₗ[R] AdicCompletion I M :=
  lift I
    (fun n => match n with
      | 0 => 0
      | k + 1 => (e k).symm.toLinearMap.comp (c.π.app (op k)).hom)
    (by
      intro m n h
      cases m with
      | zero =>
        ext x
        have := subsingleton_quotient_pow_zero_smul_top I M
        exact Subsingleton.elim _ _
      | succ m =>
        cases n with
        | zero => omega
        | succ n =>
          ext x
          apply (e m).injective
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
          rw [← he (Nat.le_of_succ_le_succ h)]
          simp only [LinearEquiv.apply_symm_apply]
          exact congrArg (fun f : c.pt ⟶ S.obj (op m) => f x)
            (c.w (homOfLE (Nat.le_of_succ_le_succ h)).op))

/-- The defining property of `AdicCompletion.quotientSystemConeLift` at level `n + 1`. -/
public theorem eval_quotientSystemConeLift (c : Cone S) (n : ℕ) (x : c.pt) :
    eval I M (n + 1) (quotientSystemConeLift I M S e he c x) = (e n).symm (c.π.app (op n) x) :=
  rfl

/-- `AdicCompletion I M` is the limit of a shifted system of adic quotients of `M`: a
compatible family of elements of the `S.obj (op n)` is, through the equivalences `e`, a
compatible family of elements of the `M ⧸ I ^ n • M`, hence an element of the completion. -/
public def quotientSystemConeIsLimit : IsLimit (quotientSystemCone I M S e he) where
  lift c := ModuleCat.ofHom (quotientSystemConeLift I M S e he c)
  fac c n := by
    ext x
    change e n.unop (eval I M (n.unop + 1) (quotientSystemConeLift I M S e he c x)) =
      c.π.app n x
    rw [eval_quotientSystemConeLift, LinearEquiv.apply_symm_apply]
  uniq c f hf := by
    ext x
    apply AdicCompletion.ext
    intro n
    cases n with
    | zero =>
      have := subsingleton_quotient_pow_zero_smul_top I M
      exact Subsingleton.elim _ _
    | succ n =>
      apply (e n).injective
      change e n (eval I M (n + 1) (f x)) =
        e n (eval I M (n + 1) (quotientSystemConeLift I M S e he c x))
      rw [eval_quotientSystemConeLift, LinearEquiv.apply_symm_apply]
      exact congrArg (fun g : c.pt ⟶ S.obj (op n) => g x) (hf (op n))

/-- The comparison isomorphism between the adic completion of `M` and the categorical limit
of a shifted system of adic quotients of `M`. -/
public def quotientSystemLimitEquiv : AdicCompletion I M ≃ₗ[R] (limit S : ModuleCat.{u} R) :=
  (IsLimit.conePointUniqueUpToIso (quotientSystemConeIsLimit I M S e he)
    (limit.isLimit S)).toLinearEquiv

/-- The components of `AdicCompletion.quotientSystemLimitEquiv`: projecting to the `n`-th term
of the system recovers the level-`n + 1` evaluation, read through `e n`. -/
public theorem limit_π_quotientSystemLimitEquiv (n : ℕ) (x : AdicCompletion I M) :
    limit.π S (op n) (quotientSystemLimitEquiv I M S e he x) = e n (eval I M (n + 1) x) :=
  congrArg (fun f : ModuleCat.of R (AdicCompletion I M) ⟶ S.obj (op n) => f x)
    (IsLimit.conePointUniqueUpToIso_hom_comp (quotientSystemConeIsLimit I M S e he)
      (limit.isLimit S) (op n))

/-- `AdicCompletion.quotientSystemLimitEquiv` on the image of an element of `M`: its `n`-th
component is the class of that element in `M ⧸ I ^ (n + 1) • M`, read through `e n`. -/
public theorem limit_π_quotientSystemLimitEquiv_of (n : ℕ) (x : M) :
    limit.π S (op n) (quotientSystemLimitEquiv I M S e he (of I M x)) =
      e n (Submodule.Quotient.mk x) := by
  rw [limit_π_quotientSystemLimitEquiv, eval_of, Submodule.mkQ_apply]

end AdicCompletion

end
