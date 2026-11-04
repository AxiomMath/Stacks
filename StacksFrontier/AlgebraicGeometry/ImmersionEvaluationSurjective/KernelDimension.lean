module

public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.NonSmoothLocusFibreDimension

/-!
# The kernel of the evaluation at a point

Let `X` be a scheme over a field `k`, let `ℒ` be an `𝒪_X`-module, let `x ∈ X`, and let
`s₀, …, sₙ` be global sections of `ℒ`. The quotient `ℒ_x/𝔪_x²ℒ_x` is a `k`-vector space by
restriction of scalars along the structure map `k → 𝒪_{X,x}`, and the evaluation
`ev_x : kⁿ⁺¹ → ℒ_x/𝔪_x²ℒ_x`, `c ↦ ∑ⱼ cⱼ·(sⱼ)_x`, is `k`-linear. With `r = n + 1`, if `ev_x` is
surjective then

* `dim ker ev_x = r - dim(ℒ_x/𝔪_x²ℒ_x)`, and
* `dim(ℒ_x/𝔪_x²ℒ_x) ≤ r`.

## Main definitions

* `Stacks.ImmersionEvaluationSurjective.evalQuotient`: the quotient `ℒ_x/𝔪_x²ℒ_x` carrying the
  `k`-vector space structure of the base field.
* `Stacks.ImmersionEvaluationSurjective.evalCoord`: **the evaluation `ev_x` as a `k`-linear map**
  `(Fin (n+1) → k) →ₗ[k] ℒ_x/𝔪_x²ℒ_x`.

## Main results

* `Stacks.ImmersionEvaluationSurjective.surjective_evalCoord`: the linear map `evalCoord` is
  surjective when the evaluation on coordinate tuples is.
* `Stacks.ImmersionEvaluationSurjective.finrank_ker_evalCoord`: for a surjective evaluation,
  `dim ker ev_x = r - dim(ℒ_x/𝔪_x²ℒ_x)`.
* `Stacks.ImmersionEvaluationSurjective.finrank_evalQuotient_le`: for a surjective evaluation,
  `dim(ℒ_x/𝔪_x²ℒ_x) ≤ r`.
* `Stacks.ImmersionEvaluationSurjective.surjective_evalCoord_of_isClosed`: the evaluation is
  surjective at a closed point of a scheme locally of finite type over an algebraically closed
  field, for sections defining an immersion into projective space.
* `Stacks.ImmersionEvaluationSurjective.finrank_ker_evalCoord_of_isClosed` and
  `Stacks.ImmersionEvaluationSurjective.finrank_evalQuotient_le_of_isClosed`: the two dimension
  statements in that situation.

## Implementation notes

`ℒ_x/𝔪_x²ℒ_x` is a module over `𝒪_{X,x}`, and the `k`-structure is the restriction of scalars
along `Stacks.ImmersionEvaluationSurjective.baseGerm`. That ring map is not determined by the
quotient's type, so the restricted structure cannot be an instance on the quotient itself;
`evalQuotient` is therefore a definition carrying the structure morphism `f` in its type, on
which the `k`-module structure *is* an instance. Both scalar actions are available on it and
agree with each other through `baseGerm` definitionally
(`Stacks.ImmersionEvaluationSurjective.evalQuotient_smul_def`).

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.ImmersionEvaluationSurjective

open Stacks.ModuleStalk Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] {X : Scheme.{u}} {L : X.Modules}

/-- **The target of the evaluation at `x`**: the quotient `ℒ_x/𝔪_x²ℒ_x` of the stalk of `ℒ`,
carrying the vector space structure over the base field `k` of the structure morphism `f`. -/
def evalQuotient (_f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) (x : X) : Type u :=
  (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x) ⧸ maximalSqSmul L x

variable {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤)) (f : X ⟶ Spec (CommRingCat.of k)) (x : X)

/-- The additive group structure of the quotient `ℒ_x/𝔪_x²ℒ_x`. -/
instance addCommGroup_evalQuotient : AddCommGroup (evalQuotient f L x) :=
  inferInstanceAs (AddCommGroup
    ((TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x) ⧸ maximalSqSmul L x))

/-- The quotient `ℒ_x/𝔪_x²ℒ_x` is a module over the local ring `𝒪_{X,x}`. -/
instance module_stalk_evalQuotient : Module (X.presheaf.stalk x) (evalQuotient f L x) :=
  inferInstanceAs (Module (X.presheaf.stalk x)
    ((TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x) ⧸ maximalSqSmul L x))

/-- The `k`-vector space structure on `ℒ_x/𝔪_x²ℒ_x`, by restriction of scalars along the structure
map `k → 𝒪_{X,x}`. -/
instance module_base_evalQuotient : Module k (evalQuotient f L x) :=
  Module.compHom _ (baseGerm f x)

/-- The scalar action of the base field on `ℒ_x/𝔪_x²ℒ_x` is the action of `𝒪_{X,x}` through the
structure map. -/
theorem evalQuotient_smul_def (c : k) (q : evalQuotient f L x) :
    c • q = baseGerm f x c • q :=
  rfl

/-- The class of a germ of `ℒ` in `ℒ_x/𝔪_x²ℒ_x`. -/
def evalQuotientMk (w : TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x) :
    evalQuotient f L x :=
  Submodule.Quotient.mk (p := maximalSqSmul L x) w

/-- **The evaluation `ev_x : V → ℒ_x/𝔪_x²ℒ_x` as a `k`-linear map**, in the coordinates that a
basis of `V` mapping to the family `s` supplies: a tuple `c` goes to the class of
`∑ⱼ cⱼ·(sⱼ)_x`. -/
def evalCoord (s : Fin (n + 1) → Γ(L, ⊤)) (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    (Fin (n + 1) → k) →ₗ[k] evalQuotient f L x where
  toFun c := evalQuotientMk f x (∑ j, baseGerm f x (c j) • (L.presheaf.Γgerm x).hom (s j))
  map_add' c d := by
    change evalQuotientMk f x (∑ j, baseGerm f x ((c + d) j) • _) = _
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    rfl
  map_smul' a c := by
    change evalQuotientMk f x (∑ j, baseGerm f x ((a • c) j) • _) = _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum]
    rfl

/-- The evaluation sends a tuple `c` to the class of `∑ⱼ cⱼ·(sⱼ)_x`. -/
@[simp]
theorem evalCoord_apply (c : Fin (n + 1) → k) :
    evalCoord s f x c =
      evalQuotientMk f x (∑ j, baseGerm f x (c j) • (L.presheaf.Γgerm x).hom (s j)) :=
  rfl

/-- **The evaluation is surjective as a linear map** when it is surjective as a map of
coordinate tuples. -/
theorem surjective_evalCoord
    (h : Function.Surjective fun c : Fin (n + 1) → k =>
      Submodule.Quotient.mk (p := maximalSqSmul L x)
        (∑ j, baseGerm f x (c j) • (L.presheaf.Γgerm x).hom (s j))) :
    Function.Surjective (evalCoord s f x) :=
  h

/-- **The kernel of a surjective evaluation has dimension `r - dim(ℒ_x/𝔪_x²ℒ_x)`**, where
`r = n + 1` is the dimension of the linear system. -/
theorem finrank_ker_evalCoord (hev : Function.Surjective (evalCoord s f x)) :
    Module.finrank k (LinearMap.ker (evalCoord s f x)) =
      (n + 1) - Module.finrank k (evalQuotient f L x) := by
  rw [LinearMap.finrank_ker_eq_sub_of_surjective hev, Module.finrank_fin_fun]

/-- **A surjective evaluation forces `dim(ℒ_x/𝔪_x²ℒ_x) ≤ r`**, where `r = n + 1` is the
dimension of the linear system. -/
theorem finrank_evalQuotient_le (hev : Function.Surjective (evalCoord s f x)) :
    Module.finrank k (evalQuotient f L x) ≤ n + 1 := by
  have h := LinearMap.finrank_ker_add_finrank_eq_of_surjective hev
  rw [Module.finrank_fin_fun] at h
  omega

/-! ### At a closed point over an algebraically closed field -/

variable [Stacks.Ample.IsInvertibleModule X L] (hs : GeneratesStalks s)
  {V : Type u} [AddCommGroup V] [Module k V] [IsAlgClosed k] [LocallyOfFiniteType f]

/-- **The evaluation is surjective at a closed point**: if `k` is algebraically closed, `X` is
locally of finite type over `k`, `ℒ` is invertible, and the sections `s` generate the stalks of `ℒ`
and define an immersion into projective space, then `evalCoord s f x` is surjective at every
closed point `x`. -/
theorem surjective_evalCoord_of_isClosed (b : Module.Basis (Fin (n + 1)) k V)
    [AlgebraicGeometry.IsImmersion (AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f)]
    (hx : IsClosed ({x} : Set X)) :
    Function.Surjective (evalCoord s f x) :=
  surjective_evalCoord s f x (surjective_evalQuotient_of_isClosed s hs f b hx)

/-- **The kernel of the evaluation at a closed point has dimension
`r - dim(ℒ_x/𝔪_x²ℒ_x)`**, under the hypotheses of
`Stacks.ImmersionEvaluationSurjective.surjective_evalCoord_of_isClosed`. -/
theorem finrank_ker_evalCoord_of_isClosed (b : Module.Basis (Fin (n + 1)) k V)
    [AlgebraicGeometry.IsImmersion (AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f)]
    (hx : IsClosed ({x} : Set X)) :
    Module.finrank k (LinearMap.ker (evalCoord s f x)) =
      (n + 1) - Module.finrank k (evalQuotient f L x) :=
  finrank_ker_evalCoord s f x (surjective_evalCoord_of_isClosed s f x hs b hx)

/-- **At a closed point the target of the evaluation has dimension at most `r`**, under the
hypotheses of `Stacks.ImmersionEvaluationSurjective.surjective_evalCoord_of_isClosed`. -/
theorem finrank_evalQuotient_le_of_isClosed (b : Module.Basis (Fin (n + 1)) k V)
    [AlgebraicGeometry.IsImmersion (AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f)]
    (hx : IsClosed ({x} : Set X)) :
    Module.finrank k (evalQuotient f L x) ≤ n + 1 :=
  finrank_evalQuotient_le s f x (surjective_evalCoord_of_isClosed s f x hs b hx)

end Stacks.ImmersionEvaluationSurjective

end
