module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Linear forms making a family of pairings perfect are unique up to a unit

Let `k` be a field, `R` a commutative `k`-algebra and `V` an `R`-module. A linear form
`t : V → k` gives the pairing `R × V → k`, `(g, v) ↦ t (g • v)`. If this pairing is perfect, every
linear form on `V` is `v ↦ t (g • v)` for exactly one `g ∈ R`.

Suppose moreover that `c i : A i × B i → V` is a family of `k`-bilinear maps, `R`-linear in the
first variable, one of which is the action `R × V → V` up to identifications. If `t` makes every
pairing `t ∘ c i` perfect, then a second linear form `t'` makes every `t' ∘ c i` perfect if and
only if `t' = t ∘ (u • -)` for a unit `u` of `R`, and this unit is unique. This is the uniqueness
argument of [Stacks, Tag 0FW4], where `R = H⁰(X, 𝒪_X)`, `V = H^d(X, Ω^d_{X/k})` and the pairings
are the cup products in complementary bidegrees.

## Main definitions

* `LinearMap.smulPairing`: the pairing `(g, v) ↦ t (g • v)`.

## Main results

* `LinearMap.existsUnique_smulPairing_eq`: if `smulPairing t` is perfect, every linear form on `V`
  is `smulPairing t g` for a unique `g`.
* `LinearMap.isPerfPair_compr₂_iff_existsUnique_unit`: the classification of the linear forms
  making a family of pairings perfect.

## References

* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
-/

@[expose] public section

namespace LinearMap

variable {k R V : Type*} [Field k] [CommRing R] [Algebra k R]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]

/-- The pairing `R × V → k`, `(g, v) ↦ t (g • v)`, attached to a linear form `t` on an
`R`-module `V`. -/
noncomputable def smulPairing (t : V →ₗ[k] k) : R →ₗ[k] V →ₗ[k] k :=
  LinearMap.mk₂ k (fun g v ↦ t (g • v)) (fun g g' v ↦ by rw [add_smul, map_add])
    (fun c g v ↦ by rw [smul_assoc, map_smul]) (fun g v v' ↦ by rw [smul_add, map_add])
    (fun c g v ↦ by rw [smul_comm, map_smul])

/-- `smulPairing t g v` is `t (g • v)`. -/
@[simp]
theorem smulPairing_apply (t : V →ₗ[k] k) (g : R) (v : V) :
    smulPairing t g v = t (g • v) :=
  rfl

/-- `smulPairing t g` is `t` precomposed with the action of `g`. -/
theorem smulPairing_eq_comp (t : V →ₗ[k] k) (g : R) :
    smulPairing t g = t ∘ₗ Algebra.lsmul k k V g :=
  rfl

/-- If `(g, v) ↦ t (g • v)` is a perfect pairing, every linear form on `V` is
`v ↦ t (g • v)` for exactly one `g ∈ R`. -/
theorem existsUnique_smulPairing_eq (t : V →ₗ[k] k) [(smulPairing (R := R) t).IsPerfPair]
    (t' : V →ₗ[k] k) : ∃! g : R, smulPairing t g = t' :=
  (IsPerfPair.bijective_left (smulPairing (R := R) t)).existsUnique t'

/-- The action of a unit `u` of `R` on an `R`-module, as a `k`-linear automorphism. -/
noncomputable def unitSMulEquiv (M : Type*) [AddCommGroup M] [Module k M] [Module R M]
    [IsScalarTower k R M] (u : Rˣ) : M ≃ₗ[k] M :=
  LinearMap.GeneralLinearGroup.toLinearEquiv
    (Units.map (Algebra.lsmul k k M).toMonoidHom u)

/-- `unitSMulEquiv M u` sends `a` to `u • a`. -/
@[simp]
theorem unitSMulEquiv_apply (M : Type*) [AddCommGroup M] [Module k M] [Module R M]
    [IsScalarTower k R M] (u : Rˣ) (a : M) : unitSMulEquiv (k := k) M u a = (u : R) • a :=
  rfl

section Family

variable {ι : Type*} {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
  [∀ i, Module R (A i)] [∀ i, IsScalarTower k R (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, Module k (B i)]

omit [∀ i, Module R (A i)] [∀ i, IsScalarTower k R (A i)] in
/-- If one member `c i₀` of the family is the action `R × V → V` up to identifications, the
pairing `t ∘ c i₀` is perfect exactly when `smulPairing t` is. -/
theorem isPerfPair_smulPairing_of_compr₂ (c : ∀ i, A i →ₗ[k] B i →ₗ[k] V) {i₀ : ι}
    (eA : R ≃ₗ[k] A i₀) (eB : V ≃ₗ[k] B i₀) (h₀ : ∀ (g : R) (v : V), c i₀ (eA g) (eB v) = g • v)
    (t : V →ₗ[k] k) [((c i₀).compr₂ t).IsPerfPair] : (smulPairing (R := R) t).IsPerfPair :=
  IsPerfPair.congr ((c i₀).compr₂ t) eA eB _
    (by ext a b; simpa using congrArg t (h₀ (eA.symm a) (eB.symm b)).symm)

/-- **Linear forms making a family of pairings perfect are unique up to a unit.** Let
`c i : A i × B i → V` be `k`-bilinear and `R`-linear in the first variable, and let one member
`c i₀` be the action `R × V → V` up to the identifications `eA`, `eB`. If `t` makes every pairing
`t ∘ c i` perfect, then `t'` makes every `t' ∘ c i` perfect if and only if
`t' = t ∘ (u • -)` for a unit `u` of `R`, which is then unique. -/
theorem isPerfPair_compr₂_iff_existsUnique_unit (c : ∀ i, A i →ₗ[k] B i →ₗ[k] V)
    (hc : ∀ i (g : R) (a : A i) (b : B i), c i (g • a) b = g • c i a b) {i₀ : ι}
    (eA : R ≃ₗ[k] A i₀) (eB : V ≃ₗ[k] B i₀) (h₀ : ∀ (g : R) (v : V), c i₀ (eA g) (eB v) = g • v)
    (t t' : V →ₗ[k] k) (ht : ∀ i, ((c i).compr₂ t).IsPerfPair) :
    (∀ i, ((c i).compr₂ t').IsPerfPair) ↔
      ∃! u : Rˣ, t' = t ∘ₗ Algebra.lsmul k k V (u : R) := by
  have := ht i₀
  have hP := isPerfPair_smulPairing_of_compr₂ c eA eB h₀ t
  constructor
  · intro ht'
    have := ht' i₀
    have hP' := isPerfPair_smulPairing_of_compr₂ c eA eB h₀ t'
    obtain ⟨g, hg⟩ := (existsUnique_smulPairing_eq (R := R) t t').exists
    -- `smulPairing t'` is `smulPairing t` precomposed with multiplication by `g`
    have hcomp : (smulPairing (R := R) t' : R → V →ₗ[k] k) =
        (smulPairing (R := R) t) ∘ (fun a ↦ g * a) := by
      funext a
      ext v
      simp [← hg, smul_smul]
    have hmul : Function.Bijective (fun a : R ↦ g * a) := by
      have h := IsPerfPair.bijective_left (smulPairing (R := R) t')
      rw [hcomp] at h
      exact (Function.Bijective.of_comp_iff' (IsPerfPair.bijective_left _) _).1 h
    obtain ⟨a, ha⟩ := hmul.2 1
    let u : Rˣ := ⟨g, a, ha, by rw [mul_comm]; exact ha⟩
    refine ⟨u, by rw [← hg]; rfl, fun u' hu' ↦ Units.ext
      ((existsUnique_smulPairing_eq (R := R) t t').unique (by rw [smulPairing_eq_comp, ← hu']) hg)⟩
  · rintro ⟨u, hu, -⟩ i
    have := ht i
    have h : (c i).compr₂ t' =
        ((c i).compr₂ t).compl₁₂ (unitSMulEquiv (A i) u).toLinearMap
          (LinearEquiv.refl k (B i)).toLinearMap := by
      ext a b
      simp [hu, hc]
    rw [h]
    infer_instance

end Family

end LinearMap
