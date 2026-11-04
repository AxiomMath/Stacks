module

public import StacksFrontier.RingTheory.FormsTrace.Basic

/-!
# Uniqueness of trace maps on forms over a nice base

Let `A → B` be a finite projective ring map. Call `h ∈ A` a *nice element* for `B/A` if `h` is a
nonzerodivisor on every module of forms `Ω^p_A`, some power of `h` kills `Ω_{B/A}`, and the kernel
of `B ⊗_A Ω_A → Ω_B` is `h`-power torsion. For instance the discriminant of a finite free algebra
which is étale over a dense open of a base smooth over `ℤ` is such an element; these are the
universal cases of the proof of Stacks, Lemma 0FLB ("uniqueness") and Proposition 0FLC.

Over a nice element a family `Θ^p : Ω^p_B → Ω^p_A` with property (1) of Lemma 0FLB is unique, and
it is automatically linear over the forms of `A` (property (2) of Proposition 0FLC): after
multiplying by a power of `h`, every form of `B` is a combination `∑ bᵢ · f^*ωᵢ`, on which both
conditions are forced, and `h` is a nonzerodivisor on the target.

## Main definitions

* `Stacks.FormsTrace.IsNiceElement`: the three conditions on `h`.
* `Stacks.FormsTrace.pulledBackSpan`: the `B`-span of the pulled back forms in `Ω^p_B`.

## Main results

* `Stacks.FormsTrace.IsNiceElement.pow_smul_mem_pulledBackSpan`: `h^{pN} · η` is a combination of
  pulled back forms.
* `Stacks.FormsTrace.IsFormsTrace.apply_eq_of_mem_pulledBackSpan`: two families with property (1)
  agree on combinations of pulled back forms.
* `Stacks.FormsTrace.IsFormsTrace.eq_of_isNiceElement`: uniqueness over a nice element.
* `Stacks.FormsTrace.IsFormsTrace.isWedgeLinear_of_isNiceElement`: property (2) over a nice
  element.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u

namespace Stacks.FormsTrace

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **A nice element** `h ∈ A` for `B/A`: it is a nonzerodivisor on every `Ω^p_A`, a power of it
kills `Ω_{B/A}`, and the kernel of `B ⊗_A Ω_A → Ω_B` is `h`-power torsion. -/
structure IsNiceElement (h : A) : Prop where
  /-- `h` is a nonzerodivisor on the forms of `A`. -/
  regular : ∀ p : ℕ, IsSMulRegular (⋀[A]^p Ω[A⁄ℤ]) h
  /-- A power of `h` kills the relative differentials. -/
  pow_smul_kaehler : ∃ N : ℕ, ∀ x : Ω[B⁄A], h ^ N • x = 0
  /-- The kernel of `B ⊗_A Ω_A → Ω_B` is `h`-power torsion. -/
  ker_torsion : ∀ x ∈ LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ A B),
    ∃ n : ℕ, h ^ n • x = 0

/-- The `B`-span of the pulled back forms `f^*ω`, `ω ∈ Ω^p_A`, inside `Ω^p_B`. -/
abbrev pulledBackSpan (p : ℕ) : Submodule B (⋀[B]^p Ω[B⁄ℤ]) :=
  Submodule.span B (Set.range (formsMap A B p))

variable {A B}

/-- A pulled back form lies in the span of pulled back forms. -/
theorem formsMap_mem_pulledBackSpan (p : ℕ) (ω : ⋀[A]^p Ω[A⁄ℤ]) :
    formsMap A B p ω ∈ pulledBackSpan A B p :=
  Submodule.subset_span ⟨ω, rfl⟩

/-- The span of pulled back forms is closed under the wedge product. -/
theorem wedgeMul_mem_pulledBackSpan {q p : ℕ} {x : ⋀[B]^q Ω[B⁄ℤ]} {y : ⋀[B]^p Ω[B⁄ℤ]}
    (hx : x ∈ pulledBackSpan A B q) (hy : y ∈ pulledBackSpan A B p) :
    exteriorPower.wedgeMul q p x y ∈ pulledBackSpan A B (q + p) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨η, rfl⟩ := hy
      rw [← formsMap_wedgeMul]
      exact formsMap_mem_pulledBackSpan _ _
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul b y _ hy => rw [map_smul]; exact Submodule.smul_mem _ b hy
  | zero => simp
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hz
  | smul b x _ hx => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ b hx

/-- **Degree one**: if `h^N` kills `Ω_{B/A}`, then `h^N · dx` is a combination of pulled back
forms for every `x ∈ Ω_B`. -/
theorem pow_smul_oneEquiv_symm_mem_pulledBackSpan {h : A} {N : ℕ}
    (hN : ∀ x : Ω[B⁄A], h ^ N • x = 0) (x : Ω[B⁄ℤ]) :
    h ^ N • (exteriorPower.oneEquiv B Ω[B⁄ℤ]).symm x ∈ pulledBackSpan A B 1 := by
  have hx : h ^ N • x ∈ LinearMap.range (KaehlerDifferential.mapBaseChange ℤ A B) := by
    rw [(KaehlerDifferential.exact_mapBaseChange_map ℤ A B).linearMap_ker_eq.symm,
      LinearMap.mem_ker, ← algebraMap_smul B, map_smul, algebraMap_smul]
    exact hN _
  obtain ⟨y, hy⟩ := hx
  rw [← algebraMap_smul B (h ^ N), ← map_smul, algebraMap_smul, ← hy]
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul, map_smul]
    refine Submodule.smul_mem _ b ?_
    have : (exteriorPower.oneEquiv B Ω[B⁄ℤ]).symm (KaehlerDifferential.map ℤ ℤ A B ω) =
        formsMap A B 1 ((exteriorPower.oneEquiv A Ω[A⁄ℤ]).symm ω) := by
      rw [exteriorPower.oneEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply, formsMap_ιMulti]
    rw [this]
    exact formsMap_mem_pulledBackSpan _ _
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

/-- Scalars of `A` pass through the wedge product of forms of `B`. -/
theorem smul_wedgeMul_smul {q p : ℕ} (c d : A) (x : ⋀[B]^q Ω[B⁄ℤ]) (y : ⋀[B]^p Ω[B⁄ℤ]) :
    exteriorPower.wedgeMul q p (c • x) (d • y) = (c * d) • exteriorPower.wedgeMul q p x y := by
  rw [← algebraMap_smul B c x, ← algebraMap_smul B d y, map_smul, map_smul, LinearMap.smul_apply,
    smul_smul, ← map_mul, mul_comm, algebraMap_smul]

/-- The `h^{pN}`-multiple of a wedge of `p` Kähler differentials of `B` is a combination of
pulled back forms, when `h^N` kills `Ω_{B/A}`. -/
theorem pow_smul_ιMulti_mem_pulledBackSpan {h : A} {N : ℕ} (hN : ∀ x : Ω[B⁄A], h ^ N • x = 0) :
    ∀ (p : ℕ) (v : Fin p → Ω[B⁄ℤ]),
      (h ^ N) ^ p • exteriorPower.ιMulti B p v ∈ pulledBackSpan A B p := by
  intro p
  induction p with
  | zero =>
    intro v
    rw [pow_zero, one_smul]
    have : exteriorPower.ιMulti B 0 v = formsMap A B 0 (exteriorPower.ιMulti A 0 Fin.elim0) := by
      rw [formsMap_ιMulti]
      congr 1
      funext i
      exact i.elim0
    rw [this]
    exact formsMap_mem_pulledBackSpan _ _
  | succ p ih =>
    intro v
    have hsplit : exteriorPower.ιMulti B (p + 1) v =
        exteriorPower.wedgeMul p 1 (exteriorPower.ιMulti B p (Fin.init v))
          ((exteriorPower.oneEquiv B Ω[B⁄ℤ]).symm (v (Fin.last p))) := by
      rw [exteriorPower.oneEquiv_symm_apply, exteriorPower.wedgeMul_ιMulti,
        Fin.append_right_eq_snoc, Fin.snoc_init_self]
    rw [hsplit, pow_succ, ← smul_wedgeMul_smul]
    exact wedgeMul_mem_pulledBackSpan (ih _) (pow_smul_oneEquiv_symm_mem_pulledBackSpan hN _)

/-- **Every form becomes a combination of pulled back forms after multiplication by a power of
`h`**, when `h^N` kills `Ω_{B/A}`: `h^{pN} · η ∈ pulledBackSpan A B p`. -/
theorem pow_smul_mem_pulledBackSpan {h : A} {N : ℕ} (hN : ∀ x : Ω[B⁄A], h ^ N • x = 0)
    (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) : (h ^ N) ^ p • η ∈ pulledBackSpan A B p := by
  have hη : η ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B p)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact pow_smul_ιMulti_mem_pulledBackSpan hN p v
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ b hx

/-- The `h^{pN}`-multiple of a form of `B` is a combination of pulled back forms, for a nice
element `h`. -/
theorem IsNiceElement.exists_pow_smul_mem_pulledBackSpan {h : A} (hh : IsNiceElement A B h) :
    ∃ N : ℕ, ∀ (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]), (h ^ N) ^ p • η ∈ pulledBackSpan A B p := by
  obtain ⟨N, hN⟩ := hh.pow_smul_kaehler
  exact ⟨N, pow_smul_mem_pulledBackSpan hN⟩

variable [Module.Finite A B] [Module.Projective A B]

/-- **A family with property (1) of Lemma 0FLB is determined on combinations of pulled back
forms**: there it is `∑ bᵢ · f^*ωᵢ ↦ ∑ Trace(bᵢ) · ωᵢ`. -/
theorem IsFormsTrace.exists_apply_of_mem_pulledBackSpan
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ) {p : ℕ}
    {x : ⋀[B]^p Ω[B⁄ℤ]} (hx : x ∈ pulledBackSpan A B p) :
    ∃ c : ⋀[A]^p Ω[A⁄ℤ] →₀ B, (c.sum fun ω b => b • formsMap A B p ω) = x ∧
      Θ p x = c.sum fun ω b => trace A B b • ω := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨c, rfl, ?_⟩
  rw [map_finsuppSum]
  exact Finsupp.sum_congr fun ω _ => hΘ p _ ω

/-- Two families with property (1) of Lemma 0FLB agree on combinations of pulled back forms. -/
theorem IsFormsTrace.apply_eq_of_mem_pulledBackSpan
    {Θ Θ' : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ)
    (hΘ' : IsFormsTrace A B Θ') {p : ℕ} {x : ⋀[B]^p Ω[B⁄ℤ]} (hx : x ∈ pulledBackSpan A B p) :
    Θ p x = Θ' p x := by
  obtain ⟨c, rfl, hc⟩ := hΘ.exists_apply_of_mem_pulledBackSpan hx
  rw [hc, map_finsuppSum]
  exact Finsupp.sum_congr fun ω _ => (hΘ' p _ ω).symm

/-- **Uniqueness over a nice element** (proof of Stacks, Lemma 0FLB, "uniqueness"): two families
`Θ^p : Ω^p_B → Ω^p_A` with property (1) are equal. -/
theorem IsFormsTrace.eq_of_isNiceElement {h : A} (hh : IsNiceElement A B h)
    {Θ Θ' : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ)
    (hΘ' : IsFormsTrace A B Θ') : Θ = Θ' := by
  obtain ⟨N, hN⟩ := hh.exists_pow_smul_mem_pulledBackSpan
  funext p
  refine LinearMap.ext fun η => ?_
  refine ((hh.regular p).pow (N * p)) ?_
  show h ^ (N * p) • Θ p η = h ^ (N * p) • Θ' p η
  rw [pow_mul, ← map_smul, ← map_smul]
  exact hΘ.apply_eq_of_mem_pulledBackSpan hΘ' (hN p η)

/-- **Linearity over the forms of `A`** (property (2) of Stacks, Proposition 0FLC) holds on
combinations of pulled back forms, for a family with property (1). -/
theorem IsFormsTrace.wedge_of_mem_pulledBackSpan
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ) {q p : ℕ}
    (ω : ⋀[A]^q Ω[A⁄ℤ]) {x : ⋀[B]^p Ω[B⁄ℤ]} (hx : x ∈ pulledBackSpan A B p) :
    Θ (q + p) (exteriorPower.wedgeMul q p (formsMap A B q ω) x) =
      exteriorPower.wedgeMul q p ω (Θ p x) := by
  obtain ⟨c, rfl, hc⟩ := hΘ.exists_apply_of_mem_pulledBackSpan hx
  rw [hc, map_finsuppSum, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun η _ => ?_
  rw [map_smul, ← formsMap_wedgeMul, hΘ, map_smul]

/-- **Linearity over the forms of `A` over a nice element** (property (2) of Stacks,
Proposition 0FLC): a family with property (1) of Lemma 0FLB satisfies
`Θ(ω ∧ η) = ω ∧ Θ(η)`. -/
theorem IsFormsTrace.isWedgeLinear_of_isNiceElement {h : A} (hh : IsNiceElement A B h)
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ) :
    IsWedgeLinear A B Θ := by
  obtain ⟨N, hN⟩ := hh.exists_pow_smul_mem_pulledBackSpan
  intro q p ω η
  refine ((hh.regular (q + p)).pow (N * p)) ?_
  show h ^ (N * p) • Θ (q + p) _ = h ^ (N * p) • _
  have h1 : exteriorPower.wedgeMul q p ω (h ^ (N * p) • Θ p η) =
      h ^ (N * p) • exteriorPower.wedgeMul q p ω (Θ p η) := map_smul _ _ _
  have h2 : exteriorPower.wedgeMul q p (formsMap A B q ω) (h ^ (N * p) • η) =
      h ^ (N * p) • exteriorPower.wedgeMul q p (formsMap A B q ω) η := by
    rw [← algebraMap_smul B, map_smul, algebraMap_smul]
  rw [← map_smul, ← h1, ← h2, ← map_smul, pow_mul]
  exact hΘ.wedge_of_mem_pulledBackSpan ω (hN p η)

end Stacks.FormsTrace

end
