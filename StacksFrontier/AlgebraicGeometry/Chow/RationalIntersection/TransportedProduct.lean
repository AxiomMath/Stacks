module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Products transported along a bijective family of commuting operators

Let `R` be a commutative ring, `K` and `V` modules over `R`, and `T : K → End_R(V)` a linear
map whose operators `T a` pairwise commute. Suppose given `e ∈ V` such that `Φ : a ↦ T a e` is a
bijection `K ≅ V`. Then

  `α · β = T (Φ⁻¹ α) β`

is an `R`-bilinear product on `V`, the unique one with `(T a e) · β = T a β`, and it is
commutative and associative with unit `e`: writing `α = T a e`, `β = T b e`, `γ = T c e`, both
`α · β` and `β · α` are `T a (T b e) = T b (T a e)`, and both bracketings of `α · β · γ` are
`T a (T b (T c e))` up to reordering the operators.

This is the algebra underlying the rational intersection product of Stacks, Section 0FEX: there
`V = CH_*(X) ⊗ 𝐐` for a regular scheme `X`, `K = K_0(Vect(X)) ⊗ 𝐐`, `T a = ch(a) ∩ -` and
`e = [X]`, and Lemma 0FEY says that `Φ` is bijective. The Chern character caps commute, but no
multiplicativity of `T` enters: commutativity of the operators alone gives associativity.

The product respects gradings. Suppose `V` carries an independent family of submodules `V^i`
indexed by a commutative monoid, that `T = ∑_{p ∈ N} T_p` for a finite set `N` of components
`T_p` which pairwise commute and map `V^i` into `V^{i+p}`, and that `e ∈ V^0`. If `α ∈ V^i` then
`α = ∑_p T_p(Φ⁻¹ α) e` with `T_p(Φ⁻¹ α) e ∈ V^p`, so `T_p(Φ⁻¹ α) e = 0` for `p ≠ i`; hence
`T_p(Φ⁻¹ α) β = T(Φ⁻¹ β) (T_p(Φ⁻¹ α) e) = 0` for `p ≠ i`, and `α · β = T_i(Φ⁻¹ α) β`, which lies
in `V^{i+j}` when `β ∈ V^j`.

## Main definitions

* `Stacks.Chow.transportedProduct` — the product `α · β = T (Φ⁻¹ α) β`.

## Main results

* `Stacks.Chow.transportedProduct_apply_left` — `(T a e) · β = T a β`.
* `Stacks.Chow.eq_transportedProduct` — uniqueness of a bilinear product with that property.
* `Stacks.Chow.transportedProduct_apply_base`, `Stacks.Chow.transportedProduct_base_apply`,
  `Stacks.Chow.transportedProduct_base_apply_of_eq_one` — `e` is a unit.
* `Stacks.Chow.transportedProduct_comm`, `Stacks.Chow.transportedProduct_assoc` — commutativity
  and associativity, from the commutativity of the operators.
* `Stacks.Chow.transportedProduct_apply_eq_component` — for `α ∈ V^i`, `α · β = T_i(Φ⁻¹ α) β`.
* `Stacks.Chow.transportedProduct_mem` — `V^i · V^j ⊆ V^{i+j}`.

## References

* [Stacks Project, Tag 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
-/

@[expose] public noncomputable section

namespace Stacks.Chow

section Product

variable {R K V : Type*} [CommSemiring R] [AddCommMonoid K] [Module R K] [AddCommMonoid V]
  [Module R V] (T : K →ₗ[R] Module.End R V) (e : V) (hT : Function.Bijective (T.flip e))

/-- **The product transported along `a ↦ T a e`.** For a linear family of operators
`T : K → End(V)` and `e ∈ V` such that `Φ : a ↦ T a e` is bijective, the bilinear product
`α · β = T (Φ⁻¹ α) β` on `V`. -/
def transportedProduct : V →ₗ[R] V →ₗ[R] V :=
  T ∘ₗ (LinearEquiv.ofBijective (T.flip e) hT).symm.toLinearMap

/-- The transported product, unfolded: `α · β = T (Φ⁻¹ α) β`. -/
theorem transportedProduct_apply (α β : V) :
    transportedProduct T e hT α β = T ((LinearEquiv.ofBijective (T.flip e) hT).symm α) β :=
  rfl

/-- The preimage of `α` under `a ↦ T a e` is sent to `α`. -/
theorem apply_symm_ofBijective_flip (α : V) :
    T ((LinearEquiv.ofBijective (T.flip e) hT).symm α) e = α :=
  (LinearEquiv.ofBijective (T.flip e) hT).apply_symm_apply α

/-- **The defining property of the transported product:** `(T a e) · β = T a β`. -/
theorem transportedProduct_apply_left (a : K) (β : V) :
    transportedProduct T e hT (T a e) β = T a β := by
  rw [transportedProduct_apply]
  congr 2
  exact (LinearEquiv.ofBijective (T.flip e) hT).symm_apply_apply a

/-- Commuting endomorphisms can be applied in either order. -/
private theorem apply_apply_comm {f g : Module.End R V} (h : Commute f g) (x : V) :
    f (g x) = g (f x) :=
  LinearMap.congr_fun h.eq x

/-- **Uniqueness of the transported product:** a bilinear product with `(T a e) · β = T a β`
for all `a` and `β` is the transported product. -/
theorem eq_transportedProduct {μ : V →ₗ[R] V →ₗ[R] V} (h : ∀ a β, μ (T a e) β = T a β) :
    μ = transportedProduct T e hT := by
  refine LinearMap.ext fun α ↦ LinearMap.ext fun β ↦ ?_
  obtain ⟨a, rfl⟩ := hT.2 α
  rw [LinearMap.flip_apply, h, transportedProduct_apply_left]

/-- `e` is a right unit: `α · e = α`. -/
theorem transportedProduct_apply_base (α : V) : transportedProduct T e hT α e = α :=
  apply_symm_ofBijective_flip T e hT α

/-- `e` is a left unit as soon as some `a₀` acts as the identity. -/
theorem transportedProduct_base_apply_of_eq_one {a₀ : K} (ha₀ : T a₀ = 1) (β : V) :
    transportedProduct T e hT e β = β := by
  simpa only [ha₀, Module.End.one_apply] using transportedProduct_apply_left T e hT a₀ β

/-- **Commutativity of the transported product**, when the operators `T a` pairwise commute. -/
theorem transportedProduct_comm (hc : ∀ a b, Commute (T a) (T b)) (α β : V) :
    transportedProduct T e hT α β = transportedProduct T e hT β α := by
  obtain ⟨a, rfl⟩ := hT.2 α
  obtain ⟨b, rfl⟩ := hT.2 β
  simp only [LinearMap.flip_apply, transportedProduct_apply_left]
  exact apply_apply_comm (hc a b) e

/-- `e` is a two-sided unit when the operators `T a` pairwise commute. -/
theorem transportedProduct_base_apply (hc : ∀ a b, Commute (T a) (T b)) (β : V) :
    transportedProduct T e hT e β = β := by
  rw [transportedProduct_comm T e hT hc, transportedProduct_apply_base]

/-- **Associativity of the transported product**, when the operators `T a` pairwise commute. No
multiplicativity of `T` is needed. -/
theorem transportedProduct_assoc (hc : ∀ a b, Commute (T a) (T b)) (α β γ : V) :
    transportedProduct T e hT (transportedProduct T e hT α β) γ =
      transportedProduct T e hT α (transportedProduct T e hT β γ) := by
  obtain ⟨a, rfl⟩ := hT.2 α
  obtain ⟨b, rfl⟩ := hT.2 β
  obtain ⟨c, rfl⟩ := hT.2 γ
  simp only [LinearMap.flip_apply, transportedProduct_apply_left]
  obtain ⟨d, hd⟩ : ∃ d, T d e = T a (T b e) := hT.2 _
  rw [← hd, transportedProduct_apply_left, apply_apply_comm (hc d c), hd,
    apply_apply_comm (hc c a), apply_apply_comm (hc c b)]

end Product

section Grading

variable {R K V ι : Type*} [CommRing R] [AddCommGroup K] [Module R K] [AddCommGroup V]
  [Module R V] [AddCommMonoid ι] {𝒱 : ι → Submodule R V}

/-- In an independent family of submodules, if a finite sum `∑_{p ∈ N} x_p` with `x_p ∈ V^p`
lies in `V^i`, then every summand with `p ≠ i` vanishes. -/
theorem iSupIndep.eq_zero_of_sum_mem {ι : Type*} {𝒱 : ι → Submodule R V} (h𝒱 : iSupIndep 𝒱)
    {N : Finset ι} {x : ι → V} (hx : ∀ p ∈ N, x p ∈ 𝒱 p) {i : ι} (hsum : ∑ p ∈ N, x p ∈ 𝒱 i)
    {p : ι} (hp : p ∈ N) (hpi : p ≠ i) : x p = 0 := by
  classical
  let W : Submodule R V := ⨆ (j : ι) (_ : j ≠ p), 𝒱 j
  have hle : ∀ j, j ≠ p → 𝒱 j ≤ W := fun j hj ↦ le_iSup₂ (f := fun j (_ : j ≠ p) ↦ 𝒱 j) j hj
  have hrest : ∑ q ∈ N.erase p, x q ∈ W :=
    Submodule.sum_mem _ fun q hq ↦
      hle q (Finset.ne_of_mem_erase hq) (hx q (Finset.mem_of_mem_erase hq))
  refine Submodule.disjoint_def.1 (h𝒱 p) _ (hx p hp) ?_
  simpa [← Finset.add_sum_erase N x hp] using W.sub_mem (hle i hpi.symm hsum) hrest

variable (T : K →ₗ[R] Module.End R V) (e : V) (hT : Function.Bijective (T.flip e))
  {N : Finset ι} {Tc : ι → K →ₗ[R] Module.End R V}

omit [AddCommMonoid ι] in
/-- If `T = ∑_{p ∈ N} T_p` with pairwise commuting components, then the operators `T a`
pairwise commute. -/
theorem commute_of_eq_sum (hsum : T = ∑ p ∈ N, Tc p)
    (hcomm : ∀ p ∈ N, ∀ q ∈ N, ∀ a b, Commute (Tc p a) (Tc q b)) (a b : K) :
    Commute (T a) (T b) := by
  rw [hsum, LinearMap.sum_apply, LinearMap.sum_apply]
  exact Commute.sum_left _ _ _ fun p hp ↦ Commute.sum_right _ _ _ fun q hq ↦ hcomm p hp q hq a b

omit [AddCommMonoid ι] in
/-- A component `T_p a` commutes with every operator `T b`. -/
theorem commute_component_of_eq_sum (hsum : T = ∑ p ∈ N, Tc p)
    (hcomm : ∀ p ∈ N, ∀ q ∈ N, ∀ a b, Commute (Tc p a) (Tc q b)) {p : ι} (hp : p ∈ N)
    (a b : K) : Commute (Tc p a) (T b) := by
  rw [hsum, LinearMap.sum_apply]
  exact Commute.sum_right _ _ _ fun q hq ↦ hcomm p hp q hq a b

/-- **The transported product of a homogeneous element.** If `α ∈ V^i`, then only the component
`T_i` of `T` contributes to `α · β`: it is `T_i(Φ⁻¹ α) β` if `i ∈ N`, and `0` otherwise. -/
theorem transportedProduct_apply_eq_component [DecidableEq ι] (h𝒱 : iSupIndep 𝒱)
    (hsum : T = ∑ p ∈ N, Tc p)
    (hcomm : ∀ p ∈ N, ∀ q ∈ N, ∀ a b, Commute (Tc p a) (Tc q b))
    (hgr : ∀ p ∈ N, ∀ a i, ∀ x ∈ 𝒱 i, Tc p a x ∈ 𝒱 (i + p)) (he : e ∈ 𝒱 0) {i : ι} {α : V}
    (hα : α ∈ 𝒱 i) (β : V) :
    transportedProduct T e hT α β =
      if i ∈ N then Tc i ((LinearEquiv.ofBijective (T.flip e) hT).symm α) β else 0 := by
  have hTe : ∀ c, T c = ∑ p ∈ N, Tc p c := fun c ↦ by rw [hsum, LinearMap.sum_apply]
  have hα' := apply_symm_ofBijective_flip T e hT α
  rw [transportedProduct_apply]
  generalize (LinearEquiv.ofBijective (T.flip e) hT).symm α = a at hα' ⊢
  obtain ⟨b, rfl⟩ : ∃ b, T b e = β := ⟨_, apply_symm_ofBijective_flip T e hT β⟩
  rw [hTe a, LinearMap.sum_apply] at hα'
  -- the components of `α = T a e` other than the `i`th vanish
  have hcomp : ∀ p ∈ N, p ≠ i → Tc p a e = 0 := by
    intro p hp hpi
    refine iSupIndep.eq_zero_of_sum_mem h𝒱 (x := fun p ↦ Tc p a e)
      (fun q hq ↦ by simpa using hgr q hq a 0 e he) ?_ hp hpi
    rwa [hα']
  -- hence so do those of `α · β`
  have hvan : ∀ p ∈ N, p ≠ i → Tc p a (T b e) = 0 := by
    intro p hp hpi
    rw [apply_apply_comm (commute_component_of_eq_sum T hsum hcomm hp a b), hcomp p hp hpi,
      map_zero]
  rw [hTe, LinearMap.sum_apply]
  split_ifs with hi
  · exact Finset.sum_eq_single_of_mem i hi hvan
  · exact Finset.sum_eq_zero fun p hp ↦ hvan p hp fun hpi ↦ hi (hpi ▸ hp)

/-- **The transported product respects the grading:** `V^i · V^j ⊆ V^{i+j}`. -/
theorem transportedProduct_mem (h𝒱 : iSupIndep 𝒱) (hsum : T = ∑ p ∈ N, Tc p)
    (hcomm : ∀ p ∈ N, ∀ q ∈ N, ∀ a b, Commute (Tc p a) (Tc q b))
    (hgr : ∀ p ∈ N, ∀ a i, ∀ x ∈ 𝒱 i, Tc p a x ∈ 𝒱 (i + p)) (he : e ∈ 𝒱 0) {i j : ι} {α β : V}
    (hα : α ∈ 𝒱 i) (hβ : β ∈ 𝒱 j) : transportedProduct T e hT α β ∈ 𝒱 (i + j) := by
  classical
  rw [transportedProduct_apply_eq_component T e hT h𝒱 hsum hcomm hgr he hα]
  split_ifs with hi
  · rw [add_comm]
    exact hgr i hi _ j β hβ
  · exact zero_mem _

end Grading

end Stacks.Chow

end
