module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.DualNumber
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.Representation.Cofibered

/-!
# Infinitesimal automorphisms of a representation (Stacks 0DVT)

Let `ρ₀ : Γ → GL_k(V)` be a finite-dimensional representation. Then the infinitesimal
automorphism group of its deformation category is `H⁰(Γ, End_k(V))`.

Following Stacks Project, Tag 0DVT: let `M` be the module of a deformation of `(V, ρ₀)`
over the dual numbers, so `M` is finite free over `k[ε]` with `M/εM = V`. An element of the
infinitesimal automorphism group is an automorphism `γ : M → M` over `k[ε]`, compatible
with the reduction to `V` and commuting with the action of `Γ`. Writing
`γ = id + ε ψ` with `ψ` an endomorphism of `V`, commutation with `Γ` says exactly that `ψ`
is `Γ`-equivariant, and composition of two such automorphisms adds the corresponding `ψ`
because `ε² = 0`. The `Γ`-equivariant endomorphisms of `V` are the invariants of the
conjugation representation `Representation.linHom ρ₀ ρ₀`, i.e. `H⁰(Γ, End_k(V))`.

## Implementation notes

The condition defining the infinitesimal automorphism group of Tag 06JQ — commuting with
the canonical map back to the special fibre — is automatic here: the object of the
deformation category over the residue field is a terminal object of that category, since
the residue field is terminal in `𝒞_Λ` and a morphism over an isomorphism in a category
cofibered in groupoids is an isomorphism. So the group is the full automorphism group of
the chosen pushforward in its fibre.

The dual-number structure is used only through two facts about the element `ε` of the
coefficient algebra: a scalar is killed by the reduction map exactly when `ε` divides it,
and `ε` annihilates exactly its own multiples. Everything else is a computation in a free
module with a basis.

## Main results

* `Deformation.infinitesimalAutomorphismsEquivH0`: **Stacks 0DVT**.
* `Deformation.exists_infinitesimalAutomorphismsLinearEquivH0`: **Stacks 0DVT**, the clause
  that the space of infinitesimal automorphisms is always finite dimensional. The group of
  infinitesimal automorphisms is a subgroup of an automorphism group, so the `k`-vector space
  structure the clause speaks of is produced there too, pinned by having composition for its
  addition and the identification above for a `k`-linear equivalence.
* `Deformation.finiteDimensional_groupCohomology_zero_linHom`: the same finiteness on the
  other side of that identification.

## References

* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u w

variable {Λ : Type u} {k Γ : Type w} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]

/-! ### The element `ε` of a coefficient algebra isomorphic to the dual numbers -/

/-- In the dual numbers over a field, `ε` annihilates exactly the elements with vanishing
constant term. -/
theorem DualNumber.eps_mul_eq_zero_iff {κ : Type*} [Field κ] (z : DualNumber κ) :
    DualNumber.eps * z = 0 ↔ z.fst = 0 := by
  constructor
  · intro h
    simpa [TrivSqZeroExt.snd_mul] using congrArg TrivSqZeroExt.snd h
  · intro h
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul]
    · simp [TrivSqZeroExt.snd_mul, h]

namespace ArtinianLocalAlgCat

/-- An object of `𝒞_Λ` isomorphic to the dual numbers over `k` carries an element `ε`
whose multiples are exactly the kernel of any morphism to an object with vanishing maximal
ideal, and which annihilates exactly its own multiples. These two properties are all that
the dual-number structure is used for. -/
theorem exists_eps {R K : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (hR : Nonempty (R ≃ₐ[Λ] DualNumber k)) (hK : IsLocalRing.maximalIdeal K = ⊥)
    (π : R ⟶ K) :
    ∃ ε : R, (∀ a : R, π.hom a = 0 ↔ ε ∣ a) ∧ (∀ a : R, ε * a = 0 ↔ ε ∣ a) := by
  obtain ⟨κ⟩ := hR
  have hdvd : ∀ a : R, κ.symm DualNumber.eps ∣ a ↔ DualNumber.eps ∣ κ a := by
    intro a
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨κ c, by rw [map_mul, AlgEquiv.apply_symm_apply]⟩
    · rintro ⟨z, hz⟩
      refine ⟨κ.symm z, ?_⟩
      rw [← map_mul, ← hz, AlgEquiv.symm_apply_apply]
  have hunit : ∀ a : R, ¬ IsUnit a ↔ DualNumber.eps ∣ κ a := by
    intro a
    have h1 : IsUnit (κ a) ↔ IsUnit a := MulEquiv.isUnit_map κ
    have h2 : (κ a ∈ IsLocalRing.maximalIdeal (DualNumber k)) ↔ ¬ IsUnit (κ a) :=
      IsLocalRing.mem_maximalIdeal _
    have h3 : (κ a ∈ IsLocalRing.maximalIdeal (DualNumber k)) ↔
        DualNumber.eps ∣ κ a := by
      rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.mem_span_singleton]
    exact ((not_congr h1).symm.trans h2.symm).trans h3
  refine ⟨κ.symm DualNumber.eps, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [hom_eq_zero_iff_not_isUnit R K hK π a, hdvd a, hunit a]
  · rw [hdvd a, ← map_eq_zero_iff κ κ.injective, map_mul, AlgEquiv.apply_symm_apply,
      DualNumber.eps_mul_eq_zero_iff, DualNumber.fst_eq_zero_iff_eps_dvd]

end ArtinianLocalAlgCat

/-! ### First-order automorphisms of a module over a square-zero extension

Let `M` be a module over a ring `R` carrying an element `ε` with `ε² = 0`, let `V` be a
module over a field `κ` and let `ψ : M → V` be a surjective additive map, semilinear along
a surjective `π : R → κ`, whose kernel is both the annihilator of `ε` and the set of
multiples of `ε`. Then the `R`-linear endomorphisms of `M` compatible with `ψ` are exactly
the maps `m ↦ m + ε φ(ψ m)` for `φ` an endomorphism of `V`, and composing two of them adds
the corresponding endomorphisms of `V`, since `ε² = 0`.
-/

section FirstOrder

variable {R : Type*} [CommRing R] {κ : Type*} [Field κ]
  {M : Type*} [AddCommGroup M] [Module R M]
  {V : Type*} [AddCommGroup V] [Module κ V]

/-- The data making `V` the first-order reduction of `M` along a square-zero element `ε`:
the reduction map `ψ` is surjective and semilinear along a surjective `π`, its kernel is
both the annihilator of `ε` and the set of multiples of `ε`, and `ε² = 0`. -/
structure IsFirstOrderReduction (eps : R) (π : R →+* κ) (ψ : M →+ V) : Prop where
  /-- The map of scalars is surjective. -/
  pi_surjective : Function.Surjective π
  /-- The reduction map is semilinear along the map of scalars. -/
  map_smul : ∀ (a : R) (mm : M), ψ (a • mm) = π a • ψ mm
  /-- The reduction map is surjective. -/
  surjective : Function.Surjective ψ
  /-- The kernel of the reduction map is the annihilator of `ε`. -/
  ker_eq : ∀ mm : M, ψ mm = 0 ↔ eps • mm = 0
  /-- The kernel of the reduction map consists of the multiples of `ε`. -/
  exists_eq_smul : ∀ mm : M, ψ mm = 0 → ∃ m' : M, mm = eps • m'
  /-- The element `ε` has square zero. -/
  eps_mul_eps : eps * eps = 0

variable {eps : R} {π : R →+* κ} {ψ : M →+ V} (h : IsFirstOrderReduction eps π ψ)

/-- The additive section of the reduction map scaled by `ε`: it sends `ψ m` to `ε • m`,
which is well defined because `ε` annihilates the kernel of `ψ`. -/
noncomputable def epsLift : V →+ M where
  toFun v := eps • Function.surjInv h.surjective v
  map_zero' := by
    refine (h.ker_eq _).mp ?_
    rw [Function.surjInv_eq h.surjective]
  map_add' v v' := by
    have h0 : ψ (Function.surjInv h.surjective (v + v') -
        (Function.surjInv h.surjective v + Function.surjInv h.surjective v')) = 0 := by
      rw [map_sub, map_add, Function.surjInv_eq h.surjective,
        Function.surjInv_eq h.surjective, Function.surjInv_eq h.surjective, sub_self]
    have h1 := (h.ker_eq _).mp h0
    rwa [smul_sub, smul_add, sub_eq_zero] at h1

/-- The scaled section sends `ψ m` to `ε • m`. -/
@[simp]
theorem epsLift_apply_map (mm : M) : epsLift h (ψ mm) = eps • mm := by
  have h0 : ψ (Function.surjInv h.surjective (ψ mm) - mm) = 0 := by
    rw [map_sub, Function.surjInv_eq h.surjective, sub_self]
  have h1 := (h.ker_eq _).mp h0
  rwa [smul_sub, sub_eq_zero] at h1

/-- The scaled section vanishes at `v` exactly when `v = 0`. -/
theorem epsLift_eq_zero_iff (v : V) : epsLift h v = 0 ↔ v = 0 := by
  obtain ⟨mm, rfl⟩ := h.surjective v
  rw [epsLift_apply_map, ← h.ker_eq]

/-- The scaled section is injective. -/
theorem epsLift_injective : Function.Injective (epsLift h) := by
  intro v v' hvv
  have hz : epsLift h (v - v') = 0 := by rw [map_sub, hvv, sub_self]
  exact sub_eq_zero.mp ((epsLift_eq_zero_iff h _).mp hz)

/-- The image of the scaled section lies in the kernel of the reduction map. -/
theorem map_epsLift (v : V) : ψ (epsLift h v) = 0 := by
  obtain ⟨mm, rfl⟩ := h.surjective v
  rw [epsLift_apply_map, h.ker_eq, smul_smul, h.eps_mul_eps, zero_smul]

/-- The scaled section is semilinear along `π`: it sends `π a • v` to `a • epsLift h v`. -/
theorem epsLift_smul (a : R) (v : V) : epsLift h (π a • v) = a • epsLift h v := by
  obtain ⟨mm, rfl⟩ := h.surjective v
  rw [← h.map_smul, epsLift_apply_map, epsLift_apply_map, smul_smul, smul_smul, mul_comm]

/-- The `R`-linear endomorphism `m ↦ m + ε φ(ψ m)` of `M` attached to an endomorphism `φ`
of the first-order reduction `V`. -/
noncomputable def epsEndo (φ : V →ₗ[κ] V) : M →ₗ[R] M where
  toFun mm := mm + epsLift h (φ (ψ mm))
  map_add' mm mm' := by
    simp only [map_add]
    abel
  map_smul' a mm := by
    change a • mm + epsLift h (φ (ψ (a • mm))) = a • (mm + epsLift h (φ (ψ mm)))
    rw [h.map_smul, map_smul, epsLift_smul h, smul_add]

/-- The endomorphism `epsEndo h φ` sends `m` to `m + epsLift h (φ (ψ m))`. -/
@[simp]
theorem epsEndo_apply (φ : V →ₗ[κ] V) (mm : M) :
    epsEndo h φ mm = mm + epsLift h (φ (ψ mm)) := rfl

/-- The endomorphism `epsEndo h φ` is compatible with the reduction map. -/
theorem map_epsEndo (φ : V →ₗ[κ] V) (mm : M) : ψ (epsEndo h φ mm) = ψ mm := by
  rw [epsEndo_apply, map_add, map_epsLift h, add_zero]

/-- Composing `epsEndo h φ'` with `epsEndo h φ` gives `epsEndo h (φ + φ')`. -/
theorem epsEndo_epsEndo (φ φ' : V →ₗ[κ] V) (mm : M) :
    epsEndo h φ (epsEndo h φ' mm) = epsEndo h (φ + φ') mm := by
  show epsEndo h φ' mm + epsLift h (φ (ψ (epsEndo h φ' mm))) =
    mm + epsLift h ((φ + φ') (ψ mm))
  rw [map_epsEndo h]
  show mm + epsLift h (φ' (ψ mm)) + epsLift h (φ (ψ mm)) =
    mm + epsLift h ((φ + φ') (ψ mm))
  simp only [LinearMap.add_apply, map_add]
  abel

/-- The endomorphism attached to `0` is the identity. -/
@[simp]
theorem epsEndo_zero (mm : M) : epsEndo h 0 mm = mm := by simp

/-- Each endomorphism `epsEndo h φ` is bijective, with inverse `epsEndo h (-φ)`. -/
theorem epsEndo_bijective (φ : V →ₗ[κ] V) : Function.Bijective (epsEndo h φ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨epsEndo h (-φ), fun mm ↦ by rw [epsEndo_epsEndo h, neg_add_cancel, epsEndo_zero],
      fun mm ↦ by rw [epsEndo_epsEndo h, add_neg_cancel, epsEndo_zero]⟩

/-- The endomorphism `φ` is determined by `epsEndo h φ`. -/
theorem epsEndo_inj {φ φ' : V →ₗ[κ] V}
    (hh : ∀ mm : M, epsEndo h φ mm = epsEndo h φ' mm) : φ = φ' := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨mm, rfl⟩ := h.surjective v
  have hmm := hh mm
  rw [epsEndo_apply, epsEndo_apply, add_right_inj] at hmm
  exact epsLift_injective h hmm

/-- Every `R`-linear endomorphism of `M` compatible with the reduction map has the form
`m ↦ m + ε φ(ψ m)`. -/
theorem exists_epsEndo (χ : M →ₗ[R] M) (hχ : ∀ mm : M, ψ (χ mm) = ψ mm) :
    ∃ φ : V →ₗ[κ] V, ∀ mm : M, χ mm = epsEndo h φ mm := by
  classical
  set δ : M →ₗ[R] M := χ - LinearMap.id with hδ
  have hδapply : ∀ mm : M, δ mm = χ mm - mm := fun mm ↦ rfl
  have hsi : ∀ v : V, ψ (Function.surjInv h.surjective v) = v := Function.surjInv_eq h.surjective
  have hδker : ∀ mm : M, ψ (δ mm) = 0 := by
    intro mm
    rw [hδapply, map_sub, hχ, sub_self]
  have hδfac : ∀ mm mm' : M, ψ mm = ψ mm' → δ mm = δ mm' := by
    intro mm mm' hmm
    have h0 : ψ (mm - mm') = 0 := by rw [map_sub, hmm, sub_self]
    obtain ⟨m'', hm''⟩ := h.exists_eq_smul _ h0
    have h1 : δ mm - δ mm' = eps • δ m'' := by rw [← map_sub, hm'', map_smul]
    have h3 : eps • δ m'' = 0 := (h.ker_eq _).mp (hδker m'')
    exact sub_eq_zero.mp (by rw [h1, h3])
  have hex : ∀ v : V, ∃ ww : V,
      epsLift h ww = δ (Function.surjInv h.surjective v) := by
    intro v
    obtain ⟨m'', hm''⟩ := h.exists_eq_smul _ (hδker (Function.surjInv h.surjective v))
    exact ⟨ψ m'', by rw [epsLift_apply_map, hm'']⟩
  choose ww hww using hex
  have hwadd : ∀ v v' : V, ww (v + v') = ww v + ww v' := by
    intro v v'
    refine epsLift_injective h ?_
    rw [map_add, hww, hww, hww, ← map_add]
    refine hδfac _ _ ?_
    rw [map_add, hsi, hsi, hsi]
  have hwsmul : ∀ (c : κ) (v : V), ww (c • v) = c • ww v := by
    intro c v
    obtain ⟨a, rfl⟩ := h.pi_surjective c
    refine epsLift_injective h ?_
    rw [hww, epsLift_smul h, hww, ← map_smul]
    refine hδfac _ _ ?_
    rw [h.map_smul, hsi, hsi]
  refine ⟨{ toFun := ww, map_add' := hwadd, map_smul' := hwsmul }, fun mm ↦ ?_⟩
  rw [epsEndo_apply]
  show χ mm = mm + epsLift h (ww (ψ mm))
  rw [hww, hδfac _ mm (hsi _), hδapply]
  abel

/-- A finite combination of basis vectors vanishes exactly when all its coefficients do. -/
private theorem sum_smul_basis_eq_zero_iff {ι S N : Type*} [Fintype ι] [Ring S]
    [AddCommGroup N] [Module S N] (b : Module.Basis ι S N) (c : ι → S) :
    ∑ j, c j • b j = 0 ↔ ∀ j, c j = 0 :=
  ⟨Fintype.linearIndependent_iff.mp b.linearIndependent c, fun hz ↦ by simp [hz]⟩

/-- A finite free module whose reduction map carries a basis to a basis is a first-order
reduction, provided the scalars `π` kills are exactly the multiples of `ε`, and `ε`
annihilates exactly its own multiples. -/
theorem isFirstOrderReduction_of_basis {ι : Type*} [Finite ι]
    (bM : Module.Basis ι R M) (bV : Module.Basis ι κ V)
    (hpi : ∀ a : R, π a = 0 ↔ eps ∣ a) (hmul : ∀ a : R, eps * a = 0 ↔ eps ∣ a)
    (hpisurj : Function.Surjective π)
    (hsmul : ∀ (a : R) (mm : M), ψ (a • mm) = π a • ψ mm)
    (hbV : ∀ j, bV j = ψ (bM j)) : IsFirstOrderReduction eps π ψ := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hexp : ∀ mm : M, ψ mm = ∑ j, π (bM.repr mm j) • bV j := by
    intro mm
    conv_lhs => rw [← bM.sum_repr mm]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hsmul, hbV]
  have hcoeff : ∀ mm : M, ψ mm = 0 ↔ ∀ j, π (bM.repr mm j) = 0 := fun mm ↦ by
    rw [hexp, sum_smul_basis_eq_zero_iff]
  have hexpM : ∀ mm : M, eps • mm = ∑ j, (eps * bM.repr mm j) • bM j := by
    intro mm
    conv_lhs => rw [← bM.sum_repr mm]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_smul]
  have hcoeffM : ∀ mm : M, eps • mm = 0 ↔ ∀ j, eps * bM.repr mm j = 0 := fun mm ↦ by
    rw [hexpM, sum_smul_basis_eq_zero_iff]
  refine { pi_surjective := hpisurj, map_smul := hsmul, surjective := ?_, ker_eq := ?_,
           exists_eq_smul := ?_, eps_mul_eps := (hmul eps).mpr dvd_rfl }
  · intro v
    choose c hc using fun j ↦ hpisurj (bV.repr v j)
    refine ⟨∑ j, c j • bM j, ?_⟩
    rw [map_sum, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦
      show ψ (c j • bM j) = bV.repr v j • bV j by rw [hsmul, hbV, hc]]
    exact bV.sum_repr v
  · intro mm
    rw [hcoeff mm, hcoeffM mm]
    exact forall_congr' fun j ↦ (hpi _).trans (hmul _).symm
  · intro mm hz
    choose c hc using fun j ↦ (hpi (bM.repr mm j)).mp ((hcoeff mm).mp hz j)
    refine ⟨∑ j, c j • bM j, ?_⟩
    rw [Finset.smul_sum]
    conv_lhs => rw [← bM.sum_repr mm]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hc j, mul_smul]

variable {G : Type*} [Monoid G]

/-- If the reduction map intertwines the representations `ρM` and `ρ₀`, then so does the
scaled section `epsLift h`. -/
theorem epsLift_equivariant (ρM : Representation R G M) (ρ₀ : Representation κ G V)
    (hψeq : ∀ (γ : G) (mm : M), ψ (ρM γ mm) = ρ₀ γ (ψ mm)) (γ : G) (v : V) :
    epsLift h (ρ₀ γ v) = ρM γ (epsLift h v) := by
  obtain ⟨mm, rfl⟩ := h.surjective v
  rw [← hψeq, epsLift_apply_map, epsLift_apply_map, map_smul]

/-- A first-order automorphism of `M` is `Γ`-equivariant exactly when the corresponding
endomorphism of the reduction is. -/
theorem epsEndo_equivariant_iff (ρM : Representation R G M) (ρ₀ : Representation κ G V)
    (hψeq : ∀ (γ : G) (mm : M), ψ (ρM γ mm) = ρ₀ γ (ψ mm)) (φ : V →ₗ[κ] V) :
    (∀ (γ : G) (mm : M), epsEndo h φ (ρM γ mm) = ρM γ (epsEndo h φ mm)) ↔
      ∀ (γ : G) (v : V), φ (ρ₀ γ v) = ρ₀ γ (φ v) := by
  have key : ∀ (γ : G) (mm : M),
      (epsEndo h φ (ρM γ mm) = ρM γ (epsEndo h φ mm)) ↔
        φ (ρ₀ γ (ψ mm)) = ρ₀ γ (φ (ψ mm)) := by
    intro γ mm
    rw [epsEndo_apply, epsEndo_apply, map_add, hψeq,
      ← epsLift_equivariant h ρM ρ₀ hψeq, add_right_inj]
    exact ⟨fun hh ↦ epsLift_injective h hh, fun hh ↦ by rw [hh]⟩
  constructor
  · intro H γ v
    obtain ⟨mm, rfl⟩ := h.surjective v
    exact (key γ mm).mp (H γ mm)
  · intro H γ mm
    exact (key γ mm).mpr (H γ (ψ mm))

end FirstOrder

/-! ### The special fibre is a terminal object of the deformation category -/

/-- An object of the deformation category of a representation lying over a terminal
coefficient algebra is a terminal object of the deformation category. -/
noncomputable def RepresentationCategory.isTerminal_of_isTerminal_base
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (z : RepresentationCategory.deformationCategory (Λ := Λ) V ρ₀)
    (hz : Limits.IsTerminal z.left.base) : Limits.IsTerminal z := by
  have hbase : IsIso (representationProjection.map z.hom) :=
    isIso_of_isTerminal hz Examples.isTerminal_residueFieldBase _
  have hiso : IsIso z.hom :=
    isIso_of_isCofiberedInGroupoids_of_map_isIso
      RepresentationCategory.representationProjection_isCofiberedInGroupoids z.hom
  exact Limits.IsTerminal.ofIso Over.mkIdTerminal
    (Over.isoMk (asIso z.hom) (by simp)).symm

/-- In the deformation category of a representation, the infinitesimal automorphism group
at a chosen pushforward over the dual numbers is the whole automorphism group of that
pushforward in its fibre: the condition of commuting with the map back to the special
fibre is automatic, because the special fibre is terminal. -/
theorem RepresentationCategory.infinitesimalAutomorphisms_eq_top
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {A₀ Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber A₀}
    {xε : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift g i) :
    infinitesimalAutomorphisms
      (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀)
      g e hpair i hi = ⊤ := by
  have hmax : IsLocalRing.maximalIdeal A₀ = ⊥ := by
    obtain ⟨i₀, -, -, -, -⟩ := hpair
    rw [← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact MulEquiv.isField (Field.toIsField k) i₀.toMulEquiv
  have hA₀ : Limits.IsTerminal A₀ :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot A₀ hmax
  have hx₀base : Limits.IsTerminal x₀.1.left.base := by
    rw [show x₀.1.left.base = A₀ from x₀.2]
    exact hA₀
  have hterm : Limits.IsTerminal x₀.1 :=
    RepresentationCategory.isTerminal_of_isTerminal_base (Λ := Λ) V ρ₀ x₀.1 hx₀base
  rw [Subgroup.eq_top_iff']
  intro a
  rw [mem_infinitesimalAutomorphisms_iff]
  exact hterm.hom_ext _ _

/-! ### Assembling the identification with degree-zero group cohomology -/

/-- `Γ`-equivariance of an endomorphism of `V` is membership in the invariants of the
conjugation representation on `End_k(V)`. -/
theorem mem_invariants_linHom_iff {V : Type w} [AddCommGroup V] [Module k V]
    (ρ₀ : Representation k Γ V) (φ : V →ₗ[k] V) :
    φ ∈ (Representation.linHom ρ₀ ρ₀).invariants ↔
      ∀ (γ : Γ) (v : V), φ (ρ₀ γ v) = ρ₀ γ (φ v) := by
  rw [Representation.mem_invariants]
  constructor
  · intro hh γ v
    exact (show (ρ₀ γ) (φ v) = φ ((ρ₀ γ) v) by
      simpa [Representation.linHom] using LinearMap.congr_fun (hh γ) (ρ₀ γ v)).symm
  · intro hh γ
    refine LinearMap.ext fun v ↦ ?_
    simp only [Representation.linHom, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.coe_comp, Function.comp_apply]
    rw [hh]
    simp

/-- A deformation of `(V, ρ₀)` over a coefficient algebra isomorphic to the dual numbers
exhibits `V` as a first-order reduction of its module. -/
theorem RepresentationCategory.exists_isFirstOrderReduction
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (xε : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber Aε)
    (hNE : Nonempty (xε.1.left.base ≃ₐ[Λ] DualNumber k)) :
    ∃ eps : xε.1.left.base,
      IsFirstOrderReduction (κ := k) (V := V) eps
        xε.1.hom.base.hom.toRingHom xε.1.hom.map := by
  classical
  obtain ⟨eps, hpi, hmul⟩ := ArtinianLocalAlgCat.exists_eps hNE
    (Examples.maximalIdeal_residueFieldBase Λ k) xε.1.hom.base
  refine ⟨eps, ?_⟩
  have : Module.Free xε.1.left.base xε.1.left.carrier :=
    Module.free_of_flat_of_isLocalRing
  let bM := Module.Free.chooseBasis xε.1.left.base xε.1.left.carrier
  have : Finite (Module.Free.ChooseBasisIndex xε.1.left.base xε.1.left.carrier) :=
    Module.Finite.finite_basis bM
  let pi : xε.1.left.base →+* k := xε.1.hom.base.hom.toRingHom
  let psi : xε.1.left.carrier →+ V := xε.1.hom.map
  have hsmul : ∀ (a : xε.1.left.base) (mm : xε.1.left.carrier),
      psi (a • mm) = pi a • psi mm := xε.1.hom.map_smul
  let : Algebra xε.1.left.base k := pi.toAlgebra
  let : Module xε.1.left.base V := Module.compHom V pi
  have : IsScalarTower xε.1.left.base k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hbc : IsBaseChange (k : Type w) (restrictAddHom pi psi hsmul) :=
    xε.1.hom.isBaseChange
  let bV : Module.Basis _ k V := (bM.baseChange (k : Type w)).map hbc.equiv
  have hbV : ∀ j, bV j = xε.1.hom.map (bM j) := by
    intro j
    show hbc.equiv ((bM.baseChange (k : Type w)) j) = _
    rw [Module.Basis.baseChange_apply, IsBaseChange.equiv_tmul, one_smul]
    rfl
  exact isFirstOrderReduction_of_basis bM bV hpi hmul
    (ArtinianLocalAlgCat.hom_surjective _ _
      (Examples.maximalIdeal_residueFieldBase Λ k) xε.1.hom.base)
    xε.1.hom.map_smul hbV

/-- The automorphism group of a first-order deformation of `(V, ρ₀)` in its fibre is the
multiplicative presentation of the `Γ`-equivariant endomorphisms of `V`: an automorphism
is `id + ε φ` for a unique `φ`, and composition adds the `φ`'s. -/
noncomputable def RepresentationCategory.autEquivInvariants
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (xε : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber Aε)
    (eps : xε.1.left.base)
    (hfo : IsFirstOrderReduction (κ := k) (V := V) eps
      xε.1.hom.base.hom.toRingHom xε.1.hom.map) :
    Aut xε ≃* Multiplicative ↥((Representation.linHom ρ₀ ρ₀).invariants) := by
  classical
  have hequiv : ∀ φ : ↥((Representation.linHom ρ₀ ρ₀).invariants),
      ∀ (γ : Γ) (mm : xε.1.left.carrier),
        epsEndo hfo φ.1 (xε.1.left.action γ mm) =
          xε.1.left.action γ (epsEndo hfo φ.1 mm) := fun φ ↦
    (epsEndo_equivariant_iff hfo xε.1.left.action ρ₀ xε.1.hom.equivariant φ.1).mpr
      ((mem_invariants_linHom_iff ρ₀ φ.1).mp φ.2)
  let mkHom : ↥((Representation.linHom ρ₀ ρ₀).invariants) →
      (xε.1.left ⟶ xε.1.left) := fun φ ↦
    { base := 𝟙 xε.1.left.base
      map := (epsEndo hfo φ.1).toAddMonoidHom
      map_smul := fun r mm ↦ (epsEndo hfo φ.1).map_smul r mm
      equivariant := hequiv φ
      isBaseChange := IsBaseChange.ofEquiv
        (LinearEquiv.ofBijective (epsEndo hfo φ.1) (epsEndo_bijective hfo φ.1)) }
  let mkOver : ↥((Representation.linHom ρ₀ ρ₀).invariants) → (xε.1 ⟶ xε.1) := fun φ ↦
    Over.homMk (mkHom φ) (RepresentationCategory.Hom.ext (Category.id_comp _)
      (AddMonoidHom.ext fun mm ↦ map_epsEndo hfo φ.1 mm))
  have hlift : ∀ φ : ↥((Representation.linHom ρ₀ ρ₀).invariants),
      (deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift (𝟙 Aε) (mkOver φ) := by
    intro φ
    refine IsHomLift.of_fac' _ (𝟙 Aε) (mkOver φ) xε.2 xε.2 ?_
    have hid : (deformationCategoryProjection (Λ := Λ) V ρ₀).map (mkOver φ) =
        𝟙 ((deformationCategoryProjection (Λ := Λ) V ρ₀).obj xε.1) := rfl
    rw [hid]
    simp
  let mkFib : ↥((Representation.linHom ρ₀ ρ₀).invariants) → (xε ⟶ xε) := fun φ ↦
    ⟨mkOver φ, hlift φ⟩
  have hcomp : ∀ (φ φ' : ↥((Representation.linHom ρ₀ ρ₀).invariants)),
      mkFib φ ≫ mkFib φ' = mkFib (φ + φ') := by
    intro φ φ'
    refine Subtype.ext (Over.OverMorphism.ext
      (RepresentationCategory.Hom.ext (Category.id_comp _)
        (AddMonoidHom.ext fun mm ↦ ?_)))
    change epsEndo hfo φ'.1 (epsEndo hfo φ.1 mm) = epsEndo hfo (φ + φ').1 mm
    rw [epsEndo_epsEndo hfo]
    change epsEndo hfo (φ'.1 + φ.1) mm = epsEndo hfo (φ.1 + φ'.1) mm
    rw [add_comm]
  have hzero : mkFib 0 = 𝟙 xε := by
    refine Subtype.ext (Over.OverMorphism.ext
      (RepresentationCategory.Hom.ext rfl (AddMonoidHom.ext fun mm ↦ ?_)))
    change epsEndo hfo (0 : ↥((Representation.linHom ρ₀ ρ₀).invariants)).1 mm = mm
    exact epsEndo_zero hfo mm
  let F : Multiplicative ↥((Representation.linHom ρ₀ ρ₀).invariants) →* Aut xε :=
    { toFun := fun x ↦
        { hom := mkFib (Multiplicative.toAdd x)
          inv := mkFib (-Multiplicative.toAdd x)
          hom_inv_id := by rw [hcomp, add_neg_cancel, hzero]
          inv_hom_id := by rw [hcomp, neg_add_cancel, hzero] }
      map_one' := Iso.ext hzero
      map_mul' := fun x y ↦ Iso.ext (by
        change mkFib (Multiplicative.toAdd x + Multiplicative.toAdd y) =
          mkFib (Multiplicative.toAdd y) ≫ mkFib (Multiplicative.toAdd x)
        rw [hcomp, add_comm]) }
  have hFhom : ∀ (x : Multiplicative ↥((Representation.linHom ρ₀ ρ₀).invariants))
      (mm : xε.1.left.carrier), (F x).hom.1.left.map mm =
        epsEndo hfo (Multiplicative.toAdd x).1 mm := fun _ _ ↦ rfl
  have hinj : Function.Injective F := by
    intro x y hxy
    refine Multiplicative.toAdd.injective (Subtype.ext (epsEndo_inj hfo fun mm ↦ ?_))
    rw [← hFhom x mm, ← hFhom y mm, hxy]
  have hsurj : Function.Surjective F := by
    intro a
    have := a.hom.2
    have hub : a.hom.1.left.base = 𝟙 xε.1.left.base := by
      have hfac := IsHomLift.fac'
        (deformationCategoryProjection (Λ := Λ) V ρ₀) (𝟙 Aε) a.hom.1
      have h2 : (deformationCategoryProjection (Λ := Λ) V ρ₀).map a.hom.1 =
          𝟙 ((deformationCategoryProjection (Λ := Λ) V ρ₀).obj xε.1) := by
        simpa using hfac
      exact h2
    let χ : xε.1.left.carrier →ₗ[xε.1.left.base] xε.1.left.carrier :=
      { toFun := a.hom.1.left.map
        map_add' := a.hom.1.left.map.map_add
        map_smul' := fun r mm ↦ by
          change a.hom.1.left.map (r • mm) = r • a.hom.1.left.map mm
          rw [a.hom.1.left.map_smul, hub]
          rfl }
    have hχψ : ∀ mm, xε.1.hom.map (χ mm) = xε.1.hom.map mm := fun mm ↦
      congrArg
        (fun q : RepresentationCategory.Hom xε.1.left
          (RepresentationCategory.specialFiber (Λ := Λ) V ρ₀) ↦ q.map mm) (Over.w a.hom.1)
    obtain ⟨φ, hφ⟩ := exists_epsEndo hfo χ hχψ
    have hφinv : φ ∈ (Representation.linHom ρ₀ ρ₀).invariants := by
      rw [mem_invariants_linHom_iff]
      refine (epsEndo_equivariant_iff hfo xε.1.left.action ρ₀
        xε.1.hom.equivariant φ).mp fun γ mm ↦ ?_
      rw [← hφ, ← hφ]
      exact a.hom.1.left.equivariant γ mm
    refine ⟨Multiplicative.ofAdd ⟨φ, hφinv⟩, Iso.ext (Subtype.ext
      (Over.OverMorphism.ext (RepresentationCategory.Hom.ext hub.symm
        (AddMonoidHom.ext fun mm ↦ ?_))))⟩
    change epsEndo hfo φ mm = a.hom.1.left.map mm
    exact (hφ mm).symm
  exact (MulEquiv.ofBijective F ⟨hinj, hsurj⟩).symm

/-- The infinitesimal automorphisms of the deformation category of a finite-dimensional
representation `ρ₀` are the degree-zero group cohomology of the conjugation action on its
endomorphisms. -/
@[stacks 0DVT "clause 3: `Inf Def_{V,ρ₀} = H⁰(Γ, End_k(V))`, the infinitesimal automorphisms \
of the deformation category of a finite-dimensional representation `ρ₀` are the `Γ`-invariant \
`k`-endomorphisms of `V`, i.e. the `ψ` with `id + εψ` an automorphism of `V ⊗_k k[ε]`"]
noncomputable def infinitesimalAutomorphismsEquivH0
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {A₀ Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber A₀}
    {xε : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift g i) :
    ↥(infinitesimalAutomorphisms
        (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀)
        g e hpair i hi) ≃*
      Multiplicative (groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0) := by
  have hNE : Nonempty (xε.1.left.base ≃ₐ[Λ] DualNumber k) := by
    obtain ⟨-, iε, -, -, -⟩ := hpair
    exact ⟨(ArtinianLocalAlgCat.algEquivOfEq (show xε.1.left.base = Aε from xε.2)).trans iε⟩
  let hfo := RepresentationCategory.exists_isFirstOrderReduction V ρ₀ xε hNE
  let L : groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 ≃ₗ[k]
      ↥((Representation.linHom ρ₀ ρ₀).invariants) :=
    Iso.toLinearEquiv (groupCohomology.H0Iso (Rep.of (Representation.linHom ρ₀ ρ₀)))
  exact (((MulEquiv.subgroupCongr
    (RepresentationCategory.infinitesimalAutomorphisms_eq_top V ρ₀ g e hpair i
      hi)).trans Subgroup.topEquiv).trans
    (RepresentationCategory.autEquivInvariants V ρ₀ xε (Classical.choose hfo)
      (Classical.choose_spec hfo))).trans
    (AddEquiv.toMultiplicative L.toAddEquiv).symm

/-- The degree-zero group cohomology of the conjugation action on the endomorphisms of a
finite-dimensional representation is finite dimensional over `k`, with no hypothesis on the
group `Γ`: it is the submodule of `Γ`-invariants of `End_k(V)`, and a submodule of a
finite-dimensional space is finite dimensional.

This is one half of the finiteness clause of Stacks 0DVT; the clause itself is about
`Inf Def_{V,ρ₀}`, and is
`Deformation.exists_infinitesimalAutomorphismsLinearEquivH0`. -/
theorem finiteDimensional_groupCohomology_zero_linHom
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) :
    FiniteDimensional k (groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0) :=
  (Iso.toLinearEquiv
    (groupCohomology.H0Iso (Rep.of (Representation.linHom ρ₀ ρ₀)))).symm.finiteDimensional

/-- **Stacks 0DVT**, the finiteness clause for infinitesimal automorphisms, stated of
`Inf Def_{V,ρ₀}` itself: the group of infinitesimal automorphisms of the deformation category
of a finite-dimensional representation carries a `k`-vector space structure whose addition is
composition of automorphisms, for which the identification of clause 3 with `H⁰(Γ, End_k(V))`
is `k`-linear, and it is *always* finite dimensional over `k` — no hypothesis whatsoever on
the group `Γ`.

`Inf Def_{V,ρ₀}` is presented as a subgroup of the automorphism group of a dual-number
pushforward (`Deformation.infinitesimalAutomorphisms`), so it carries no `k`-module structure
to begin with and `FiniteDimensional k` does not even typecheck on it. The structure is
therefore produced here, exactly as in `Stacks 0DVQ`'s version of the same statement for
finite projective modules
(`Deformation.Examples.FiniteProjectiveModule.exists_infinitesimalAutomorphismsLinearEquivEnd`),
and it is pinned: addition is composition, which fixes the additive group, and the `k`-linear
equivalence is required to be the group isomorphism
`Deformation.infinitesimalAutomorphismsEquivH0` of clause 3, which fixes the scalar action.
Compare Stacks 06JV (1), which puts the same structure on the tangent space at the identity of
the automorphism functor of a category cofibered in groupoids satisfying (RS).

Finite dimensionality is then `Deformation.finiteDimensional_groupCohomology_zero_linHom`
transported along that equivalence. This is in contrast with the tangent space, whose
finiteness needs `Γ` to be finitely generated
(`Deformation.finiteDimensional_tangentSpace_representation`). -/
@[stacks 0DVT "clause 4: `Inf Def_{V,ρ₀}` is ALWAYS finite dimensional over `k`, with no \
hypothesis whatsoever on `Γ`. Stated of `Inf Def_{V,ρ₀}` itself, which is a subgroup of an \
automorphism group and so is given here the `k`-vector space structure the claim needs: \
addition is composition of automorphisms and the clause-3 identification with \
`H⁰(Γ, End_k(V))` is `k`-linear. Contrast clause 5, where `Γ` must be finitely generated"]
theorem exists_infinitesimalAutomorphismsLinearEquivH0
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {A₀ Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber A₀}
    {xε : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift g i) :
    ∃ A : AddCommGroup ↥(infinitesimalAutomorphisms
        (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀)
        g e hpair i hi),
      letI := A
      ∃ _ : Module k ↥(infinitesimalAutomorphisms
          (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀)
          g e hpair i hi),
        (∀ a b : ↥(infinitesimalAutomorphisms
            (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀)
            g e hpair i hi), a + b = a * b) ∧
        (∃ L : ↥(infinitesimalAutomorphisms
              (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀)
              g e hpair i hi) ≃ₗ[k]
            groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0,
          ∀ a, Multiplicative.ofAdd (L a) =
            infinitesimalAutomorphismsEquivH0 (Λ := Λ) V ρ₀ g e hpair i hi a) ∧
        FiniteDimensional k ↥(infinitesimalAutomorphisms
          (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀)
          g e hpair i hi) := by
  classical
  let E := infinitesimalAutomorphismsEquivH0 (Λ := Λ) V ρ₀ g e hpair i hi
  let eqv : ↥(infinitesimalAutomorphisms
      (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀) g e hpair i hi) ≃
      groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 :=
    E.toEquiv.trans Multiplicative.toAdd
  let A : AddCommGroup ↥(infinitesimalAutomorphisms
      (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀) g e hpair i hi) :=
    eqv.addCommGroup
  let eadd : ↥(infinitesimalAutomorphisms
      (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀) g e hpair i hi) ≃+
      groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 :=
    { toEquiv := eqv
      map_add' := fun _ _ ↦ eqv.apply_symm_apply _ }
  let Mo : Module k ↥(infinitesimalAutomorphisms
      (deformationCategoryProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀) g e hpair i hi) :=
    eadd.module k
  let L := eadd.linearEquiv k
  refine ⟨A, Mo, fun a b ↦ eqv.injective ?_, ⟨L, fun a ↦ rfl⟩, ?_⟩
  · have h₁ : eqv (a + b) = eqv a + eqv b := eadd.map_add a b
    have h₂ : eqv (a * b) = eqv a + eqv b := by
      show Multiplicative.toAdd (E (a * b)) = _
      rw [E.map_mul]
      rfl
    rw [h₁, h₂]
  · have := finiteDimensional_groupCohomology_zero_linHom (Γ := Γ) V ρ₀
    exact Module.Finite.of_injective L.toLinearMap L.injective

end Deformation

end
