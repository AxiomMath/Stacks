module

public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminant
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Free
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant map over a local ring is an isomorphism when the cokernel is free

Let `(R, 𝔪)` be a local ring and let

`M₁ --α--> M₀ --π--> F ⟶ 0`

be a right-exact sequence of `R`-modules with `M₁` free of rank `r₁`, `M₀` free of rank
`r₁ + r` and `F` free of rank `r`. This file proves that the determinant map

`⋀^r F ⟶ ⋀^{r₁}(M₁^∨) ⊗ ⋀^{r₁ + r} M₀`

of `Stacks.Duality.determinantMap` is then bijective.

This is **the stalkwise content of the easy direction of the criterion of [Stacks, Tag 0E9Y]**:
the stalks of a sheaf of modules on a locally ringed space are modules over a local ring, the
stalks of a finite locally free sheaf of rank `r` are free of rank `r`, and Tag 0E9Y asserts
that the canonical map is an isomorphism on the stalk at `x` as soon as the cokernel is finite
locally free of the expected rank near `x`.

## The content

`Stacks.Duality.bijective_determinantMap_of_adapted` already settles the case of a presentation
*adapted* to a basis: there the family `α(t₁), …, α(t_{r₁}), s̃₁, …, s̃_r` is assumed to be a
basis of `M₀`. The content here is the production of such an adapted basis from the three
freeness hypotheses alone, and it is a genuinely local statement — it is false over a general
commutative ring, where `α` need not be injective even when all three modules are free of the
expected ranks.

The argument is the usual one. Lifting a basis `d` of `F` along `π` splits `π`, so `ker π` is a
direct summand of `M₀`, hence finite projective, hence — and this is where the ring is used —
flat, hence free, by `Module.free_of_flat_of_isLocalRing` (Tag 00NZ). Counting ranks in
`M₀ ≅ ker π ⊕ F` gives `rank (ker π) = r₁`, so `α` is a surjection between free modules of rank
`r₁`; composing with an isomorphism `ker π ≅ M₁` turns it into a surjective endomorphism of a
finite module, which is injective by Orzech's theorem. With `α` injective the lifted basis and
the image of the basis of `M₁` concatenate to a basis of `M₀`, which is the adapted basis.

## Main results

* `Stacks.Duality.injective_of_isLocalRing`: over a local ring the first map of such a
  presentation is injective.
* `Stacks.Duality.exists_adapted_basis_of_isLocalRing`: the presentation admits an adapted
  basis, i.e. one whose first block is the image of a basis of `M₁`.
* `Stacks.Duality.bijective_determinantMap_of_isLocalRing`: **the determinant map of Tag 0E9Y
  is bijective over a local ring when the cokernel is free of the expected rank.**
* `Stacks.Duality.bijective_of_wedge_formula`: the same conclusion for **any** map
  `⋀^{r₁} M₁ ⊗ ⋀^{r} F ⟶ ⋀^{r₁+r} M₀` satisfying the wedge-and-lift formula of Tag 0E9Y. This
  is the form in which the easy direction of the criterion is to be applied to a stalk: the
  consumer needs only the formula on germs, not an identification of the stalk of the
  sheaf-level map with a particular module-theoretic map.

## Where the rest is

The converse direction over a local ring is
`Stacks.Duality.nonempty_basis_of_surjective_wedge_formula` in
`StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantConverse`; the passage to the
stalks of the sheaf-level pairing is `Stacks.Duality.detStalkPairing_wedge` in
`StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantStalk`; and Tag 0E9Y itself,
for the canonical map in the source's form, is proved in
`StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantSource`.

## References

* [Stacks Project, Tag 0E9Y](https://stacks.math.columbia.edu/tag/0E9Y)
* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
-/

@[expose] public section

open Stacks.DeRham
open scoped TensorProduct

universe u v w x

namespace Stacks.Duality

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R] {M₁ : Type v} {M₀ : Type w} {F : Type x}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup F] [Module R F]

/-- The splitting of `π` determined by a basis `d` of `F` and a choice of lifts of its members:
the linear map sending `d i` to the chosen lift. -/
noncomputable def splitOfBasis (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π) {r : ℕ}
    (d : Module.Basis (Fin r) R F) : F →ₗ[R] M₀ :=
  d.constr ℕ fun i => (hπ (d i)).choose

omit [IsLocalRing R] in
/-- The splitting of `π` determined by a basis `d` sends `d i` to the chosen lift of `d i`. -/
theorem splitOfBasis_basis (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π) {r : ℕ}
    (d : Module.Basis (Fin r) R F) (i : Fin r) :
    splitOfBasis π hπ d (d i) = (hπ (d i)).choose :=
  Module.Basis.constr_basis d ℕ _ i

omit [IsLocalRing R] in
/-- The splitting of `π` determined by a basis of `F` is a section of `π`. -/
theorem apply_splitOfBasis (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π) {r : ℕ}
    (d : Module.Basis (Fin r) R F) (y : F) : π (splitOfBasis π hπ d y) = y := by
  have h : π.comp (splitOfBasis π hπ d) = LinearMap.id := by
    refine d.ext fun i => ?_
    rw [LinearMap.comp_apply, splitOfBasis_basis, (hπ (d i)).choose_spec, LinearMap.id_apply]
  exact LinearMap.congr_fun h y

omit [IsLocalRing R] in
/-- A section of a surjection is injective. -/
theorem injective_splitOfBasis (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π) {r : ℕ}
    (d : Module.Basis (Fin r) R F) : Function.Injective (splitOfBasis π hπ d) :=
  Function.LeftInverse.injective (apply_splitOfBasis π hπ d)

omit [IsLocalRing R] in
/-- **The kernel of `π` and the image of the splitting are complementary submodules of `M₀`.**
This is the splitting of the sequence `0 → ker π → M₀ → F → 0` produced by lifting a basis of
`F`. -/
theorem isCompl_ker_range_splitOfBasis (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π) {r : ℕ}
    (d : Module.Basis (Fin r) R F) :
    IsCompl (LinearMap.ker π) (LinearMap.range (splitOfBasis π hπ d)) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hx, y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, apply_splitOfBasis] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  · rw [codisjoint_iff_le_sup]
    intro x _
    have h₁ : x - splitOfBasis π hπ d (π x) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, apply_splitOfBasis, sub_self]
    simpa using Submodule.add_mem_sup h₁ (LinearMap.mem_range_self (splitOfBasis π hπ d) (π x))

omit [IsLocalRing R] in
/-- The kernel of `π` is a finite projective module: it is a direct summand of the finite free
module `M₀`, the projection being `x ↦ x - σ(π x)` for the splitting `σ`. -/
theorem finite_projective_ker {r : ℕ} (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (d : Module.Basis (Fin r) R F) [Module.Finite R M₀] [Module.Free R M₀] :
    Module.Finite R (LinearMap.ker π) ∧ Module.Projective R (LinearMap.ker π) := by
  set θ : M₀ →ₗ[R] M₀ := LinearMap.id - (splitOfBasis π hπ d).comp π with hθ
  have hmem : ∀ x : M₀, θ x ∈ LinearMap.ker π := by
    intro x
    rw [hθ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.mem_ker,
      map_sub, apply_splitOfBasis, sub_self]
  set ρ : M₀ →ₗ[R] LinearMap.ker π :=
    LinearMap.codRestrict (LinearMap.ker π) θ hmem with hρ
  have hρid : ∀ n : LinearMap.ker π, ρ n = n := by
    intro n
    refine Subtype.ext ?_
    have hn : π (n : M₀) = 0 := LinearMap.mem_ker.1 n.2
    rw [hρ, LinearMap.codRestrict_apply, hθ, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hn, map_zero, sub_zero]
  refine ⟨Module.Finite.of_surjective ρ fun n => ⟨(n : M₀), hρid n⟩, ?_⟩
  exact Module.Projective.of_split (LinearMap.ker π).subtype ρ (LinearMap.ext hρid)

/-- **The rank of the kernel of `π` is `r₁`.** The kernel is free, by
`Module.free_of_flat_of_isLocalRing`, and `M₀` is the direct sum of the kernel and a copy of
`F`. -/
@[sga "6 I 1.3" "special case"]
theorem free_finite_finrank_ker {r₁ r : ℕ} (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (c₀ : Module.Basis (Fin (r₁ + r)) R M₀) (d : Module.Basis (Fin r) R F) :
    Module.Free R (LinearMap.ker π) ∧ Module.Finite R (LinearMap.ker π) ∧
      Module.finrank R (LinearMap.ker π) = r₁ := by
  have : Module.Free R M₀ := Module.Free.of_basis c₀
  have : Module.Finite R M₀ := Module.Finite.of_basis c₀
  have : Module.Free R F := Module.Free.of_basis d
  have : Module.Finite R F := Module.Finite.of_basis d
  obtain ⟨hfinK, hprojK⟩ := finite_projective_ker π hπ d
  have := hfinK
  have := hprojK
  have : Module.Flat R (LinearMap.ker π) := Module.Flat.of_projective
  have hfreeK : Module.Free R (LinearMap.ker π) := Module.free_of_flat_of_isLocalRing
  refine ⟨hfreeK, hfinK, ?_⟩
  set σ := splitOfBasis π hπ d
  have : Module.Free R (LinearMap.range σ) :=
    Module.Free.of_equiv (LinearEquiv.ofInjective σ (injective_splitOfBasis π hπ d))
  have : Module.Finite R (LinearMap.range σ) :=
    Module.Finite.equiv (LinearEquiv.ofInjective σ (injective_splitOfBasis π hπ d))
  have hsum : Module.finrank R M₀ =
      Module.finrank R (LinearMap.ker π) + Module.finrank R (LinearMap.range σ) := by
    rw [← (Submodule.prodEquivOfIsCompl (LinearMap.ker π) (LinearMap.range σ)
      (isCompl_ker_range_splitOfBasis π hπ d)).finrank_eq, Module.finrank_prod]
  have hS : Module.finrank R (LinearMap.range σ) = r := by
    rw [← (LinearEquiv.ofInjective σ (injective_splitOfBasis π hπ d)).finrank_eq,
      Module.finrank_eq_card_basis d, Fintype.card_fin]
  have h₀ : Module.finrank R M₀ = r₁ + r := by
    rw [Module.finrank_eq_card_basis c₀, Fintype.card_fin]
  omega

/-- **Over a local ring the first map of a right-exact presentation by free modules of the
expected ranks is injective.** If `M₁ --α--> M₀ --π--> F ⟶ 0` is right exact with `M₁` free of
rank `r₁`, `M₀` free of rank `r₁ + r` and `F` free of rank `r`, then `α` is injective. Over a
general commutative ring this fails. -/
theorem injective_of_isLocalRing {r₁ r : ℕ} (α : M₁ →ₗ[R] M₀)
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π)
    (c₀ : Module.Basis (Fin (r₁ + r)) R M₀) (d : Module.Basis (Fin r) R F) :
    Function.Injective α := by
  have : Module.Finite R M₁ := Module.Finite.of_basis b
  obtain ⟨hfreeK, hfinK, hrankK⟩ := free_finite_finrank_ker (r₁ := r₁) π hπ c₀ d
  have := hfreeK
  have := hfinK
  set bK : Module.Basis (Fin r₁) R (LinearMap.ker π) :=
    Module.finBasisOfFinrankEq R (LinearMap.ker π) hrankK
  set α' : M₁ →ₗ[R] LinearMap.ker π :=
    LinearMap.codRestrict (LinearMap.ker π) α fun m => hex.le (LinearMap.mem_range_self α m)
  have hα'surj : Function.Surjective α' := by
    intro n
    obtain ⟨m, hm⟩ := hex.ge n.2
    exact ⟨m, Subtype.ext hm⟩
  set e : (LinearMap.ker π) ≃ₗ[R] M₁ := bK.equiv b (Equiv.refl (Fin r₁))
  have hcomp : Function.Injective (e.toLinearMap.comp α') :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hα'surj)
  exact fun y z hyz => hcomp (congrArg e (Subtype.ext hyz : α' y = α' z))

/-- A linear map is determined by its values on a basis, via the coordinates. -/
private theorem map_eq_sum_repr {A ι N P : Type*} [CommRing A] [Fintype ι] [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) (b : Module.Basis ι A N) (x : N) :
    f x = ∑ i, b.repr x i • f (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul]

/-- **Over a local ring a right-exact presentation by free modules of the expected ranks admits
an adapted basis**: a basis of `M₀` whose first `r₁` members are the images under `α` of a basis
of `M₁` and whose remaining `r` members are lifts of a basis of `F`. This is the hypothesis of
`Stacks.Duality.bijective_determinantMap_of_adapted`. -/
theorem exists_adapted_basis_of_isLocalRing {r₁ r : ℕ} (α : M₁ →ₗ[R] M₀)
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π)
    (c₀ : Module.Basis (Fin (r₁ + r)) R M₀) (d : Module.Basis (Fin r) R F) :
    ∃ (w : Fin r → M₀) (c : Module.Basis (Fin (r₁ + r)) R M₀),
      ∀ i, c i = Fin.append (fun j => α (b j)) w i := by
  classical
  have hαinj : Function.Injective α := injective_of_isLocalRing α b π hπ hex c₀ d
  set σ := splitOfBasis π hπ d with hσ
  set w : Fin r → M₀ := fun i => σ (d i) with hw
  have hwπ : ∀ i, π (w i) = d i := fun i => by rw [hw, apply_splitOfBasis]
  have hαπ : ∀ j, π (α (b j)) = 0 :=
    fun j => LinearMap.mem_ker.1 (hex.le (LinearMap.mem_range_self α (b j)))
  have hindep : LinearIndependent R (Fin.append (fun j => α (b j)) w) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsplit : (∑ j, g (Fin.castAdd r j) • α (b j)) + ∑ i, g (Fin.natAdd r₁ i) • w i = 0 := by
      refine Eq.trans (Eq.symm ?_) hg
      refine Eq.trans (Fin.sum_univ_add _) ?_
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_)
        (Finset.sum_congr rfl fun i _ => ?_)
      · rw [Fin.append_left]
      · rw [Fin.append_right]
    have hsnd : ∀ i, g (Fin.natAdd r₁ i) = 0 := by
      have hzero : ∑ i, g (Fin.natAdd r₁ i) • d i = 0 := by
        have h := congrArg π hsplit
        rw [map_add, map_sum, map_sum, map_zero] at h
        have hfirst : ∑ j, π (g (Fin.castAdd r j) • α (b j)) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [map_smul, hαπ, smul_zero]
        rw [hfirst, zero_add] at h
        refine Eq.trans (Eq.symm ?_) h
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hwπ]
      exact (Fintype.linearIndependent_iff.1 d.linearIndependent) _ hzero
    have hfst : ∀ j, g (Fin.castAdd r j) = 0 := by
      have hzero : α (∑ j, g (Fin.castAdd r j) • b j) = 0 := by
        have h : ∑ i, g (Fin.natAdd r₁ i) • w i = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hsnd i, zero_smul]
        rw [h, add_zero] at hsplit
        rw [map_sum]
        exact (Finset.sum_congr rfl fun j _ => map_smul α _ _).trans hsplit
      have := hαinj (hzero.trans (map_zero α).symm)
      exact (Fintype.linearIndependent_iff.1 b.linearIndependent) _ this
    intro i
    refine Fin.addCases (fun j => ?_) (fun i => ?_) i
    · exact hfst j
    · exact hsnd i
  have hspan : (⊤ : Submodule R M₀) ≤
      Submodule.span R (Set.range (Fin.append (fun j => α (b j)) w)) := by
    intro x _
    have hmem : x - σ (π x) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hσ, apply_splitOfBasis, sub_self]
    obtain ⟨m, hm⟩ := hex.ge hmem
    have hx : x = α m + σ (π x) := by
      rw [hm]
      abel
    rw [hx]
    refine Submodule.add_mem _ ?_ ?_
    · rw [map_eq_sum_repr α b m]
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨Fin.castAdd r j, Fin.append_left _ _ j⟩
    · rw [map_eq_sum_repr σ d (π x)]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨Fin.natAdd r₁ i, Fin.append_right _ _ i⟩
  exact ⟨w, Module.Basis.mk hindep hspan, fun i => Module.Basis.mk_apply _ _ i⟩

/-- **The determinant map of [Stacks, Tag 0E9Y] is bijective over a local ring when the cokernel
is free of the expected rank.** For a right-exact sequence `M₁ --α--> M₀ --π--> F ⟶ 0` of modules
over a local ring with `M₁` free of rank `r₁`, `M₀` free of rank `r₁ + r` and `F` free of rank
`r`, the map

`⋀^r F ⟶ ⋀^{r₁}(M₁^∨) ⊗ ⋀^{r₁+r} M₀`

is bijective. This is the stalkwise content of the easy direction of the criterion of Tag 0E9Y:
the stalks of a sheaf of modules on a locally ringed space are modules over a local ring, and
the stalks of a sheaf which is finite locally free of rank `r` are free of rank `r`. -/
theorem bijective_determinantMap_of_isLocalRing {r₁ r : ℕ} (α : M₁ →ₗ[R] M₀)
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π)
    (c₀ : Module.Basis (Fin (r₁ + r)) R M₀) (d : Module.Basis (Fin r) R F) :
    Function.Bijective (determinantMap α b r π hπ hex) := by
  obtain ⟨w, c, hc⟩ := exists_adapted_basis_of_isLocalRing α b π hπ hex c₀ d
  exact bijective_determinantMap_of_adapted α b π hπ hex w c hc

/-- **The wedge-and-lift formula forces bijectivity, over a local ring, when the three modules
are free of the expected ranks.** Let `M₁ --α--> M₀ --π--> F ⟶ 0` be right exact over a local
ring with `M₁` free of rank `r₁`, `M₀` free of rank `r₁ + r` and `F` free of rank `r`. Then
**any** linear map

`Ψ : ⋀^{r₁} M₁ ⊗ ⋀^{r} F ⟶ ⋀^{r₁+r} M₀`

satisfying the formula of [Stacks, Tag 0E9Y] — the value on
`(v₁ ∧ ⋯ ∧ v_{r₁}) ⊗ (π(u₁) ∧ ⋯ ∧ π(u_r))` is `α(v₁) ∧ ⋯ ∧ α(v_{r₁}) ∧ u₁ ∧ ⋯ ∧ u_r` — is
bijective.

This is the form in which the easy direction of the criterion of Tag 0E9Y is to be applied to a
stalk: the consumer has to know only that the stalk of the sheaf-level map satisfies the
wedge-and-lift formula on germs, not that it is any particular map. -/
theorem bijective_of_wedge_formula {r₁ r : ℕ} (α : M₁ →ₗ[R] M₀)
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π)
    (c₀ : Module.Basis (Fin (r₁ + r)) R M₀) (dF : Module.Basis (Fin r) R F)
    (Ψ : ((⋀[R]^r₁ M₁) ⊗[R] (⋀[R]^r F)) →ₗ[R] ⋀[R]^(r₁ + r) M₀)
    (hΨ : ∀ (v : Fin r₁ → M₁) (u : Fin r → M₀),
      Ψ (exteriorPower.ιMulti R r₁ v ⊗ₜ[R] exteriorPower.ιMulti R r fun i => π (u i)) =
        exteriorPower.ιMulti R (r₁ + r) (Fin.append (fun j => α (v j)) u)) :
    Function.Bijective Ψ := by
  obtain ⟨w, c, hc⟩ := exists_adapted_basis_of_isLocalRing α b π hπ hex c₀ dF
  set d : Module.Basis (Fin r) R F := basisOfAdapted α b π hπ hex w c hc
  have hdapp : ∀ i, (d : Fin r → F) i = π (w i) := basisOfAdapted_apply α b π hπ hex w c hc
  have hgen : Ψ (exteriorPower.ιMulti R r₁ (b : Fin r₁ → M₁) ⊗ₜ[R]
      exteriorPower.ιMulti R r (d : Fin r → F)) =
      exteriorPower.ιMulti R (r₁ + r) (c : Fin (r₁ + r) → M₀) := by
    have h₁ : (fun i => π (w i)) = (d : Fin r → F) := (funext hdapp).symm
    have h₂ := hΨ (b : Fin r₁ → M₁) w
    rw [h₁] at h₂
    refine h₂.trans (congrArg (exteriorPower.ιMulti R (r₁ + r)) ?_)
    exact (funext hc).symm
  have hspan : Submodule.span R {exteriorPower.ιMulti R r₁ (b : Fin r₁ → M₁) ⊗ₜ[R]
      exteriorPower.ιMulti R r (d : Fin r → F)} = (⊤ : Submodule R _) :=
    span_singleton_tmul_eq_top _ _ (span_singleton_ιMulti_basis b)
      (span_singleton_ιMulti_basis d)
  have hz : ∀ z, z = (basisTopDual c (Ψ z)) •
      (exteriorPower.ιMulti R r₁ (b : Fin r₁ → M₁) ⊗ₜ[R]
        exteriorPower.ιMulti R r (d : Fin r → F)) := by
    intro z
    obtain ⟨t, rfl⟩ :=
      Submodule.mem_span_singleton.1 (hspan.ge (Submodule.mem_top : z ∈ ⊤))
    rw [map_smul, map_smul, hgen, basisTopDual_apply, smul_eq_mul, mul_one]
  refine ⟨fun z z' h => ?_, fun y => ?_⟩
  · rw [hz z, hz z', h]
  · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1
      ((span_singleton_ιMulti_basis c).ge (Submodule.mem_top : y ∈ ⊤))
    exact ⟨t • (exteriorPower.ιMulti R r₁ (b : Fin r₁ → M₁) ⊗ₜ[R]
      exteriorPower.ιMulti R r (d : Fin r → F)), by rw [map_smul, hgen]⟩

end Local

end Stacks.Duality

end
