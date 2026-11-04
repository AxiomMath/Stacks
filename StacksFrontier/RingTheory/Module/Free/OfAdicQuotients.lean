module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nakayama

/-!
# Freeness from freeness of the adic quotients

Let `R` be a Noetherian local ring, `I ⊆ R` an ideal with `I ≠ R` and `M` a finite `R`-module.
If every adic quotient `M / I ^ (n + 1) M` is free over `R / I ^ (n + 1)`, then `M` is free
over `R`.

The hypothesis for a single `n` says nothing: for `n` with `I ^ (n + 1) = 0` it *is* the
conclusion, and for `I = m` the maximal ideal the case `n = 0` holds for every `M`. It is the
whole tower that forces freeness, through Krull's intersection theorem.

## Main results

* `Stacks.FreeOfAdicQuotients.linearIndependent_of_free_of_minimal_span_eq_top` — a minimal
  generating family of a finite free module over a local ring is a basis.
* `Stacks.FreeOfAdicQuotients.free_of_forall_free_quotient_pow_smul_top` — the theorem above.

## Implementation notes

The quotient `M / J M` is `M ⧸ (J • ⊤ : Submodule R M)`, which carries an `R / J`-module
structure automatically, and `R / J` is local as soon as `J ≠ R`, being a surjective image of
the local ring `R`.

The argument is the classical one and runs as follows. Nakayama's lemma lifts a basis of the
fibre `k ⊗_R M`, `k = R / m` the residue field, to a family `v : κ → M` which generates `M`
and is *minimal*: no subfamily obtained by deleting one member still generates, because the
basis of the fibre is linearly independent. Reducing `v` modulo `J = I ^ (n + 1)` keeps both
properties — minimality survives because `J ≤ m`, so Nakayama applies over `R` again — and a
minimal generating family of a finite free module over a local ring is a basis, by
`Module.exists_basis_of_span_of_flat`. Hence every coefficient of a relation
`∑ i, l i • v i = 0` lies in `I ^ (n + 1)` for every `n`, so in `⨅ n, I ^ n`, which is `0` by
Krull's intersection theorem for a Noetherian local ring
(`Ideal.iInf_pow_eq_bot_of_isLocalRing`). So `v` is linearly independent, and a basis.

Minimality is phrased as `∀ i, Submodule.span R (v '' {j | j ≠ i}) ≠ ⊤` rather than through a
cardinality or rank invariant: that is the form Nakayama's lemma transports along the reduction
maps, and it is the form `Module.exists_basis_of_span_of_flat` consumes, since that lemma
returns a basis indexed by a *subfamily* of the given generators.
-/

@[expose] public section

open Module Submodule TensorProduct

namespace Stacks.FreeOfAdicQuotients

universe u

/-- **A minimal generating family of a finite free module over a local ring is a basis.**
If `v` generates the finite free module `N` over the local ring `S` and no subfamily obtained
by deleting a single member of `v` generates `N`, then `v` is linearly independent.

`Module.exists_basis_of_span_of_flat` extracts from `v` a subfamily which is a basis;
minimality forces that subfamily to be all of `v`. -/
theorem linearIndependent_of_free_of_minimal_span_eq_top
    {S : Type*} [CommRing S] [IsLocalRing S] {N : Type*} [AddCommGroup N] [Module S N]
    [Module.Finite S N] [Module.Free S N] {κ : Type u} (v : κ → N)
    (hsp : Submodule.span S (Set.range v) = ⊤)
    (hmin : ∀ i : κ, Submodule.span S (v '' {j | j ≠ i}) ≠ ⊤) :
    LinearIndependent S v := by
  have : Module.FinitePresentation S N := Module.finitePresentation_of_projective S N
  obtain ⟨κ', a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hsp
  have hrange : Set.range b = Set.range (v ∘ a) := congrArg Set.range (funext hb)
  have hasurj : Function.Surjective a := by
    intro i
    by_contra hi
    refine hmin i ?_
    rw [eq_top_iff, ← b.span_eq, hrange]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨a j, fun h => hi ⟨j, h⟩, rfl⟩
  have hainj : Function.Injective a := fun j j' h => b.injective (by rw [hb, hb, h])
  exact (linearIndependent_equiv' (Equiv.ofBijective a ⟨hainj, hasurj⟩)
    (funext fun j => (hb j).symm)).mp b.linearIndependent

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- **The coefficients of a relation among a minimal generating family lie in `J`**, as soon as
`M / J M` is free over `R / J`. This is the step of
`Stacks.FreeOfAdicQuotients.free_of_forall_free_quotient_pow_smul_top` run at one level of the
tower; the theorem itself intersects the conclusions over all `J = I ^ (n + 1)`. -/
theorem mem_of_sum_smul_eq_zero
    [Module.Finite R M] {κ : Type u} [Fintype κ] (v : κ → M)
    (hmin : ∀ i : κ, Submodule.span R (v '' {j | j ≠ i}) ≠ ⊤)
    (hsp : Submodule.span R (Set.range v) = ⊤)
    {J : Ideal R} (hJ : J ≠ ⊤)
    (hfreeJ : Module.Free (R ⧸ J) (M ⧸ (J • ⊤ : Submodule R M)))
    (l : κ → R) (hl : ∑ i, l i • v i = 0) (i : κ) : l i ∈ J := by
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have := hfreeJ
  have : Module.Finite (R ⧸ J) (M ⧸ (J • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ J) _
  set P : Submodule R M := J • ⊤
  set v' : κ → (M ⧸ P) := fun j => P.mkQ (v j) with hv'
  have hspR : ∀ T : Set κ, Submodule.span R (v' '' T) =
      Submodule.map P.mkQ (Submodule.span R (v '' T)) := by
    intro T
    rw [Submodule.map_span, ← Set.image_comp]
    rfl
  -- the reduced family still generates
  have hsp' : Submodule.span (R ⧸ J) (Set.range v') = ⊤ := by
    rw [← Submodule.restrictScalars_eq_top_iff R,
      Submodule.restrictScalars_span R (R ⧸ J) Ideal.Quotient.mk_surjective]
    rw [← Set.image_univ, hspR, Set.image_univ, hsp, Submodule.map_top, LinearMap.range_eq_top]
    exact P.mkQ_surjective
  -- and still minimally so, by Nakayama over `R`, using `J ≤ m`
  have hmin' : ∀ j : κ, Submodule.span (R ⧸ J) (v' '' {j' | j' ≠ j}) ≠ ⊤ := by
    intro j hcon
    rw [← Submodule.restrictScalars_eq_top_iff R,
      Submodule.restrictScalars_span R (R ⧸ J) Ideal.Quotient.mk_surjective, hspR] at hcon
    have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (v '' {j' | j' ≠ j}) ⊔ P := by
      have hc := congrArg (Submodule.comap P.mkQ) hcon
      rw [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at hc
      exact hc.ge
    refine hmin j (le_antisymm le_top ?_)
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R)
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) (hsup.trans ?_)
    exact sup_le_sup_left (Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal hJ)) _
  have hli' : LinearIndependent (R ⧸ J) v' :=
    linearIndependent_of_free_of_minimal_span_eq_top v' hsp' hmin'
  have hrel : ∑ j, (Ideal.Quotient.mk J (l j)) • v' j = 0 := by
    have hterm : ∀ j, (Ideal.Quotient.mk J (l j)) • v' j = P.mkQ (l j • v j) := by
      intro j
      rw [hv']
      simp
    simp only [hterm, ← map_sum, hl, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((Fintype.linearIndependent_iff.mp hli') _ hrel i)

/-- **Freeness descends from the adic quotients over a Noetherian local ring.**
Let `R` be a Noetherian local ring, `I ≠ R` an ideal of `R` and `M` a finite `R`-module. If
`M / I ^ (n + 1) M` is free over `R / I ^ (n + 1)` for every `n`, then `M` is free over `R`.

Nakayama's lemma lifts a basis of the fibre `k ⊗_R M` to a minimal generating family `v`; its
reduction modulo `I ^ (n + 1)` is then a basis of `M / I ^ (n + 1) M`, so every coefficient of
a relation among the `v` lies in `I ^ (n + 1)`, hence in `⨅ n, I ^ n`, which is `0` by Krull's
intersection theorem. -/
theorem free_of_forall_free_quotient_pow_smul_top
    [IsNoetherianRing R] [Module.Finite R M] {I : Ideal R} (hI : I ≠ ⊤)
    (hfree : ∀ n : ℕ,
      Module.Free (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))) :
    Module.Free R M := by
  classical
  set k := IsLocalRing.ResidueField R
  set w := Module.Free.chooseBasis k (k ⊗[R] M)
  obtain ⟨v, hv⟩ :=
    (TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective).comp_left w
  have hsp : Submodule.span R (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v w (congr_fun hv)
  -- minimality of `v`, from linear independence of the basis `w` of the fibre
  have hmin : ∀ i, Submodule.span R (v '' {j | j ≠ i}) ≠ ⊤ := by
    intro i hcon
    have himg : (TensorProduct.mk R k M 1) '' (v '' {j | j ≠ i}) = w '' {j | j ≠ i} := by
      rw [← Set.image_comp]
      exact congrArg (· '' {j | j ≠ i}) hv
    have htop : Submodule.span k (w '' {j | j ≠ i}) = ⊤ := by
      rw [← Submodule.restrictScalars_eq_top_iff R,
        Submodule.restrictScalars_span R k Ideal.Quotient.mk_surjective, ← himg,
        ← Submodule.map_span, hcon, Submodule.map_top, LinearMap.range_eq_top]
      exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
    exact w.linearIndependent.notMem_span_image (s := {j | j ≠ i}) (x := i) (by simp)
      (htop ▸ Submodule.mem_top)
  -- linear independence of `v`, via Krull's intersection theorem
  have hli : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro l hl i
    have key : l i ∈ (⨅ n : ℕ, I ^ n) := by
      refine Submodule.mem_iInf _ |>.mpr fun n => ?_
      cases n with
      | zero => simp
      | succ m =>
          have hpow : I ^ (m + 1) ≠ ⊤ := fun hc =>
            hI (top_le_iff.mp (hc.ge.trans (Ideal.pow_le_self (Nat.succ_ne_zero m))))
          exact mem_of_sum_smul_eq_zero v hmin hsp hpow (hfree m) l hl i
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing I hI, Ideal.mem_bot] at key
  exact Module.Free.of_basis (Module.Basis.mk hli hsp.ge)

/-- **Freeness descends from the adic quotients**, with the ideal given inside the maximal
ideal. This is the form in which the hypothesis arises geometrically: `I` is the ideal of a
closed subscheme through the point. -/
theorem free_of_forall_free_quotient_pow_smul_top_of_le_maximalIdeal
    [IsNoetherianRing R] [Module.Finite R M] {I : Ideal R}
    (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hfree : ∀ n : ℕ,
      Module.Free (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))) :
    Module.Free R M :=
  free_of_forall_free_quotient_pow_smul_top
    (fun h => IsLocalRing.maximalIdeal.isMaximal R |>.ne_top (top_le_iff.mp (h ▸ hI))) hfree

end Stacks.FreeOfAdicQuotients

end
