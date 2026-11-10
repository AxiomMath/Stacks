module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Deformation.FlatAlgebraLiftCompletion

/-!
# Deformations of localizations

Let `A' → A` be a surjection of Noetherian rings with nilpotent kernel, let `B` be a finite
type flat `A`-algebra and let `S ⊆ B` be a multiplicative subset which meets no prime of `B`
containing an ideal `𝔟` such that `A → B_h` is syntomic for every `h ∈ 𝔟`. Stacks 0DZ7 says
that `B` has a flat lift to `A'` if and only if `S⁻¹B` does. This file proves the ingredients
of the source's proof that are particular to the localization. That proof runs through Stacks
0DZ2, which is false; the equivalence is proved without it as
`Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_localization` of
`StacksFrontier.Deformation.FlatAlgebraLiftLocalizationNilpotent`.

The proof is the source's, and it is the proof of Stacks 0DZ3 with the localization in place of
the `𝔟`-adic completion. Choose a surjection `P = A[x_1, …, x_n] → B`, let `P'` be the
polynomial algebra over `A'`, let `𝔭' ⊆ P'` be the preimage of `𝔟` and let `T' ⊆ P'` be the
preimage of `S`. Flat algebra lifts of `B` to `A'` are the same thing as `A'`-flat `P'`-module
lifts of `B`, and likewise over `Q' = (T')⁻¹P'`, whose base change `Q = P ⊗_{P'} Q'` presents
`S⁻¹B`. The map `P' → Q'` is flat and induces `P'/𝔭' = Q'/𝔭'Q'`, because every element of `T'`
is already invertible modulo `𝔭'`; so the two module-lifting problems are compared by Stacks
0DZ2, whose local liftability hypothesis is supplied by Stacks 07M8 exactly as for Stacks
0DZ3.

## Main results

* `Deformation.isUnit_quotient_mk_of_forall_isPrime`: an element lying in no prime ideal
  containing `𝔟` is invertible modulo `𝔟`.
* `Deformation.bijective_quotientMap_localization`: if every element of a multiplicative subset
  `T` of `R` is invertible modulo an ideal `I`, then `R/I = (T⁻¹R)/I(T⁻¹R)`.
* **Stacks 0DZ7**, the equivalence, is
  `Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_localization` of
  `StacksFrontier.Deformation.FlatAlgebraLiftLocalizationNilpotent`, which does not assume 0DZ2.

## Implementation notes

**`h0DZ2` IS FALSE, so the source's proof sketched above is not a proof.**
`Deformation.FlatModuleLiftBaseChangeStatement` — Stacks 0DZ2 at the source's hypotheses,
restricted to a finite module — is refuted by
`StacksFrontier.Deformation.Examples.Linear.NodalArtinSchreierLift`, whose counterexample module is
finite and cyclic, so the finiteness restriction does not save it. A theorem taking `h0DZ2` as a
hypothesis is therefore vacuously true and establishes nothing. The `_of_sqZero` variants are
not the repair, because Stacks 0DZ7 (Lemma 93.13.1) says `nilpotent kernel`. What is left open
is the route through the consumers: there `M` comes from a syntomic `B_h`, where the higher
`Ext` carrying the obstruction vanishes, so the obstruction cannot arise — extra vanishing that
0DZ2's own hypotheses do not supply. That route to the three tags is not
pursued here.

**The hypothesis `h0DZ2`.** It is `Deformation.FlatModuleLiftBaseChangeStatement`, taken as a
hypothesis exactly as in Stacks 0DZ3; see the implementation notes of
`StacksFrontier.Deformation.FlatAlgebraLiftCompletion` for what separates it from the proved forms
of Stacks 0DZ2.

**The hypotheses on `𝔟` and `S`.** The source asks that `Spec(B) → Spec(A)` be syntomic at
every prime `𝔮` meeting `S`. That is carried here by an ideal `𝔟` cutting out the
non-syntomic locus: `hsyn` says `A → B_h` is syntomic for every `h ∈ 𝔟`, which is the affine
reading of "`Spec(B) → Spec(A)` is syntomic on the complement of `V(𝔟)`", and `hSb` says that
`S` meets no prime containing `𝔟`, which is the source's condition once `V(𝔟)` is the
non-syntomic locus. Together they are exactly what the proof consumes: `hsyn` feeds Stacks 07M8
through `Deformation.exists_flatModuleLift_localization_of_syntomic`, and `hSb` makes every
element of `S` invertible modulo `𝔟`, which is what identifies `P'/𝔭'` with `Q'/𝔭'Q'`.

**The second implication.** As for Stacks 0DZ3 it needs the presentation to lift along `Q'`,
and the source observes that this is easier for a localization than for a completion: if `C'`
is a flat algebra lift of `C = S⁻¹B`, the reduction `C' → C` is surjective with nilpotent
kernel, so an element of `C'` whose image in `C` is invertible is itself invertible. Every
element of `T'` therefore becomes a unit in `C'` under the formally smooth lift `P' → C'` of
the presentation, and `IsLocalization.lift` extends that lift to `Q' → C'`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Invertibility modulo an ideal -/

/-- An element of a commutative ring lying in no prime ideal containing `𝔟` is invertible
modulo `𝔟`: otherwise the principal ideal it generates in `B/𝔟` is proper, hence contained in a
maximal ideal, whose preimage in `B` is a prime containing `𝔟` and the element. -/
theorem isUnit_quotient_mk_of_forall_isPrime {B : Type u} [CommRing B] (b : Ideal B) (s : B)
    (hs : ∀ q : Ideal B, q.IsPrime → b ≤ q → s ∉ q) :
    IsUnit (Ideal.Quotient.mk b s) := by
  by_contra hns
  have hne : Ideal.span ({Ideal.Quotient.mk b s} : Set (B ⧸ b)) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hns
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have : m.IsPrime := hmax.isPrime
  refine hs (m.comap (Ideal.Quotient.mk b)) (Ideal.comap_isPrime _ _) (fun x hx => ?_) ?_
  · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact m.zero_mem
  · exact Ideal.mem_comap.mpr (hle (Ideal.mem_span_singleton_self _))

/-! ### The reduction of a localization -/

/-- If every element of a multiplicative subset `T` of a commutative ring `R` is invertible
modulo an ideal `I`, then the canonical map `R/I → (T⁻¹R)/I(T⁻¹R)` is bijective.

Injectivity holds because the reduction `R → R/I` extends over the localization, since every
element of `T` is already a unit there; surjectivity because `a/t` and `au` agree modulo
`I(T⁻¹R)` whenever `tu ≡ 1` modulo `I`. -/
theorem bijective_quotientMap_localization {R : Type u} [CommRing R] (T : Submonoid R)
    (Rt : Type u) [CommRing Rt] [Algebra R Rt] [IsLocalization T Rt] (I : Ideal R)
    (hunit : ∀ t ∈ T, IsUnit (Ideal.Quotient.mk I t)) :
    Function.Bijective (Ideal.quotientMap (I.map (algebraMap R Rt)) (algebraMap R Rt)
      Ideal.le_comap_map) := by
  have hg : ∀ t : T, IsUnit ((Ideal.Quotient.mk I : R →+* R ⧸ I) t) := fun t => hunit t.1 t.2
  have hpsi : ∀ x : R, IsLocalization.lift (M := T) hg (algebraMap R Rt x) =
      Ideal.Quotient.mk I x := fun x => IsLocalization.lift_eq hg x
  have hker : ∀ z ∈ I.map (algebraMap R Rt), IsLocalization.lift (M := T) hg z = 0 := by
    intro z hz
    refine Submodule.span_induction (p := fun w _ => IsLocalization.lift (M := T) hg w = 0)
      (fun w hw => ?_) (map_zero _) (fun x y _ _ hx hy => by rw [map_add, hx, hy, add_zero])
      (fun a x _ hx => by rw [Algebra.smul_def, map_mul, hx, mul_zero]) hz
    obtain ⟨x, hx, rfl⟩ := hw
    rw [hpsi, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  set psi : (Rt ⧸ I.map (algebraMap R Rt)) →+* R ⧸ I :=
    Ideal.Quotient.lift _ (IsLocalization.lift (M := T) hg) hker with hpsidef
  have hpsimk : ∀ z : Rt, psi (Ideal.Quotient.mk _ z) =
      IsLocalization.lift (M := T) hg z := fun _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hround : psi (Ideal.quotientMap (I.map (algebraMap R Rt)) (algebraMap R Rt)
        Ideal.le_comap_map (Ideal.Quotient.mk I x)) = Ideal.Quotient.mk I x := by
      rw [Ideal.quotientMap_mk, hpsimk, hpsi]
    rw [hz, map_zero] at hround
    exact hround.symm
  · intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj (M := T) y
    obtain ⟨v, hv⟩ := (hunit t.1 t.2).exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hu : (t : R) * u - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hv, sub_self]
    refine ⟨Ideal.Quotient.mk I (a * u), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hcalc : algebraMap R Rt (a * u) - y = y * algebraMap R Rt ((t : R) * u - 1) := by
      rw [map_sub, map_mul, map_mul, map_one, ← hat]
      ring
    rw [hcalc]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hu)

/-! ### The localized presentation -/

/-- The chain of isomorphisms identifying `(P ⊗_{P'} Q') ⊗_P B` with the localization of `B` at
the image of `T'`, for `Q'` the localization of `P'` at `T'`. -/
private theorem exists_ringEquiv_tensorLocalization
    (P' P B : Type u) [CommRing P'] [CommRing P] [CommRing B]
    [Algebra P' P] [Algebra P' B] [Algebra P B] [IsScalarTower P' P B]
    (T' : Submonoid P') (Q' : Type u) [CommRing Q'] [Algebra P' Q'] [IsLocalization T' Q']
    (C : Type u) [CommRing C] [Algebra B C]
    [IsLocalization (Algebra.algebraMapSubmonoid B T') C] :
    ∃ e : ((P ⊗[P'] Q') ⊗[P] B) ≃+* C,
      ∀ p : P, e ((p ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) =
        algebraMap B C (algebraMap P B p) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B T') (B ⊗[P'] Q') :=
    IsLocalization.tensor (R := P') (S := B) Q' T'
  refine ⟨(Algebra.TensorProduct.comm P (P ⊗[P'] Q') B).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange P' P B B Q').toRingEquiv.trans
      (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B T')
        (B ⊗[P'] Q') C).toRingEquiv), fun p => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
  simp only [AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  rw [Algebra.smul_def, mul_one]
  exact (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B T')
    (B ⊗[P'] Q') C).commutes (algebraMap P B p)

/-! ### Lifting a presentation to a flat algebra lift of a localization -/

/-- Let `C'` be a flat lift of `C` to `A'`. The reduction `C' → C` is a surjection with
nilpotent kernel, so a formally smooth presentation `P' → C` lifts to `C'` and carries every
element of a multiplicative subset `T' ⊆ P'` which becomes invertible in `C` to a unit of `C'`;
hence the lift extends to the localization `Q'` of `P'` at `T'`. -/
private theorem exists_algHom_localization_of_algebraLift
    (A' A P' C C' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing C] [CommRing C']
    [Algebra A' A] [Algebra A' P'] [Algebra A' C] [Algebra A' C'] [Algebra A C] [Algebra P' C]
    [IsScalarTower A' A C] [IsScalarTower A' P' C] [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (T' : Submonoid P') (Q' : Type u) [CommRing Q'] [Algebra P' Q'] [IsLocalization T' Q']
    [Algebra A' Q'] [IsScalarTower A' P' Q'] [Algebra Q' C] [IsScalarTower P' Q' C]
    (hunit : ∀ t ∈ T', IsUnit (algebraMap P' C t))
    (eC : (A ⊗[A'] C') ≃ₐ[A] C) :
    ∃ g : Q' →ₐ[A'] C', ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x := by
  -- the reduction of the lift, a surjection with nilpotent kernel
  set rho : C' →ₐ[A'] C :=
    (eC.restrictScalars A').toAlgHom.comp Algebra.TensorProduct.includeRight with hrhodef
  have hrhoapp : ∀ y : C', rho y = eC (1 ⊗ₜ[A'] y) := fun _ => rfl
  have hrhosurj : Function.Surjective rho :=
    (eC.restrictScalars A').surjective.comp (surjective_includeRight A' A C' hsurjA)
  have hrhoker : RingHom.ker rho = (RingHom.ker (algebraMap A' A)).map (algebraMap A' C') :=
    ker_comp_includeRight C C' hsurjA (eC.restrictScalars A')
  have hrhonil : IsNilpotent (RingHom.ker rho) := by
    rw [hrhoker]
    exact isNilpotent_ideal_map hnilA _
  -- the lift of the presentation
  set eta : P' →ₐ[A'] C' := Algebra.FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom A' P' C) rho hrhosurj hrhonil with hetadef
  have heta : ∀ x : P', rho (eta x) = algebraMap P' C x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ rho hrhosurj hrhonil x
  -- every element of `T'` becomes a unit in `C'`
  have hunit' : ∀ t : T', IsUnit ((eta : P' →+* C') t) := by
    intro t
    obtain ⟨k, hk⟩ := hrhonil
    obtain ⟨v, hv⟩ := (hunit t.1 t.2).exists_right_inv
    obtain ⟨w, hw⟩ := hrhosurj v
    have hmem : eta t.1 * w - 1 ∈ RingHom.ker rho := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, heta, hw, hv, sub_self]
    have hnilx : IsNilpotent (eta t.1 * w - 1) := by
      refine ⟨k, ?_⟩
      have hp := Ideal.pow_mem_pow hmem k
      rw [hk, Ideal.zero_eq_bot, Submodule.mem_bot] at hp
      exact hp
    have hprod : IsUnit (eta t.1 * w) := by
      have h1 : eta t.1 * w = 1 + (eta t.1 * w - 1) := by ring
      rw [h1]
      exact hnilx.isUnit_one_add
    obtain ⟨z, hz⟩ := hprod.exists_right_inv
    exact IsUnit.of_mul_eq_one (w * z) (by rw [← mul_assoc]; exact hz)
  -- the extension of the lift across the localization
  have hcomm : ∀ a' : A', IsLocalization.lift (M := T') hunit' (algebraMap A' Q' a') =
      algebraMap A' C' a' := by
    intro a'
    rw [IsScalarTower.algebraMap_apply A' P' Q', IsLocalization.lift_eq]
    exact eta.commutes a'
  refine ⟨⟨(IsLocalization.lift (M := T') hunit' : Q' →+* C'), hcomm⟩, fun x => ?_⟩
  have hext : (rho.toRingHom.comp (IsLocalization.lift (M := T') hunit') : Q' →+* C) =
      algebraMap Q' C := by
    refine IsLocalization.ringHom_ext T' (RingHom.ext fun y => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, IsLocalization.lift_eq,
      ← IsScalarTower.algebraMap_apply P' Q' C]
    exact heta y
  rw [← hrhoapp]
  exact RingHom.congr_fun hext x

end Deformation

end
