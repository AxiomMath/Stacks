module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PolynomialLocalizationReduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutQuotient
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ResidueFibreSeparation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ResidueFibreSpreadout
public import StacksFrontier.RingTheory.Flat.MaximalBadPrime

/-!
# Claim 2 of the proof of Stacks 05U9

In Situation 0AT0, assume in addition that `B` is a localization of a polynomial algebra over
`A` at a prime and that `N` is finitely presented over `B`. Then `u ⊗ id_{κ(𝔭)}` is injective
for **every** prime `𝔭` of `A`.

The Zorn argument of the source is
`AlgebraicGeometry.rTensor_residueField_injective_of_spreadout_of_step`, which reduces the
claim to its two halves. The spreading-out half is
`AlgebraicGeometry.exists_fg_ideal_rTensor_residueField_injective_of_le`. This file supplies
the second half: a prime all of whose strict specializations are good is good.

For the maximal ideal that is unconditional. For a smaller prime `𝔭`, the source argues: for
`f ∈ A ∖ 𝔭` every prime containing `𝔭 + (f)` strictly contains `𝔭`, hence is good, so Stacks
0AT9 applied over `A/(𝔭 + (f))` makes `u ⊗ id_{A/(𝔭+(f))}` injective; it therefore suffices
that `N/𝔭N` be separated for the topology defined by the submodules `f(N/𝔭N)`, which is
`Stacks.ResidueFibre.eq_zero_of_forall_mem_smul_top`.

## Main results

* `AlgebraicGeometry.rTensor_quotient_injective_of_rTensor_residueField_injective_of_le`:
  Stacks 0AT9 base changed to a quotient of the base ring, so that only the fibres above the
  quotient are needed.
* `AlgebraicGeometry.rTensor_residueField_injective_of_forall_gt`: the second half of Claim
  2 — a prime all of whose strict specializations are good is good.
* `AlgebraicGeometry.rTensor_residueField_injective_of_claims`: Claim 2 itself.

## Implementation notes

One hypothesis is carried rather than proved, because it is being proved elsewhere.

`hflat` is what the file needs of Claim 1: `N/𝔭N` is flat over `A/𝔭` for every prime `𝔭`. In
the source this comes from the finitely generated nilpotent ideal `I₀` with `N/I₀N` flat over
`A/I₀`, base changed along `A/I₀ → A/𝔭`, which is legitimate because a nilpotent ideal is
contained in every prime; that derivation is
`AlgebraicGeometry.flat_quotient_primes_of_isNilpotent`.

The content ideals the separatedness step needs — Stacks 05U7 together with Stacks 0ASD, that
over a henselian local ring a finite module over a local algebra essentially of finite type
which is flat over the base has content ideals — are
`Module.exists_isContentIdeal_of_colimit_free_presentation`, and
`Stacks.ResidueFibre.eq_zero_of_forall_mem_smul_top` consumes them with no hypothesis of its
own.

Situation 0AT0 keeps its module `N` and its target `M` in independent universes, while Stacks
0AT9 tests both in one; so `N` and `M` are `ULift`ed to their join before the situation of
Stacks 0AT6 is assembled, and the resulting injectivity statements are transported back along
those lifts.

## References

* [Stacks Project, Tag 0AT9](https://stacks.math.columbia.edu/tag/0AT9)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

open TensorProduct

/-- Conjugating a map by linear equivalences on both sides does not change injectivity of
its tensorings. -/
private theorem injective_rTensor_conj {R : Type*} [CommRing R]
    {N N' M M' Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup Q]
    [Module R Q] (e : N' ≃ₗ[R] N) (e' : M' ≃ₗ[R] M) (u : N →ₗ[R] M) :
    Function.Injective
        ((e'.symm.toLinearMap ∘ₗ u ∘ₗ e.toLinearMap).rTensor Q) ↔
      Function.Injective (u.rTensor Q) := by
  have hg : Function.Injective (e'.symm.toLinearMap.rTensor Q) :=
    (e'.symm.rTensor Q).injective
  have hh : Function.Bijective (e.toLinearMap.rTensor Q) := (e.rTensor Q).bijective
  have hcomp : ⇑((e'.symm.toLinearMap ∘ₗ u ∘ₗ e.toLinearMap).rTensor Q) =
      ⇑(e'.symm.toLinearMap.rTensor Q) ∘ ⇑(u.rTensor Q) ∘
        ⇑(e.toLinearMap.rTensor Q) := by
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp]
    rfl
  rw [hcomp, hg.of_comp_iff, Function.Injective.of_comp_iff' _ hh]

/-- Injectivity on the residue-field fibres above a fixed ideal gives injectivity after
tensoring with any field killing that ideal. -/
private theorem injective_lTensor_field_of_fibres
    {R N M : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (f : N →ₗ[R] M) (J : Ideal R)
    (hf : ∀ (p : Ideal R) [p.IsPrime], J ≤ p →
      Function.Injective (f.rTensor p.ResidueField))
    (K : Type*) [Field K] [Algebra R K] (hJ : J ≤ RingHom.ker (algebraMap R K)) :
    Function.Injective (f.lTensor K) := by
  let p : Ideal R := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime (algebraMap R K)
  exact injective_lTensor_field_of_fibre f K p rfl (hf p hJ)

/-- **Stacks 0AT9 after a base change, with only the fibres above the base change
needed.** -/
private theorem universallyInjective_baseChange_of_flat_of_fibres
    {R B₀ B N M : Type*} [CommRing R] [CommRing B₀] [CommRing B]
    [Algebra R B₀] [Algebra B₀ B] [Algebra R B] [IsScalarTower R B₀ B]
    [Algebra.FinitePresentation R B₀] (W : Submonoid B₀) [IsLocalization W B]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.FinitePresentation B N]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : N →ₗ[R] M) (J : Ideal R)
    (hf : ∀ (p : Ideal R) [p.IsPrime], J ≤ p →
      Function.Injective (f.rTensor p.ResidueField))
    (S : Type*) [CommRing S] [Algebra R S] [Module.Flat S (S ⊗[R] N)]
    (hJ : J ≤ RingHom.ker (algebraMap R S)) :
    UniversallyInjectivePoly.{_, u₅} (f.baseChange S) := by
  let B₀' := S ⊗[R] B₀
  let B' := S ⊗[R] B
  let g : B₀' →ₐ[S] B' :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R B₀ B)
  let : Algebra B₀' B' := g.toRingHom.toAlgebra
  let : IsScalarTower S B₀' B' := IsScalarTower.of_algebraMap_eq' (by
    ext s
    exact (g.commutes s).symm)
  let : Algebra B B' := Algebra.TensorProduct.rightAlgebra
  let W' := W.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  let : IsLocalization W' B' :=
    IsLocalization.tensorProduct_tensorProduct_right R S W B (by
      ext b
      rfl)
  let N' := B' ⊗[B] N
  let eN : N' ≃ₗ[S] S ⊗[R] N := Algebra.IsPushout.cancelBaseChange R S B B' N
  let : Module.Flat S N' := Module.Flat.of_linearEquiv eN
  let f' := f.baseChange S ∘ₗ eN.toLinearMap
  have hf' : ∀ (p : Ideal S) [p.IsPrime],
      Function.Injective (f'.rTensor p.ResidueField) := by
    intro p hp
    have hJ' : J ≤ RingHom.ker (algebraMap R p.ResidueField) := by
      intro x hx
      apply RingHom.mem_ker.mpr
      rw [IsScalarTower.algebraMap_apply R S p.ResidueField,
        RingHom.mem_ker.mp (hJ hx), map_zero]
    have h : Function.Injective ((f.baseChange S).lTensor p.ResidueField) :=
      (injective_lTensor_baseChange_iff f).mpr
        (injective_lTensor_field_of_fibres f J hf p.ResidueField hJ')
    have h' := (LinearMap.lTensor_inj_iff_rTensor_inj p.ResidueField (f.baseChange S)).mp h
    show Function.Injective ((f.baseChange S ∘ₗ eN.toLinearMap).rTensor p.ResidueField)
    rw [LinearMap.rTensor_comp]
    exact h'.comp (eN.rTensor p.ResidueField).injective
  have h := universallyInjective_of_flat_of_fibres (B₀ := B₀') (B := B') W' f' hf'
  intro Q _ _
  have hQ := h Q
  change Function.Injective ((f.baseChange S ∘ₗ eN.toLinearMap).rTensor Q) at hQ
  rw [LinearMap.rTensor_comp] at hQ
  exact (Function.Injective.of_comp_iff' _ (eN.rTensor Q).bijective).mp hQ

/-- **Stacks 0AT9 modulo an ideal.** If a linear map out of a finitely presented module over
a localization of a finitely presented algebra is injective on the residue-field fibre at
every prime containing an ideal `J`, and if the reduction of the module modulo `J` is flat
over `A ⧸ J`, then the map stays injective after tensoring with `A ⧸ J`. -/
theorem rTensor_quotient_injective_of_rTensor_residueField_injective_of_le
    {R B₀ B N M : Type*} [CommRing R] [CommRing B₀] [CommRing B]
    [Algebra R B₀] [Algebra B₀ B] [Algebra R B] [IsScalarTower R B₀ B]
    [Algebra.FinitePresentation R B₀] (W : Submonoid B₀) [IsLocalization W B]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.FinitePresentation B N]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : N →ₗ[R] M) (J : Ideal R) [Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] N)]
    (hf : ∀ (p : Ideal R) [p.IsPrime], J ≤ p →
      Function.Injective (f.rTensor p.ResidueField)) :
    Function.Injective (f.rTensor (R ⧸ J)) := by
  have hJ : J ≤ RingHom.ker (algebraMap R (R ⧸ J)) := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have h := universallyInjective_baseChange_of_flat_of_fibres (B₀ := B₀) (B := B)
    W f J hf (R ⧸ J) hJ
  exact injective_rTensor_of_universallyInjective_baseChange f (R ⧸ J) h (R ⧸ J)

/-- Injectivity of the reduction modulo a prime gives injectivity on the residue-field
fibre, because the residue field is a localization, hence flat, over the quotient. -/
private theorem injective_rTensor_residueField_of_injective_mapQ
    {R N M : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (f : N →ₗ[R] M) (p : Ideal R) [p.IsPrime]
    (hf : Function.Injective ((p • (⊤ : Submodule R N)).mapQ
      (p • (⊤ : Submodule R M)) f (Submodule.smul_top_le_comap_smul_top p f))) :
    Function.Injective (f.rTensor p.ResidueField) := by
  have hquot := (mapQ_injective_iff_rTensor_quotient f p).mp hf
  have hbase : Function.Injective (f.baseChange (R ⧸ p)) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj (R ⧸ p) f).mpr hquot
  have : Module.Flat (R ⧸ p) p.ResidueField :=
    IsLocalization.flat _ (nonZeroDivisors (R ⧸ p))
  have h := Module.Flat.lTensor_preserves_injective_linearMap
    (M := p.ResidueField) (f.baseChange (R ⧸ p)) hbase
  exact (LinearMap.lTensor_inj_iff_rTensor_inj p.ResidueField f).mp
    ((injective_lTensor_baseChange_iff (S := R ⧸ p) f).mp h)

/-- The flatness of `N ⧸ 𝔮N` over `A ⧸ 𝔮` in the tensor-product shape in which Stacks 0AT9
consumes it. -/
private theorem flat_quotient_tensor_of_flat_quotient
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (J : Ideal R)
    (h : Module.Flat (R ⧸ J) (N ⧸ (J • (⊤ : Submodule R N)))) :
    Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] N) :=
  let := h
  Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective (S := R ⧸ J) Ideal.Quotient.mk_surjective
      (TensorProduct.quotTensorEquivQuotSMul N J))

/-- Flatness of the reduction modulo a prime passes to the reduction modulo any larger
ideal, by base change along the induced map of quotients. -/
private theorem flat_quotient_tensor_of_le
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] {p J : Ideal R} (hpJ : p ≤ J)
    (h : Module.Flat (R ⧸ p) ((R ⧸ p) ⊗[R] N)) :
    Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] N) := by
  let := h
  let : Algebra (R ⧸ p) (R ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (by simpa using hpJ)
  have : IsScalarTower R (R ⧸ p) (R ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ p) (R ⧸ J) (R ⧸ J) N).symm

/-- **The prime-by-prime form of Claim 1 of the proof of Stacks 05U9 from its nilpotent-ideal
form.** If `N ⧸ IN` is flat over `R ⧸ I` for a nilpotent ideal `I`, then `N ⧸ 𝔮N` is flat over
`R ⧸ 𝔮` for every prime `𝔮`.

A nilpotent ideal lies in every prime, and flatness of a reduction is inherited by every
further reduction by base change along the induced map of quotients. -/
theorem flat_quotient_primes_of_isNilpotent
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] {I : Ideal R}
    (hI : IsNilpotent I) (h : Module.Flat (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))))
    (q : Ideal R) [hq : q.IsPrime] :
    Module.Flat (R ⧸ q) (N ⧸ (q • (⊤ : Submodule R N))) := by
  obtain ⟨n, hn⟩ := hI
  have hIq : I ≤ q := by
    intro x hx
    have hmem : x ^ n = 0 := by simpa [hn] using Ideal.pow_mem_pow hx n
    exact hq.mem_of_pow_mem n (hmem ▸ q.zero_mem)
  let := flat_quotient_tensor_of_le (N := N) hIq (flat_quotient_tensor_of_flat_quotient I h)
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective (S := R ⧸ q) Ideal.Quotient.mk_surjective
      (TensorProduct.quotTensorEquivQuotSMul N q)).symm

/-- **The second half of Claim 2 in the proof of Stacks 05U9.** In the situation of Stacks
0AT0 with `B` a localization of a finitely presented `A`-algebra and `N` finitely presented
over `B`, a prime `𝔭` all of whose strict specializations are good is itself good.

At the maximal ideal this is the hypothesis `hmax`. Below it, for `f ∈ A ∖ 𝔭` every prime
containing `𝔭 + (f)` strictly contains `𝔭`, hence is good, so Stacks 0AT9 over
`A/(𝔭 + (f))` makes `u ⊗ id_{A/(𝔭+(f))}` injective; an element of the kernel of
`N/𝔭N → M/𝔭M` therefore lies in `f(N/𝔭N)` for every such `f`, and the separatedness of
`N/𝔭N` finishes. -/
theorem rTensor_residueField_injective_of_forall_gt
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    [IsLocalRing X.A] [IsLocalRing X.Bₛ] [IsLocalHom (algebraMap X.A X.Bₛ)]
    [Algebra.EssFiniteType X.A X.Bₛ]
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hmax : Function.Injective (u.rTensor (IsLocalRing.maximalIdeal X.A).ResidueField))
    (hflat : ∀ (q : Ideal X.A) [q.IsPrime],
      Module.Flat (X.A ⧸ q) (X.N ⧸ (q • (⊤ : Submodule X.A X.N))))
    (p : Ideal X.A) [p.IsPrime]
    (hgt : ∀ (q : Ideal X.A) [q.IsPrime], p < q →
      Function.Injective (u.rTensor q.ResidueField)) :
    Function.Injective (u.rTensor p.ResidueField) := by
  by_cases hpm : p = IsLocalRing.maximalIdeal X.A
  · subst hpm
    exact hmax
  refine injective_rTensor_residueField_of_injective_mapQ u p ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (p • (⊤ : Submodule X.A X.N)) x
  have hfn : u n ∈ p • (⊤ : Submodule X.A M) := by
    rwa [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  have hmem : ∀ f₀ : X.A, f₀ ∉ p →
      (Submodule.Quotient.mk n : X.N ⧸ (p • (⊤ : Submodule X.A X.N))) ∈
        Ideal.span {f₀} • (⊤ : Submodule X.A (X.N ⧸ (p • (⊤ : Submodule X.A X.N)))) := by
    intro f₀ hf₀
    set J : Ideal X.A := p ⊔ Ideal.span {f₀} with hJ
    have hpJ : p ≤ J := le_sup_left
    have : Module.Flat (X.A ⧸ J) ((X.A ⧸ J) ⊗[X.A] X.N) :=
      flat_quotient_tensor_of_le hpJ (flat_quotient_tensor_of_flat_quotient p (hflat p))
    have hfib : ∀ (q : Ideal X.A) [q.IsPrime], J ≤ q →
        Function.Injective (u.rTensor q.ResidueField) := by
      intro q hq hJq
      exact hgt q (lt_of_le_of_ne (le_sup_left.trans hJq) fun hpq =>
        hf₀ (hpq ▸ hJq (Submodule.mem_sup_right (Ideal.mem_span_singleton_self f₀))))
    have hJinj : Function.Injective (u.rTensor (X.A ⧸ J)) :=
      rTensor_quotient_injective_of_rTensor_residueField_injective_of_le
        (B₀ := X.B) (B := X.Bₛ) X.S u J hfib
    have hnJ : n ∈ J • (⊤ : Submodule X.A X.N) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply (mapQ_injective_iff_rTensor_quotient u J).mpr hJinj
      rw [Submodule.mapQ_apply, map_zero, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mono_left hpJ hfn
    rw [hJ, Submodule.sup_smul] at hnJ
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hnJ
    have hxz : (Submodule.Quotient.mk n : X.N ⧸ (p • (⊤ : Submodule X.A X.N))) =
        Submodule.Quotient.mk z := by
      rw [← hyz, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).mpr hy, zero_add]
    have hmap : Submodule.map (p • (⊤ : Submodule X.A X.N)).mkQ
        (Ideal.span {f₀} • (⊤ : Submodule X.A X.N)) =
        Ideal.span {f₀} • (⊤ : Submodule X.A (X.N ⧸ (p • (⊤ : Submodule X.A X.N)))) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [hxz, ← hmap]
    exact Submodule.mem_map_of_mem hz
  exact Stacks.ResidueFibre.eq_zero_of_forall_mem_smul_top (B := X.Bₛ) p hpm (hflat p) _ hmem

/-- Flatness of the reduction of a module modulo an ideal transports along a linear
equivalence of modules. -/
private theorem flat_quotient_of_linearEquiv
    {R N N' : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (J : Ideal R) (e : N ≃ₗ[R] N')
    (h : Module.Flat (R ⧸ J) (N ⧸ (J • (⊤ : Submodule R N)))) :
    Module.Flat (R ⧸ J) (N' ⧸ (J • (⊤ : Submodule R N'))) := by
  let := h
  have hmap : Submodule.map (e : N →ₗ[R] N') (J • (⊤ : Submodule R N)) =
      J • (⊤ : Submodule R N') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective (S := R ⧸ J) Ideal.Quotient.mk_surjective
      (Submodule.Quotient.equiv _ _ e hmap)).symm

/-- **Claim 2 of the proof of Stacks 05U9.** In Situation 0AT0, with `B` presented as the
localization at a prime of a polynomial algebra over `A` in finitely many variables and `N`
finitely presented over `B`, the map `u ⊗ id_{κ(𝔭)}` is injective for every prime `𝔭` of `A`.

The Zorn argument is `rTensor_residueField_injective_of_spreadout_of_step`; its two
hypotheses are `exists_fg_ideal_rTensor_residueField_injective_of_le` and
`rTensor_residueField_injective_of_forall_gt`.

`hclaim1` is what this proof needs of Claim 1 of the source. -/
theorem rTensor_residueField_injective_of_claims
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    [Module.FinitePresentation S.B S.N]
    (hclaim1 : ∀ (q : Ideal S.A) [q.IsPrime],
      Module.Flat (S.A ⧸ q) (S.N ⧸ (q • (⊤ : Submodule S.A S.N))))
    (p : Ideal S.A) [p.IsPrime] :
    Function.Injective (S.u.rTensor p.ResidueField) := by
  let := P.prime_isPrime
  let := P.polynomialAlgebra
  let := P.scalarTower
  let := P.isLocalization
  let N' := ULift.{max u₃ u₄, u₄} S.N
  let M' := ULift.{max u₃ u₄, u₃} S.M
  let eNB : N' ≃ₗ[S.B] S.N := ULift.moduleEquiv
  let : Module.FinitePresentation S.B N' := Module.FinitePresentation.of_equiv eNB.symm
  let X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₁, u₂, max u₃ u₄} :=
    { A := S.A, B := MvPolynomial (Fin P.variableCount) S.A, Bₛ := S.B, N := N',
      S := P.prime.primeCompl }
  let : Module S.A X.N := X.moduleBase
  let eN : X.N ≃ₗ[S.A] S.N :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r n
        show (algebraMap (MvPolynomial (Fin P.variableCount) S.A) S.B
          (algebraMap S.A (MvPolynomial (Fin P.variableCount) S.A) r)) • n.down =
            r • n.down
        rw [← IsScalarTower.algebraMap_apply S.A
          (MvPolynomial (Fin P.variableCount) S.A) S.B, IsScalarTower.algebraMap_smul] }
  let eM : M' ≃ₗ[S.A] S.M := ULift.moduleEquiv
  let : Module.Flat S.A M' := Module.Flat.of_linearEquiv eM
  let u' : X.N →ₗ[S.A] M' := eM.symm.toLinearMap ∘ₗ S.u ∘ₗ eN.toLinearMap
  have hmapeq : ∀ r : X.A,
      (@algebraMap X.A X.Bₛ _ _ X.algebraLocalized) r = algebraMap S.A S.B r := fun r =>
    (IsScalarTower.algebraMap_apply S.A (MvPolynomial (Fin P.variableCount) S.A) S.B r).symm
  have halgeq : X.algebraLocalized = S.algebraAB := Algebra.algebra_ext _ _ hmapeq
  have : IsLocalRing X.A := S.localRingA
  have : IsLocalRing X.Bₛ := S.localRingB
  have : IsLocalHom (@algebraMap X.A X.Bₛ _ _ X.algebraLocalized) :=
    ⟨fun r hr => S.localHom.map_nonunit r (hmapeq r ▸ hr)⟩
  have : @Algebra.EssFiniteType X.A X.Bₛ _ _ X.algebraLocalized := by
    rw [halgeq]
    exact S.essentiallyFiniteType
  have hflat' : ∀ (q : Ideal S.A) [q.IsPrime],
      Module.Flat (S.A ⧸ q) (X.N ⧸ (q • (⊤ : Submodule S.A X.N))) :=
    fun q _ => flat_quotient_of_linearEquiv q eN.symm (hclaim1 q)
  have hspread : ∀ (q : Ideal S.A) [q.IsPrime],
      Function.Injective (S.u.rTensor q.ResidueField) →
        ∃ a : Ideal (Localization.AtPrime q), a.FG ∧
          a ≤ q.map (algebraMap S.A (Localization.AtPrime q)) ∧
          ∀ (r : Ideal S.A) [r.IsPrime], r ≤ q →
            a ≤ r.map (algebraMap S.A (Localization.AtPrime q)) →
              Function.Injective (S.u.rTensor r.ResidueField) := by
    intro q _ hq
    obtain ⟨a, hfg, hle, hall⟩ := exists_fg_ideal_rTensor_residueField_injective_of_le
      X u' q ((injective_rTensor_conj eN eM S.u).mpr hq)
    exact ⟨a, hfg, hle, fun r _ hrq hra =>
      (injective_rTensor_conj eN eM S.u).mp (hall r hrq hra)⟩
  have hstep : ∀ (q : Ideal S.A) [q.IsPrime],
      (∀ (r : Ideal S.A) [r.IsPrime], q < r →
        Function.Injective (S.u.rTensor r.ResidueField)) →
          Function.Injective (S.u.rTensor q.ResidueField) := by
    intro q _ hgt
    exact (injective_rTensor_conj eN eM S.u).mp (rTensor_residueField_injective_of_forall_gt X u'
      ((injective_rTensor_conj eN eM S.u).mpr (rTensor_residueField_maximalIdeal_injective S))
      hflat' q fun r _ hqr => (injective_rTensor_conj eN eM S.u).mpr (hgt r hqr))
  exact rTensor_residueField_injective_of_spreadout_of_step S hspread hstep p

end AlgebraicGeometry

end
