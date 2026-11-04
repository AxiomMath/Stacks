module

public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Flat.TensorProductFiniteness
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant
public import StacksFrontier.RingTheory.Noetherian.ArtinRees
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Lifting flatness along the filtration by the powers of an ideal

Let `R` be a ring, `I ⊆ R` an ideal and `M` an `R`-module. This file proves two statements.

* If `M/IM` is flat over `R/I` and the multiplication map `M ⊗_R I^n/I^{n+1} → I^nM/I^{n+1}M` is
  injective for `n = 1, …, k`, then `M/I^{k+1}M` is flat over `R/I^{k+1}`.
* If `R → S` is a ring map with `R` and `S` Noetherian, `M` is a finite `S`-module and `M/IⁿM` is
  flat over `R/Iⁿ` for every `n ≥ 1`, then for every prime `q` of `S` with `IS ⊆ q` the
  localization `M_q` is flat over `R`.

## Main results

* `Module.flat_quotient_pow_succ_of_flat_quotient_of_exact` (also
  `Stacks.Flatness.AdicFiltrationLifting.solution`): flatness of `M/I^{k+1}M` over `R/I^{k+1}` from
  flatness of `M/IM` over `R/I` and the injectivity of the multiplication maps on the graded pieces
  `I^n/I^{n+1}`, `n = 1, …, k`.
* `Module.Flat.of_flat_quotient_pow` (also `Stacks.Flatness.ArtinReesLocalization.solution`):
  flatness over `R` of the localization `M_q` at every prime `q ⊇ IS`, when `M/IⁿM` is flat over
  `R/Iⁿ` for every `n ≥ 1`.

## References

* [Stacks Project, Tag 0AS8](https://stacks.math.columbia.edu/tag/0AS8)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)

## Tags

flat module, local criterion of flatness, Artin-Rees, adic filtration, graded piece, ideal power,
localization
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flatness.AdicFiltrationLifting


section Exact

variable {R : Type*} [Ring R] {A B C D : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]

/-- Let `D --f--> A --q--> B --g--> C` be linear maps with `q` surjective and `q ∘ f = 0`. If `f`
is exact into `g ∘ q`, then `g` is injective. -/
private theorem injective_of_exact_comp_of_surjective {f : D →ₗ[R] A} {q : A →ₗ[R] B}
    {g : B →ₗ[R] C} (hq : Function.Surjective q) (hqf : q ∘ₗ f = 0)
    (h : Function.Exact f (g ∘ₗ q)) : Function.Injective g := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro b hb
  obtain ⟨a, rfl⟩ := hq b
  obtain ⟨d, rfl⟩ := (h a).mp hb
  exact congr($hqf d)

end Exact

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- If `R → S` is surjective, so is the induced map `I → I S` for any ideal `I` of `R`. -/
private theorem idealMap_surjective_of_surjective {S : Type*} [CommRing S] [Algebra R S]
    (hsurj : Function.Surjective (algebraMap R S)) (I : Ideal R) :
    Function.Surjective (Algebra.idealMap S I) := fun z => by
  obtain ⟨y, hy, hyz⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp z.2
  exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

/-- The exactness of `M ⊗_R L → M ⊗_R K → M/LM`, for ideals `L ≤ K` of `R`, read with the tensor
factors in the other order and the target `M/LM` replaced by `(R/L) ⊗_R M`:
`L ⊗_R M → K ⊗_R M → (R/L) ⊗_R M`, where the second map is induced by `K ⊆ R → R/L`. -/
private theorem exact_rTensor_of_exact_lTensor {L K : Ideal R} (hLK : L ≤ K)
    (hexact : Function.Exact ((Submodule.inclusion hLK).lTensor M)
      ((L • (⊤ : Submodule R M)).mkQ ∘ₗ (TensorProduct.rid R M).toLinearMap ∘ₗ
        K.subtype.lTensor M)) :
    Function.Exact (LinearMap.rTensor M (Submodule.inclusion hLK))
      (LinearMap.rTensor M (L.mkQ ∘ₗ K.subtype)) :=
  Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm R M L) (e₂ := TensorProduct.comm R M K)
    (e₃ := (TensorProduct.quotTensorEquivQuotSMul M L).symm)
    (LinearMap.rTensor_comp_comm _)
    (TensorProduct.ext' fun m x => by
      simp [TensorProduct.smul_tmul', Algebra.smul_def, Ideal.Quotient.algebraMap_eq])
    hexact

/-- For ideals `L ≤ K` of `R`, the `R`-linear comparison map `(K/L) ⊗_R M → (R/L) ⊗_R M` is
injective as soon as `M ⊗_R L → M ⊗_R K → M/LM` is exact. -/
private theorem rTensor_subtype_map_mk_injective_of_exact {L K : Ideal R} (hLK : L ≤ K)
    (hexact : Function.Exact ((Submodule.inclusion hLK).lTensor M)
      ((L • (⊤ : Submodule R M)).mkQ ∘ₗ (TensorProduct.rid R M).toLinearMap ∘ₗ
        K.subtype.lTensor M)) :
    Function.Injective (LinearMap.rTensor M
      ((Ideal.map (Ideal.Quotient.mk L) K).subtype.restrictScalars R)) := by
  set q : ↥K →ₗ[R] ↥(Ideal.map (Ideal.Quotient.mk L) K) := Algebra.idealMap (R ⧸ L) K
  have hqsurj : Function.Surjective q :=
    idealMap_surjective_of_surjective Ideal.Quotient.mk_surjective K
  have hqL : q ∘ₗ Submodule.inclusion hLK = 0 :=
    LinearMap.ext fun y => Subtype.ext ((Submodule.Quotient.mk_eq_zero L).mpr y.2)
  have hqsub : ((Ideal.map (Ideal.Quotient.mk L) K).subtype.restrictScalars R) ∘ₗ q
      = L.mkQ ∘ₗ K.subtype := LinearMap.ext fun _ => rfl
  refine injective_of_exact_comp_of_surjective
    (f := LinearMap.rTensor M (Submodule.inclusion hLK))
    (LinearMap.rTensor_surjective M hqsurj) ?_ ?_
  · rw [← LinearMap.rTensor_comp, hqL, LinearMap.rTensor_zero]
  · rw [← LinearMap.rTensor_comp, hqsub]
    exact exact_rTensor_of_exact_lTensor hLK hexact

/-- For ideals `L ≤ K` of `R` with `K² ⊆ L`, flatness of `M/KM` over `R/K` together with the
exactness of `M ⊗_R L → M ⊗_R K → M/LM` gives flatness of `M/LM` over `R/L`. -/
private theorem flat_quotient_smul_top_of_flat_quotient_smul_top_of_exact {L K : Ideal R}
    (hLK : L ≤ K) (hsq : K ^ 2 ≤ L)
    (hflat : Module.Flat (R ⧸ K) (M ⧸ (K • (⊤ : Submodule R M))))
    (hexact : Function.Exact ((Submodule.inclusion hLK).lTensor M)
      ((L • (⊤ : Submodule R M)).mkQ ∘ₗ (TensorProduct.rid R M).toLinearMap ∘ₗ
        K.subtype.lTensor M)) :
    Module.Flat (R ⧸ L) (M ⧸ (L • (⊤ : Submodule R M))) :=
  flat_of_sq_zero_local_criterion (Ideal.map (Ideal.Quotient.mk L) K)
    (by rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]; exact hsq)
    (flat_quotient_map_quotient K L hflat)
    (injective_lift_lsmul_of_rTensor_injective L _
      (rTensor_subtype_map_mk_injective_of_exact hLK hexact))

/-- Let `R` be a ring, `I ⊆ R` an ideal and `M` an `R`-module. If `M/IM` is flat over `R/I` and the
multiplication map `M ⊗_R I^n/I^{n+1} → I^nM/I^{n+1}M` is injective for `n = 1, …, k`, then
`M/I^{k+1}M` is flat over `R/I^{k+1}`. -/
public theorem solution {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hexact : ∀ n, 1 ≤ n → n ≤ k →
      Function.Exact
        ((Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ : I ^ (n + 1) ≤ I ^ n)).lTensor M)
        ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ ∘ₗ
          (TensorProduct.rid R M).toLinearMap ∘ₗ (I ^ n).subtype.lTensor M)) :
    Module.Flat (R ⧸ I ^ (k + 1)) (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M))) := by
  induction k with
  | zero =>
    rw [show I ^ (0 + 1) = I by simp]
    exact hflat
  | succ k ih =>
    exact flat_quotient_smul_top_of_flat_quotient_smul_top_of_exact
      (K := I ^ (k + 1)) (L := I ^ (k + 2)) (Ideal.pow_le_pow_right (by omega))
      (by rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega))
      (ih fun n h1 h2 => hexact n h1 (by omega)) (hexact (k + 1) (by omega) le_rfl)

end Stacks.Flatness.AdicFiltrationLifting

/-!
## The statement of `Module.flat_quotient_pow_succ_of_flat_quotient_of_exact`

Part (1) of Tag 0AS8 is the case `k = 1` and part (2) the general `k`, so only the general form is
stated and tagged. The case `k = 0` is the hypothesis `hflat` itself.

`M/JM` is `M ⧸ (J • ⊤ : Submodule R M)`, an `R ⧸ J`-module through
`Module.instQuotientIdealSubmoduleHSMulTop`; this is the spelling in which flatness of the quotient
is stated.

The source's injectivity hypothesis is rendered as the exactness of
`M ⊗_R I^{n+1} → M ⊗_R I^n → M/I^{n+1}M`, where the first map is `lTensor M` of the inclusion
`I^{n+1} ⊆ I^n` and the second is `m ⊗ x ↦ x • m` followed by the quotient map. This is equivalent
to the injectivity of the source's map, in two steps, neither of which loses information. First,
the target may be enlarged from `I^nM/I^{n+1}M` to `M/I^{n+1}M`: the map
`I^nM/I^{n+1}M → M/I^{n+1}M` induced by `I^nM ⊆ M` is injective, because an element of `I^nM` lying
in `I^{n+1}M` is zero in `I^nM/I^{n+1}M`. Second, `M ⊗_R I^n/I^{n+1}` is the quotient of
`M ⊗_R I^n` by the range of `lTensor M` of the inclusion — this is right exactness of the tensor
product, `lTensor.equiv` applied to the exact sequence `I^{n+1} → I^n → I^n/I^{n+1}` — and a map
out of a quotient `X/X₀` is injective exactly when the kernel of the corresponding map on `X` is
`X₀`. Since the composite of the two maps is zero (an element of `I^{n+1}` times an element of `M`
lies in `I^{n+1}M`), the inclusion `range ⊆ ker` is free and `Function.Exact` carries no more than
the source's injectivity. Stating the hypothesis this way keeps both maps canonical and avoids
naming a subquotient of `M`, at the cost of the reformulation recorded here; `LinearMap.exact_iff`
reads it as `ker = range`.

The tensor factors are in the source's order, `M` first, so the multiplication map `M ⊗_R I^n → M`
is `(TensorProduct.rid R M) ∘ₗ (I ^ n).subtype.lTensor M`; over a commutative ring this is the map
`Ideal.subtype_rTensor_range` treats in the other order, whose range is `I^n • ⊤ = I^nM`.
-/



namespace Module

/-- Let `R` be a ring, `I ⊆ R` an ideal and `M` an `R`-module. If `M/IM` is flat over `R/I` and the
multiplication map `M ⊗_R I^n/I^{n+1} → I^nM/I^{n+1}M` is injective for `n = 1, …, k`, then
`M/I^{k+1}M` is flat over `R/I^{k+1}`.

The injectivity of `M ⊗_R I^n/I^{n+1} → I^nM/I^{n+1}M` is spelled as the exactness of
`M ⊗_R I^{n+1} → M ⊗_R I^n → M/I^{n+1}M`, the first map being `lTensor M` of the inclusion
`I^{n+1} ⊆ I^n` and the second `m ⊗ x ↦ x • m` followed by the quotient map; see the module
docstring for why this is the same condition. -/
@[stacks 0AS8 "Both parts: part (1) is the case `k = 1`. The injectivity of
`M ⊗_R I^n/I^{n + 1} → I^nM/I^{n + 1}M` is stated as exactness of
`M ⊗_R I^{n + 1} → M ⊗_R I^n → M/I^{n + 1}M`, an equivalent form; see the module docstring."]
public theorem flat_quotient_pow_succ_of_flat_quotient_of_exact {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hexact : ∀ n, 1 ≤ n → n ≤ k →
      Function.Exact
        ((Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ : I ^ (n + 1) ≤ I ^ n)).lTensor M)
        ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ ∘ₗ
          (TensorProduct.rid R M).toLinearMap ∘ₗ (I ^ n).subtype.lTensor M)) :
    Module.Flat (R ⧸ I ^ (k + 1)) (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M))) :=
      by exact Stacks.Flatness.AdicFiltrationLifting.solution I M k hflat hexact

end Module


namespace Stacks.Flatness.ArtinReesLocalization

open TensorProduct

/-- The image of `M ⊗_R N → M ⊗_R I` lies in `Iⁿ · (M ⊗_R I)` for any submodule `N` of `I`
contained in `Iⁿ⁺¹`. -/
private theorem lTensor_range_subtype_le_pow_smul_top {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ) (N : Submodule R (↥I))
    (hN : N ≤ Submodule.comap I.subtype (I ^ (n + 1))) :
    LinearMap.range (LinearMap.lTensor M N.subtype)
      ≤ I ^ n • (⊤ : Submodule R (M ⊗[R] ↥I)) := by
  have hP : Submodule.map I.subtype (I ^ n • (⊤ : Submodule R ↥I)) = I ^ (n + 1) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, pow_succ,
      Ideal.smul_eq_mul]
  have hsub : Submodule.comap I.subtype (I ^ (n + 1)) ≤ I ^ n • (⊤ : Submodule R ↥I) := by
    rw [← hP, Submodule.comap_map_eq_of_injective Subtype.val_injective]
  have key : ∀ (m : M) (y : ↥I), y ∈ I ^ n • (⊤ : Submodule R ↥I) →
      m ⊗ₜ[R] y ∈ I ^ n • (⊤ : Submodule R (M ⊗[R] ↥I)) := by
    intro m y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr z _
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro y z hy hz
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => simpa using key m _ (hsub (hN x.2))
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv

/-- If `M/Iⁿ⁺¹M` is flat over `R/Iⁿ⁺¹` for every `n`, then every element of the kernel of
`M ⊗_R I → M` lies in `Iⁿ · (M ⊗_R I)`. -/
private theorem mem_pow_smul_top_of_lTensor_subtype_eq_zero {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hflat : ∀ n : ℕ,
      Module.Flat (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))))
    (n : ℕ) {x : M ⊗[R] ↥I} (hx : LinearMap.lTensor M I.subtype x = 0) :
    x ∈ I ^ n • (⊤ : Submodule R (M ⊗[R] ↥I)) := by
  set L : Ideal R := I ^ (n + 1) with hL
  have hsurj : Function.Surjective (algebraMap R (R ⧸ L)) := Ideal.Quotient.mk_surjective
  have : Module.Flat (R ⧸ L) (M ⧸ (L • (⊤ : Submodule R M))) := hflat n
  have hbc : Module.Flat (R ⧸ L) ((R ⧸ L) ⊗[R] M) :=
    Module.Flat.of_linearEquiv
      (LinearEquiv.extendScalarsOfSurjective hsurj (TensorProduct.quotTensorEquivQuotSMul M L))
  set π : ↥I →ₗ[R] ↥(I.map (algebraMap R (R ⧸ L))) := Algebra.idealMap (R ⧸ L) I with hπ
  have hinj : Function.Injective (LinearMap.lTensor M
      ((I.map (algebraMap R (R ⧸ L))).subtype.restrictScalars R)) := by
    rw [LinearMap.lTensor_inj_iff_rTensor_inj]
    exact rTensor_subtype_baseChange_inj _ hbc
  have hπsurj : Function.Surjective π :=
    Stacks.Flatness.AdicFiltrationLifting.idealMap_surjective_of_surjective hsurj I
  have hxπ : LinearMap.lTensor M π x = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show ((I.map (algebraMap R (R ⧸ L))).subtype.restrictScalars R) ∘ₗ π
        = (Algebra.linearMap R (R ⧸ L)) ∘ₗ I.subtype from by ext y; rfl,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hx, map_zero]
  have hmem : x ∈ LinearMap.range (LinearMap.lTensor M (LinearMap.ker π).subtype) := by
    rw [← LinearMap.exact_iff.mp
      (lTensor_exact M (LinearMap.exact_subtype_ker_map π) hπsurj)]
    exact hxπ
  refine lTensor_range_subtype_le_pow_smul_top I n (LinearMap.ker π) (fun y hy => ?_) hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hy)

/-- An element of `⋂ₙ Jⁿ N`, for `N` a finite module over a Noetherian ring `S` and `J` an ideal
contained in a prime `q`, is killed by an element outside `q`. -/
private theorem exists_mem_primeCompl_smul_eq_zero {S : Type*} [CommRing S] [IsNoetherianRing S]
    {N : Type*} [AddCommGroup N] [Module S N] [Module.Finite S N] (J q : Ideal S) [q.IsPrime]
    (hq : J ≤ q) {z : N} (hz : z ∈ krullIntersection N J) :
    ∃ t : q.primeCompl, (t : S) • z = 0 := by
  obtain ⟨g, hgq, hg⟩ := exists_notMem_localized_krullIntersection_eq_bot (M := N) J q hq
  have h0 : IsLocalizedModule.mk'
      (LocalizedModule.mkLinearMap (Submonoid.powers g) N) z (1 : Submonoid.powers g) = 0 := by
    rw [← Submodule.mem_bot (Localization (Submonoid.powers g)), ← hg]
    exact ⟨z, hz, 1, rfl⟩
  obtain ⟨t, ht⟩ := (IsLocalizedModule.mk'_eq_zero'
    (LocalizedModule.mkLinearMap (Submonoid.powers g) N) (1 : Submonoid.powers g)).mp h0
  obtain ⟨k, hk⟩ := t.2
  exact ⟨⟨t, hk ▸ pow_mem hgq k⟩, by simpa [Submonoid.smul_def] using ht⟩

/-- Let `R → S` be a ring map with `R` and `S` Noetherian and `M` a finite `S`-module such that
`M/Iⁿ⁺¹M` is flat over `R/Iⁿ⁺¹` for every `n`. Then for every prime `q` of `S` containing `IS` and
every localization `Mq` of `M` at `q`, the map `Mq ⊗_R I → Mq ⊗_R R` induced by `I ⊆ R` is
injective. -/
private theorem lTensor_subtype_injective_of_isLocalizedModule {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hflat : ∀ n : ℕ,
      Module.Flat (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))))
    (q : Ideal S) [q.IsPrime] (hq : I.map (algebraMap R S) ≤ q)
    (Mq : Type*) [AddCommGroup Mq] [Module R Mq] [Module S Mq] [IsScalarTower R S Mq]
    (f : M →ₗ[S] Mq) [IsLocalizedModule.AtPrime q f] :
    Function.Injective (LinearMap.lTensor Mq I.subtype) := by
  have : Module.Finite S (M ⊗[R] ↥I) := Module.Finite.tensorProduct_right R S M ↥I
  refine Stacks.Flat.LocalCriterion.lTensor_injective_of_isLocalizedModule q.primeCompl f
    I.subtype fun z hz =>
    exists_mem_primeCompl_smul_eq_zero (I.map (algebraMap R S)) q hq ?_
  simp only [krullIntersection, Submodule.mem_iInf]
  intro n
  show z ∈ Submodule.restrictScalars R
    ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S (M ⊗[R] ↥I)))
  rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  exact mem_pow_smul_top_of_lTensor_subtype_eq_zero I hflat n hz

/-- Under the hypotheses of `Module.Flat.of_flat_quotient_pow`, the localization
`LocalizedModule q.primeCompl M` is flat over `R`. -/
@[ega "0 10.2.1" "d ⇒ a"]
private theorem flat_of_flat_quotient_pow_localizedModule {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hflat : ∀ n : ℕ,
      Module.Flat (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))))
    (q : Ideal S) [q.IsPrime] (hq : I.map (algebraMap R S) ≤ q) :
    Module.Flat R (LocalizedModule q.primeCompl M) := by
  have hp : (q.comap (algebraMap R S)).IsPrime := Ideal.IsPrime.comap _
  let A := Localization.AtPrime (q.comap (algebraMap R S))
  let B := Localization.AtPrime q
  let Mq := LocalizedModule q.primeCompl M
  let f : M →ₗ[S] Mq := LocalizedModule.mkLinearMap q.primeCompl M
  let _ : Algebra A B :=
    (Localization.localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl).toAlgebra
  have _ : IsLocalHom (algebraMap A B) :=
    Localization.isLocalHom_localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl
  let _ : Module A Mq := Module.compHom _ (algebraMap A B)
  have _ : IsScalarTower A B Mq := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower R A Mq := IsScalarTower.of_algebraMap_smul fun r x => by
    calc algebraMap R A r • x = algebraMap A B (algebraMap R A r) • x := rfl
      _ = algebraMap S B (algebraMap R S r) • x := by
            rw [show algebraMap A B (algebraMap R A r)
              = algebraMap S B (algebraMap R S r) from
              Localization.localRingHom_to_map _ _ _ _ r]
      _ = algebraMap R S r • x := IsScalarTower.algebraMap_smul _ _ _
      _ = r • x := IsScalarTower.algebraMap_smul _ _ _
  have hIA : I.map (algebraMap R A) ≠ ⊤ := fun hcon =>
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top <| top_le_iff.mp <| by
      rw [← hcon, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono fun r hr => Ideal.mem_comap.2 (hq (Ideal.mem_map_of_mem _ hr))
  have hinj : Function.Injective
      (LinearMap.rTensor Mq (I.map (algebraMap R A)).subtype) :=
    Ideal.rTensor_subtype_map_injective A I Mq (by
      rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
      exact lTensor_subtype_injective_of_isLocalizedModule I M hflat q hq Mq f)
  have hquot : Module.Flat (A ⧸ I.map (algebraMap R A))
      (Mq ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A Mq))) :=
    Stacks.Flatness.flat_quotient_map_of_isLocalization (q.comap (algebraMap R S)).primeCompl A I Mq
      (Stacks.Flat.LocalCriterion.flat_quotient_of_isLocalizedModule I q.primeCompl f
        (pow_one I ▸ hflat 0))
  have : Module.Flat A Mq :=
    Module.Flat.of_rTensor_subtype_injective_of_flat_quotient B Mq
      (I.map (algebraMap R A)) hIA hinj hquot
  have : Module.Flat R A := IsLocalization.flat A (q.comap (algebraMap R S)).primeCompl
  exact Module.Flat.trans R A Mq

end Stacks.Flatness.ArtinReesLocalization

/-!
## The statement of `Module.Flat.of_flat_quotient_pow`

Localizing `S` at a prime `q` is the identity when `S` is local with maximal ideal `q`, so the
statement contains the source's "in particular": if `S` is local and `IS` is contained in its
maximal ideal, then `M` itself is flat over `R`.

The ring map `R → S` is an `Algebra R S` instance, and `M` carries compatible `R`- and `S`-module
structures (`IsScalarTower R S M`) rather than being handed the restriction of scalars of an
`S`-module; this is the spelling in which `Module.flat_of_isLocalized_maximal` and the rest of
`Mathlib.RingTheory.Flat.Localization` are phrased.

`M/JM` for an ideal `J ⊆ R` is `M ⧸ (J • ⊤ : Submodule R M)`, an `R ⧸ J`-module through
`Module.instQuotientIdealSubmoduleHSMulTop`. Because of the scalar tower, `J • ⊤` computed over `R`
is the submodule `(JS)M` of the source, so nothing is lost by taking the quotient over `R`. The
hypothesis is indexed as `∀ n : ℕ` applied to `I ^ (n + 1)`, which is exactly the source's range
`n ≥ 1`; the omitted `n = 0` instance is vacuous, `R ⧸ I ^ 0` being the zero ring.

The condition `q ∈ V(IS)` is written as the ideal inequality `I.map (algebraMap R S) ≤ q`, and the
localization `M_q` is given abstractly: an arbitrary `S`-module `Mq` together with `f : M →ₗ[S] Mq`
exhibiting it as a localization at `q`, in the sense of `IsLocalizedModule.AtPrime q f`. Stating
the instance rather than fixing the model `LocalizedModule q.primeCompl M` lets a user with any
other construction of `M_q` — for instance `M` itself when `S` is local with maximal ideal `q` —
apply the lemma directly. That last case is the source's concluding "in particular", obtained with
`Mq = M` and `f = LinearMap.id`, which is why it needs no separate declaration.
-/


namespace Module.Flat

/-- Let `R → S` be a ring map with `R` and `S` Noetherian, let `I ⊆ R` be an ideal and let `M` be a
finite `S`-module. If `M/IⁿM` is flat over `R/Iⁿ` for every `n ≥ 1`, then for every prime `q` of
`S` containing `IS` the localization `M_q` is flat over `R`.

The localization is taken abstractly: `Mq` is any `S`-module with a map `f : M →ₗ[S] Mq` exhibiting
it as the localization of `M` at `q`. Taking `S` local with maximal ideal `q`, `Mq = M` and
`f = LinearMap.id` shows that `M` is flat over `R` when `IS` is contained in the maximal ideal of a
local `S`. -/
@[stacks 0523 "Both statements: the second is the case where `S` is local, `q` is its maximal
ideal and the localization is taken to be `M` itself. `M/IⁿM` is
`M ⧸ (I ^ n • ⊤ : Submodule R M)` and `M_q` is given by `IsLocalizedModule.AtPrime q f`; see the
module docstring.", ega "0 10.2.1" "d ⇒ a"]
public theorem of_flat_quotient_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hflat : ∀ n : ℕ,
      Module.Flat (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))))
    (q : Ideal S) [q.IsPrime] (hq : I.map (algebraMap R S) ≤ q)
    (Mq : Type*) [AddCommGroup Mq] [Module R Mq] [Module S Mq] [IsScalarTower R S Mq]
    (f : M →ₗ[S] Mq) [IsLocalizedModule.AtPrime q f] :
    Module.Flat R Mq :=
  have : Module.Flat R (LocalizedModule q.primeCompl M) :=
    Stacks.Flatness.ArtinReesLocalization.flat_of_flat_quotient_pow_localizedModule I M hflat q hq
  Module.Flat.of_linearEquiv
    ((IsLocalizedModule.linearEquiv q.primeCompl f
      (LocalizedModule.mkLinearMap q.primeCompl M)).restrictScalars R)

end Module.Flat

namespace Stacks.Flatness.ArtinReesLocalization

/-- Let `R → S` be a ring map with `R` and `S` Noetherian, let `I ⊆ R` be an ideal and let `M` be a
finite `S`-module. If `M/IⁿM` is flat over `R/Iⁿ` for every `n ≥ 1`, then for every prime `q` of
`S` containing `IS`, every localization `Mq` of `M` at `q` is flat over `R`. -/
public alias solution := Module.Flat.of_flat_quotient_pow

end Stacks.Flatness.ArtinReesLocalization
