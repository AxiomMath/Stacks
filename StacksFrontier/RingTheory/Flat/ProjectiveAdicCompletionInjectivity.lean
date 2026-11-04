module

public import StacksFrontier.RingTheory.AdicCompletion.FiniteFreeTensor
public import StacksFrontier.RingTheory.Flat.TensorProductFiniteness
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatTensorProduct
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Ideal.RelativeAssassin
public import StacksFrontier.RingTheory.Noetherian.ArtinRees

/-!
# Universal injectivity of the map into an adic completion

Let `R → S` be a map of Noetherian rings, let `I ⊆ R` be an ideal and let `N` be a finite
`S`-module. This file proves Stacks 05DL: if for every finite `R`-module `Q` and every associated
prime `q` of `N ⊗[R] Q` the ideal `IS + q` is proper, then `N → N^∧` is universally injective as
a map of `R`-modules.

The argument is the source's. By a colimit argument it suffices to test injectivity of
`N ⊗ Q → N^∧ ⊗ Q` on finite `R`-modules `Q`; the comparison map
`N^∧ ⊗ Q → (N ⊗ Q)^∧` then reduces that to injectivity of `N' → (N')^∧` for the single module
`N' = N ⊗[R] Q`, which is again finite over `S`. For such an `N'` the kernel of `N' → (N')^∧` is
`⋂_n IⁿN' = ⋂_n (IS)ⁿN'`, and `N'` embeds into the product of its localizations at its associated
primes (Stacks 0311), so it suffices to kill that intersection at each associated prime `q`. The
hypothesis gives a maximal ideal above `IS + q`, and Stacks 00IQ supplies an element outside it
which annihilates `⋂_n (IS)ⁿN'` after localization; being outside a prime above `q` it is outside
`q`, which is exactly what is needed.

Stacks 05DM is the flat case, in which the hypothesis need only be checked on the associated
primes of the *fibres* `N ⊗[R] κ(𝔭)`: by Stacks 05C2 and Stacks 05GB the associated primes of
`N ⊗[R] Q`, for `Q` any finite `R`-module, are already associated primes of a fibre.

## Main results

* `AdicCompletion.universallyInjective_of_associatedPrimes`: Stacks 05DL.
* `AdicCompletion.universallyInjective_of_flat_of_fibre_associatedPrimes`: Stacks 05DM.

## Implementation notes

The extended ideal `IS` of the source is `I.map (algebraMap R S)` and `IS + q` is the supremum of
ideals. Associatedness in the hypothesis is `IsAssociatedPrimeStacks`, the source's definition;
the proof converts it to Mathlib's `associatedPrimes` where the library API is stated that way.
The tensor product is written `N ⊗[R] Q`, with `N` on the left, so that it carries its standard
`S`-module structure.

The reduction to finite `Q` is `injective_rTensor_of_finite_test` and is carried out by hand
rather than by citing Stacks 058K: that lemma is stated for a ring and modules in a single
universe, whereas the statement here lets the module universe be independent of the universe of
`R`.

## References

* [Stacks Project, Tag 05DL](https://stacks.math.columbia.edu/tag/05DL)
* [Stacks Project, Tag 05DM](https://stacks.math.columbia.edu/tag/05DM)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace AdicCompletion

/-- The source's `IsAssociatedPrimeStacks` agrees with Mathlib's `associatedPrimes`. -/
private theorem isAssociatedPrimeStacks_iff_mem_associatedPrimes {S M : Type*} [CommRing S]
    [IsNoetherianRing S] [AddCommGroup M] [Module S M] {q : Ideal S} :
    IsAssociatedPrimeStacks S M q ↔ q ∈ associatedPrimes S M := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  refine and_congr_right fun _ => exists_congr fun m => ?_
  rw [eq_comm, Submodule.colon_span]

/-- The special case of Stacks 05DL in which the test module is trivial: for a finite module `M`
over a Noetherian `R`-algebra `S`, if `IS + q` is proper for every associated prime `q` of `M`,
then `M → M^∧` is injective. -/
private theorem injective_of_associatedPrimes {R : Type u} [CommRing R] (I : Ideal R)
    {S : Type v} [CommRing S] [Algebra R S] {M : Type w} [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [IsNoetherianRing S] [Module.Finite S M]
    (h : ∀ q : Ideal S, IsAssociatedPrimeStacks S M q → I.map (algebraMap R S) ⊔ q ≠ ⊤) :
    Function.Injective (AdicCompletion.of I M) := by
  classical
  set J : Ideal S := I.map (algebraMap R S) with hJ
  intro x y hxy
  have hker : x - y ∈ LinearMap.ker (AdicCompletion.of I M) := by
    rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
  -- The kernel of `M → M^∧` is `⋂_n IⁿM`, which as a set is `⋂_n (IS)ⁿM`.
  have hxJ : x - y ∈ krullIntersection M J := by
    rw [krullIntersection, Submodule.mem_iInf]
    intro n
    have hv := congrArg (fun z : AdicCompletion I M => z.val n) (LinearMap.mem_ker.mp hker)
    simp only [AdicCompletion.of_apply] at hv
    have hn : x - y ∈ I ^ n • (⊤ : Submodule R M) := (Submodule.Quotient.mk_eq_zero _).mp hv
    have hrestrict : I ^ n • (⊤ : Submodule R M) =
        (J ^ n • (⊤ : Submodule S M)).restrictScalars R := by
      simpa [hJ, ← Ideal.map_pow] using
        (Ideal.smul_restrictScalars (I := I ^ n) (N := (⊤ : Submodule S M))).symm
    rwa [hrestrict] at hn
  -- It dies in every localization at an associated prime.
  have hlocal : ∀ p : associatedPrimes S M,
      LocalizedModule.mkLinearMap p.1.primeCompl M (x - y) = 0 := by
    intro p
    have hp : IsAssociatedPrimeStacks S M p.1 :=
      isAssociatedPrimeStacks_iff_mem_associatedPrimes.mpr p.2
    obtain ⟨q, hqmax, hpq⟩ := Ideal.exists_le_maximal (J ⊔ p.1) (h p.1 hp)
    have : q.IsPrime := hqmax.isPrime
    obtain ⟨f, hfq, hloc⟩ :=
      exists_notMem_localized_krullIntersection_eq_bot (M := M) J q (le_sup_left.trans hpq)
    have hmem : LocalizedModule.mkLinearMap (Submonoid.powers f) M (x - y) ∈
        (krullIntersection M J).localized (Submonoid.powers f) := by
      show LocalizedModule.mkLinearMap (Submonoid.powers f) M (x - y) ∈
        Submodule.localized' (Localization (Submonoid.powers f)) (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M) (krullIntersection M J)
      rw [Submodule.mem_localized']
      exact ⟨x - y, hxJ, 1, by simp⟩
    have hmem' : LocalizedModule.mkLinearMap (Submonoid.powers f) M (x - y) ∈
        (⊥ : Submodule (Localization (Submonoid.powers f))
          (LocalizedModule (Submonoid.powers f) M)) := by
      simpa [hloc] using hmem
    obtain ⟨r, hrpow, hr⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp
      (LinearMap.mem_ker.mpr ((Submodule.mem_bot _).mp hmem'))
    refine (LinearMap.mem_ker (f := LocalizedModule.mkLinearMap p.1.primeCompl M)).mp
      (LocalizedModule.mem_ker_mkLinearMap_iff.mpr ⟨r, fun hrp => ?_, hr⟩)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff r f).mp hrpow
    exact hfq (le_sup_right.trans hpq (hp.1.mem_of_pow_mem n (hn ▸ hrp)))
  have hass : assMap S M (x - y) = 0 := by
    ext p
    simpa [assMap] using hlocal p
  exact sub_eq_zero.mp (zero_at_ass_zero S M (by simpa using hass))

/-- Enlarging a submodule of the right-hand tensor factor keeps an element in the range. -/
private theorem range_lTensor_subtype_mono {R : Type u} [CommRing R] {N Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] {K₁ K₂ : Submodule R Q}
    (hK : K₁ ≤ K₂) {x : N ⊗[R] Q} (hx : x ∈ LinearMap.range (K₁.subtype.lTensor N)) :
    x ∈ LinearMap.range (K₂.subtype.lTensor N) := by
  rw [← Submodule.subtype_comp_inclusion _ _ hK, LinearMap.lTensor_comp] at hx
  exact LinearMap.range_comp_le_range _ _ hx

/-- An element of `N ⊗ K` already comes from `N ⊗ K'` for a finitely generated `K' ≤ K`: only the
finitely many elements of `K` appearing in a representation as a sum of tensors are needed. -/
private theorem exists_fg_le_of_mem_range_lTensor {R : Type u} [CommRing R] {N Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] (K : Submodule R Q)
    {x : N ⊗[R] Q} (hx : x ∈ LinearMap.range (K.subtype.lTensor N)) :
    ∃ K' : Submodule R Q, K' ≤ K ∧ K'.FG ∧
      x ∈ LinearMap.range (K'.subtype.lTensor N) := by
  obtain ⟨x, rfl⟩ := hx
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, bot_le, Submodule.fg_bot, by simp⟩
  | tmul m k =>
      refine ⟨Submodule.span R {(k : Q)}, ?_, Submodule.fg_span_singleton _, ?_⟩
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr k.2)
      · exact ⟨m ⊗ₜ ⟨k, Submodule.mem_span_singleton_self _⟩, by simp⟩
  | add x y hx hy =>
      obtain ⟨K₁, hK₁, hfg₁, h₁⟩ := hx
      obtain ⟨K₂, hK₂, hfg₂, h₂⟩ := hy
      refine ⟨K₁ ⊔ K₂, sup_le hK₁ hK₂, hfg₁.sup hfg₂, ?_⟩
      rw [map_add]
      exact add_mem (range_lTensor_subtype_mono le_sup_left h₁)
        (range_lTensor_subtype_mono le_sup_right h₂)

/-- `TensorProduct.comm` intertwines `lTensor` and `rTensor`. -/
private theorem comm_lTensor {R : Type u} [CommRing R] {N P Q : Type*} [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q)
    (x : N ⊗[R] P) :
    TensorProduct.comm R N Q (g.lTensor N x) = g.rTensor N (TensorProduct.comm R N P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n p => simp
  | add x y hx hy => simp [hx, hy]

/-- `lTensor` and `rTensor` in the two factors of a tensor product commute. -/
private theorem lTensor_rTensor_comm {R : Type u} [CommRing R] {M N P Q : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (x : M ⊗[R] P) :
    g.lTensor N (f.rTensor P x) = f.rTensor Q (g.lTensor M x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

/-- The `lTensor` form of `Submodule.FG.exists_rTensor_fg_inclusion_eq`: two elements of `N ⊗ Q₀`,
for `Q₀` finitely generated, with the same image in `N ⊗ Q` already agree in `N ⊗ Q₁` for some
finitely generated `Q₁` above `Q₀`. -/
private theorem exists_fg_lTensor_inclusion_eq {R : Type u} [CommRing R] {N Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] {Q₀ : Submodule R Q}
    (h₀ : Q₀.FG) {x y : N ⊗[R] Q₀} (hxy : Q₀.subtype.lTensor N x = Q₀.subtype.lTensor N y) :
    ∃ Q₁ : Submodule R Q, Q₁.FG ∧ ∃ h : Q₀ ≤ Q₁,
      (Submodule.inclusion h).lTensor N x = (Submodule.inclusion h).lTensor N y := by
  obtain ⟨Q₁, hfg, hle, heq⟩ := h₀.exists_rTensor_fg_inclusion_eq (M := N)
    (x := TensorProduct.comm R N Q₀ x) (y := TensorProduct.comm R N Q₀ y)
    (by rw [← comm_lTensor, ← comm_lTensor, hxy])
  refine ⟨Q₁, hfg, hle, (TensorProduct.comm R N Q₁).injective ?_⟩
  rw [comm_lTensor, comm_lTensor, heq]

/-- Injectivity of `f ⊗ id_Q` for all *finite* `Q` already gives it for all `Q`: both an element
of the kernel and the vanishing of its image are witnessed on a finitely generated submodule
of `Q`. -/
private theorem injective_rTensor_of_finite_test {R : Type u} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hfinite : ∀ (Q : Type w) [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
      Function.Injective (f.rTensor Q))
    (Q : Type w) [AddCommGroup Q] [Module R Q] : Function.Injective (f.rTensor Q) := by
  classical
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun z hz => ?_)
  have htop : Function.Surjective ((⊤ : Submodule R Q).subtype) := fun q => ⟨⟨q, trivial⟩, rfl⟩
  obtain ⟨Q₀, -, hQ₀fg, z₀, hz₀⟩ :=
    exists_fg_le_of_mem_range_lTensor (N := M) (Q := Q) (⊤ : Submodule R Q) (x := z)
      (LinearMap.mem_range.mpr (LinearMap.lTensor_surjective M htop z))
  have : Module.Finite R Q₀ := Module.Finite.iff_fg.mpr hQ₀fg
  obtain ⟨Q₁, hQ₁fg, hle, heq⟩ := exists_fg_lTensor_inclusion_eq (N := N) hQ₀fg
    (x := f.rTensor Q₀ z₀) (y := 0) (by rw [_root_.map_zero, lTensor_rTensor_comm, hz₀, hz])
  have : Module.Finite R Q₁ := Module.Finite.iff_fg.mpr hQ₁fg
  have h₁ : (Submodule.inclusion hle).lTensor M z₀ = 0 := by
    refine hfinite Q₁ ?_
    rw [← lTensor_rTensor_comm f (Submodule.inclusion hle), heq]
    simp
  rw [← hz₀, ← Submodule.subtype_comp_inclusion _ _ hle, LinearMap.lTensor_comp,
    LinearMap.comp_apply, h₁, _root_.map_zero]

/-- **Stacks Project, Tag 05DL.** Let `R → S` be a map of Noetherian rings, let `I ⊆ R` be an
ideal and let `N` be a finite `S`-module. If for every finite `R`-module `Q` and every associated
prime `q` of `N ⊗[R] Q` the ideal `IS + q` is proper, then the canonical map from `N` to its
`I`-adic completion is universally injective as a map of `R`-modules. -/
@[stacks 05DL "`IS` is `I.map (algebraMap R S)` and `IS + 𝔮` is a supremum of ideals; associatedness
is `IsAssociatedPrimeStacks`, the source's definition; the tensor product is written `N ⊗[R] Q`,
with `N` on the left, so that it carries its standard `S`-module structure. The source's
hypothesis that `R` be Noetherian is dropped: the argument runs entirely over `S`, using Tag 00IQ
and Tag 0311 there, so this is strictly more general than the source's statement."]
theorem universallyInjective_of_associatedPrimes {R : Type u} [CommRing R] (I : Ideal R)
    {S : Type v} [CommRing S] [Algebra R S] {N : Type w} [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] [IsNoetherianRing S] [Module.Finite S N]
    (h : ∀ (Q : Type w) [AddCommGroup Q] [Module R Q] [Module.Finite R Q] (q : Ideal S),
      IsAssociatedPrimeStacks S (N ⊗[R] Q) q → I.map (algebraMap R S) ⊔ q ≠ ⊤) :
    UniversallyInjective (AdicCompletion.of I N) := by
  classical
  have hfinite : ∀ (Q : Type w) [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
      Function.Injective ((AdicCompletion.of I N).rTensor Q) := by
    intro Q _ _ _
    have : Module.Finite S (N ⊗[R] Q) := Module.Finite.tensorProduct_right R S N Q
    have hOf : Function.Injective (AdicCompletion.of I (N ⊗[R] Q)) :=
      injective_of_associatedPrimes I fun q hq => h Q q hq
    have hcomp : adicCompletionTensorMap I N Q ∘ₗ (AdicCompletion.of I N).rTensor Q =
        AdicCompletion.of I (N ⊗[R] Q) := by
      refine LinearMap.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul n q => simp [adicCompletionTensorMap_tmul, AdicCompletion.map_of]
      | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂]
    exact fun x y hxy => (hcomp ▸ hOf) (congrArg (adicCompletionTensorMap I N Q) hxy)
  exact fun Q _ _ => injective_rTensor_of_finite_test (AdicCompletion.of I N) hfinite Q

/-- The contraction of a prime of an algebra over a residue field `κ(𝔭)` is `𝔭`. -/
private theorem comap_comp_algebraMap_residueField {R A : Type*} [CommRing R] [CommRing A]
    (p : Ideal R) [p.IsPrime] (f : p.ResidueField →+* A) (Q : Ideal A) [Q.IsPrime] :
    Q.comap (f.comp (algebraMap R p.ResidueField)) = p := by
  rw [← Ideal.comap_comap,
    (Ideal.eq_bot_or_top _).resolve_right (Ideal.comap_isPrime f Q).ne_top,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

/-- For `N` flat over `R`, the hypothesis of Stacks 05DL on all finite test modules follows from
its special case on the fibres `N ⊗[R] κ(𝔭)`: every associated prime of `N ⊗[R] Q` is an
associated prime of such a fibre, by Stacks 05C2 and Stacks 05GB. -/
private theorem proper_of_fibre_associatedPrimes {R S N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R N] (I : Ideal R)
    (h : ∀ q : PrimeSpectrum S, q.asIdeal ∈ associatedPrimes S
        (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) →
      I.map (algebraMap R S) ⊔ q.asIdeal ≠ ⊤) :
    ∀ (Q : Type*) [AddCommGroup Q] [Module R Q] (q : Ideal S),
      IsAssociatedPrimeStacks S (N ⊗[R] Q) q → I.map (algebraMap R S) ⊔ q ≠ ⊤ := by
  intro Q _ _ q hq
  have hqa : q ∈ associatedPrimes S (N ⊗[R] Q) :=
    isAssociatedPrimeStacks_iff_mem_associatedPrimes.mp hq
  let qs : PrimeSpectrum S := ⟨q, (AssociatedPrimes.mem_iff.mp hqa).1⟩
  have hq' : qs ∈ (⋃ p ∈ {p : PrimeSpectrum R | p.asIdeal ∈ associatedPrimes R Q},
      PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
        {Q' | Q'.asIdeal ∈ associatedPrimes (S ⊗[R] p.asIdeal.ResidueField)
          ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N)}) := by
    rw [← (associatedPrimes.tensorProduct_of_flat_fiberRing
      (R := R) (S := S) (M := Q) (N := N)).2 inferInstance]
    exact hqa
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hq'
  obtain ⟨p, -, Qp, hQp, hqs⟩ := hq'
  have hcontract : PrimeSpectrum.comap (algebraMap R S) qs = p := PrimeSpectrum.ext <| by
    rw [← hqs]
    exact Stacks.AssociatedPrimes.FibreRings.comap_comap_algebraMap_fibre p.asIdeal Qp.asIdeal
  have hfibre : qs.asIdeal ∈ associatedPrimes S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) qs).asIdeal.ResidueField) := by
    subst hcontract
    show qs ∈ {q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimes S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)}
    rw [(Module.relativeAssassin_comparison R S N rfl rfl rfl rfl rfl rfl).1]
    exact ⟨Qp, hQp, hqs⟩
  simpa [qs] using h qs hfibre

/-- **Stacks Project, Tag 05DM.** Let `R → S` be a map of Noetherian rings, let `I ⊆ R` be an
ideal and let `N` be a finite `S`-module which is flat over `R`. If for every prime `𝔮` of `S`
which is an associated prime of the fibre `N ⊗[R] κ(𝔭)`, where `𝔭 = R ∩ 𝔮`, the ideal `IS + 𝔮` is
proper, then the canonical map from `N` to its `I`-adic completion is universally injective as a
map of `R`-modules. -/
@[stacks 05DM "`IS` is `I.map (algebraMap R S)` and `IS + 𝔮` is a supremum of ideals; the
contraction `𝔭 = R ∩ 𝔮` is `PrimeSpectrum.comap (algebraMap R S) 𝔮`, and `κ(𝔭)` is its
`ResidueField`; the tensor product is written `N ⊗[R] κ(𝔭)`, with `N` on the left, so that it
carries its standard `S`-module structure."]
theorem universallyInjective_of_flat_of_fibre_associatedPrimes {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (N : Type w) [AddCommGroup N]
    [Module S N] [Module R N] [IsScalarTower R S N] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite S N] [Module.Flat R N]
    (h : ∀ q : PrimeSpectrum S, q.asIdeal ∈ associatedPrimes S
        (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) →
      I.map (algebraMap R S) ⊔ q.asIdeal ≠ ⊤) :
    UniversallyInjective (AdicCompletion.of I N) :=
  universallyInjective_of_associatedPrimes I
    fun Q _ _ _ => proper_of_fibre_associatedPrimes I h Q

end AdicCompletion

end
