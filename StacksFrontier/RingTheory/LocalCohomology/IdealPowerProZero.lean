module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.StableImage

/-!
# Pro-zero local cohomology of the ideal-power filtration

Let `A` be a commutative ring, `I ⊆ A` an ideal, `M` an `A`-module and `T ⊆ Spec(A)` a subset.
The submodules `IⁿM` form an inverse system `{IⁿM}` of `A`-modules, and each of them sits in a
short exact sequence

`0 → IⁿM → M → M/IⁿM → 0`

whose third term is the `n`-th term of the tower `{M/IⁿM}` of
`StacksFrontier/RingTheory/LocalCohomology/EssentiallyConstantConsequences.lean`.

[Stacks, Tag 0EFX] asserts, in the bootstrap situation of [Stacks, Tag 0EFU], that the inverse
systems `{H^i_T(IⁿM)}` are pro-zero for `i ≤ s`, and that the images of the transition maps in
degree `s + 1` inject into one fixed term. [Stacks, Tag 0EFY] draws seven consequences; its
first, the injectivity of `H^i_T(M) → H^i_T(M/IⁿM)` for `i ≤ s` and `n ≫ 0`, is the one the
proof of [Stacks, Tag 0EIE] uses to upgrade "Mittag-Leffler plus limit" to essential constancy.

What is proved here is the passage from local to global and the first consequence:

* the two globalization steps of Tag 0EFX, which are the final paragraph of its proof: from the
  per-prime hypothesis — uniform in `𝔭 ∈ T` — that the transition maps of
  `{H^i_{𝔭A_𝔭}((IⁿM)_𝔭)}` eventually vanish, respectively have stable image injecting into the
  zeroth term, Lemmas [Stacks, Tag 0EF9] and [Stacks, Tag 0EFA] give the two global assertions
  about `H^i_T` and `H^{i+1}_T`;
* the passage to part (1) of Tag 0EFY from the pro-zero assertion of Tag 0EFX.

The per-prime hypothesis is where the local duality theorem enters in the source; it is proved
in `StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapUniformProZero.lean` and
`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapUniformStableImage.lean`, where the tag
itself is proved; see the implementation notes.

## Main definitions

* `Stacks.LocalCohomology.idealPowerTower` — the inverse system `{IⁿM}`.
* `Stacks.LocalCohomology.idealPowerShortComplex` — the short exact sequence
  `0 → IⁿM → M → M/IⁿM → 0`.

## Main results

* `Stacks.LocalCohomology.idealPowerShortComplex_shortExact` — that sequence is short exact.
* `Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_local` — the pro-zero half of
  Tag 0EFX, globalized from the per-prime hypothesis.
* `Stacks.LocalCohomology.exists_eventually_injective_image_idealPowerTower_of_local` — the
  stable-image half of Tag 0EFX, globalized from the per-prime hypothesis.
* `Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_neg` — the pro-zero half in
  negative degrees, with no hypothesis at all.
* `Stacks.LocalCohomology.exists_forall_injective_localCohomologyAdicProjection_of_proZero` — the
  passage to part (1) of Tag 0EFY: a single `m₀` beyond which `H^i_T(M) → H^i_T(M/IⁿM)` is
  injective for every `i ≤ s` simultaneously, given the pro-zero assertion of Tag 0EFX.

## Implementation notes

The source proves the per-prime hypothesis of Tag 0EFX by local duality: a dualizing complex
`ω_A^•` with dimension function `δ` is chosen, the Ext modules `Ext^j_A(IⁿM, ω_A^•)` are finite,
and local duality identifies the completion of `Ext^{-d-i}_A(IⁿM, ω_A^•)_𝔭` with the Matlis dual
of `H^i_𝔭((IⁿM)_𝔭)`; finiteness spreads the vanishing from `𝔭` to a neighbourhood, and the
quasi-compactness of `T_d = {𝔭 ∈ T : δ(𝔭) = d}` makes the bound uniform. That argument needs
the dualizing complex of Situation [Stacks, Tag 0EFU], which this module does not see, so the
per-prime assertion is a hypothesis of both globalization theorems below; their hypotheses are
exactly what Tags 0EF9 and 0EFA consume. The per-prime assertion is proved, uniformly in `𝔭`, by
`Stacks.Algebraization.exists_forall_localized_localCohomology_map_eq_zero` and
`Stacks.Algebraization.exists_forall_localized_ker_le_ker_idealPowerTower`.

Finite Krull dimension is an explicit hypothesis rather than a consequence of the bootstrap
situation's assumption (1). The library's form of [Stacks, Tag 0A80],
`Dualizing.ringKrullDim_lt_top_of_isDualizingComplex`, asks for a dualizing complex in
`DerivedCategory (ModuleCat.{u} A)` for `A : Type u`, whereas
`Stacks.Algebraization.BootstrapSituation.dualizing` provides one in `ModuleCat.{max u w}`; the
two are not the same universe, so the implication is not available at the generality the
situation is stated in.

Part (1) is stated about the projections of `localCohomologyAdicCone`, the cone whose point is
`H^i_T(M)`, because that is the cone Tag 0EIE's essential-constancy assertion is phrased with.
The single `m₀` valid for all `i ≤ s` at once is obtained as a finite supremum over the degrees
`0 ≤ i ≤ s`; in negative degrees `H^i_T(M)` vanishes, so injectivity is automatic there.

### Where Tag 0EFX is proved

The full statement of Tag 0EFX, both assertions in Situation [Stacks, Tag 0EFU], is
`Stacks.Algebraization.isProZero_and_hasStableImage_idealPowerCohomology`. The two globalization
theorems here, `exists_map_idealPowerTower_eq_zero_of_local` and
`exists_eventually_injective_image_idealPowerTower_of_local`, are steps of its proof (Lemmas
[Stacks, Tag 0EF9] and [Stacks, Tag 0EFA] at the tower `{IⁿM}`) and carry no tag. The statement
in negative degrees, which needs no hypothesis, is `exists_map_idealPowerTower_eq_zero_of_neg`.

### Where Tag 0EFY is proved

All seven parts of Tag 0EFY in Situation [Stacks, Tag 0EFU], at one and the same `m₀`, are
`Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`; its part (1) is
`exists_forall_injective_localCohomologyAdicProjection_of_proZero` below with the hypothesis
discharged.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EF9](https://stacks.math.columbia.edu/tag/0EF9)
* [Stacks Project, Tag 0EFA](https://stacks.math.columbia.edu/tag/0EFA)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### The inverse system `{IⁿM}` and the short exact sequences `0 → IⁿM → M → M/IⁿM → 0` -/

/-- The inverse system `{IⁿM}` of ideal-power submodules of `M`, with the transition maps given
by the inclusions `IⁿM ⊆ IᵐM` for `m ≤ n`. -/
def idealPowerTower (I : Ideal A) (M : ModuleCat.{max u v} A) : ℕᵒᵖ ⥤ ModuleCat.{max u v} A where
  obj n := ModuleCat.of A ↥(I ^ n.unop • (⊤ : Submodule A M))
  map f := ModuleCat.ofHom (Submodule.inclusion (Submodule.pow_smul_top_le I M (leOfHom f.unop)))
  map_id _ := by apply ModuleCat.hom_ext; ext; rfl
  map_comp _ _ := by apply ModuleCat.hom_ext; ext; rfl

/-- The inclusion `IⁿM ⊆ M`, out of the `n`-th term of `idealPowerTower`. The declared type is
what keeps the source of this map spelled as a term of the tower; see the implementation
notes. -/
def idealPowerInclusion (I : Ideal A) (M : ModuleCat.{max u v} A) (n : ℕ) :
    (idealPowerTower.{u, v} I M).obj (op n) ⟶ M :=
  ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype

/-- The quotient map `M → M/IⁿM`, into the `n`-th term of `idealPowerQuotientTower`. -/
def idealPowerProjection (I : Ideal A) (M : ModuleCat.{max u v} A) (n : ℕ) :
    M ⟶ (idealPowerQuotientTower.{u, v} I M).obj (op n) :=
  ModuleCat.ofHom (Submodule.mkQ (I ^ n • (⊤ : Submodule A M)))

/-- The quotient map `M → M/IⁿM` is the `n`-th projection of the cone of `idealPowerQuotientTower`
with point `M`. -/
theorem idealPowerQuotientCone_π_app (I : Ideal A) (M : ModuleCat.{max u v} A) (n : ℕ) :
    (idealPowerQuotientCone.{u, v} I M).π.app (op n) = idealPowerProjection.{u, v} I M n := rfl

/-- The short exact sequence `0 → IⁿM → M → M/IⁿM → 0`. Its first term is the `n`-th term of
`idealPowerTower` and its third term is the `n`-th term of `idealPowerQuotientTower`. -/
def idealPowerShortComplex (I : Ideal A) (M : ModuleCat.{max u v} A) (n : ℕ) :
    ShortComplex (ModuleCat.{max u v} A) :=
  ShortComplex.mk (idealPowerInclusion.{u, v} I M n) (idealPowerProjection.{u, v} I M n)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero _).2 x.2)

/-- The sequence `0 → IⁿM → M → M/IⁿM → 0` is short exact. -/
theorem idealPowerShortComplex_shortExact (I : Ideal A) (M : ModuleCat.{max u v} A) (n : ℕ) :
    (idealPowerShortComplex.{u, v} I M n).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact ((Submodule.range_subtype (I ^ n • (⊤ : Submodule A M))).trans
      (Submodule.ker_mkQ (I ^ n • (⊤ : Submodule A M))).symm)
  mono_f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).2
    (Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule A M)))

/-- Composing two transition maps of `{IⁿM}` gives the transition map of the composite bound. -/
private theorem idealPowerTower_map_comp_map (I : Ideal A) (M : ModuleCat.{max u v} A)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (idealPowerTower.{u, v} I M).map (homOfLE hjk).op ≫
        (idealPowerTower.{u, v} I M).map (homOfLE hij).op =
      (idealPowerTower.{u, v} I M).map (homOfLE (hij.trans hjk)).op := by
  rw [← Functor.map_comp]; congr 1

/-- The inclusion `IᵏM ⊆ M` factors through `IᵐM` for `m ≤ k`. -/
private theorem idealPowerTower_map_comp_inclusion (I : Ideal A) (M : ModuleCat.{max u v} A)
    {m k : ℕ} (h : m ≤ k) :
    (idealPowerTower.{u, v} I M).map (homOfLE h).op ≫ idealPowerInclusion.{u, v} I M m =
      idealPowerInclusion.{u, v} I M k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-! ### Tag 0EFX: from the per-prime assertions to the assertions about `H^i_T` -/

/-- **The pro-zero globalization step in the proof of [Stacks, Tag 0EFX].** If for every `m` the
transition maps `H^i_{𝔭A_𝔭}((IᵏM)_𝔭) → H^i_{𝔭A_𝔭}((IᵐM)_𝔭)` vanish for every `𝔭 ∈ T` and every
`k ≥ m'(m)`, then the inverse system `{H^i_T(IⁿM)}` is pro-zero: for every `m` some transition
map into the `m`-th term is zero.

This is the last paragraph of the source's proof, which reduces the lemma to the per-prime
assertion: the reduction is Lemma [Stacks, Tag 0EF9], applied to the tower `{IⁿM}`. The per-prime
assertion itself, which the source proves by local duality, is the hypothesis `hlocal`; in
Situation [Stacks, Tag 0EFU] it is
`Stacks.Algebraization.exists_forall_localized_localCohomology_map_eq_zero`, and the tag is
`Stacks.Algebraization.isProZero_and_hasStableImage_idealPowerCohomology`. -/
theorem exists_map_idealPowerTower_eq_zero_of_local [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℕ) (m' : ℕ → ℕ) (hm' : ∀ m, m ≤ m' m)
    (hlocal : ∀ (m k : ℕ) (_hbound : m' m ≤ k), ∀ p : PrimeSpectrum A, p ∈ T →
      ((ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
        ((idealPowerTower.{u, v} I M).map (homOfLE ((hm' m).trans _hbound)).op) = 0))
    (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
        ((idealPowerTower.{u, v} I M).map (homOfLE h).op) = 0 :=
  ⟨m'^[2 ^ ((topologicalKrullDim (↥T)).unbotD 0).toNat] m,
    Function.id_le_iterate_of_id_le hm' _ m,
    localCohomologyWithSupportIn_map_eq_zero_of_local.{u, v} A hdim T hT
      (idealPowerTower.{u, v} I M) i m' hm' hlocal m _ le_rfl⟩

/-- **The stable-image globalization step in the proof of [Stacks, Tag 0EFX].** If for every
`m` there is a `c ≥ m` such that at every `𝔭 ∈ T` and for every `k ≥ c` the transition map of
`{H^{i-1}_{𝔭A_𝔭}((IⁿM)_𝔭)}` vanishes, the transition image of `{H^i_{𝔭A_𝔭}((IⁿM)_𝔭)}` is
independent of `k` and that image injects into the zeroth term, then there is an `m₀` such that
for every `m ≥ m₀` the image of `H^i_T(IᵏM) → H^i_T(IᵐM)` injects into `H^i_T(I^{m₀}M)` for all
large `k`.

This is the reduction Lemma [Stacks, Tag 0EFA], applied to the tower `{IⁿM}`; in the source it is
applied in degree `i = s + 1`. The per-prime hypothesis `hloc` is the local-duality half of the
source's proof; the tag itself is
`Stacks.Algebraization.isProZero_and_hasStableImage_idealPowerCohomology`, which uses the variant
`exists_eventually_injective_image_idealPowerTower_of_local_image_injective` of this step. -/
theorem exists_eventually_injective_image_idealPowerTower_of_local [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℕ)
    (hloc : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ p ∈ T, ∀ (k : ℕ) (hck : c ≤ k),
      ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
        p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
          (Localization p.asIdeal.primeCompl) ((i : ℤ) - 1)).map
            (homOfLE (hmc.trans hck)).op = 0) ∧
      (LinearMap.range ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map (homOfLE (hmc.trans hck)).op).hom =
        LinearMap.range ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map (homOfLE hmc).op).hom) ∧
      (∀ x : (idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).obj (op k),
        ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map
              (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
            p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
              (Localization p.asIdeal.primeCompl) (i : ℤ)).map
                (homOfLE (Nat.zero_le m)).op).hom →
        ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map
              (homOfLE (hmc.trans hck)).op).hom x = 0)) :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).obj (op k),
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, v} I M ⋙
            localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0 :=
  eventually_injective_image_localCohomologyWithSupportIn.{u, v} A hdim T hT
    (idealPowerTower.{u, v} I M) i hloc

/-- **Stacks Project, Tag 0EFX** in negative degrees, with no hypothesis. For `i < 0` every term
of `{H^i_T(IⁿM)}` vanishes, so every transition map is zero and the system is pro-zero. -/
@[stacks 0EFX "the pro-zero assertion in negative degrees, unconditionally"]
theorem exists_map_idealPowerTower_eq_zero_of_neg (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ) (hi : i < 0) (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        ((idealPowerTower.{u, v} I M).map (homOfLE h).op) = 0 :=
  ⟨m, le_rfl, (isZero_localCohomologyWithSupportIn_single_of_neg.{u, v} A T
    ((idealPowerTower.{u, v} I M).obj (op m)) i hi).eq_of_tgt _ _⟩

/-! ### Tag 0EFY, part (1) -/

/-- The map `H^i_T(IᵏM) → H^i_T(M)` vanishes as soon as one of the transition maps of `{IⁿM}`
below `k` has vanishing local cohomology: the inclusion `IᵏM ⊆ M` factors through it. -/
private theorem localCohomology_idealPowerInclusion_eq_zero
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ) {m k n : ℕ}
    (h : m ≤ k) (hkn : k ≤ n)
    (hzero : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
      ((idealPowerTower.{u, v} I M).map (homOfLE h).op) = 0) :
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
      (idealPowerInclusion.{u, v} I M n) = 0 := by
  have hfac : idealPowerInclusion.{u, v} I M n =
      (idealPowerTower.{u, v} I M).map (homOfLE hkn).op ≫
        ((idealPowerTower.{u, v} I M).map (homOfLE h).op ≫
          idealPowerInclusion.{u, v} I M m) := by
    rw [← Category.assoc, idealPowerTower_map_comp_map I M h hkn,
      idealPowerTower_map_comp_inclusion I M (h.trans hkn)]
  rw [hfac, Functor.map_comp, Functor.map_comp, hzero, zero_comp, comp_zero]

/-- If `H^i_T(IⁿM) → H^i_T(M)` is zero then `H^i_T(M) → H^i_T(M/IⁿM)` is injective: the long
exact sequence of `0 → IⁿM → M → M/IⁿM → 0` identifies the kernel of the second map with the
image of the first. -/
private theorem injective_localCohomologyAdicProjection_of_inclusion_eq_zero
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ) (n : ℕ)
    (hzero : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
      (idealPowerInclusion.{u, v} I M n) = 0) :
    Function.Injective ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom := by
  have hex : ∀ x, ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom x = 0 →
      ∃ y, ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        (idealPowerInclusion.{u, v} I M n)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp
      (localCohomology_exact₂.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M n) i)
  have hzero' : ∀ z, ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
      (idealPowerInclusion.{u, v} I M n)).hom z = 0 := by
    intro z
    rw [hzero]
    simp
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, hy⟩ := hex x hx
  exact hy.symm.trans (hzero' y)

/-- **The passage to part (1) of [Stacks, Tag 0EFY].** There is an integer `m₀` such that
`H^i_T(M) → H^i_T(M/IⁿM)` is injective for all `i ≤ s` and all `n ≥ m₀`.

*Argument.* Fix `i ≤ s`. By the pro-zero assertion of Tag 0EFX there are `k` and a transition map
`IᵏM → M` of the tower `{IⁿM}` with vanishing `H^i_T`; since `IⁿM ⊆ M` factors through `IᵏM` for
`n ≥ k`, the map `H^i_T(IⁿM) → H^i_T(M)` is then zero for every `n ≥ k`, and the long exact
sequence of `0 → IⁿM → M → M/IⁿM → 0` makes `H^i_T(M) → H^i_T(M/IⁿM)` injective. A single `m₀`
serving every `i ≤ s` is the supremum of the finitely many `k` for `0 ≤ i ≤ s`, together with the
vanishing of `H^i_T` in negative degrees.

Only the pro-zero assertion of Tag 0EFX is used, and it is a hypothesis here, this module making
no use of Situation [Stacks, Tag 0EFU]. In that situation the hypothesis is discharged by
`Stacks.Algebraization.isProZeroIdealPowerCohomology`, which gives
`Stacks.Algebraization.exists_forall_injective_localCohomologyAdicProjection`; the complete
Tag 0EFY is `Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`. -/
theorem exists_forall_injective_localCohomologyAdicProjection_of_proZero
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{max u v} A) (s : ℤ)
    (hpro : ∀ i ≤ s, ∃ k : ℕ, ∃ h : 0 ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        ((idealPowerTower.{u, v} I M).map (homOfLE h).op) = 0) :
    ∃ m₀ : ℕ, ∀ i ≤ s, ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom := by
  classical
  have hdeg : ∀ j : ℕ, ∃ k : ℕ, (j : ℤ) ≤ s → ∀ n : ℕ, k ≤ n →
      Function.Injective
        ((localCohomologyAdicCone.{u, v} A T I (j : ℤ) M).π.app (op n)).hom := by
    intro j
    by_cases hj : (j : ℤ) ≤ s
    · obtain ⟨k, hk, hzero⟩ := hpro (j : ℤ) hj
      exact ⟨k, fun _ n hn =>
        injective_localCohomologyAdicProjection_of_inclusion_eq_zero.{u, v} T I M _ n
          (localCohomology_idealPowerInclusion_eq_zero.{u, v} T I M _ hk hn hzero)⟩
    · exact ⟨0, fun hcon => absurd hcon hj⟩
  choose f hf using hdeg
  refine ⟨(Finset.range (s.toNat + 1)).sup f, ?_⟩
  intro i hi n hn
  by_cases hneg : i < 0
  · have hz := isZero_localCohomologyWithSupportIn_single_of_neg.{u, v} A T M i hneg
    intro x y _
    exact (ModuleCat.isZero_iff_subsingleton.mp hz).elim x y
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) :=
      ⟨i.toNat, (Int.toNat_of_nonneg (not_lt.mp hneg)).symm⟩
    have hjmem : j ∈ Finset.range (s.toNat + 1) := by
      refine Finset.mem_range.2 ?_
      omega
    exact hf j hi n (le_trans (Finset.le_sup hjmem) hn)

end Stacks.LocalCohomology

end
