module

public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapSpreadingOut
public import StacksFrontier.RingTheory.Flat.DevissageElementaryNeighborhood
public import StacksFrontier.RingTheory.Flat.DevissageLocalize
public import StacksFrontier.RingTheory.Flat.EtaleNeighborhoodProjectiveSections

/-!
# Away-localizing a complete dévissage, and projectivity over a general base

Let `N` be a finitely presented module over a finitely presented `R`-algebra `S`, flat over `R`,
and let `q` be a prime of `S`. If `N/S/R` admits a complete dévissage at `q`, then there is an
element `a` of `R` outside `q ∩ R` such that `N_a` is projective over `R_a`. This is the
projectivity conclusion of Stacks 05IB over an arbitrary base, in the form the proof of
Stacks 05ID needs; the library's form (`Module.CompleteDevissage.projective_of_flat`) asks for a
local base, where no element has to be inverted.

Two ingredients are supplied here. The first is the transport of a complete dévissage along the
localization `R → R_a`: `Module.CompleteDevissage.localizeAway` is the companion of
`Module.CompleteDevissage.localize`, which transports only along `R → R_r`. The second is the
stagewise flatness of Stacks 05I4 over a general base: the recursion
`Module.CompleteDevissage.flat_localizedModule_stage` is stated for a local base, and
`Module.CompleteDevissage.flat_localizedModule_stage_of_under` runs the same induction with no
locality hypothesis, the half of Stacks 05I3 it needs being available over any base as
`Module.flat_localizedModule_coker_of_flat_localizedModule`.

With those, Stacks 05IA produces at each stage an element `f i ∉ q ∩ R` after inverting which
`alpha i` becomes injective, and the product `a` of the finitely many `f i` inverts them all at
once. The away-localized dévissage then has injective stage maps, and
`Module.CompleteDevissage.projective_of_injective_alpha` turns that into projectivity of `N_a`
over `R_a`.

## Main definitions

* `Module.CompleteDevissage.localizeAway`: the base change of a complete dévissage over a prime
  `r` along the localization of `R` away from an element outside `r`, with abstract models for
  the localized algebra and the localized module.
* `Module.CompleteDevissage.localizeAwayCanonical`: the same with the canonical models, taking
  the base ring, the algebra and the module in one universe.
* `Module.CompleteDevissage.locAwayA`, `locAwayB`, `locAwayM`, `locAwayToLeft`, `locAwayToRight`,
  `locAwayToA₀`, `locAwayMk`, `locAwayAlpha`, `locAwayCokerMap`, `locAwayCokerEquiv`: the
  localized stage data, each of which is a field of the result.

## Main results

* `Stacks.Flatness.exists_smul_eq_zero_of_injective_localizedModule_map` and
  `Stacks.Flatness.injective_of_isLocalizedModule_of_exists_mul`: injectivity of the localization
  of a linear map at the powers of one element passes to its localization at the powers of a
  multiple of that element, in any realization of the latter localization.
* `AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyIrreducible`: a smooth
  algebra with geometrically irreducible fibres has geometrically integral fibres.
* `Module.flat_localizedModule_coker_finsupp_of_flat_localizedModule`: the flatness half of
  Stacks 05I3 (1) ⟹ (3) over a general base, for a map out of `Fin n →₀ B`.
* `Module.CompleteDevissage.flat_localizedModule_stage_of_under`: the downward recursion of
  Stacks 05I4 over a general base.
* `Module.CompleteDevissage.exists_away_injective_alpha_of_flat_localizedModule`: one element of
  `R` outside `r` whose inversion makes every stage map of the dévissage injective, from a chosen
  family of stage primes at which the stage modules are flat over `R`.
* `Module.NonemptyCompleteDevissageAt.exists_away_injective_alpha`: the same for a dévissage at a
  prime, the stage primes being the ones it records.
* `Module.NonemptyCompleteDevissageAt.exists_away_projective`: **the projectivity conclusion of
  Stacks 05IB over a general base.**

## Implementation notes

### Why the dévissage has to sit at a prime

Over a local base the recursion of Stacks 05IB needs no stage primes at all: flatness of `N` over
`R` propagates to *global* flatness of every stage module
(`Module.CompleteDevissage.flat_stageModule`), because Stacks 05I3 then makes `alpha i`
universally injective over `R` itself. Over a general base that fails — the source's `alpha_r` is
universally injective only after localizing the base at `r` — so the recursion has to carry
flatness of the localizations `(M i)_{q i}` at stage primes `q i`, and then it also needs the
unique prime of `A i` above `q i` in order to compare the three localizations of a stage module.
Both the stage primes and the uniqueness are data of
`Module.NonemptyCompleteDevissageAt` and are not available for a dévissage merely *over* a prime,
which is why the main result here is stated for a dévissage *at* a prime — more than Stacks 05IB
assumes, but exactly what Stacks 05HR and Remark 05I0 produce, hence what the proof of
Stacks 05ID has to work with. Stacks 05IB for a dévissage merely over a prime is
`Module.CompleteDevissage.exists_away_decomposition_projective` in
`StacksFrontier.RingTheory.Flat.DevissageAwayGeneralBase`, which supplies the stagewise flatness
from the local case instead of from this recursion.

### The away-localized dévissage

`Module.CompleteDevissage.localizeAway` is `Module.CompleteDevissage.localize` with the
multiplicative set `Submonoid.powers a` in place of `r.primeCompl`. Every condition is one of the
lemmas of `StacksFrontier.RingTheory.Flat.DevissageBaseChange`, which are stated for an arbitrary
submonoid of the base, so the only new input is that `Submonoid.powers a` misses the fibre prime
`rBᵢ`: that is `Module.CompleteDevissage.disjoint_map_powers`, which shrinks
`Module.CompleteDevissage.disjoint_map` along `Submonoid.powers a ≤ r.primeCompl`. The primality
of `rR_a`, which the result is a dévissage over, cannot be an instance — it depends on `a ∉ r` —
so it is taken as an instance argument and supplied by the caller.

### Comparing the two localizations of `N`

The localized module of `Module.CompleteDevissage.localizeAway` is a localization of `N` at a
submonoid of `S`, namely the image of `Submonoid.powers a`, whereas the statement of
Stacks 05IB speaks of `LocalizedModule (Submonoid.powers a) N`, the localization of `N` as an
`R`-module. The two are identified by `IsLocalizedModule.linearEquiv`, both being localizations of
`N` at `Submonoid.powers a` over `R`, and the identification is upgraded to an `R_a`-linear
equivalence by `LinearEquiv.extendScalarsOfIsLocalization`.

### Transporting injectivity between localizations

Stacks 05IA gives, at each stage, injectivity of the localization of `alpha i` at the powers of
some `f i`, while what the away-localized dévissage records is its localization at the powers of
the product `a`. Those two submonoids are incomparable, so the passage is not monotonicity in the
submonoid; what holds is that every element of `Submonoid.powers (f i)` has a multiple in
`Submonoid.powers a`. `Stacks.Flatness.injective_of_isLocalizedModule_of_exists_mul` is stated
with exactly that hypothesis, and takes the localizations at the second submonoid as abstract
`IsLocalizedModule` data, which is what lets it be applied to
`Module.CompleteDevissage.locAwayAlpha` directly.

## References

* [Stacks Project, Tag 05IB](https://stacks.math.columbia.edu/tag/05IB)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05HY](https://stacks.math.columbia.edu/tag/05HY)
-/

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u v w

/-! ### Injectivity of a localized map, transported between localizations -/

namespace Stacks.Flatness

/-- **The kernel of a map whose localization at a submonoid is injective is killed by that
submonoid.** If the localization of `alpha : X → M` at `T ⊆ R` is injective, then every element
of `X` annihilated by `alpha` is annihilated by some element of `T`. -/
public theorem exists_smul_eq_zero_of_injective_localizedModule_map
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {X M : Type*} [AddCommGroup X] [Module R X] [Module B X] [IsScalarTower R B X]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    (T : Submonoid R) (alpha : X →ₗ[B] M)
    (hinj : Function.Injective (LocalizedModule.map T (alpha.restrictScalars R)))
    (x : X) (hx : alpha x = 0) :
    ∃ t ∈ T, (algebraMap R B t) • x = 0 := by
  have h0 : LocalizedModule.map T (alpha.restrictScalars R)
      (LocalizedModule.mkLinearMap T X x) = 0 := by
    simp [LocalizedModule.mkLinearMap_apply, hx]
  have h1 := hinj (h0.trans (map_zero _).symm)
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T X)).mp h1
  exact ⟨t, t.2, by rw [algebraMap_smul]; exact ht⟩

/-- **Injectivity of a localized map passes to a further localization.** Let `alpha : X → M` be a
map of `B`-modules whose kernel is killed by a submonoid `T` of a base ring `R`, and let
`alpha'` be a localization of `alpha` at a submonoid `T'` of `B`, presented through arbitrary
localization maps `gX` and `gM`. If every element of `T` has a multiple in `T'` — which is what
holds when `T` is the powers of an element and `T'` the powers of a multiple of it — then `alpha'`
is injective.

The hypothesis on the kernel is what
`Stacks.Flatness.exists_smul_eq_zero_of_injective_localizedModule_map` extracts from injectivity
of the localization of `alpha` at `T`. -/
public theorem injective_of_isLocalizedModule_of_exists_mul
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {X M X' M' : Type*} [AddCommGroup X] [Module B X] [AddCommGroup M] [Module B M]
    [AddCommGroup X'] [Module B X'] [AddCommGroup M'] [Module B M']
    {T : Submonoid R} {T' : Submonoid B}
    (hTT' : ∀ t ∈ T, ∃ u : B, algebraMap R B t * u ∈ T')
    (gX : X →ₗ[B] X') [IsLocalizedModule T' gX]
    (gM : M →ₗ[B] M') [IsLocalizedModule T' gM]
    (alpha : X →ₗ[B] M) (alpha' : X' →ₗ[B] M')
    (halpha : ∀ x, alpha' (gX x) = gM (alpha x))
    (hker : ∀ x : X, alpha x = 0 → ∃ t ∈ T, (algebraMap R B t) • x = 0) :
    Function.Injective alpha' := by
  rw [injective_iff_map_eq_zero]
  intro x' hx'
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj T' gX x'
  have hs' : (s : B) • x' = gX x := hs
  have h1 : gM (alpha x) = 0 := by
    rw [← halpha, ← hs', map_smul, hx', smul_zero]
  obtain ⟨s', hs'0⟩ := (IsLocalizedModule.eq_zero_iff T' gM).mp h1
  have h2 : alpha ((s' : B) • x) = 0 := by rw [map_smul]; exact hs'0
  obtain ⟨t, htT, ht⟩ := hker _ h2
  obtain ⟨u, hu⟩ := hTT' t htT
  have h3 : ((algebraMap R B t * u) * (s' : B)) • x = 0 := by
    calc ((algebraMap R B t * u) * (s' : B)) • x
        = u • ((algebraMap R B t) • ((s' : B) • x)) := by
          rw [smul_smul, smul_smul]; ring_nf
      _ = 0 := by rw [ht, smul_zero]
  have hw : ((algebraMap R B t * u) * (s' : B)) * (s : B) ∈ T' :=
    mul_mem (mul_mem hu s'.2) s.2
  have h4 : (⟨_, hw⟩ : T') • x' = (⟨_, hw⟩ : T') • (0 : X') := by
    rw [smul_zero, Submonoid.smul_def]
    calc ((algebraMap R B t * u) * (s' : B) * (s : B)) • x'
        = ((algebraMap R B t * u) * (s' : B)) • ((s : B) • x') := by rw [smul_smul]
      _ = gX (((algebraMap R B t * u) * (s' : B)) • x) := by rw [hs', map_smul]
      _ = 0 := by rw [h3, map_zero]
  exact IsLocalizedModule.smul_injective gX _ h4

end Stacks.Flatness

/-! ### Stagewise flatness over a general base -/

/-- **Stacks Project, Tag 056T for a smooth algebra.** A smooth algebra whose fibres are
geometrically irreducible has geometrically integral fibres: smoothness supplies geometric
reducedness. -/
public theorem AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyIrreducible
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B)))] :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap R B))) :=
  have : AlgebraicGeometry.Smooth (Spec.map (ofHom (algebraMap R B))) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).2
      (RingHom.smooth_algebraMap.2 inferInstance)
  have : GeometricallyReduced (Spec.map (ofHom (algebraMap R B))) :=
    geometricallyReduced_of_smooth _
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- Precomposing a map out of `Fin n →₀ B` with the inverse of `Finsupp.linearEquivFunOnFinite`
preserves bijectivity of its base change to an algebra `k`, in the `rTensor` form. -/
private theorem rTensor_comp_funOnFinite_symm_bijective
    {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] (k : Type*) [CommRing k] [Algebra B k]
    {n : ℕ} (alpha : (Fin n →₀ B) →ₗ[B] M) (h : Function.Bijective (alpha.baseChange k)) :
    Function.Bijective
      ((alpha ∘ₗ (Finsupp.linearEquivFunOnFinite B B (Fin n)).symm.toLinearMap).rTensor k) := by
  set e := Finsupp.linearEquivFunOnFinite B B (Fin n) with he
  rw [← LinearMap.lTensor_bij_iff_rTensor_bij, ← LinearMap.baseChange_eq_lTensor,
    LinearMap.baseChange_comp]
  refine h.comp ?_
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.lTensor_bij_iff_rTensor_bij,
    ← LinearEquiv.coe_rTensor _ e.symm]
  exact (e.symm.rTensor _).bijective

/-- **Stacks Project, Tag 05I3, the flatness half of the implication (1) ⟹ (3), over a general
base**, for a map out of a finite free module presented as `Fin n →₀ B`.

This is `Module.flat_localizedModule_coker_of_flat_localizedModule` with the source of `alpha`
spelled as in a complete dévissage and with its fibre hypothesis stated by
`LinearMap.baseChange`; the fibre prime is a parameter so that the primality instance a dévissage
carries may be used. -/
public theorem Module.flat_localizedModule_coker_finsupp_of_flat_localizedModule
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] [Module.Flat R B]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R B)))]
    (q : Ideal B) [q.IsPrime]
    (M : Type u) [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
    [Module.Finite B M]
    (p : Ideal B) [p.IsPrime] (hp : p = Ideal.map (algebraMap R B) (q.under R))
    (n : ℕ) (alpha : (Fin n →₀ B) →ₗ[B] M)
    (halpha : Function.Bijective (alpha.baseChange p.ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl M)) :
    Module.Flat R (LocalizedModule q.primeCompl (M ⧸ LinearMap.range alpha)) := by
  classical
  subst hp
  set e : (Fin n →₀ B) ≃ₗ[B] (Fin n → B) := Finsupp.linearEquivFunOnFinite B B (Fin n) with he
  have hbase := (rTensor_comp_funOnFinite_symm_bijective _ alpha halpha).1
  have hrange : LinearMap.range (alpha ∘ₗ e.symm.toLinearMap) = LinearMap.range alpha :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.symm.surjective)
  have h := Module.flat_localizedModule_coker_of_flat_localizedModule R B q M n
    (alpha ∘ₗ e.symm.toLinearMap) hbase hflat
  rwa [hrange] at h

namespace Module.CompleteDevissage

section Flatness

variable {R : Type u} {S : Type v} {N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {r : Ideal R} [r.IsPrime]

/-- **The downward recursion of Stacks 05I4 over a general base**: stagewise flatness from
flatness at `q`.

This is `Module.CompleteDevissage.flat_localizedModule_stage` with the locality of the base
dropped. The stage primes `p i` lie over the prime `r` the dévissage sits over rather than over a
maximal ideal, and the half of Stacks 05I3 that drives the induction is
`Module.flat_localizedModule_coker_finsupp_of_flat_localizedModule`, which needs no local base;
projectivity of the lower algebras, a hypothesis of the local statement, is then not needed
either. -/
public theorem flat_localizedModule_stage_of_under [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissage R S N r)
    (q : Ideal S) [q.IsPrime]
    (p : ∀ i, Ideal (D.B i)) (hp : ∀ i, (p i).IsPrime)
    (hp_under : ∀ i, (p i).comap (algebraMap R (D.B i)) = r)
    (P : ∀ i, Ideal (D.A i)) (hP : ∀ i, (P i).IsPrime)
    (hP_under : ∀ i, (P i).comap (D.toLeft i).toRingHom = p i)
    (hP_uniq : ∀ i (P' : Ideal (D.A i)), P'.IsPrime →
      P'.comap (D.toLeft i).toRingHom = p i → P' = P i)
    (h_initial : (P 0).comap D.toA₀.toRingHom = q)
    (h_transition : ∀ j : Fin D.stepCount,
      (P j.succ).comap (D.toRight j).toRingHom = p j.castSucc)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N))
    (i : Fin (D.stepCount + 1)) :
    letI : Module (D.B i) (D.M i) := Module.compHom (D.M i) (D.toLeft i).toRingHom
    letI : Module R (D.M i) := Module.compHom (D.M i) (algebraMap R (D.A i))
    letI : IsScalarTower R (D.B i) (D.M i) :=
      Module.isScalarTower_compHom R (D.B i) (D.A i) (D.M i) (D.toLeft i)
    Module.Flat R (LocalizedModule (p i).primeCompl (D.M i)) := by
  let : ∀ j, Module (D.B j) (D.M j) := fun j =>
    Module.compHom (D.M j) (D.toLeft j).toRingHom
  let : ∀ j, Module R (D.M j) := fun j =>
    Module.compHom (D.M j) (algebraMap R (D.A j))
  let : ∀ j, IsScalarTower R (D.B j) (D.M j) := fun j =>
    Module.isScalarTower_compHom R (D.B j) (D.A j) (D.M j) (D.toLeft j)
  let : ∀ j, IsScalarTower R (D.A j) (D.M j) := fun j =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : ∀ j, Algebra (D.B j) (D.A j) := fun j => (D.toLeft j).toRingHom.toAlgebra
  let : ∀ j, IsScalarTower R (D.B j) (D.A j) := fun j =>
    IsScalarTower.of_algebraMap_eq fun x => ((D.toLeft j).commutes x).symm
  let : ∀ j, IsScalarTower (D.B j) (D.A j) (D.M j) := fun j =>
    ⟨fun b x m => by change (D.toLeft j b * x) • m = D.toLeft j b • (x • m); rw [mul_smul]⟩
  let : ∀ j, Module.Finite (D.B j) (D.A j) := fun j =>
    RingHom.finite_algebraMap.mp (D.left_finite j)
  let : ∀ j, Algebra.IsIntegral (D.B j) (D.A j) := fun j => Algebra.IsIntegral.of_finite _ _
  let : ∀ j, Module.Finite (D.B j) (D.M j) := fun j => Module.Finite.trans (D.A j) (D.M j)
  let : ∀ j, (p j).IsPrime := hp
  let : ∀ j, (P j).IsPrime := hP
  let : ∀ j, GeometricallyIntegral (Spec.map (ofHom (algebraMap R (D.B j)))) := fun j =>
    AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyIrreducible R (D.B j)
  -- Stacks 00EA at each stage: the unique prime of `A j` over `p j` computes the same
  -- localization of `M j`.
  have hUL : ∀ j, Module.Flat R (LocalizedModule (p j).primeCompl (D.M j)) ↔
      Module.Flat R (LocalizedModule (P j).primeCompl (D.M j)) := fun j =>
    Module.flat_localizedModule_atPrime_under_iff_of_unique_prime_over
      (R := R) (A := D.B j) (B := D.A j) (D.M j) (p j) (P j) (hP_under j)
      (fun P' hP' hcomp => hP_uniq j P' hP' hcomp)
  induction i using Fin.induction with
  | zero =>
    let : Module S (D.M 0) := Module.compHom (D.M 0) D.toA₀.toRingHom
    let : IsScalarTower R S (D.M 0) :=
      Module.isScalarTower_compHom R S (D.A 0) (D.M 0) D.toA₀
    let : Algebra S (D.A 0) := D.toA₀.toRingHom.toAlgebra
    let : IsScalarTower R S (D.A 0) :=
      IsScalarTower.of_algebraMap_eq fun x => (D.toA₀.commutes x).symm
    let : IsScalarTower S (D.A 0) (D.M 0) :=
      ⟨fun b x m => by change (D.toA₀ b * x) • m = D.toA₀ b • (x • m); rw [mul_smul]⟩
    let : Module.Finite S (D.A 0) := RingHom.finite_algebraMap.mp
      (RingHom.Finite.of_surjective D.toA₀.toRingHom D.initial_surjective)
    let : Algebra.IsIntegral S (D.A 0) := Algebra.IsIntegral.of_finite _ _
    have h1 : Module.Flat R (LocalizedModule q.primeCompl (D.M 0)) :=
      (Module.flat_localizedModule_congr q.primeCompl D.initialEquiv).mp hflat
    refine (hUL 0).mpr
      (Module.flat_localizedModule_atPrime_under_iff_of_unique_prime_over
        (R := R) (A := S) (B := D.A 0) (D.M 0) q (P 0) h_initial
        (fun P' hP' hcomp =>
          Ideal.comap_injective_of_surjective _ D.initial_surjective
            (hcomp.trans h_initial.symm)) |>.mp h1)
  | succ j ih =>
    have hcoker : Module.Flat R (LocalizedModule (p j.castSucc).primeCompl
        (D.M j.castSucc ⧸ LinearMap.range (D.alpha j.castSucc))) :=
      Module.flat_localizedModule_coker_finsupp_of_flat_localizedModule
        R (D.B j.castSucc) (p j.castSucc) (D.M j.castSucc)
        (Ideal.map (algebraMap R (D.B j.castSucc)) r)
        (by rw [Ideal.under_def, hp_under j.castSucc])
        (D.multiplicity j.castSucc) (D.alpha j.castSucc) (D.fiber_bijective j.castSucc) ih
    let : Module (D.B j.castSucc) (D.M j.succ) :=
      Module.compHom (D.M j.succ) (D.toRight j).toRingHom
    let : IsScalarTower R (D.B j.castSucc) (D.M j.succ) :=
      Module.isScalarTower_compHom R (D.B j.castSucc) (D.A j.succ) (D.M j.succ) (D.toRight j)
    let : Algebra (D.B j.castSucc) (D.A j.succ) := (D.toRight j).toRingHom.toAlgebra
    let : IsScalarTower R (D.B j.castSucc) (D.A j.succ) :=
      IsScalarTower.of_algebraMap_eq fun x => ((D.toRight j).commutes x).symm
    let : IsScalarTower (D.B j.castSucc) (D.A j.succ) (D.M j.succ) :=
      ⟨fun b x m => by change (D.toRight j b * x) • m = D.toRight j b • (x • m); rw [mul_smul]⟩
    let : Module.Finite (D.B j.castSucc) (D.A j.succ) := RingHom.finite_algebraMap.mp
      (RingHom.Finite.of_surjective (D.toRight j).toRingHom (D.transition_surjective j))
    let : Algebra.IsIntegral (D.B j.castSucc) (D.A j.succ) := Algebra.IsIntegral.of_finite _ _
    have h1 : Module.Flat R (LocalizedModule (p j.castSucc).primeCompl (D.M j.succ)) :=
      (Module.flat_localizedModule_congr (p j.castSucc).primeCompl (D.cokerEquiv j)).mp hcoker
    refine (hUL j.succ).mpr
      (Module.flat_localizedModule_atPrime_under_iff_of_unique_prime_over
        (R := R) (A := D.B j.castSucc) (B := D.A j.succ) (D.M j.succ) (p j.castSucc) (P j.succ)
        (h_transition j)
        (fun P' hP' hcomp =>
          Ideal.comap_injective_of_surjective _ (D.transition_surjective j)
            (hcomp.trans (h_transition j).symm)) |>.mp h1)

end Flatness

/-! ### The away-localized stage data -/

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime] (D : CompleteDevissage R S N r) (a : R)

/-- The localization of the upper algebra at stage `i` of a dévissage, away from `a`. -/
public abbrev locAwayA (i : Fin (D.stepCount + 1)) : Type u :=
  Localization (Algebra.algebraMapSubmonoid (D.A i) (Submonoid.powers a))

/-- The localization of the lower algebra at stage `i` of a dévissage, away from `a`. -/
public abbrev locAwayB (i : Fin (D.stepCount + 1)) : Type u :=
  Localization (Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a))

/-- The localization of the module at stage `i` of a dévissage, away from `a`. -/
public abbrev locAwayM (i : Fin (D.stepCount + 1)) : Type max u w :=
  LocalizedModule (Algebra.algebraMapSubmonoid (D.A i) (Submonoid.powers a)) (D.M i)

/-- The localization away from `a` of the map from the lower to the upper algebra at stage `i`. -/
public noncomputable def locAwayToLeft (i : Fin (D.stepCount + 1)) :
    D.locAwayB a i →ₐ[Localization.Away a] D.locAwayA a i :=
  IsLocalization.mapₐ (Submonoid.powers a) (Localization.Away a) (D.locAwayB a i)
    (D.locAwayA a i) (D.toLeft i)

/-- The localization away from `a` of the map from a lower algebra to the next upper algebra. -/
public noncomputable def locAwayToRight (i : Fin D.stepCount) :
    D.locAwayB a i.castSucc →ₐ[Localization.Away a] D.locAwayA a i.succ :=
  IsLocalization.mapₐ (Submonoid.powers a) (Localization.Away a) (D.locAwayB a i.castSucc)
    (D.locAwayA a i.succ) (D.toRight i)

@[simp]
public theorem locAwayToLeft_algebraMap (i : Fin (D.stepCount + 1)) (b : D.B i) :
    D.locAwayToLeft a i (algebraMap (D.B i) (D.locAwayB a i) b)
      = algebraMap (D.A i) (D.locAwayA a i) (D.toLeft i b) :=
  IsLocalization.map_eq (Algebra.algebraMapSubmonoid_le_comap (Submonoid.powers a) (D.toLeft i)) b

@[simp]
public theorem locAwayToRight_algebraMap (i : Fin D.stepCount) (b : D.B i.castSucc) :
    D.locAwayToRight a i (algebraMap (D.B i.castSucc) (D.locAwayB a i.castSucc) b)
      = algebraMap (D.A i.succ) (D.locAwayA a i.succ) (D.toRight i b) :=
  IsLocalization.map_eq
    (Algebra.algebraMapSubmonoid_le_comap (Submonoid.powers a) (D.toRight i)) b

/-- The away-localized lower algebra at a stage acts on the away-localized module through the
away-localized `toLeft`. -/
public noncomputable instance moduleLocAwayBLocAwayM (i : Fin (D.stepCount + 1)) :
    Module (D.locAwayB a i) (D.locAwayM a i) :=
  Module.compHom (D.locAwayM a i) (D.locAwayToLeft a i).toRingHom

/-- The away-localized upper algebra at a stage is an algebra over the away-localized lower
one. -/
public noncomputable instance algebraLocAwayBLocAwayA (i : Fin (D.stepCount + 1)) :
    Algebra (D.locAwayB a i) (D.locAwayA a i) := (D.locAwayToLeft a i).toRingHom.toAlgebra

public instance isScalarTowerLocAwayBLocAwayALocAwayM (i : Fin (D.stepCount + 1)) :
    IsScalarTower (D.locAwayB a i) (D.locAwayA a i) (D.locAwayM a i) :=
  ⟨fun b x m => by
    change (D.locAwayToLeft a i b * x) • m = D.locAwayToLeft a i b • (x • m); rw [mul_smul]⟩

public instance isScalarTowerBLocAwayBLocAwayA (i : Fin (D.stepCount + 1)) :
    IsScalarTower (D.B i) (D.locAwayB a i) (D.locAwayA a i) :=
  IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply (D.B i) (D.A i) (D.locAwayA a i)]
    exact (D.locAwayToLeft_algebraMap a i b).symm

public instance isScalarTowerBLocAwayBLocAwayM (i : Fin (D.stepCount + 1)) :
    IsScalarTower (D.B i) (D.locAwayB a i) (D.locAwayM a i) :=
  IsScalarTower.of_algebraMap_smul fun b x => by
    rw [← IsScalarTower.algebraMap_smul (D.locAwayA a i)
        (algebraMap (D.B i) (D.locAwayB a i) b) x,
      ← IsScalarTower.algebraMap_apply (D.B i) (D.locAwayB a i) (D.locAwayA a i),
      IsScalarTower.algebraMap_apply (D.B i) (D.A i) (D.locAwayA a i),
      IsScalarTower.algebraMap_smul (D.locAwayA a i) (algebraMap (D.B i) (D.A i) b) x,
      IsScalarTower.algebraMap_smul (D.A i) b x]

/-- The away-localization map of the module at stage `i`, as a map of modules over the lower
algebra. -/
public noncomputable def locAwayMk (i : Fin (D.stepCount + 1)) : D.M i →ₗ[D.B i] D.locAwayM a i :=
  (LocalizedModule.mkLinearMap
    (Algebra.algebraMapSubmonoid (D.A i) (Submonoid.powers a)) (D.M i)).restrictScalars (D.B i)

@[simp]
public theorem locAwayMk_apply (i : Fin (D.stepCount + 1)) (m : D.M i) :
    D.locAwayMk a i m = LocalizedModule.mk m 1 := rfl

public instance isLocalizedModule_locAwayMk (i : Fin (D.stepCount + 1)) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a))
      (D.locAwayMk a i) := by
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (D.A i)
      (Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a)))
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (D.A i) (Submonoid.powers a)) (D.M i)) := by
    rw [Algebra.algebraMapSubmonoid_map_map (A := D.B i)]; infer_instance
  exact IsLocalizedModule.restrictScalars _ _

/-- The localization away from `a` of the map of a dévissage stage. -/
public noncomputable def locAwayAlpha (i : Fin (D.stepCount + 1)) :
    (Fin (D.multiplicity i) →₀ D.locAwayB a i) →ₗ[D.locAwayB a i] D.locAwayM a i :=
  IsLocalizedModule.mapExtendScalars
    (Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a))
    (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locAwayB a i))) (D.locAwayMk a i)
    (D.locAwayB a i) (D.alpha i)

/-- The away-localized map of a stage is the away-localization of the map of that stage. -/
public theorem locAwayAlpha_mapRange (i : Fin (D.stepCount + 1))
    (x : Fin (D.multiplicity i) →₀ D.B i) :
    D.locAwayAlpha a i
        (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locAwayB a i)) x)
      = D.locAwayMk a i (D.alpha i x) := by
  rw [locAwayAlpha, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]

/-! ### The away-localized transition data -/

/-- The away-localized lower algebra at a stage acts on the next stage's away-localized module
through the away-localized `toRight`. -/
public noncomputable instance moduleLocAwayBLocAwayMsucc (i : Fin D.stepCount) :
    Module (D.locAwayB a i.castSucc) (D.locAwayM a i.succ) :=
  Module.compHom (D.locAwayM a i.succ) (D.locAwayToRight a i).toRingHom

/-- The next stage's away-localized upper algebra is an algebra over the away-localized lower
one. -/
public noncomputable instance algebraLocAwayBLocAwayAsucc (i : Fin D.stepCount) :
    Algebra (D.locAwayB a i.castSucc) (D.locAwayA a i.succ) :=
  (D.locAwayToRight a i).toRingHom.toAlgebra

public instance isScalarTowerLocAwayBLocAwayALocAwayMsucc (i : Fin D.stepCount) :
    IsScalarTower (D.locAwayB a i.castSucc) (D.locAwayA a i.succ) (D.locAwayM a i.succ) :=
  ⟨fun b x m => by
    change (D.locAwayToRight a i b * x) • m = D.locAwayToRight a i b • (x • m); rw [mul_smul]⟩

public instance isScalarTowerBLocAwayBLocAwayAsucc (i : Fin D.stepCount) :
    IsScalarTower (D.B i.castSucc) (D.locAwayB a i.castSucc) (D.locAwayA a i.succ) :=
  IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply (D.B i.castSucc) (D.A i.succ) (D.locAwayA a i.succ)]
    exact (D.locAwayToRight_algebraMap a i b).symm

public instance isScalarTowerBLocAwayBLocAwayMsucc (i : Fin D.stepCount) :
    IsScalarTower (D.B i.castSucc) (D.locAwayB a i.castSucc) (D.locAwayM a i.succ) :=
  IsScalarTower.of_algebraMap_smul fun b x => by
    rw [← IsScalarTower.algebraMap_smul (D.locAwayA a i.succ)
        (algebraMap (D.B i.castSucc) (D.locAwayB a i.castSucc) b) x,
      ← IsScalarTower.algebraMap_apply (D.B i.castSucc) (D.locAwayB a i.castSucc)
        (D.locAwayA a i.succ),
      IsScalarTower.algebraMap_apply (D.B i.castSucc) (D.A i.succ) (D.locAwayA a i.succ),
      IsScalarTower.algebraMap_smul (D.locAwayA a i.succ)
        (algebraMap (D.B i.castSucc) (D.A i.succ) b) x,
      IsScalarTower.algebraMap_smul (D.A i.succ) b x]

/-- The away-localization map of the next stage's module, as a map of modules over the lower
algebra of the current stage. -/
public noncomputable def locAwayMkSucc (i : Fin D.stepCount) :
    D.M i.succ →ₗ[D.B i.castSucc] D.locAwayM a i.succ :=
  (LocalizedModule.mkLinearMap
    (Algebra.algebraMapSubmonoid (D.A i.succ) (Submonoid.powers a))
    (D.M i.succ)).restrictScalars (D.B i.castSucc)

public instance isLocalizedModule_locAwayMkSucc (i : Fin D.stepCount) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (D.B i.castSucc) (Submonoid.powers a))
      (D.locAwayMkSucc a i) := by
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (D.A i.succ)
      (Algebra.algebraMapSubmonoid (D.B i.castSucc) (Submonoid.powers a)))
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (D.A i.succ) (Submonoid.powers a)) (D.M i.succ)) := by
    rw [Algebra.algebraMapSubmonoid_map_map (A := D.B i.castSucc)]; infer_instance
  exact IsLocalizedModule.restrictScalars _ _

/-- The image of the map of a stage lands in the kernel of the away-localized quotient map. -/
public theorem range_alpha_le_ker_locAway (i : Fin (D.stepCount + 1)) :
    LinearMap.range (D.alpha i) ≤ LinearMap.ker
      (((LinearMap.range (D.locAwayAlpha a i)).mkQ).restrictScalars (D.B i) ∘ₗ
        D.locAwayMk a i) := by
  rintro y ⟨x, rfl⟩
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locAwayB a i)) x,
    D.locAwayAlpha_mapRange a i x⟩

/-- The map on cokernels induced by the away-localization map of a stage. -/
public noncomputable def locAwayCokerMap (i : Fin (D.stepCount + 1)) :
    (D.M i ⧸ LinearMap.range (D.alpha i)) →ₗ[D.B i]
      (D.locAwayM a i ⧸ LinearMap.range (D.locAwayAlpha a i)) :=
  Submodule.liftQ _ _ (D.range_alpha_le_ker_locAway a i)

public instance isLocalizedModule_locAwayCokerMap (i : Fin (D.stepCount + 1)) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a))
      (D.locAwayCokerMap a i) :=
  Stacks.Flatness.isLocalizedModule_of_quotient_range
    (Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a))
    (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locAwayB a i))) (D.locAwayMk a i)
    (D.alpha i) (D.locAwayAlpha a i) (D.locAwayAlpha_mapRange a i) (D.locAwayCokerMap a i)
    fun _ => rfl

/-- The cokernel identification of a stage, away-localized. -/
public noncomputable def locAwayCokerEquiv (i : Fin D.stepCount) :
    (D.locAwayM a i.castSucc ⧸ LinearMap.range (D.locAwayAlpha a i.castSucc))
      ≃ₗ[D.locAwayB a i.castSucc] D.locAwayM a i.succ :=
  IsLocalizedModule.mapEquiv
    (Algebra.algebraMapSubmonoid (D.B i.castSucc) (Submonoid.powers a))
    (D.locAwayCokerMap a i.castSucc) (D.locAwayMkSucc a i) (D.locAwayB a i.castSucc)
    (D.cokerEquiv i)

/-- **The powers of an element outside the base prime miss the fibre prime of a stage.** This is
`Module.CompleteDevissage.disjoint_map` shrunk along `Submonoid.powers a ≤ r.primeCompl`. -/
public theorem disjoint_map_powers (ha : a ∈ r.primeCompl) (i : Fin (D.stepCount + 1)) :
    Disjoint
      ((Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a) : Submonoid (D.B i)) :
        Set (D.B i))
      ((Ideal.map (algebraMap R (D.B i)) r : Ideal (D.B i)) : Set (D.B i)) :=
  Set.disjoint_of_subset_left
    (fun _ hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, r.primeCompl.powers_le.mpr ha hy, rfl⟩)
    (D.disjoint_map i)

/-- **The fibre prime of a stage stays prime in the away-localized stage.** -/
public theorem isPrime_map_locAwayB (ha : a ∈ r.primeCompl) (i : Fin (D.stepCount + 1)) :
    (Ideal.map (algebraMap (Localization.Away a) (D.locAwayB a i))
      (Ideal.map (algebraMap R (Localization.Away a)) r)).IsPrime :=
  Stacks.Flatness.isPrime_map_algebraMap_of_disjoint (Submonoid.powers a) r
    (Localization.Away a) (D.locAwayB a i) (D.disjoint_map_powers a ha i)

/-- **The base prime stays prime after inverting an element outside it.** -/
public theorem isPrime_map_algebraMap_powers {R : Type u} [CommRing R] {r : Ideal R}
    [r.IsPrime] {a : R} (ha : a ∈ r.primeCompl) :
    (Ideal.map (algebraMap R (Localization.Away a)) r).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) (Localization.Away a) r ‹_›
    (Set.disjoint_left.mpr fun _ hx hx' => by
      obtain ⟨k, rfl⟩ := hx
      exact r.primeCompl.pow_mem ha k hx')

/-! ### The away-localized initial data -/

/-- The away-localization map of the first stage's module, as a map of modules over the original
algebra. -/
public noncomputable def locAwayMk₀ : D.M 0 →ₗ[S] D.locAwayM a 0 :=
  (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (D.A 0) (Submonoid.powers a))
    (D.M 0)).restrictScalars S

public instance isLocalizedModule_locAwayMk₀ :
    IsLocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) (D.locAwayMk₀ a) := by
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (D.A 0)
      (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (D.A 0) (Submonoid.powers a)) (D.M 0)) := by
    rw [Algebra.algebraMapSubmonoid_map_map (A := S)]; infer_instance
  exact IsLocalizedModule.restrictScalars _ _

section Initial

variable (S' : Type v) [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S']
  [Algebra (Localization.Away a) S'] [IsScalarTower R (Localization.Away a) S']

/-- The away-localization of the map from the original algebra to the first upper algebra. -/
public noncomputable def locAwayToA₀ : S' →ₐ[Localization.Away a] D.locAwayA a 0 :=
  IsLocalization.mapₐ (Submonoid.powers a) (Localization.Away a) S' (D.locAwayA a 0) D.toA₀

@[simp]
public theorem locAwayToA₀_algebraMap (s : S) :
    D.locAwayToA₀ a S' (algebraMap S S' s) = algebraMap (D.A 0) (D.locAwayA a 0) (D.toA₀ s) :=
  IsLocalization.map_eq (Algebra.algebraMapSubmonoid_le_comap (Submonoid.powers a) D.toA₀) s

/-- The away-localized original algebra acts on the first away-localized module through the
away-localized initial map. -/
public noncomputable instance moduleS'LocAwayM₀ : Module S' (D.locAwayM a 0) :=
  Module.compHom (D.locAwayM a 0) (D.locAwayToA₀ a S').toRingHom

/-- The first away-localized upper algebra is an algebra over the away-localized original
algebra. -/
public noncomputable instance algebraS'LocAwayA₀ : Algebra S' (D.locAwayA a 0) :=
  (D.locAwayToA₀ a S').toRingHom.toAlgebra

public instance isScalarTowerS'LocAwayA₀LocAwayM₀ :
    IsScalarTower S' (D.locAwayA a 0) (D.locAwayM a 0) :=
  ⟨fun b x m => by
    change (D.locAwayToA₀ a S' b * x) • m = D.locAwayToA₀ a S' b • (x • m); rw [mul_smul]⟩

public instance isScalarTowerSS'LocAwayA₀ : IsScalarTower S S' (D.locAwayA a 0) :=
  IsScalarTower.of_algebraMap_eq fun s => by
    rw [IsScalarTower.algebraMap_apply S (D.A 0) (D.locAwayA a 0)]
    exact (D.locAwayToA₀_algebraMap a S' s).symm

public instance isScalarTowerSS'LocAwayM₀ : IsScalarTower S S' (D.locAwayM a 0) :=
  IsScalarTower.of_algebraMap_smul fun s x => by
    rw [← IsScalarTower.algebraMap_smul (D.locAwayA a 0) (algebraMap S S' s) x,
      ← IsScalarTower.algebraMap_apply S S' (D.locAwayA a 0),
      IsScalarTower.algebraMap_apply S (D.A 0) (D.locAwayA a 0),
      IsScalarTower.algebraMap_smul (D.locAwayA a 0) (algebraMap S (D.A 0) s) x,
      IsScalarTower.algebraMap_smul (D.A 0) s x]

variable (N' : Type max u w) [AddCommGroup N'] [Module S N'] [Module S' N']
  [IsScalarTower S S' N'] [Module.Finite S' N'] (gN : N →ₗ[S] N')
  [IsLocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) gN]
  [Algebra.FiniteType (Localization.Away a) S']

/-- **The base change of a complete dévissage along the localization of its base away from an
element outside its prime.**

Given a complete dévissage of `N/S/R` over a prime `r` of `R` (Stacks 05HX) and an element
`a ∉ r`, localizing every ring and every module at the image of the powers of `a` gives a
complete dévissage of `N'/S'/R_a` over `rR_a`. This is the base change the general-base form of
Stacks 05IB performs, as `Module.CompleteDevissage.localize` is the one Stacks 05I5 performs.

The localized algebra `S'` and the localized module `N'` are parameters carrying `IsLocalization`
and `IsLocalizedModule` hypotheses; the stage algebras and stage modules are built as
`Localization` and `LocalizedModule` of the originals, because the dependent fields `alpha`,
`cokerEquiv` and `fiber_bijective` are typed against the module structure restricted along the
localized `toLeft`. -/
public noncomputable def localizeAway (ha : a ∈ r.primeCompl)
    [(Ideal.map (algebraMap R (Localization.Away a)) r).IsPrime] :
    CompleteDevissage (Localization.Away a) S' N'
      (Ideal.map (algebraMap R (Localization.Away a)) r) where
  stepCount := D.stepCount
  A := D.locAwayA a
  B := D.locAwayB a
  M := D.locAwayM a
  toA₀ := D.locAwayToA₀ a S'
  toLeft := D.locAwayToLeft a
  toRight := D.locAwayToRight a
  multiplicity := D.multiplicity
  alpha := D.locAwayAlpha a
  finiteM i := Module.Finite.of_isLocalizedModule
    (Algebra.algebraMapSubmonoid (D.A i) (Submonoid.powers a))
    (LocalizedModule.mkLinearMap _ (D.M i))
  initial_surjective := IsLocalization.mapₐ_surjective_of_surjective (Submonoid.powers a)
    (Localization.Away a) S' (D.locAwayA a 0) D.toA₀ D.initial_surjective
  initial_finitePresentation := Stacks.Flatness.finitePresentation_mapₐ_of_isLocalization
    (Submonoid.powers a) D.toA₀ D.initial_surjective D.initial_finitePresentation
    (Localization.Away a) S' (D.locAwayA a 0)
  transition_surjective i := IsLocalization.mapₐ_surjective_of_surjective (Submonoid.powers a)
    (Localization.Away a) (D.locAwayB a i.castSucc) (D.locAwayA a i.succ) (D.toRight i)
    (D.transition_surjective i)
  transition_finitePresentation i := Stacks.Flatness.finitePresentation_mapₐ_of_isLocalization
    (Submonoid.powers a) (D.toRight i) (D.transition_surjective i)
    (D.transition_finitePresentation i)
    (Localization.Away a) (D.locAwayB a i.castSucc) (D.locAwayA a i.succ)
  left_finite i := RingHom.finite_algebraMap.mpr
    (Stacks.Flatness.finite_of_isLocalization (Submonoid.powers a) (A := D.A i) (B := D.B i)
      (D.locAwayB a i) (D.locAwayA a i))
  smooth i := Stacks.Flatness.smooth_of_isLocalization (D.B i) (Submonoid.powers a)
    (Localization.Away a) (D.locAwayB a i)
  geometricallyIrreducibleFibers i :=
    Stacks.Flatness.geometricallyIrreducible_of_isLocalization (D.B i) (Submonoid.powers a)
      (Localization.Away a) (D.locAwayB a i)
  initialEquiv := IsLocalizedModule.mapEquiv
    (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) gN (D.locAwayMk₀ a) S' D.initialEquiv
  cokerEquiv := D.locAwayCokerEquiv a
  map_isPrime i := D.isPrime_map_locAwayB a ha i
  fiber_bijective i :=
    haveI := D.isPrime_map_locAwayB a ha i
    Stacks.Flatness.fiber_bijective_of_isLocalization (D.alpha i)
      (Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers a)) (D.locAwayMk a i)
      (D.locAwayAlpha a i) (D.locAwayAlpha_mapRange a i) (Ideal.map (algebraMap R (D.B i)) r)
      (Ideal.map (algebraMap (Localization.Away a) (D.locAwayB a i))
        (Ideal.map (algebraMap R (Localization.Away a)) r))
      (Stacks.Flatness.map_algebraMap_eq_comap_of_disjoint (Submonoid.powers a) r
        (Localization.Away a) (D.locAwayB a i) (D.disjoint_map_powers a ha i))
      (D.fiber_bijective i)
  final_surjective := Stacks.Flatness.surjective_of_isLocalization
    (Algebra.algebraMapSubmonoid (D.B (Fin.last D.stepCount)) (Submonoid.powers a))
    (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B (Fin.last D.stepCount))
      (D.locAwayB a (Fin.last D.stepCount))))
    (D.locAwayMk a (Fin.last D.stepCount)) (D.alpha (Fin.last D.stepCount))
    (D.locAwayAlpha a (Fin.last D.stepCount))
    (D.locAwayAlpha_mapRange a (Fin.last D.stepCount)) D.final_surjective

@[simp]
public theorem stepCount_localizeAway (ha : a ∈ r.primeCompl)
    [(Ideal.map (algebraMap R (Localization.Away a)) r).IsPrime] :
    (D.localizeAway a S' N' gN ha).stepCount = D.stepCount := rfl

end Initial

/-- **The canonical base change of a complete dévissage away from an element outside its prime.**

This is `Module.CompleteDevissage.localizeAway` with the canonical models for the localized
algebra and the localized module. The base ring, the algebra and the module are taken in one
universe, which is what `Stacks.Flatness.finiteType_of_isLocalization` needs in order to supply
`Algebra.FiniteType R_a S_a`. -/
public noncomputable def localizeAwayCanonical {R S N : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    {r : Ideal R} [r.IsPrime] (D : CompleteDevissage R S N r) (a : R) (ha : a ∈ r.primeCompl)
    [(Ideal.map (algebraMap R (Localization.Away a)) r).IsPrime] :
    CompleteDevissage (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N)
      (Ideal.map (algebraMap R (Localization.Away a)) r) :=
  letI : Module.Finite (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) :=
    Module.Finite.of_isLocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
      (LocalizedModule.mkLinearMap _ N)
  D.localizeAway a _ _
    (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) ha

end Module.CompleteDevissage

/-! ### Stacks 05IB over a general base -/

namespace Module.CompleteDevissage

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FinitePresentation R S] [AddCommGroup N] [Module S N] [Module R N]
  [IsScalarTower R S N] [Module.FinitePresentation S N] {r : Ideal R} [r.IsPrime]

omit [Module R N] [IsScalarTower R S N] in
/-- **The element of Stacks 05IB, from stagewise flatness at a chosen family of stage primes.**
Let `N` be a finitely presented module over a finitely presented `R`-algebra `S` carrying a
complete dévissage over a prime `r` of `R`, and choose in every lower algebra a prime over `r` at
which the stage module is flat over `R`. Then there is an `a ∈ R`, `a ∉ r`, such that every stage
map of the dévissage becomes injective after inverting `a`.

Finite presentation of the stage module over the lower algebra is Stacks 05HY
(`Module.CompleteDevissage.finitePresentation_iff_all_stages`), and Stacks 05IA
(`Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule`) then produces
an element `f i ∉ r` after inverting which the stage map is universally injective. The product of
the finitely many `f i` inverts them all at once:
`Stacks.Flatness.injective_of_isLocalizedModule_of_exists_mul` carries injectivity from the
powers of `f i` to the powers of the product.

The stage primes are a parameter because the two ways of supplying the flatness use different
ones. For a dévissage *at* a prime `q` of `S` they are the primes the dévissage records and the
flatness is the downward recursion of Stacks 05I4
(`Module.NonemptyCompleteDevissageAt.exists_away_injective_alpha`); for a dévissage merely *over*
`r` with `N` flat over `R` they are the generic points `rBᵢ` of the fibres over `r` and the
flatness comes from the local case through the base change to `R_r`
(`Module.CompleteDevissage.exists_away_injective_alpha`). -/
public theorem exists_away_injective_alpha_of_flat_localizedModule
    (D : CompleteDevissage R S N r)
    (p : ∀ i, Ideal (D.B i)) (hp : ∀ i, (p i).IsPrime) (hp_under : ∀ i, (p i).under R = r)
    (hfl : ∀ i, letI : Module (D.B i) (D.M i) :=
        Module.compHom (D.M i) (D.toLeft i).toRingHom
      letI : Module R (D.M i) := Module.compHom (D.M i) (algebraMap R (D.A i))
      letI : IsScalarTower R (D.B i) (D.M i) :=
        Module.isScalarTower_compHom R (D.B i) (D.A i) (D.M i) (D.toLeft i)
      Module.Flat R (LocalizedModule (p i).primeCompl (D.M i))) :
    ∃ a ∈ r.primeCompl, ∀ i, Function.Injective (D.locAwayAlpha a i) := by
  classical
  have hfp : ∀ i, let : Module (D.B i) (D.M i) :=
      Module.compHom (D.M i) (D.toLeft i).toRingHom
      Module.FinitePresentation (D.B i) (D.M i) := fun i =>
    (D.finitePresentation_iff_all_stages.mp
      (D.finitePresentation_iff_initial_over_lower.mp
        (D.finitePresentation_iff_initial_over_upper.mp ‹_›)) i).2
  let _ : ∀ i, Module (D.B i) (D.M i) := fun i =>
    Module.compHom (D.M i) (D.toLeft i).toRingHom
  let _ : ∀ i, Module R (D.M i) := fun i =>
    Module.compHom (D.M i) (algebraMap R (D.A i))
  let _ : ∀ i, IsScalarTower R (D.B i) (D.M i) := fun i =>
    Module.isScalarTower_compHom R (D.B i) (D.A i) (D.M i) (D.toLeft i)
  let _ : ∀ i, Module.FinitePresentation (D.B i) (D.M i) := hfp
  let _ : ∀ i, (p i).IsPrime := hp
  let _ : ∀ i, GeometricallyIntegral (Spec.map (ofHom (algebraMap R (D.B i)))) := fun i =>
    AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyIrreducible R (D.B i)
  have hstage : ∀ i, ∃ f ∈ r.primeCompl, ∀ x,
      D.alpha i x = 0 → ∃ t ∈ Submonoid.powers f, (algebraMap R (D.B i) t) • x = 0 := by
    intro i
    set e : (Fin (D.multiplicity i) →₀ D.B i) ≃ₗ[D.B i] (Fin (D.multiplicity i) → D.B i) :=
      Finsupp.linearEquivFunOnFinite (D.B i) (D.B i) (Fin (D.multiplicity i)) with he
    have hbij := rTensor_comp_funOnFinite_symm_bijective _ (D.alpha i) (D.fiber_bijective i)
    obtain ⟨g, hg, huniv⟩ :=
      Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule
        R (D.B i) r (p i) (hp_under i)
        (D.M i) (D.multiplicity i) (D.alpha i ∘ₗ e.symm.toLinearMap) hbij (hfl i)
    refine ⟨g, hg, fun x hx => ?_⟩
    have hinj : Function.Injective (LocalizedModule.map (Submonoid.powers g)
        ((D.alpha i ∘ₗ e.symm.toLinearMap).restrictScalars R)) :=
      Module.injective_of_rTensor_injective
        ((LocalizedModule.map (Submonoid.powers g)
          ((D.alpha i ∘ₗ e.symm.toLinearMap).restrictScalars R)).restrictScalars R) huniv
    obtain ⟨t, htm, ht⟩ := Stacks.Flatness.exists_smul_eq_zero_of_injective_localizedModule_map
      (Submonoid.powers g) (D.alpha i ∘ₗ e.symm.toLinearMap) hinj (e x)
      (by simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply]; exact hx)
    refine ⟨t, htm, ?_⟩
    have h : e.symm ((algebraMap R (D.B i) t) • e x) = e.symm 0 := congrArg e.symm ht
    rwa [map_smul, e.symm_apply_apply, map_zero] at h
  choose f hf hker using hstage
  refine ⟨∏ i, f i, Submonoid.prod_mem _ fun i _ => hf i, fun i => ?_⟩
  have hab : f i * ∏ j ∈ Finset.univ.erase i, f j = ∏ j, f j :=
    Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)
  have hTT' : ∀ t ∈ Submonoid.powers (f i), ∃ u : D.B i,
      algebraMap R (D.B i) t * u ∈
        Algebra.algebraMapSubmonoid (D.B i) (Submonoid.powers (∏ j, f j)) := by
    rintro t ⟨k, rfl⟩
    refine ⟨algebraMap R (D.B i) ((∏ j ∈ Finset.univ.erase i, f j) ^ k), ?_⟩
    rw [← map_mul, ← mul_pow, hab]
    exact Submonoid.mem_map_of_mem _ ⟨k, rfl⟩
  exact Stacks.Flatness.injective_of_isLocalizedModule_of_exists_mul hTT'
    (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locAwayB (∏ j, f j) i)))
    (D.locAwayMk (∏ j, f j) i) (D.alpha i)
    ((D.locAwayAlpha (∏ j, f j) i).restrictScalars (D.B i))
    (D.locAwayAlpha_mapRange (∏ j, f j) i) (hker i)

end Module.CompleteDevissage

namespace Module.NonemptyCompleteDevissageAt

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FinitePresentation R S] [AddCommGroup N] [Module S N] [Module R N]
  [IsScalarTower R S N] [Module.FinitePresentation S N] [Module.Flat R N]
  {q : Ideal S} [q.IsPrime]

/-- **The element of Stacks 05IB.** Let `N` be a finitely presented module over a finitely
presented `R`-algebra `S`, flat over `R`, with a complete dévissage at a prime `q` of `S`. Then
there is an `a ∈ R`, `a ∉ q ∩ R`, such that every stage map of the dévissage becomes injective
after inverting `a`.

This is `Module.CompleteDevissage.exists_away_injective_alpha_of_flat_localizedModule` at the
stage primes the dévissage records, whose stagewise flatness over `R` is the downward recursion
of Stacks 05I4, `Module.CompleteDevissage.flat_localizedModule_stage_of_under`. -/
public theorem exists_away_injective_alpha (E : NonemptyCompleteDevissageAt R S N q) :
    ∃ a ∈ (q.under R).primeCompl, ∀ i,
      Function.Injective (E.toCompleteDevissage.locAwayAlpha a i) :=
  E.toCompleteDevissage.exists_away_injective_alpha_of_flat_localizedModule E.lowerPrime
    E.lowerPrime_isPrime (fun i => ((E.lowerPrime_liesOver i).over).symm)
    (E.toCompleteDevissage.flat_localizedModule_stage_of_under q E.lowerPrime
      E.lowerPrime_isPrime (fun i => ((E.lowerPrime_liesOver i).over).symm)
      E.upperPrime E.upperPrime_isPrime E.upperPrime_under E.upperPrime_unique
      E.initial_under E.transition_under
      (Stacks.UniversalInjectivity.flat_localizedModule q.primeCompl))

/-- **Stacks Project, Tag 05IB, the projectivity conclusion over a general base.** Let `N` be a
finitely presented module over a finitely presented `R`-algebra `S` which is flat over `R`, and
let `q` be a prime of `S` at which `N/S/R` admits a complete dévissage. Then there is an `a ∈ R`
outside `q ∩ R` such that `N_a` is projective over `R_a`.

The library's form of this conclusion
(`Module.CompleteDevissage.projective_of_flat`) asks for a local base, where the element may be
taken to be `1`. Here the dévissage is transported along `R → R_a` by
`Module.CompleteDevissage.localizeAwayCanonical` for the element `a` of
`Module.NonemptyCompleteDevissageAt.exists_away_injective_alpha`, which makes every stage map of
the transported dévissage injective, and
`Module.CompleteDevissage.projective_of_injective_alpha` then gives projectivity over `R_a`. -/
public theorem exists_away_projective (E : NonemptyCompleteDevissageAt R S N q) :
    ∃ a ∈ (q.under R).primeCompl,
      Module.Projective (Localization.Away a) (LocalizedModule (Submonoid.powers a) N) := by
  obtain ⟨a, ha, hinj⟩ := E.exists_away_injective_alpha
  refine ⟨a, ha, ?_⟩
  have :=
    Module.CompleteDevissage.isPrime_map_algebraMap_powers (r := q.under R) (a := a) ha
  let : Module (Localization.Away a)
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) :=
    Module.compHom _ (algebraMap (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))))
  have : IsScalarTower (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R (Localization.Away a)
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) :=
    IsScalarTower.of_algebraMap_smul fun x m => by
      change algebraMap (Localization.Away a)
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
          (algebraMap R (Localization.Away a) x) • m = x • m
      rw [← IsScalarTower.algebraMap_apply R (Localization.Away a)
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))),
        IsScalarTower.algebraMap_smul
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))]
  have : IsLocalizedModule (Submonoid.powers a)
      ((LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N).restrictScalars R) :=
    IsLocalizedModule.restrictScalars _ _
  have := (E.toCompleteDevissage.localizeAwayCanonical a ha).projective_of_injective_alpha hinj
  exact Module.Projective.of_equiv'
    (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers a) (Localization.Away a)
      (IsLocalizedModule.linearEquiv (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) N)
        ((LocalizedModule.mkLinearMap
          (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N).restrictScalars R))).symm

end Module.NonemptyCompleteDevissageAt

end
