module

public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Flat.DevissageDecomposition
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus
public import StacksFrontier.RingTheory.Localization.UniquePrimeOver
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Stagewise flatness along a complete dévissage

Stacks 05I4 draws three conclusions about a finite module `N` over a finitely presented algebra
`S` of a local ring `R` which is flat over `R` at a prime `q` over the closed point and carries a
complete dévissage there. `StacksFrontier.RingTheory.Flat.DevissageDecomposition` proves all three
from two hypotheses: projectivity over `R` of the smooth lower algebras `Bᵢ`, and injectivity of
the maps `αᵢ`. The second of those is Stacks 05I3 at stage `i`, whose own input is flatness over
`R` of `(Mᵢ)_{𝔮ᵢ}` at every stage.

This file supplies that stagewise flatness. The source obtains it by a recursion down the
dévissage, which is what `Module.CompleteDevissage.flat_localizedModule_stage` carries out, and
with it the three conclusions of Stacks 05I4 rest on nothing outside the library: the
projectivity of the lower algebras is `Module.CompleteDevissage.projective_lowerAlgebra`, which
is unconditional, so the three conclusions are proved here outright. Together with smoothness and
geometric irreducibility of the fibres of the lower algebras they make up Stacks 05I4, which is
`Module.CompleteDevissageAt.finitePresentation_free_linearEquiv_directSum_of_flat`.

## Main results

* `Module.flat_localizedModule_congr`: localizing linearly equivalent modules at the same
  submonoid gives the same flatness over a common base.
* `Module.flat_localizedModule_atPrime_under_iff_of_unique_prime_over`: Stacks 00EA for modules.
* `Module.flat_localizedModule_coker_of_flat_localizedModule_of_projective_finsupp`: the flatness
  half of Stacks 05I3 (1) ⟹ (3), which is the half that drives the recursion.
* `Module.CompleteDevissage.flat_localizedModule_stage` and
  `Module.NonemptyCompleteDevissageAt.flat_localizedModule_stage`: the recursion.
* `Module.NonemptyCompleteDevissageAt.injective_alpha_of_flat`: the injectivity hypothesis of
  Stacks 05I4, discharged from flatness at `q`.
* `Module.CompleteDevissageAt.nonempty_linearEquiv_directSum_of_flat`,
  `Module.CompleteDevissageAt.finitePresentation_of_flat` and
  `Module.CompleteDevissageAt.free_of_flat`: the three conclusions of Stacks 05I4, one at a time.
* `Module.CompleteDevissageAt.smooth_lowerAlgebra` and
  `Module.CompleteDevissageAt.geometricallyIrreducible_lowerAlgebra`: the lower algebras of a
  complete dévissage at a prime are smooth with geometrically irreducible fibres.
* `Module.CompleteDevissageAt.finitePresentation_free_linearEquiv_directSum_of_flat`:
  **Stacks 05I4**, all of its conclusions in one statement.

## Implementation notes

### The recursion needs no shifted dévissage

The source phrases the recursion as an induction on the number of stages: it observes that
`(Aᵢ, Bᵢ, Mᵢ, αᵢ, 𝔮ᵢ)_{i = 2, …, n}` is a complete dévissage of `Coker α₁ / B₁ / R` at `𝔮₁` and
applies the induction hypothesis to it. That shifted dévissage is not constructed here, and does
not need to be: the only consequence of it the argument uses is flatness over `R` of
`(Mᵢ₊₁)_{𝔮ᵢ₊₁}`, and that follows from flatness of `(Coker αᵢ)_{𝔮ᵢ}` by the identifications the
dévissage already records. So the recursion is a plain `Fin.induction` on the stage index, with
no transport of indices and no truncation construction — the same simplification that made
`Module.CompleteDevissage.tail` unnecessary for the tail recursion of
`StacksFrontier.RingTheory.Flat.DevissageTail`.

### The three localizations at a stage

Each step compares three localizations of a stage module:

* over `Bᵢ` at `𝔮ᵢ`, which is the form Stacks 05I3 consumes;
* over `Aᵢ` at the unique prime `𝔮'ᵢ` above `𝔮ᵢ`, which is the form the cokernel identification
  produces, since the dévissage presents `Mᵢ` as an `Aᵢ`-module;
* over `Bᵢ₋₁` at `𝔮ᵢ₋₁`, along the surjection `Bᵢ₋₁ → Aᵢ`.

`Module.flat_localizedModule_atPrime_under_iff_of_unique_prime_over` identifies the first two and
also the last two, so one lemma covers both: it asks only that the ring map satisfy going up and
that the upper prime be the only one over its contraction. For `Bᵢ → Aᵢ` going up holds because
the map is finite, hence integral, and uniqueness is the dévissage field `upperPrime_unique`; for
the surjections `S → A₀` and `Bᵢ → Aᵢ₊₁` going up holds for the same reason and uniqueness is
injectivity of contraction along a surjection.

Its proof is Stacks 00EA, `localization_eq_of_unique_prime_over`, whose conclusion is an equality
of *ring* localizations. The passage to modules is through `isLocalizedModule_iff_isBaseChange`:
both submonoids localize the module to a base change along the same ring, so the two module
localizations are canonically isomorphic. The going-up disjunct of Stacks 00EA is phrased there as
an explicit proposition rather than by `Algebra.HasGoingUp`, so it is produced from
`Ideal.exists_ideal_ge_liesOver_of_le`.

## References

* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 00EA](https://stacks.math.columbia.edu/tag/00EA)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
-/

@[expose] public section

open scoped DirectSum Pointwise

universe u v w

namespace Module

/-- Localizing two linearly equivalent modules at the same submonoid gives the same flatness
condition over a common base. -/
public theorem flat_localizedModule_congr {R A X Y : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup X] [Module R X] [Module A X] [IsScalarTower R A X]
    [AddCommGroup Y] [Module R Y] [Module A Y] [IsScalarTower R A Y]
    (S : Submonoid A) (e : X ≃ₗ[A] Y) :
    Module.Flat R (LocalizedModule S X) ↔ Module.Flat R (LocalizedModule S Y) :=
  Module.Flat.equiv_iff ((IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S X)
    ((LocalizedModule.mkLinearMap S Y).comp e.toLinearMap)).restrictScalars R)

/-- **Stacks 00EA for modules.** Let `A → B` satisfy going up and let `q` be a prime of `B` which
is the only prime of `B` lying over its contraction `p` to `A`. For a `B`-module `X` the
localizations `X_p` and `X_q` agree, so they have the same flatness over a common base. -/
public theorem flat_localizedModule_atPrime_under_iff_of_unique_prime_over
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.HasGoingUp A B]
    (X : Type*) [AddCommGroup X] [Module R X] [Module A X] [Module B X]
    [IsScalarTower R A X] [IsScalarTower R B X] [IsScalarTower A B X]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (hpq : q.under A = p)
    (huniq : ∀ q' : Ideal B, q'.IsPrime → q'.under A = p → q' = q) :
    Module.Flat R (LocalizedModule p.primeCompl X) ↔
      Module.Flat R (LocalizedModule q.primeCompl X) := by
  subst hpq
  have : q.LiesOver (q.under A) := ⟨rfl⟩
  have hloc : IsLocalization q.primeCompl
      (Localization (Algebra.algebraMapSubmonoid B (q.under A).primeCompl)) := by
    refine localization_eq_of_unique_prime_over (q.under A) q
      (fun q' hq' hq'o => huniq q' hq' (hq'o.over).symm) (Or.inl ?_)
    intro p₁ p₂ q₁ hp₁ hp₂ hq₁ hle hover
    have := hp₂
    have := hq₁
    have : q₁.LiesOver p₁ := ⟨hover.symm⟩
    obtain ⟨Q, hQle, hQ, hQo⟩ := Ideal.exists_ideal_ge_liesOver_of_le (p := p₁) (q := p₂) q₁ hle
    exact ⟨Q, hQ, hQle, (hQo.over).symm⟩
  set T := Algebra.algebraMapSubmonoid B (q.under A).primeCompl
  let f : X →ₗ[B] LocalizedModule T X := LocalizedModule.mkLinearMap T X
  have h1 : IsLocalizedModule (q.under A).primeCompl (f.restrictScalars A) :=
    IsLocalizedModule.restrictScalars (q.under A).primeCompl f
  have h2 : IsLocalizedModule q.primeCompl f :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl (Localization T) f).mpr
      ((isLocalizedModule_iff_isBaseChange T (Localization T) f).mp inferInstance)
  exact (Module.Flat.equiv_iff ((IsLocalizedModule.linearEquiv (q.under A).primeCompl
      (LocalizedModule.mkLinearMap _ X) (f.restrictScalars A)).restrictScalars R)).trans
    (Module.Flat.equiv_iff ((IsLocalizedModule.linearEquiv q.primeCompl
      (LocalizedModule.mkLinearMap _ X) f).restrictScalars R)).symm

/-- **Stacks Project, Tag 05I3, the flatness half of the implication (1) ⟹ (3)**, for a map out
of a finite free module presented as `Fin r →₀ S`.

If `N_q` is flat over `R` then so is the localization at `q` of the cokernel of `alpha`. This is
the half of the induction step that carries the recursion of Stacks 05I4 from one dévissage stage
to the next, the other half being injectivity of `alpha`
(`Module.injective_of_flat_localizedModule_of_projective_finsupp`). -/
public theorem flat_localizedModule_coker_of_flat_localizedModule_of_projective_finsupp
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Flat R S] [Module.Projective R S]
    [(Algebra.closedFiberIdeal R S).IsPrime]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (r : ℕ) (alpha : (Fin r →₀ S) →ₗ[S] N)
    (halpha : Function.Bijective
      (alpha.baseChange (Algebra.closedFiberIdeal R S).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)) := by
  classical
  set e : (Fin r →₀ S) ≃ₗ[S] (Fin r → S) := Finsupp.linearEquivFunOnFinite S S (Fin r)
  have hbase : Function.Bijective
      ((alpha ∘ₗ e.symm.toLinearMap).rTensor (Algebra.closedFiberIdeal R S).ResidueField) := by
    rw [← LinearMap.lTensor_bij_iff_rTensor_bij, ← LinearMap.baseChange_eq_ltensor,
      LinearMap.baseChange_comp]
    refine halpha.comp ?_
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_bij_iff_rTensor_bij,
      ← LinearEquiv.coe_rTensor _ e.symm]
    exact (e.symm.rTensor _).bijective
  have hrange : LinearMap.range (alpha ∘ₗ e.symm.toLinearMap) = LinearMap.range alpha :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.symm.surjective)
  have h := (flat_localizedModule_tfae_of_projective' R S q hq N r
    (alpha ∘ₗ e.symm.toLinearMap) hbase).out 1 3
  exact hrange ▸ (h.mp hflat).2

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {r : Ideal R} [r.IsPrime]

/-- **The downward recursion of Stacks 05I4**: stagewise flatness from flatness at `q`. -/
public theorem flat_localizedModule_stage [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissage R S N r) (hr : r = IsLocalRing.maximalIdeal R)
    (hproj : ∀ i, Module.Projective R (D.B i))
    (q : Ideal S) [q.IsPrime]
    (p : ∀ i, Ideal (D.B i)) (hp : ∀ i, (p i).IsPrime)
    (hp_under : ∀ i, (p i).comap (algebraMap R (D.B i)) = IsLocalRing.maximalIdeal R)
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
  subst hr
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
    ⟨fun b a m => by change (D.toLeft j b * a) • m = D.toLeft j b • (a • m); rw [mul_smul]⟩
  let : ∀ j, Module.Finite (D.B j) (D.A j) := fun j =>
    RingHom.finite_algebraMap.mp (D.left_finite j)
  let : ∀ j, Algebra.IsIntegral (D.B j) (D.A j) := fun j => Algebra.IsIntegral.of_finite _ _
  let : ∀ j, Module.Finite (D.B j) (D.M j) := fun j => Module.Finite.trans (D.A j) (D.M j)
  let : ∀ j, Module.Projective R (D.B j) := hproj
  let : ∀ j, (p j).IsPrime := hp
  let : ∀ j, (P j).IsPrime := hP
  let : ∀ j, (Algebra.closedFiberIdeal R (D.B j)).IsPrime := D.map_isPrime
  have hUL : ∀ j, Module.Flat R (LocalizedModule (p j).primeCompl (D.M j)) ↔
      Module.Flat R (LocalizedModule (P j).primeCompl (D.M j)) := fun j =>
    Module.flat_localizedModule_atPrime_under_iff_of_unique_prime_over
      (R := R) (A := D.B j) (B := D.A j) (D.M j) (p j) (P j) (hP_under j)
      (hP_uniq j)
  induction i using Fin.induction with
  | zero =>
    let : Module S (D.M 0) := Module.compHom (D.M 0) D.toA₀.toRingHom
    let : IsScalarTower R S (D.M 0) :=
      Module.isScalarTower_compHom R S (D.A 0) (D.M 0) D.toA₀
    let : Algebra S (D.A 0) := D.toA₀.toRingHom.toAlgebra
    let : IsScalarTower R S (D.A 0) :=
      IsScalarTower.of_algebraMap_eq fun x => (D.toA₀.commutes x).symm
    let : IsScalarTower S (D.A 0) (D.M 0) :=
      ⟨fun b a m => by change (D.toA₀ b * a) • m = D.toA₀ b • (a • m); rw [mul_smul]⟩
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
      Module.flat_localizedModule_coker_of_flat_localizedModule_of_projective_finsupp
        R (D.B j.castSucc) (p j.castSucc) (hp_under j.castSucc) (D.M j.castSucc)
        (D.multiplicity j.castSucc) (D.alpha j.castSucc) (D.fiber_bijective j.castSucc) ih
    let : Module (D.B j.castSucc) (D.M j.succ) :=
      Module.compHom (D.M j.succ) (D.toRight j).toRingHom
    let : IsScalarTower R (D.B j.castSucc) (D.M j.succ) :=
      Module.isScalarTower_compHom R (D.B j.castSucc) (D.A j.succ) (D.M j.succ) (D.toRight j)
    let : Algebra (D.B j.castSucc) (D.A j.succ) := (D.toRight j).toRingHom.toAlgebra
    let : IsScalarTower R (D.B j.castSucc) (D.A j.succ) :=
      IsScalarTower.of_algebraMap_eq fun x => ((D.toRight j).commutes x).symm
    let : IsScalarTower (D.B j.castSucc) (D.A j.succ) (D.M j.succ) :=
      ⟨fun b a m => by change (D.toRight j b * a) • m = D.toRight j b • (a • m); rw [mul_smul]⟩
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

end CompleteDevissage

namespace NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- **The downward recursion of Stacks 05I4** for a nonempty complete dévissage at a prime `q`
over the closed point of a local base: flatness over `R` of `N_𝔮` propagates to flatness over `R`
of `(Mᵢ)_{𝔮ᵢ}` at every stage.

The primes and the identifications are the ones the dévissage records: the stage primes are
`lowerPrime`, the unique primes above them are `upperPrime`, and `initial_under` and
`transition_under` say that they are compatible with the surjections `S → A₀` and
`Bᵢ → Aᵢ₊₁`. -/
public theorem flat_localizedModule_stage [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (E : NonemptyCompleteDevissageAt R S N q)
    (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hproj : ∀ i, Module.Projective R (E.toCompleteDevissage.B i))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N))
    (i : Fin (E.toCompleteDevissage.stepCount + 1)) :
    letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
      Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
    letI : Module R (E.toCompleteDevissage.M i) :=
      Module.compHom (E.toCompleteDevissage.M i)
        (algebraMap R (E.toCompleteDevissage.A i))
    letI : IsScalarTower R (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
      Module.isScalarTower_compHom R (E.toCompleteDevissage.B i)
        (E.toCompleteDevissage.A i) (E.toCompleteDevissage.M i)
        (E.toCompleteDevissage.toLeft i)
    Module.Flat R (LocalizedModule (E.lowerPrime i).primeCompl (E.toCompleteDevissage.M i)) :=
  CompleteDevissage.flat_localizedModule_stage E.toCompleteDevissage hq hproj q
    E.lowerPrime E.lowerPrime_isPrime (fun j => ((E.lowerPrime_liesOver j).over).symm.trans hq)
    E.upperPrime E.upperPrime_isPrime E.upperPrime_under E.upperPrime_unique
    E.initial_under E.transition_under hflat i

/-- **The injectivity hypothesis of Stacks 05I4, discharged from flatness at `q`.** Every map
`alpha i` of a nonempty complete dévissage at `q` is injective as soon as `N_𝔮` is flat over `R`
and the lower algebras are projective over `R`.

This is `Module.NonemptyCompleteDevissageAt.injective_alpha` with its stagewise flatness
hypothesis supplied by `Module.NonemptyCompleteDevissageAt.flat_localizedModule_stage`. -/
public theorem injective_alpha_of_flat [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (E : NonemptyCompleteDevissageAt R S N q)
    (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hproj : ∀ i, Module.Projective R (E.toCompleteDevissage.B i))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N))
    (i : Fin (E.toCompleteDevissage.stepCount + 1)) :
    letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
      Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
    Function.Injective (E.toCompleteDevissage.alpha i) :=
  E.injective_alpha hq hproj (E.flat_localizedModule_stage hq hproj hflat) i

end NonemptyCompleteDevissageAt

namespace CompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- Every lower algebra of a complete dévissage at a prime is projective over the base.

This is `Module.CompleteDevissage.projective_lowerAlgebra` transported to a dévissage *at* a
prime. The empty dévissage has no stages. -/
public theorem projective_lowerAlgebra
    (D : CompleteDevissageAt R S N q) (i : Fin D.length) :
    Module.Projective R (D.lowerAlgebra i) := by
  cases D with
  | empty hN => exact Fin.elim0 i
  | nonempty E => exact CompleteDevissage.projective_lowerAlgebra E.toCompleteDevissage i

/-- Every lower algebra of a complete dévissage at a prime is smooth over the base. -/
public theorem smooth_lowerAlgebra (D : CompleteDevissageAt R S N q) (i : Fin D.length) :
    Algebra.Smooth R (D.lowerAlgebra i) := by
  cases D with
  | empty hN => exact Fin.elim0 i
  | nonempty E => exact E.toCompleteDevissage.smooth i

open AlgebraicGeometry in
/-- Every lower algebra `B` of a complete dévissage at a prime has geometrically irreducible
fibres over the base: `Spec B → Spec R` is geometrically irreducible. -/
public theorem geometricallyIrreducible_lowerAlgebra (D : CompleteDevissageAt R S N q)
    (i : Fin D.length) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R (D.lowerAlgebra i)))) := by
  cases D with
  | empty hN => exact Fin.elim0 i
  | nonempty E => exact E.toCompleteDevissage.geometricallyIrreducibleFibers i

/-- The injectivity hypothesis of the three conclusions of Stacks 05I4, discharged from flatness
at `q` alone. -/
private theorem injective_alpha_of_flat [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N))
    (E : NonemptyCompleteDevissageAt R S N q) (_hE : D = .nonempty E)
    (i : Fin (E.toCompleteDevissage.stepCount + 1)) :
    letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
      Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
    Function.Injective (E.toCompleteDevissage.alpha i) :=
  E.injective_alpha_of_flat hq (projective_lowerAlgebra (.nonempty E)) hflat i

/-- The direct sum decomposition of Stacks 05I4. Let `(R, 𝔪)` be a local ring,
`R → S` of finite type, `N` a finite `S`-module and `q` a prime of `S` lying over `𝔪` at which
`N` is flat over `R`. A complete dévissage of `N/S/R` at `q` decomposes `N`, as an `R`-module,
into a direct sum of finite free modules over the smooth lower algebras of the dévissage.

The one external input of this statement used to be constructibility of the geometrically
reduced fibre locus over a Noetherian base; it is now a theorem, the affine case of Stacks 0579,
and is supplied by `Module.CompleteDevissageAt.projective_lowerAlgebra`. -/
public theorem nonempty_linearEquiv_directSum_of_flat [IsLocalRing R] [Module R N]
    [IsScalarTower R S N]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Nonempty (N ≃ₗ[R] ⨁ i : Fin D.length, (Fin (D.multiplicity i) →₀ D.lowerAlgebra i)) :=
  D.nonempty_linearEquiv_directSum (injective_alpha_of_flat D hq hflat)
    (projective_lowerAlgebra D)

/-- Finite presentation of the module in Stacks 05I4. In the situation of Stacks 05I4 the module
`N` is of finite presentation over `S`. The whole of Stacks 05I4 is
`Module.CompleteDevissageAt.finitePresentation_free_linearEquiv_directSum_of_flat`.

Its one external input, constructibility of the geometrically reduced fibre locus over a
Noetherian base, is now the theorem
`Algebra.isConstructible_geometricallyReducedFibreLocus'`. -/
public theorem finitePresentation_of_flat [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    [Algebra.FinitePresentation R S]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.FinitePresentation S N :=
  D.finitePresentation (injective_alpha_of_flat D hq hflat)

/-- Freeness over the base in Stacks 05I4. In the situation of Stacks 05I4 the module `N` is free
as an `R`-module. The whole of Stacks 05I4 is
`Module.CompleteDevissageAt.finitePresentation_free_linearEquiv_directSum_of_flat`.

Its one external input, constructibility of the geometrically reduced fibre locus over a
Noetherian base, is now the theorem
`Algebra.isConstructible_geometricallyReducedFibreLocus'`. -/
public theorem free_of_flat [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.Free R N :=
  D.free (injective_alpha_of_flat D hq hflat) (projective_lowerAlgebra D)

open AlgebraicGeometry in
/-- **Stacks Project, Tag 05I4.** Let `(R, 𝔪)` be a local ring, let `R → S` be a ring map of
finite presentation, let `N` be a finite `S`-module and let `q` be a prime of `S` lying over `𝔪`.
Assume that `N_q` is flat over `R` and that `D` is a complete dévissage of `N/S/R` at `q`. Then `N`
is a finitely presented `S`-module, free as an `R`-module, and there is an isomorphism of
`R`-modules `N ≅ B₁^{⊕ r₁} ⊕ … ⊕ Bₙ^{⊕ rₙ}`, where `B₁, …, Bₙ` are the lower algebras of `D` and
each `Bᵢ` is a smooth `R`-algebra with geometrically irreducible fibres. -/
@[stacks 05I4]
public theorem finitePresentation_free_linearEquiv_directSum_of_flat [IsLocalRing R] [Module R N]
    [IsScalarTower R S N] [Algebra.FinitePresentation R S]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.FinitePresentation S N ∧ Module.Free R N ∧
      (∀ i : Fin D.length, Algebra.Smooth R (D.lowerAlgebra i) ∧
        GeometricallyIrreducible
          (Spec.map (CommRingCat.ofHom (algebraMap R (D.lowerAlgebra i))))) ∧
      Nonempty (N ≃ₗ[R] ⨁ i : Fin D.length, (Fin (D.multiplicity i) →₀ D.lowerAlgebra i)) :=
  ⟨D.finitePresentation_of_flat hq hflat, D.free_of_flat hq hflat,
    fun i => ⟨D.smooth_lowerAlgebra i, D.geometricallyIrreducible_lowerAlgebra i⟩,
    D.nonempty_linearEquiv_directSum_of_flat hq hflat⟩

end CompleteDevissageAt

end Module

end
