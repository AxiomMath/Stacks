module

public import StacksFrontier.RingTheory.Flat.DevissageLocalizeAwayProjective

/-!
# Stacks 05IB over a general base

Stacks 05IB says that a finitely presented module `N` over a finitely presented `R`-algebra `S`
which is flat over `R` and admits a complete dévissage over a prime `r` of `R` becomes, after
inverting a single element of `R` outside `r`, a direct sum `B₁^{⊕ r₁} ⊕ ⋯ ⊕ Bₙ^{⊕ rₙ}` of
finite free modules over the smooth stage algebras of the dévissage — which stay smooth with
geometrically irreducible fibres over the new base — and is in particular projective over that
base. This file proves it in that generality.

The two statements already in the library are weaker in different directions.
`Module.CompleteDevissage.nonempty_linearEquiv_directSum_of_flat` and
`Module.CompleteDevissage.projective_of_flat` ask for a *local* base, where no element has to be
inverted; `Module.NonemptyCompleteDevissageAt.exists_away_projective` asks for a dévissage *at* a
prime of `S`, which is more than Stacks 05IB assumes, and concludes only projectivity.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Flatness.flat_localizedModule_of_le`: flatness over a base ring survives a further
  localization — if `M[T₁⁻¹]` is flat over `R` and `T₁ ≤ T₂`, then so is `M[T₂⁻¹]`.
* `Module.CompleteDevissage.flat_localizedModule_fibrePrime`: the stagewise flatness Stacks 05IA
  needs, for a dévissage merely *over* `r`, at the generic points `rBᵢ` of the fibres over `r`.
* `Module.CompleteDevissage.exists_away_injective_alpha`: one element of `R` outside `r` whose
  inversion makes every stage map of the dévissage injective.
* `Module.CompleteDevissage.exists_away_decomposition_projective`: **Stacks 05IB.**

## Implementation notes

### How the stagewise flatness is obtained

Stacks 05IA (`Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule`)
spreads out universal injectivity of a stage map from a prime of the lower algebra over `r` to an
open neighbourhood of `r` in the base, and the hypothesis it needs is flatness over `R` of the
stage module localized at that prime. For a dévissage *at* a prime of `S` that flatness is the
downward recursion of Stacks 05I4
(`Module.CompleteDevissage.flat_localizedModule_stage_of_under`), which carries the stage primes
and the unique primes of the upper algebras above them as data; a dévissage merely *over* `r`
records neither, and the recursion cannot be run as it stands.

What a dévissage over `r` does record is that `rBᵢ` is prime, and that is a prime over `r`
(`Module.CompleteDevissage.comap_map_eq`), so it can serve as the stage prime. The flatness at it
is obtained from the local case instead of from a recursion: the dévissage base changes to the
local ring `R_r` (`Module.CompleteDevissage.localizeAtPrime`), `N_r` is flat over `R_r`, and over
a local base the stage modules are *globally* flat
(`Module.CompleteDevissage.flat_stageModule`). Flatness over `R_r` gives flatness over `R`, the
localization `R → R_r` being flat, and `Stacks.Flatness.flat_localizedModule_of_le` then moves it
from the localization of the stage module at the image of `R ∖ r` — which is what the base change
to `R_r` produces — to its localization at the complement of `rBᵢ`, a larger multiplicative set
because `rBᵢ` contracts to `r`.

### Localizing further

`Stacks.Flatness.flat_localizedModule_of_le` is the one piece of general theory this needs.
`IsLocalizedModule.liftOfLE` exhibits `M[T₂⁻¹]` as a localization of `M[T₁⁻¹]` at `T₂`, and
`Stacks.UniversalInjectivity.flat_localizedModule` localizes a module flat over `R` at a
multiplicative set of the algebra without losing flatness over `R`; the direction matters, and
only this one holds — flatness of a localization says nothing about the module itself.

### The two localizations of the module

As in `Module.NonemptyCompleteDevissageAt.exists_away_projective`, the module the away-localized
dévissage decomposes is a localization of `N` at a submonoid of `S`, whereas Stacks 05IB speaks
of `LocalizedModule (Submonoid.powers a) N`, the localization of `N` as an `R`-module. The two
are identified by `IsLocalizedModule.linearEquiv`, both being localizations of `N` at the powers
of `a` over `R`, and the identification is upgraded to an `R_a`-linear equivalence by
`LinearEquiv.extendScalarsOfIsLocalization`.

The base ring, the algebra and the module are taken in one universe, which is what Stacks 05IA
and `Module.CompleteDevissage.localizeAtPrime` need.

## References

* [Stacks Project, Tag 05IB](https://stacks.math.columbia.edu/tag/05IB)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HY](https://stacks.math.columbia.edu/tag/05HY)
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped DirectSum

universe u v w

namespace Stacks.Flatness

/-- **Flatness over the base survives a further localization.** If the localization of an
`A`-module `M` at a multiplicative set `T₁` is flat over a base ring `R`, then so is its
localization at any larger multiplicative set `T₂`.

The localization at `T₂` is a localization of the localization at `T₁`
(`IsLocalizedModule.liftOfLE`), and localizing a module flat over `R` at a multiplicative set of
`A` keeps it flat over `R` (`Stacks.UniversalInjectivity.flat_localizedModule`). -/
public theorem flat_localizedModule_of_le {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    {T₁ T₂ : Submonoid A} (h : T₁ ≤ T₂)
    (hflat : Module.Flat R (LocalizedModule T₁ M)) :
    Module.Flat R (LocalizedModule T₂ M) := by
  let := hflat
  have h2 : Module.Flat R (LocalizedModule T₂ (LocalizedModule T₁ M)) :=
    Stacks.UniversalInjectivity.flat_localizedModule T₂
  exact (Module.Flat.equiv_iff
    ((IsLocalizedModule.linearEquiv T₂ (LocalizedModule.liftOfLE T₁ T₂ h)
      (LocalizedModule.mkLinearMap T₂ (LocalizedModule T₁ M))).restrictScalars R)).mpr h2

end Stacks.Flatness

namespace Module.CompleteDevissage

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FinitePresentation R S] [AddCommGroup N] [Module S N] [Module R N]
  [IsScalarTower R S N] [Module.FinitePresentation S N] [Module.Flat R N]
  {r : Ideal R} [r.IsPrime]

/-- If `P` acts on `M` through an `R`-algebra `Q` acting on `M`, then `R` and `P` act compatibly. -/
private theorem isScalarTower_of_smul_eq_algebraMap_smul {R P M : Type*} (Q : Type*)
    [CommSemiring R] [CommSemiring P] [CommSemiring Q] [Algebra R P] [Algebra P Q] [Algebra R Q]
    [IsScalarTower R P Q] [AddCommMonoid M] [Module Q M] [Module R M] [IsScalarTower R Q M]
    [Module P M] (h : ∀ (x : P) (m : M), x • m = algebraMap P Q x • m) :
    IsScalarTower R P M :=
  IsScalarTower.of_algebraMap_smul fun x m => by
    rw [h, ← IsScalarTower.algebraMap_apply R P Q, IsScalarTower.algebraMap_smul]

/-- **The stagewise flatness of Stacks 05IB, at the fibre primes, over a general base.** Let `N`
be a finitely presented module over a finitely presented `R`-algebra `S`, flat over `R`, with a
complete dévissage over a prime `r` of `R`. Then every stage module, localized at the complement
of the generic point `rBᵢ` of the fibre of its lower algebra over `r`, is flat over `R`.

This is the hypothesis Stacks 05IA asks for at each stage. It is obtained from the local case
rather than from the recursion of Stacks 05I4: the dévissage base changes to the local ring `R_r`
by `Module.CompleteDevissage.localizeAtPrime`, where `Module.CompleteDevissage.flat_stageModule`
gives global flatness of the stage modules over `R_r`, hence over `R`, and
`Stacks.Flatness.flat_localizedModule_of_le` passes from the localization at the image of
`R ∖ r` to the larger localization at the complement of `rBᵢ`. -/
public theorem flat_localizedModule_fibrePrime (D : CompleteDevissage R S N r)
    (i : Fin (D.stepCount + 1)) :
    letI : Module R (D.M i) := Module.compHom (D.M i) (algebraMap R (D.A i))
    letI : IsScalarTower R (D.B i) (D.M i) :=
      Module.isScalarTower_compHom R (D.B i) (D.A i) (D.M i) (D.toLeft i)
    Module.Flat R (LocalizedModule (Ideal.map (algebraMap R (D.B i)) r).primeCompl (D.M i)) := by
  let _ : Module R (D.M i) := Module.compHom (D.M i) (algebraMap R (D.A i))
  let _ : IsScalarTower R (D.B i) (D.M i) :=
    Module.isScalarTower_compHom R (D.B i) (D.A i) (D.M i) (D.toLeft i)
  let _ : IsScalarTower R (D.A i) (D.M i) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- the dévissage over the local ring at `r`
  let _ : Module (Localization r.primeCompl)
      (LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) N) :=
    Module.compHom _ (algebraMap (Localization r.primeCompl)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)))
  have _ : IsScalarTower (Localization r.primeCompl)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower R (Localization r.primeCompl)
      (LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) N) :=
    isScalarTower_of_smul_eq_algebraMap_smul (Localization (Algebra.algebraMapSubmonoid S
      r.primeCompl)) fun _ _ => rfl
  have _ : IsLocalizedModule r.primeCompl
      ((LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid S r.primeCompl) N).restrictScalars R) :=
    IsLocalizedModule.restrictScalars _ _
  have hNflat : Module.Flat (Localization r.primeCompl)
      (LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) N) :=
    Module.Flat.of_isLocalizedModule _ r.primeCompl
      ((LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid S r.primeCompl) N).restrictScalars R)
  have hmax : Ideal.map (algebraMap R (Localization r.primeCompl)) r
      = IsLocalRing.maximalIdeal (Localization r.primeCompl) :=
    Localization.AtPrime.map_eq_maximalIdeal
  let : Module (Localization r.primeCompl) (D.locM i) :=
    Module.compHom (D.locM i) (algebraMap (Localization r.primeCompl) (D.locA i))
  have hstage : Module.Flat (Localization r.primeCompl) (D.locM i) :=
    D.localizeAtPrime.flat_stageModule hmax i
  have _ : IsScalarTower R (Localization r.primeCompl) (D.locM i) :=
    isScalarTower_of_smul_eq_algebraMap_smul (D.locA i) fun _ _ => rfl
  have hflatR : Module.Flat R (D.locM i) :=
    Module.Flat.trans R (Localization r.primeCompl) (D.locM i)
  -- the complement of the fibre prime is a larger multiplicative set
  have hle : Algebra.algebraMapSubmonoid (D.A i) r.primeCompl ≤
      Algebra.algebraMapSubmonoid (D.A i)
        (Ideal.map (algebraMap R (D.B i)) r).primeCompl := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨algebraMap R (D.B i) t,
      Set.disjoint_left.mp (D.disjoint_map i) ⟨t, ht, rfl⟩,
      (IsScalarTower.algebraMap_apply R (D.B i) (D.A i) t).symm⟩
  have hT₂ := Stacks.Flatness.flat_localizedModule_of_le (R := R) hle hflatR
  have _ : IsLocalizedModule (Ideal.map (algebraMap R (D.B i)) r).primeCompl
      ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (D.A i)
        (Ideal.map (algebraMap R (D.B i)) r).primeCompl) (D.M i)).restrictScalars (D.B i)) :=
    IsLocalizedModule.restrictScalars _ _
  exact (Module.Flat.equiv_iff ((IsLocalizedModule.linearEquiv
    (Ideal.map (algebraMap R (D.B i)) r).primeCompl
    (LocalizedModule.mkLinearMap (Ideal.map (algebraMap R (D.B i)) r).primeCompl (D.M i))
    ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (D.A i)
      (Ideal.map (algebraMap R (D.B i)) r).primeCompl)
      (D.M i)).restrictScalars (D.B i))).restrictScalars R)).mpr hT₂

/-- **The element of Stacks 05IB.** Let `N` be a finitely presented module over a finitely
presented `R`-algebra `S`, flat over `R`, with a complete dévissage over a prime `r` of `R`. Then
there is an `a ∈ R`, `a ∉ r`, such that every stage map of the dévissage becomes injective after
inverting `a`.

This is `Module.CompleteDevissage.exists_away_injective_alpha_of_flat_localizedModule` at the
fibre primes `rBᵢ`, which lie over `r` by `Module.CompleteDevissage.comap_map_eq` and at which the
stage modules are flat over `R` by
`Module.CompleteDevissage.flat_localizedModule_fibrePrime`. -/
public theorem exists_away_injective_alpha (D : CompleteDevissage R S N r) :
    ∃ a ∈ r.primeCompl, ∀ i, Function.Injective (D.locAwayAlpha a i) :=
  D.exists_away_injective_alpha_of_flat_localizedModule
    (fun i => Ideal.map (algebraMap R (D.B i)) r) (fun i => D.map_isPrime i)
    (fun i => by rw [Ideal.under_def]; exact D.comap_map_eq i)
    fun i => D.flat_localizedModule_fibrePrime i

/-- **Stacks Project, Tag 05IB.** Let `N` be a finitely presented module over a finitely
presented `R`-algebra `S` which is flat over `R`, and let `N/S/R` admit a complete dévissage over
a prime `r` of `R`. Then there is an `a ∈ R` outside `r` such that, over `R_a`, the stage algebras
of the dévissage stay smooth with geometrically irreducible fibres, the module `N_a` is the direct
sum of the finite free modules `(Bᵢ)_a^{⊕ rᵢ}` over them, and `N_a` is projective.

One and the same `a` does all of this: it is the element of
`Module.CompleteDevissage.exists_away_injective_alpha`, after inverting which the away-localized
dévissage (`Module.CompleteDevissage.localizeAwayCanonical`) has injective stage maps, so that
`Module.CompleteDevissage.nonempty_linearEquiv_directSum` gives the decomposition and
`Module.CompleteDevissage.projective_of_injective_alpha` the projectivity, the lower algebras
being projective over the new base by Stacks 05FT
(`Module.CompleteDevissage.projective_lowerAlgebra`). The smoothness and the fibres are the fields
of the away-localized dévissage. -/
@[stacks 05IB "the decomposition and projectivity, over a general base"]
public theorem exists_away_decomposition_projective (D : CompleteDevissage R S N r) :
    ∃ a ∈ r.primeCompl,
      (∀ i, Algebra.Smooth (Localization.Away a) (D.locAwayB a i)) ∧
      (∀ i, GeometricallyIrreducible
        (Spec.map (ofHom (algebraMap (Localization.Away a) (D.locAwayB a i))))) ∧
      Nonempty (LocalizedModule (Submonoid.powers a) N ≃ₗ[Localization.Away a]
        ⨁ i : Fin (D.stepCount + 1), (Fin (D.multiplicity i) →₀ D.locAwayB a i)) ∧
      Module.Projective (Localization.Away a) (LocalizedModule (Submonoid.powers a) N) := by
  obtain ⟨a, ha, hinj⟩ := D.exists_away_injective_alpha
  have _ := Module.CompleteDevissage.isPrime_map_algebraMap_powers (r := r) (a := a) ha
  let _ : Module (Localization.Away a)
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) :=
    Module.compHom _ (algebraMap (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))))
  have _ : IsScalarTower (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower R (Localization.Away a)
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N) :=
    isScalarTower_of_smul_eq_algebraMap_smul
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))) fun _ _ => rfl
  have _ : IsLocalizedModule (Submonoid.powers a)
      ((LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N).restrictScalars R) :=
    IsLocalizedModule.restrictScalars _ _
  set D' := D.localizeAwayCanonical a ha
  set eN := LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers a) (Localization.Away a)
    (IsLocalizedModule.linearEquiv (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) N)
      ((LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N).restrictScalars R))
  refine ⟨a, ha, fun i => D'.smooth i, fun i => D'.geometricallyIrreducibleFibers i, ?_, ?_⟩
  · obtain ⟨e⟩ := D'.nonempty_linearEquiv_directSum hinj fun i => D'.projective_lowerAlgebra i
    exact ⟨eN ≪≫ₗ e⟩
  · have := D'.projective_of_injective_alpha hinj
    exact Module.Projective.of_equiv' eN.symm

end Module.CompleteDevissage
