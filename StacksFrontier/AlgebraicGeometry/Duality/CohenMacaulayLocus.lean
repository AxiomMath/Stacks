module

public import StacksFrontier.Algebra.Module.LocalizedRingEquiv
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
import StacksFrontier.RingTheory.Dualizing.NormalizedShift
import all StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle

/-!
# Cohen–Macaulay schemes with a dualizing complex

Let `X` be a locally Noetherian scheme carrying a dualizing complex `ω_X^•`
(`Stacks.Duality.IsDualizingComplex`, [Stacks, Tag 0A87]). This file proves [Stacks, Tag 0AWT]:
the local ring at `x` is Cohen–Macaulay exactly when the derived stalk `ω_{X,x}^•` has a single
nonzero cohomology module; `X` is Cohen–Macaulay exactly when `ω_X^•` locally has a single
nonzero cohomology sheaf; the Cohen–Macaulay locus is open and is a Cohen–Macaulay scheme; and
on a connected Cohen–Macaulay `X` the complex is a single coherent module in a single degree,
`ω_X^• = ω_X[-n]`.

## Main results

* `Stacks.Duality.isCohenMacaulayLocalRing_iff_concentrated` — the ring-level engine:
  [Stacks, Tag 0AWS] with the normalization hypothesis removed. A Noetherian local ring with a
  dualizing complex is Cohen–Macaulay exactly when that complex is concentrated in one degree.
* `Stacks.Duality.isCohenMacaulayLocalRing_localization_iff` — the same at a localization of a
  Noetherian ring with a dualizing complex, phrased on the localizations of the cohomology
  modules.
* `Stacks.Duality.isOpen_isCohenMacaulayLocalRing_localization` — the ring-level statement: for a
  Noetherian ring admitting a dualizing complex, the set of primes whose localization is a
  Cohen–Macaulay local ring is open in the prime spectrum. This is [Stacks, Tag 0EHS] read at the
  module `A` itself and re-expressed in terms of `IsCohenMacaulayLocalRing`; it is the exact
  analogue, for Cohen–Macaulayness, of `Dualizing.isOpen_gorensteinLocus`.
* `Stacks.Duality.isOpen_setOf_isCohenMacaulayLocalRing` — **[Stacks, Tag 0AWT], clause (3),
  openness.**
* `Stacks.Duality.isCohenMacaulay_cohenMacaulayLocus` — **[Stacks, Tag 0AWT], clause (3), the
  locus is Cohen–Macaulay.**
* `Stacks.Duality.isCohenMacaulayLocalRing_stalk_iff_stalkwise` and
  `Stacks.Duality.isCohenMacaulayLocalRing_stalk_iff_concentrated` — **[Stacks, Tag 0AWT],
  clause (2)**, on the stalks of the cohomology sheaves and on the derived stalk respectively.
* `Stacks.Duality.isCohenMacaulay_iff_locally_unique_homology` — **[Stacks, Tag 0AWT],
  clause (1).**
* `Stacks.Duality.exists_coherent_iso_single_of_connected` — **[Stacks, Tag 0AWT], the final
  assertion**, less the Cohen–Macaulayness of `ω_X`; see below.

## Implementation notes

*Clause (2) and the derived stalk.* The stalk functor on `D(𝒪_X)` is
`AlgebraicGeometry.derivedStalkFunctor`, the stalk functor
`Stacks.ModuleSkyscraper.modulesStalkFunctor` read on derived categories; it was already
available, with free model binders for both derived categories. Vanishing of the degree `i`
cohomology of the derived stalk is vanishing of the stalk of the degree `i` cohomology sheaf, by
`Dualizing.mapDerivedCategoryHomologyIso`, so clause (2) is proved in the latter form and
restated in the former. The affine translation table
`Stacks.Duality.exists_model_stalk_translation` is the proof of
`Stacks.Duality.isFiniteTildeOn_homology_of_hasDualizingModelOn` with the dualizing model kept
fixed across all degrees — necessary, because that lemma's existential loses the identity of the
model, while the criterion needs one model serving every degree. From there the stalk of the
cohomology sheaf is the localization of its sections
(`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ` through
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections`), and
`Dualizing.localizedHomologyAtPrimeIsoGeneric` identifies that with the cohomology of the derived
localization of the model, which is a dualizing complex by [Stacks, Tag 0A7G].

*What the final assertion does not include.* The source also asserts that `ω_X = H^n(ω_X^•)` is a
Cohen–Macaulay module in the sense of [Stacks, Tag 0343], i.e. that `ω_{X,x}` is a Cohen–Macaulay
`𝒪_{X,x}`-module for every `x`. That clause is **absent** from
`Stacks.Duality.exists_coherent_iso_single_of_connected`, whose conclusion is coherence of `ω_X`
and the isomorphism `ω_X^• ≅ ω_X[-n]`. It is **no longer missing from the development**: it is
`Stacks.Duality.sheafIsCohenMacaulay_homology_of_concentrated` of
`StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayDualizingModule.lean`, and the final assertion
with that clause included is
`Stacks.Duality.exists_coherent_cohenMacaulay_iso_single_of_connected` there. The note below
describing the identification it needs as the real content of the clause and as not done is
corrected at its last bullet.

*The predicate the clause needs does exist.* It is
`AlgebraicGeometry.SheafIsCohenMacaulay` in
`StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/Depth.lean`, which carries the attribute
`@[stacks 0343]`: a sheaf of modules is Cohen–Macaulay when it satisfies Serre's condition
`(S_k)` of [Stacks, Tag 0341] for every `k`, read stalkwise as
`min k (dim Supp(ℱ_x)) ≤ depth_{𝒪_{X,x}}(ℱ_x)` at every `x`. It is stated for a
`SheafOfModules (structureSheafRing X.toRingedSpace)`,
which is `X.Modules` by `rfl`, so it applies to `H^n(ω_X^•)` with no retyping. An earlier
revision of this note said the development had no such predicate; that was wrong.

*What is actually missing is the transport.* `Dualizing.dualizingModule_isMaximalCohenMacaulay`
(the corresponding clause of [Stacks, Tag 0AWS]) concludes
`Module.IsMaximalCohenMacaulay A (dualizingModule K)` over a *local ring* `A` carrying a
*normalized* dualizing complex, and it has to be read at `𝒪_{X,x}` and `ω_{X,x}`. Two steps
separate those:

* **The semilinear transport, which is now done.** `𝒪_{X,x}` is only isomorphic to
  `Γ(X, U)_𝔭` (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), and `ω_{X,x}` is only
  semilinearly isomorphic to `Γ(U, ω_X)_𝔭`
  (`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`, with the scalar tower
  `Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk`). The transport of maximal
  Cohen–Macaulayness across exactly that data is
  `Module.isMaximalCohenMacaulay_of_semilinearEquiv` in
  `StacksFrontier/RingTheory/Depth/SemilinearEquivCohenMacaulay.lean`, and
  `Module.min_supportDim_le_depth_of_isMaximalCohenMacaulay` there turns its conclusion into the
  `(S_k)` inequality `AlgebraicGeometry.SheafHasPropertySk` asks for, for every `k`, so no
  transport of `Module.supportDim` is needed. The two isomorphisms that those
  `IsLocalization`/`IsLocalizedModule` facts determine, and the semilinearity relating them, are
  now written down in
  `StacksFrontier/AlgebraicGeometry/Scheme/Points/StalkSemilinearLocalization.lean`:
  `Stacks.ModuleStalkSpecialization.stalkRingEquiv`,
  `Stacks.ModuleStalkSpecialization.stalkLinearEquiv` and
  `Stacks.ModuleStalkSpecialization.stalkLinearEquiv_smul` — the last for the action of the whole
  local ring, which is what the transport consumes and which `Γ(X, U)`-linearity does not give.
  `Stacks.ModuleStalkSpecialization.isMaximalCohenMacaulay_stalk` and
  `Stacks.ModuleStalkSpecialization.min_supportDim_le_depth_stalk` are the two transports
  themselves, the second stated exactly in the shape `AlgebraicGeometry.SheafHasPropertySk` asks
  for at a point. So this half of the clause is no longer owed: what is owed is the *hypothesis*
  of those two, namely maximal Cohen–Macaulayness over `Γ(X, U)_𝔭` of the localized sections of
  `ω_X`, which is the next item.
* **The identification of `ω_{X,x}` with a dualizing module, which is now done.**
  `Dualizing.dualizingModule K` is `H^{-dim A}(K)` for a *normalized* `K`, while the degree `n`
  here comes from `Stacks.Duality.exists_coherent_iso_single_of_connected` and is the same at
  every point of a connected `X`. It is
  `Dualizing.isMaximalCohenMacaulay_homology_of_concentrated` of
  `StacksFrontier/RingTheory/Dualizing/ConcentratedDualizingModule.lean`, which states the final
  clause of [Stacks, Tag 0AWS] for a dualizing complex concentrated in an *arbitrary* degree: the
  normalizing shift of `StacksFrontier/RingTheory/Dualizing/NormalizedShift.lean` moves the single
  nonvanishing degree without creating a second one, and a dualizing complex over a Noetherian
  local ring is nonzero, so the shift between `n` and `-dim A` is determined rather than assumed.
  Read at the derived localization of the affine model
  (`Stacks.Duality.exists_specModule_homology_iso`,
  `Dualizing.localizedHomologyAtPrimeIsoGeneric`) it supplies exactly the hypothesis the previous
  bullet is waiting for; the two are joined in
  `StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayDualizingModule.lean`.

*Clause (1) is read stalkwise.* "`ω_X^•` locally has a unique nonzero cohomology sheaf" is
rendered as: every point has an open neighbourhood on which all cohomology sheaves but one have
vanishing stalks. That is equivalent to the vanishing of the restricted sheaves by
[Stacks, Tag 01AG]
(`AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj`), which is what the
proof of the final assertion uses to pass from vanishing stalks everywhere to a vanishing
cohomology sheaf; the stalk of a *restriction* to an open subscheme is not identified with the
stalk of the sheaf anywhere in this development, which is why the neighbourhood form is stated
stalkwise rather than as `IsZero ((H^i K).restrict V.ι)`.

The source deduces openness from clause (2), the stalkwise criterion, by shrinking an affine
neighbourhood until a single cohomology sheaf survives. The route taken here is shorter and
needs none of clause (2): a dualizing complex on `X` restricts, at every affine open `U`, to the
associated sheaf of a dualizing complex over `Γ(X, U)` — that is the *definition* of
`Stacks.Duality.IsDualizingComplex` — so `Γ(X, U)` is a Noetherian ring *admitting* a dualizing
complex, which is all the hypothesis of [Stacks, Tag 0EHS] asks for. Only the existence of the
model is used; the isomorphism it comes with is discarded. Openness is therefore a purely
ring-theoretic fact transported along the homeomorphism `U ≅ Spec Γ(X, U)`, and the identification
of the stalk at a point of `U` with the localization at the corresponding prime is
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`. Since
`AlgebraicGeometry.IsAffineOpen.primeIdealOf` is by definition the value of
`AlgebraicGeometry.IsAffineOpen.isoSpec` at the point, the comparison map whose continuity is
used is the one the prime is produced by.

[Stacks, Tag 0EHS] states openness *inside the support* of the module, on the subtype of primes
in the support. For the module `A` the support is all of `Spec A`, hence open, so the image of
that relatively open set under `Subtype.val` is open in `Spec A`; this is the only reason the
support appears below. The locus of [Stacks, Tag 0EHS] is phrased with
`Module.IsCohenMacaulayAtMaximalIdeal (A_p) (LocalizedModule.AtPrime p A)`, which is compared with
`IsCohenMacaulayLocalRing (A_p)` by the `A_p`-linear equivalence
`LocalizedModule.AtPrime p A ≃ₗ A_p` — localizing a ring as a module over itself gives the
localized ring.

One helper below is a duplicate of a declaration that is `private` in the module that proves
it, reproduced here because a `private` declaration cannot be used from another module:

* `Stacks.Duality.support_self_eq_univ` is the `show` step inside the private lemma
  `moduleSupportDim_self_eq_ringKrullDim` of `StacksFrontier/Algebra/Module/Reflexive.lean`.

The equivalence `localizedRingEquiv` is public, in
`StacksFrontier/Algebra/Module/LocalizedRingEquiv.lean`, and is used from there.

Nothing in those modules is edited.

The derived category of `X.Modules` is an instance *argument*, matching
`Stacks.Duality.IsDualizingComplex`, so the results read at whatever model the caller works in.
The two derived categories that `Stacks.Duality.HasDualizingModelOn` chooses internally at
`HasDerivedCategory.standard` must be reintroduced by any proof that destructs it, which is what
the two instance-introducing `let`s in `exists_isDualizingComplex_sections` do.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 0343](https://stacks.math.columbia.edu/tag/0343)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AWR](https://stacks.math.columbia.edu/tag/0AWR)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 0EHS](https://stacks.math.columbia.edu/tag/0EHS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u w

namespace Stacks.Duality

section RingLevel

attribute [local instance] HasDerivedCategory.standard

/-- The Cohen–Macaulay condition of [Stacks, Tag 0EHS] at the module `A` itself is
Cohen–Macaulayness of the localized ring: `LocalizedModule.AtPrime p A` is `A_p`. -/
private lemma isCohenMacaulayAtMaximalIdeal_localizedModule_iff {A : Type u} [CommRing A]
    [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p)
        (LocalizedModule.AtPrime p A) ↔
      IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  rw [_root_.isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay,
    Module.IsCohenMacaulayAtMaximalIdeal, Module.IsMaximalCohenMacaulay,
    Module.depth_eq_depth_of_linearEquiv _ (localizedRingEquiv p),
    Module.supportDim_eq_of_equiv (localizedRingEquiv p),
    Module.supportDim_self_eq_ringKrullDim]

/-- Shifting a complex shifts its cohomology: `H^i(K⟦m⟧) = H^{m+i}(K)`. This is the shift
sequence of `DerivedCategory.homologyFunctor`, whose degree-`i` member is the `i`-th shift of
the degree-zero one by `DerivedCategory.homologyFunctor_shift`. -/
private def homologyShiftObjIso {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m i j : ℤ) (h : m + i = j) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦m⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso m i j h).app K

/-- Being concentrated in one cohomological degree is invariant under shifting. -/
private lemma concentrated_shift_iff {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    Dualizing.IsCohomologicallyConcentratedInOneDegree (K⟦m⟧) ↔
      Dualizing.IsCohomologicallyConcentratedInOneDegree K := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨m + n, fun i hi =>
      (hn (i - m) (by omega)).of_iso (homologyShiftObjIso K m (i - m) i (by omega)).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n - m, fun i hi =>
      (hn (m + i) (by omega)).of_iso (homologyShiftObjIso K m i (m + i) rfl)⟩

/-- **A Noetherian local ring with a dualizing complex is Cohen–Macaulay exactly when the
complex is concentrated in one cohomological degree.** This is [Stacks, Tag 0AWS] with the
normalization hypothesis removed: some shift of `K` is normalized
(`Dualizing.exists_isNormalizedDualizingComplex_shift`) and concentration in one degree is
shift-invariant. -/
public theorem isCohenMacaulayLocalRing_iff_concentrated {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) :
    IsCohenMacaulayLocalRing A ↔ Dualizing.IsCohomologicallyConcentratedInOneDegree K := by
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, 0} K hK
  exact ((Dualizing.isCohenMacaulay_tfae_dualizingComplex (K⟦-m⟧) hm).out 1 2).trans
    (concentrated_shift_iff K (-m))

/-- Restriction of scalars does not change the carrier, so it does not change vanishing. -/
private lemma isZero_restrictScalars_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} S) :
    Limits.IsZero ((ModuleCat.restrictScalars f).obj M) ↔ Limits.IsZero M := by
  simp only [ModuleCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-- The cohomology of the derived localization at `p` vanishes exactly when the localization at
`p` of the cohomology does. This is `Dualizing.localizedHomologyAtPrimeIsoGeneric`, read through
`ModuleCat.isZero_iff_subsingleton`. -/
private lemma isZero_localizedHomology_iff {A : Type u} [CommRing A]
    (p : Ideal A) [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.AtPrime p)) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap A (Localization.AtPrime p))).obj K)) ↔
      Subsingleton (LocalizedModule p.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) := by
  rw [← isZero_restrictScalars_iff (algebraMap A (Localization.AtPrime p)),
    ← (Dualizing.localizedHomologyAtPrimeIsoGeneric p K i).isZero_iff,
    ModuleCat.isZero_iff_subsingleton]

/-- **A localization of a Noetherian ring with a dualizing complex is Cohen–Macaulay exactly when
the cohomology of the complex localizes to zero in all but one degree.** This is
`Stacks.Duality.isCohenMacaulayLocalRing_iff_concentrated` applied to the derived localization of
the complex, which is dualizing by [Stacks, Tag 0A7G]. -/
public theorem isCohenMacaulayLocalRing_localization_iff {A : Type u} [CommRing A]
    [IsNoetherianRing A] (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsDualizingComplex ω) (p : Ideal A) [p.IsPrime] :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) ↔
      ∃ n : ℤ, ∀ i : ℤ, i ≠ n → Subsingleton (LocalizedModule p.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)) := by
  let : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have hL : Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p))).obj ω) :=
    Dualizing.isDualizingComplex_localization p.primeCompl ω hω
  rw [isCohenMacaulayLocalRing_iff_concentrated _ hL]
  exact exists_congr fun n => forall_congr' fun i => imp_congr_right fun _ =>
    isZero_localizedHomology_iff p ω i

/-- **The Cohen–Macaulay locus of a Noetherian ring with a dualizing complex is open.** This is
[Stacks, Tag 0EHS] read at the module `A` itself: the support is then all of `Spec A`, so
relative openness in the support is openness in the spectrum. -/
public theorem isOpen_isCohenMacaulayLocalRing_localization {A : Type u} [CommRing A]
    [IsNoetherianRing A] (ω : DerivedCategory (ModuleCat.{w} A))
    (hω : Dualizing.IsDualizingComplex ω) :
    IsOpen {p : PrimeSpectrum A | IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal)} := by
  have hsupp : Module.support A A = Set.univ := Module.support_self A
  have hopenSupp : IsOpen (Module.support A A) := by rw [hsupp]; exact isOpen_univ
  have h := Dualizing.isOpen_cohenMacaulayLocus (A := A) (M := A) ω hω
  have himg := hopenSupp.isOpenMap_subtype_val _ h
  convert himg using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p, hsupp ▸ Set.mem_univ p⟩,
      (isCohenMacaulayAtMaximalIdeal_localizedModule_iff p.asIdeal).mpr hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact (isCohenMacaulayAtMaximalIdeal_localizedModule_iff (q : PrimeSpectrum A).asIdeal).mp hq

end RingLevel

/-- An affine open of a locally Noetherian scheme carrying a dualizing complex has a Noetherian
ring of sections which admits a dualizing complex.

Only the *existence* of the dualizing model of `Stacks.Duality.HasDualizingModelOn` is used; the
isomorphism it carries is discarded. -/
private lemma exists_isDualizingComplex_sections {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (U : X.Opens) (hU : IsAffineOpen U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, -⟩ := hK U hU
  exact ⟨ω, hω⟩

/-- Cohen–Macaulayness of the stalk at a point of an affine open is Cohen–Macaulayness of the
localization at the prime the point defines. -/
private lemma isCohenMacaulayLocalRing_stalk_iff_localization {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      IsCohenMacaulayLocalRing (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  exact _root_.isCohenMacaulayLocalRing_iff_of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x)
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)).toRingEquiv

/-- On a locally Noetherian scheme, being Cohen–Macaulay is having Cohen–Macaulay local rings. -/
private lemma isCohenMacaulay_of_forall_isCohenMacaulayLocalRing_stalk {X : Scheme.{u}}
    [IsLocallyNoetherian X] (h : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x)) :
    AlgebraicGeometry.IsCohenMacaulay X := by
  have hstalk : IsLocallyNoetherian X ∧
      ∀ x : X, ∃ hh : IsNoetherianRing (X.presheaf.stalk x),
        @IsCohenMacaulayLocalRing (X.presheaf.stalk x) _ hh _ :=
    ⟨inferInstance, fun x => ⟨inferInstance, h x⟩⟩
  exact ((AlgebraicGeometry.isCohenMacaulay_tfae_stalk X).out 2 1).mp hstalk

/-- The local rings of a Cohen–Macaulay scheme are Cohen–Macaulay. -/
private lemma isCohenMacaulayLocalRing_stalk_of_isCohenMacaulay {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : AlgebraicGeometry.IsCohenMacaulay X) (x : X) :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) := by
  obtain ⟨-, hCM⟩ := ((AlgebraicGeometry.isCohenMacaulay_tfae_stalk X).out 1 2).mp hX
  obtain ⟨_, hx⟩ := hCM x
  exact hx

/-- **Stacks Project, Tag 0AWT, clause (3), openness.** On a locally Noetherian scheme carrying a
dualizing complex, the set of points whose local ring is Cohen–Macaulay is open. -/
@[stacks 0AWT "clause (3), the Cohen--Macaulay locus is open"]
public theorem isOpen_setOf_isCohenMacaulayLocalRing {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    IsOpen {x : X | IsCohenMacaulayLocalRing (X.presheaf.stalk x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, V))
  obtain ⟨ω, hω⟩ := exists_isDualizingComplex_sections hK V hV
  -- The Cohen–Macaulay locus in `Spec Γ(X, V)`.
  set W : Set (PrimeSpectrum Γ(X, V)) :=
    {p : PrimeSpectrum Γ(X, V) | IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal)}
    with hWdef
  have hWopen : IsOpen W := isOpen_isCohenMacaulayLocalRing_localization ω hω
  -- Cohen–Macaulayness of the stalk at a point of `V` is a statement about the prime it defines.
  have hstalk : ∀ y : V, IsCohenMacaulayLocalRing (X.presheaf.stalk y.1) ↔
      hV.primeIdealOf y ∈ W := fun y => isCohenMacaulayLocalRing_stalk_iff_localization hV y.2
  -- Transport `W` back to an open subset of `V`, then to an open subset of `X`.
  have hpre : IsOpen (hV.isoSpec.hom.base ⁻¹' W) := hWopen.preimage hV.isoSpec.hom.base.hom.2
  refine ⟨Subtype.val '' (hV.isoSpec.hom.base ⁻¹' W), ?_, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact (hstalk y).mpr hy
  · exact V.2.isOpenMap_subtype_val _ hpre
  · exact ⟨⟨x, hxV⟩, (hstalk ⟨x, hxV⟩).mp hx, rfl⟩

/-- The Cohen–Macaulay locus of a locally Noetherian scheme carrying a dualizing complex, as an
open subset. -/
public def cohenMacaulayLocus {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) : X.Opens :=
  ⟨{x : X | IsCohenMacaulayLocalRing (X.presheaf.stalk x)},
    isOpen_setOf_isCohenMacaulayLocalRing K hK⟩

/-- A point lies in `cohenMacaulayLocus K hK` if and only if its local ring is Cohen–Macaulay. -/
@[simp]
public theorem mem_cohenMacaulayLocus {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) (x : X) :
    x ∈ cohenMacaulayLocus K hK ↔ IsCohenMacaulayLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- **Stacks Project, Tag 0AWT, clause (3), the locus is Cohen–Macaulay.** The open subscheme of
points with Cohen–Macaulay local ring is a Cohen–Macaulay scheme. -/
@[stacks 0AWT "clause (3), the Cohen--Macaulay locus is Cohen--Macaulay"]
public theorem isCohenMacaulay_cohenMacaulayLocus {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    AlgebraicGeometry.IsCohenMacaulay (cohenMacaulayLocus K hK).toScheme := by
  exact isCohenMacaulay_of_forall_isCohenMacaulayLocalRing_stalk fun x =>
    (_root_.isCohenMacaulayLocalRing_iff_of_ringEquiv
      ((cohenMacaulayLocus K hK).stalkIso x).commRingCatIsoToRingEquiv).mpr x.2

section StalkwiseCriterion

open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

/-- From an identification of `F|_U` with the pullback of `N^~` along `U ≅ Spec Γ(X, U)`, the
module `Stacks.AlgebraicGeometry.CoherentTFAE.specModule` of sections of `F` over the affine
open `U` is `N`. -/
private noncomputable def specModuleIsoOfTildeIso {X : Scheme.{u}} (F : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) (N : ModuleCat.{u} Γ(X, U))
    (e : F.restrict U.ι ≅ (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde N)) :
    specModule F hU ≅ N :=
  (Scheme.Modules.restrictFunctor hU.isoSpec.inv ⋙ moduleSpecΓFunctor).mapIso e ≪≫
    moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app (tilde N)).symm) ≪≫
    moduleSpecΓFunctor.mapIso (restrictIsoSelf hU.isoSpec.symm (tilde N)) ≪≫
    (tilde.toTildeΓNatIso.app N).symm

/-- **A dualizing model at an affine open computes the sections of every cohomology sheaf.**
This is the proof of `Stacks.Duality.isFiniteTildeOn_homology_of_hasDualizingModelOn` with the
model `ω` kept fixed across all degrees, which is what the stalkwise criterion needs. -/
private lemma exists_specModule_homology_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    {U : X.Opens} (hU : IsAffineOpen U) (h : HasDualizingModelOn K U hU) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω ∧
      ∀ i : ℤ, Nonempty (specModule ((DerivedCategory.homologyFunctor X.Modules i).obj K) hU ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  refine ⟨ω, hω, fun i => ⟨specModuleIsoOfTildeIso _ hU _ ?_⟩⟩
  exact ((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (Dualizing.mapDerivedCategoryHomologyIso
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _

/-- Localization at a submonoid turns a linear equivalence into an equivalence, so it does not
change subsingleton-ness. -/
private lemma subsingleton_localizedModule_congr {R : Type*} [CommRing R] (S : Submonoid R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    Subsingleton (LocalizedModule S M) ↔ Subsingleton (LocalizedModule S N) :=
  Equiv.subsingleton_congr (IsLocalizedModule.iso S
    ((LocalizedModule.mkLinearMap S N).comp (e : M →ₗ[R] N))).toEquiv

/-- **The stalk of a quasi-coherent module at a point of an affine open is the localization of
its module of sections.** This is `Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`
transported along `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections`,
read only through subsingleton-ness. -/
private lemma subsingleton_stalk_iff_subsingleton_localizedSpecModule {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) :
    Subsingleton (F.presheaf.stalk x) ↔
      Subsingleton (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        (specModule F hU)) := by
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hx
  have : IsLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.germₗ F hx) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ F hU hx
  exact (Equiv.subsingleton_congr (IsLocalizedModule.iso
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    ((Stacks.ModuleStalkSpecialization.germₗ F hx).comp
      (specModuleIsoSections F ⟨U, hU⟩).toLinearEquiv.toLinearMap)).toEquiv).symm

/-- Vanishing of the degree `i` cohomology of the derived stalk of `K` at `x` is vanishing of
the stalk at `x` of the degree `i` cohomology sheaf of `K`. The derived stalk functor is the
stalk functor read on derived categories, and an exact functor commutes with cohomology. -/
private lemma isZero_homology_derivedStalk_iff {X : Scheme.{u}}
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules) (x : X)
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))] (i : ℤ) :
    Limits.IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
        ((AlgebraicGeometry.derivedStalkFunctor x).obj K)) ↔
      Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk x) := by
  have h1 : Limits.IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
        ((AlgebraicGeometry.derivedStalkFunctor x).obj K)) ↔
      Limits.IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :=
    ((Dualizing.mapDerivedCategoryHomologyIso
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x) i).app K).isZero_iff
  exact h1.trans ModuleCat.isZero_iff_subsingleton

/-- **The affine translation table.** At an affine open `U` of a locally Noetherian scheme
carrying a dualizing complex there is a dualizing complex `ω` over `Γ(X, U)` such that, at every
point `y` of `U` and in every degree `i`, the stalk at `y` of the `i`-th cohomology sheaf of `K`
vanishes exactly when `H^i(ω)` localizes to zero at the prime of `y`. -/
private lemma exists_model_stalk_translation {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) {U : X.Opens} (hU : IsAffineOpen U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω ∧
      ∀ (i : ℤ) (y : X) (hy : y ∈ U),
        (Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y) ↔
          Subsingleton (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω))) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, hiso⟩ := exists_specModule_homology_iso hU (hK U hU)
  refine ⟨ω, hω, fun i y hy => ?_⟩
  have : _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K) :=
    isCoherent_homology_of_isDualizingComplex hK i
  have : ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
    (isQuasicoherent_isFiniteType_of_isCoherent _).1
  exact (subsingleton_stalk_iff_subsingleton_localizedSpecModule _ hU hy).trans
    (subsingleton_localizedModule_congr _ (hiso i).some.toLinearEquiv)

/-- **Stacks Project, Tag 0AWT, clause (2), on the cohomology sheaves.** The local ring at `x` is
Cohen–Macaulay exactly when all but one of the cohomology sheaves of `K` have vanishing stalk at
`x`. -/
public theorem isCohenMacaulayLocalRing_stalk_iff_stalkwise {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) (x : X) :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      ∃ n : ℤ, ∀ i : ℤ, i ≠ n →
        Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk x) := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, htr⟩ := exists_model_stalk_translation hK hU
  let : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  rw [isCohenMacaulayLocalRing_stalk_iff_localization hU hxU,
    isCohenMacaulayLocalRing_localization_iff ω hω (hU.primeIdealOf ⟨x, hxU⟩).asIdeal]
  exact exists_congr fun n => forall_congr' fun i => imp_congr_right fun _ =>
    (htr i x hxU).symm

/-- **Stacks Project, Tag 0AWT, clause (2).** On a locally Noetherian scheme carrying a dualizing
complex `K`, the local ring at `x` is Cohen–Macaulay exactly when the derived stalk `K_x` has a
single nonzero cohomology module. -/
@[stacks 0AWT "clause (2), the stalkwise criterion"]
public theorem isCohenMacaulayLocalRing_stalk_iff_concentrated {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) (x : X)
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))] :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      ∃ n : ℤ, ∀ i : ℤ, i ≠ n → Limits.IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
        ((AlgebraicGeometry.derivedStalkFunctor x).obj K)) :=
  (isCohenMacaulayLocalRing_stalk_iff_stalkwise K hK x).trans
    (exists_congr fun _ => forall_congr' fun i => imp_congr_right fun _ =>
      (isZero_homology_derivedStalk_iff K x i).symm)

/-! ### Shrinking to a neighbourhood on which a single cohomology sheaf survives -/

section RingShrink

attribute [local instance] HasDerivedCategory.standard

/-- A dualizing complex has bounded cohomology: it is isomorphic to a bounded complex of
injectives, so its cohomology vanishes outside a finite interval. -/
private lemma exists_isZero_homology_outside_Icc {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) :
    ∃ a b : ℤ, ∀ i : ℤ, i ∉ Finset.Icc a b →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω) := by
  obtain ⟨a, b, I, hGE, hLE, -, ⟨e⟩⟩ := hω.finiteInjectiveDimension
  have hge : (DerivedCategory.Q.obj I).IsGE a :=
    (DerivedCategory.isGE_Q_obj_iff I a).2 inferInstance
  have hle : (DerivedCategory.Q.obj I).IsLE b :=
    (DerivedCategory.isLE_Q_obj_iff I b).2 inferInstance
  have hωge : ω.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hωle : ω.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  refine ⟨a, b, fun i hi => ?_⟩
  simp only [Finset.mem_Icc, not_and_or, not_le] at hi
  rcases hi with h | h
  · exact DerivedCategory.isZero_of_isGE ω a i h
  · exact DerivedCategory.isZero_of_isLE ω b i h

/-- **The ring-level shrinking step.** If all but the `n`-th cohomology module of a dualizing
complex localize to zero at `p`, then the same holds at every prime of an open neighbourhood of
`p`: only finitely many degrees contribute, and the support of a finite module is closed. -/
private lemma exists_isOpen_subsingleton_localized {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (p : PrimeSpectrum A) (n : ℤ)
    (hn : ∀ i : ℤ, i ≠ n → Subsingleton (LocalizedModule p.asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω))) :
    ∃ W : Set (PrimeSpectrum A), IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, ∀ i : ℤ, i ≠ n →
      Subsingleton (LocalizedModule q.asIdeal.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_isZero_homology_outside_Icc ω hω
  set S := (Finset.Icc a b).erase n with hS
  refine ⟨⋂ i ∈ S, (Module.support A
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω))ᶜ, ?_, ?_, ?_⟩
  · refine isOpen_biInter_finset fun i _ => ?_
    have := hω.finiteCohomology i
    exact (Module.isClosed_support (R := A)
      (M := ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω))).isOpen_compl
  · refine Set.mem_iInter₂.mpr fun i hi hmem => ?_
    exact (not_nontrivial_iff_subsingleton.mpr (hn i (Finset.mem_erase.mp hi).1))
      (Module.mem_support_iff.mp hmem)
  · intro q hq i hi
    by_cases hmem : i ∈ S
    · exact not_nontrivial_iff_subsingleton.mp
        (fun hnt => Set.mem_iInter₂.mp hq i hmem (Module.mem_support_iff.mpr hnt))
    · have hz := hab i (fun h => hmem (Finset.mem_erase.mpr ⟨hi, h⟩))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance

/-- **A dualizing complex over a Noetherian local ring is nonzero.** Its normalized shift has a
nonvanishing cohomology module in degree `-depth(A)` by [Stacks, Tag 0AWR]. -/
private lemma exists_not_isZero_homology {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) :
    ∃ i : ℤ, ¬ Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, 0} K hK
  obtain ⟨δ, hleast, -⟩ := Dualizing.depth_eq_least_nonzero_homology (K⟦-m⟧) hm
  exact ⟨-m + -(δ : ℤ), fun hz =>
    hleast.1 (hz.of_iso (homologyShiftObjIso K (-m) (-(δ : ℤ)) (-m + -(δ : ℤ)) rfl))⟩

/-- Some cohomology module of a dualizing complex survives localization at any prime: the
derived localization is a dualizing complex over the localized ring, by [Stacks, Tag 0A7G]. -/
private lemma exists_not_subsingleton_localized_homology {A : Type u} [CommRing A]
    [IsNoetherianRing A] (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsDualizingComplex ω) (p : Ideal A) [p.IsPrime] :
    ∃ i : ℤ, ¬ Subsingleton (LocalizedModule p.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)) := by
  let : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  obtain ⟨i, hi⟩ := exists_not_isZero_homology
    ((StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A (Localization.AtPrime p))).obj ω)
    (Dualizing.isDualizingComplex_localization p.primeCompl ω hω)
  exact ⟨i, fun hs => hi ((isZero_localizedHomology_iff p ω i).mpr hs)⟩

end RingShrink

/-- **The shrinking step.** If the local ring at `x` is Cohen–Macaulay then on some open
neighbourhood of `x` all cohomology sheaves of `K` but one have vanishing stalks. -/
private lemma exists_nhds_unique_nonzero_homology {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) (x : X)
    (hx : IsCohenMacaulayLocalRing (X.presheaf.stalk x)) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℤ, ∀ i : ℤ, i ≠ n → ∀ y ∈ V,
      Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y) := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, htr⟩ := exists_model_stalk_translation hK hU
  let : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  obtain ⟨n, hn⟩ := (isCohenMacaulayLocalRing_localization_iff ω hω
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal).mp
    ((isCohenMacaulayLocalRing_stalk_iff_localization hU hxU).mp hx)
  obtain ⟨W, hWopen, hpW, hWall⟩ :=
    exists_isOpen_subsingleton_localized ω hω (hU.primeIdealOf ⟨x, hxU⟩) n hn
  have hpre : IsOpen (hU.isoSpec.hom.base ⁻¹' W) := hWopen.preimage hU.isoSpec.hom.base.hom.2
  refine ⟨⟨Subtype.val '' (hU.isoSpec.hom.base ⁻¹' W), U.2.isOpenMap_subtype_val _ hpre⟩,
    ⟨⟨x, hxU⟩, hpW, rfl⟩, n, fun i hi y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hy
  exact (htr i z.1 z.2).mpr (hWall _ hz i hi)

/-- **Stacks Project, Tag 0AWT, clause (1).** A locally Noetherian scheme carrying a dualizing
complex `K` is Cohen–Macaulay exactly when `K` locally has a single nonzero cohomology sheaf:
every point has an open neighbourhood on which, for all but one degree, the cohomology sheaves
of `K` have vanishing stalks.

Vanishing of all the stalks over an open is vanishing of the restricted sheaf there, by
[Stacks, Tag 01AG] (`AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj`),
so this is the source's "`ω_X^•` locally has a unique nonzero cohomology sheaf". -/
@[stacks 0AWT "clause (1), locally a single nonzero cohomology sheaf, read stalkwise"]
public theorem isCohenMacaulay_iff_locally_unique_homology {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) :
    AlgebraicGeometry.IsCohenMacaulay X ↔
      ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℤ, ∀ i : ℤ, i ≠ n → ∀ y ∈ V,
        Subsingleton
          (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y) := by
  constructor
  · intro hX x
    exact exists_nhds_unique_nonzero_homology K hK x
      (isCohenMacaulayLocalRing_stalk_of_isCohenMacaulay hX x)
  · intro h
    refine isCohenMacaulay_of_forall_isCohenMacaulayLocalRing_stalk fun x => ?_
    obtain ⟨V, hxV, n, hn⟩ := h x
    exact (isCohenMacaulayLocalRing_stalk_iff_stalkwise K hK x).mpr
      ⟨n, fun i hi => hn i hi x hxV⟩

/-! ### The dualizing complex of a connected Cohen–Macaulay scheme -/

/-- Some cohomology sheaf of a dualizing complex has nonvanishing stalk at every point: the
derived localization of an affine model is a dualizing complex over the local ring there, and a
dualizing complex over a Noetherian local ring is nonzero. -/
private lemma exists_not_subsingleton_stalk_homology {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) :
    ∃ i : ℤ,
      ¬ Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk x) := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, htr⟩ := exists_model_stalk_translation hK hU
  let : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  obtain ⟨i, hi⟩ :=
    exists_not_subsingleton_localized_homology ω hω (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  exact ⟨i, fun hs => hi ((htr i x hxU).mp hs)⟩

/-- The degree in which the stalk of a dualizing complex is concentrated is unique, because that
stalk is nonzero. -/
private lemma unique_concentration_degree {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) {n n' : ℤ}
    (h : ∀ i : ℤ, i ≠ n →
      Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk x))
    (h' : ∀ i : ℤ, i ≠ n' →
      Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk x)) :
    n = n' := by
  obtain ⟨i, hi⟩ := exists_not_subsingleton_stalk_homology hK x
  have e1 : i = n := by by_contra hc; exact hi (h i hc)
  have e2 : i = n' := by by_contra hc; exact hi (h' i hc)
  exact e1.symm.trans e2

/-- A sheaf of modules all of whose stalks are subsingletons is a zero object. This is the
vanishing case of [Stacks, Tag 01AG]. -/
private lemma isZero_of_forall_subsingleton_stalk {X : Scheme.{u}} (F : X.Modules)
    (h : ∀ y : X, Subsingleton (F.presheaf.stalk y)) : Limits.IsZero F :=
  (AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
    X.ringCatSheaf F).mpr fun y => ModuleCat.isZero_iff_subsingleton.mpr (h y)

/-- **Stacks Project, Tag 0AWT, the final assertion, less the Cohen–Macaulayness of `ω_X`.**
If `X` is connected and Cohen–Macaulay then there is an integer `n` such that the dualizing
complex is the coherent module `ω_X = H^n(ω_X^•)` placed in degree `n`, that is
`ω_X^• = ω_X[-n]`.

The source also asserts that `ω_X` is a Cohen–Macaulay module ([Stacks, Tag 0343]); that clause
is **not** part of the statement below. The predicate it would be stated with is
`AlgebraicGeometry.SheafIsCohenMacaulay`, which exists and applies to `X.Modules` directly; what
is missing is the identification of `ω_{X,x}` with a dualizing module over `𝒪_{X,x}`. See the
implementation notes.

This is a weaker form of the final assertion of [stacks 0AWT], so it is not registered under the
tag; it is superseded by `Stacks.Duality.exists_coherent_cohenMacaulay_iso_single_of_connected`. -/
public theorem exists_coherent_iso_single_of_connected {X : Scheme.{u}}
    [IsLocallyNoetherian X] [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hX : AlgebraicGeometry.IsCohenMacaulay X) :
    ∃ n : ℤ, _root_.SheafOfModules.IsCoherent
        ((DerivedCategory.homologyFunctor X.Modules n).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules n).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj K)) := by
  classical
  have hCMx := isCohenMacaulayLocalRing_stalk_of_isCohenMacaulay hX
  set D : ℤ → Set X := fun m => {y : X | ∀ i : ℤ, i ≠ m →
    Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y)}
    with hD
  have hcover : ∀ y : X, ∃ m : ℤ, y ∈ D m := fun y =>
    (isCohenMacaulayLocalRing_stalk_iff_stalkwise K hK y).mp (hCMx y)
  have hopen : ∀ m : ℤ, IsOpen (D m) := by
    intro m
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨V, hyV, m', hm'⟩ := exists_nhds_unique_nonzero_homology K hK y (hCMx y)
    have hmm : m' = m := unique_concentration_degree hK y (fun i hi => hm' i hi y hyV) hy
    subst hmm
    exact ⟨V, fun z hz i hi => hm' i hi z hz, V.2, hyV⟩
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨n, hn⟩ := hcover x₀
  have hclopen : IsClopen (D n) := by
    refine ⟨?_, hopen n⟩
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨m, hm⟩ := hcover y
    have hmn : m ≠ n := fun h => hy (h ▸ hm)
    exact ⟨D m, fun z hz hz' => hmn (unique_concentration_degree hK z hz hz'), hopen m, hm⟩
  have hDeq : D n = Set.univ := hclopen.eq_univ ⟨x₀, hn⟩
  have hzero : ∀ i : ℤ, i ≠ n →
      Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
    intro i hi
    refine isZero_of_forall_subsingleton_stalk _ fun y => ?_
    have hy : y ∈ D n := hDeq ▸ Set.mem_univ y
    exact hy i hi
  have hGE : K.IsGE n := (DerivedCategory.isGE_iff K n).mpr fun i hi => hzero i (by omega)
  have hLE : K.IsLE n := (DerivedCategory.isLE_iff K n).mpr fun i hi => hzero i (by omega)
  refine ⟨n, isCoherent_homology_of_isDualizingComplex hK n, ?_⟩
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  let eH : (DerivedCategory.homologyFunctor X.Modules n).obj K ≅ Y :=
    (DerivedCategory.homologyFunctor X.Modules n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules n).app Y
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor X.Modules n).mapIso eH.symm⟩

end StalkwiseCriterion

end Stacks.Duality

end
