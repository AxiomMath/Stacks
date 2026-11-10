module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CompletedLocalObstruction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.LocalFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Steps of the Noetherian induction of [Stacks, Tag 0BK1]

The proof of [Stacks, Tag 0BK1] begins by reducing the tag to the punctured spectra of the local
rings along the complement; that reduction is `Stacks.LocalCohomology.puncturedSpectrumReduction`.
It is a Noetherian induction on
`dim 𝒪_{X,z}`: the inductive step is
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_basicOpen_le`, and the recursion
is driven by the strict drop of the Krull dimension when one passes from a Noetherian local ring
to its localization at a non-maximal prime.

This file collects the pieces of that recursion which are independent of the scheme-theoretic
bookkeeping: the dimension drop itself, the transport of the induction's hypothesis along an
isomorphism of local rings, and the degenerate case in which the open contains the closed point.

## Main results

* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_forall_affineOpen`: **the
  tag's opening reduction** — coherence of `j'_*𝒪_W` follows from finiteness of the sections of
  `𝒪` over the preimage of the image of `j'` in `Spec Γ(Z, V)`, for every affine open `V` of `Z`.
* `Stacks.LocalCohomology.ringKrullDim_localization_atPrime_lt`: **the measure of the
  induction** — localizing a Noetherian local ring at a prime other than the maximal ideal
  strictly drops the Krull dimension.
* `Stacks.LocalCohomology.puncturedSpectrum_eq_preimage_of_ringEquiv`: the punctured spectrum of a
  local ring pulls back to the punctured spectrum along an isomorphism of local rings.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv`:
  **coherence of the direct image of the structure sheaf of a punctured spectrum depends only on
  the isomorphism class of the local ring.** This is what lets the hypothesis of
  `Stacks.LocalCohomology.puncturedSpectrumReduction`, which is stated at the stalk
  `𝒪_{Z,z}`, be read at a concrete `Localization.AtPrime 𝔭`.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum_localization`:
  that transport carried out at the prime of `Γ(Z, V)` at which a point of an affine open sits.
* `Stacks.LocalCohomology.eq_top_of_closedPoint_mem`: an open of the spectrum of a local ring
  containing the closed point is the whole spectrum. This is the case of the induction which
  terminates immediately.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_top`: the direct image of the
  structure sheaf along the inclusion of the whole space is coherent, which is the conclusion of
  the induction in that case.

## Implementation notes

The transport along a ring isomorphism is carried out on the *sections* rather than on the sheaf:
coherence of the direct image over a Noetherian affine base is equivalent to finiteness of the
sections over the open (`Stacks.LocalCohomology.module_finite_sections_of_isCoherent` and
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_module_finite_sections`), and
finiteness of the sections travels along any flat ring map
(`Stacks.LocalCohomology.module_finite_sections_preimage_of_flat_of_isNoetherianRing`), an
isomorphism being flat by `RingHom.Flat.of_bijective`. Going through an isomorphism of *schemes*
would instead require comparing the two direct images across the induced square, which is a much
larger piece of bookkeeping for the same conclusion.

The Krull dimension lives in `WithBot ℕ∞` and `Ideal.height` in `ℕ∞`; the two are matched by
`IsLocalization.AtPrime.ringKrullDim_eq_height` and
`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`, so the strict inequality is
`Ideal.height_strict_mono_of_isPrime` read through those.

## How the reduction is proved

It is `Stacks.LocalCohomology.puncturedSpectrumReduction` in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumReductionInduction`, and
[Stacks, Tag 0BK1] follows from it as
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_completion_associatedPrime_dim`.

The recursion runs on `Stacks.LocalCohomology.ReductionBoundedBy d`, which is the statement of the
reduction with `dim 𝒪_{Z,z}` bounded by `d` along the complement. Its step
(`Stacks.LocalCohomology.reductionBoundedBy_of_forall_lt`) reduces to an affine chart by
`isCoherent_pushforward_structureSheaf_of_forall_affineOpen`, then to a localization
`A = Localization.AtPrime 𝔭` by [Stacks, Tag 0AW9]
(`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_forall_localization`), and
treats that affine-local case in
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_localRing`:
`eq_top_of_closedPoint_mem` disposes of the primes whose open still contains the closed point,
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_bot` of those whose open is empty,
and at the others the open sits inside the punctured spectrum `P` of `A`, where
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_basicOpen_le` concludes from the
statement at `d - 1` applied to `P`. The dimension hypothesis is then removed, in
`Stacks.LocalCohomology.puncturedSpectrumReduction`, by running the same opening reduction once
more and choosing `d` to be the (finite) Krull dimension of each `A`.

The three identifications this file's earlier notes recorded as missing are all in place:

* the points of `Z` in an affine open `V` matched with the primes of `Γ(Z, V)` —
  `isCoherent_pushforward_structureSheaf_puncturedSpectrum_localization` below, together with
  `Stacks.LocalCohomology.primeIdealOf_fromSpec`;
* the points, local rings, dimension drop, integrality and Noetherian-ness of
  `(Stacks.Divisors.puncturedSpectrum A).toScheme` — in
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumSchemeStalks`;
* the transfer of coherence between two open immersions with the same image —
  `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_opensRange_eq` in
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardOpensRangeTransport`. It is *not* the
  bookkeeping on sections that the earlier note predicted:
  `AlgebraicGeometry.isIso_structureSheafToPushforward_of_isIso` already said that the direct
  image of `𝒪` along an isomorphism of schemes is `𝒪`, so the whole statement is
  `Scheme.Modules.pushforwardCongr`, `Scheme.Modules.pushforwardComp` and `isCoherent_of_iso`.

One further identification, which those notes did not list, is needed to let the recursion
re-enter itself: the local rings of the punctured spectrum of `A = Γ(Z, V)_𝔭` are `A_𝔮`, whereas
the coherence hypothesis is available at localizations of `Γ(Z, V)`, and
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization` matches the two
(`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum_comap`).

Choosing the function `f` the step consumes — a nonzero element of the ideal cutting out the
complement of the open, restricted to `P` — needed no new input beyond
`Stacks.LocalCohomology.exists_eq_zeroLocusCompl`, and is
`Stacks.LocalCohomology.exists_section_basicOpen_le`.

## References

* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 0AW9](https://stacks.math.columbia.edu/tag/0AW9)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.LocalCohomology

/-! ### The affine reduction -/

open Stacks.AlgebraicGeometry.TopDegreeFiniteType in
/-- **Coherence of the direct image of the structure sheaf of an open, read on the affine
charts.** Let `j : W ⟶ Z` be an open immersion into a locally Noetherian scheme. If for every
affine open `V` of `Z` the sections of `𝒪` over the preimage of the image of `j` in
`Spec Γ(Z, V)` are a finite `Γ(Z, V)`-module, then `j_*𝒪_W` is coherent.

This is the source's opening reduction of [Stacks, Tag 0BK1], "the statement is local on `X`,
hence we may assume `X` affine", in the form the rest of its argument can consume: the hypothesis
is a statement about an honest `Spec` of a ring, which is where [Stacks, Tag 0AW9] and the
induction on the dimension take place.

The direct image is quasi-coherent because an open immersion into a locally Noetherian scheme is
quasi-compact and quasi-separated; `module_finite_sections_of_fromSpec_preimage_opensRange`
carries the hypothesis from `Spec Γ(Z, V)` back to the sections of `j_*𝒪_W` over `V`;
`Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections` reads
finite type off those, and a quasi-coherent module of finite type on a locally Noetherian scheme
is coherent ([Stacks, Tag 01XZ]). -/
@[ega "I 1.5.2" "more general"]
theorem isCoherent_pushforward_structureSheaf_of_forall_affineOpen {Z W : Scheme.{u}}
    [IsLocallyNoetherian Z] (j : W ⟶ Z) [IsOpenImmersion j]
    (h : ∀ V : Z.affineOpens, Module.Finite (ToType Γ(Z, V.1))
      Γ(Spec Γ(Z, V.1), V.2.fromSpec ⁻¹ᵁ j.opensRange)) :
    ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} W.ringCatSheaf)).IsCoherent := by
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W
  have : ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} W.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent j (SheafOfModules.unit.{u} W.ringCatSheaf)
  have := isFiniteType_of_forall_moduleFinite_sections
    ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} W.ringCatSheaf))
    fun V => module_finite_sections_of_fromSpec_preimage_opensRange j V.2 (h V)
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### The measure of the induction -/

/-- **Localizing a Noetherian local ring at a non-maximal prime strictly drops the Krull
dimension.** This is the measure on which the Noetherian induction of [Stacks, Tag 0BK1] runs:
the points of the punctured spectrum of `A` have local rings `A_𝔮` with `dim A_𝔮 < dim A`.

The dimension of a localization at a prime is the height of that prime
(`IsLocalization.AtPrime.ringKrullDim_eq_height`), the dimension of a local ring is the height of
its maximal ideal (`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`), and the height of a prime
of finite height is strictly monotone (`Ideal.height_strict_mono_of_isPrime`); every ideal of a
Noetherian ring has finite height by Krull's height theorem. -/
@[ega "0 16.1.3" "special case"]
theorem ringKrullDim_localization_atPrime_lt {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (q : Ideal A) [hq : q.IsPrime] (hne : q ≠ maximalIdeal A) :
    ringKrullDim (Localization.AtPrime q) < ringKrullDim A := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)]
  exact_mod_cast Ideal.height_strict_mono_of_isPrime ((le_maximalIdeal hq.ne_top).lt_of_ne hne)

/-! ### Transport along an isomorphism of local rings -/

/-- **The punctured spectrum pulls back to the punctured spectrum along an isomorphism of local
rings.** The induced map of spectra carries the closed point to the closed point, and reflects
it because the contraction of ideals along a surjection is injective. -/
theorem puncturedSpectrum_eq_preimage_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Stacks.Divisors.puncturedSpectrum B =
      Spec.map (CommRingCat.ofHom (e : A →+* B)) ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum A := by
  ext x
  change (x ∉ ({closedPoint B} : Set (PrimeSpectrum B))) ↔
    (Spec.map (CommRingCat.ofHom (e : A →+* B)) x ∉
      ({closedPoint A} : Set (PrimeSpectrum A)))
  refine not_congr ⟨?_, fun hx => PrimeSpectrum.ext <|
    Ideal.comap_injective_of_surjective (e : A →+* B) e.surjective <|
      (congrArg PrimeSpectrum.asIdeal hx : x.asIdeal.comap (e : A →+* B) = maximalIdeal A).trans
        (IsLocalRing.maximalIdeal_comap (e : A →+* B)).symm⟩
  rintro rfl
  exact PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap (e : A →+* B))

/-- **Coherence of the direct image of the structure sheaf of a punctured spectrum depends only
on the isomorphism class of the local ring.** Let `A` and `B` be isomorphic local rings with `A`
Noetherian. If the direct image of `𝒪` along the inclusion of the punctured spectrum of `Spec A`
is coherent, then so is the corresponding direct image over `Spec B`.

This is what lets the hypothesis of `Stacks.LocalCohomology.puncturedSpectrumReduction`, which
speaks of the stalk `𝒪_{Z,z}`, be used at a concrete localization `Localization.AtPrime 𝔭`: the
two are isomorphic but not equal.

Coherence of such a direct image over a Noetherian affine base is finiteness of the sections over
the open (`module_finite_sections_of_isCoherent` and
`isCoherent_pushforward_structureSheaf_of_module_finite_sections`), that finiteness travels along
the flat `Spec B ⟶ Spec A` (`module_finite_sections_preimage_of_flat_of_isNoetherianRing`, an
isomorphism being flat by `RingHom.Flat.of_bijective`), and the punctured spectrum pulls back to
the punctured spectrum by `puncturedSpectrum_eq_preimage_of_ringEquiv`. -/
theorem isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv {A B : Type u}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (h : ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj
      (SheafOfModules.unit.{u}
        (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum B).ι).obj
      (SheafOfModules.unit.{u}
        (Stacks.Divisors.puncturedSpectrum B).toScheme.ringCatSheaf)).IsCoherent := by
  have hB : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
  have hBc : IsNoetherianRing (CommRingCat.of B) := hB
  have hfin := module_finite_sections_preimage_of_flat_of_isNoetherianRing
    (A := CommRingCat.of A) (B := CommRingCat.of B) (CommRingCat.ofHom (e : A →+* B))
    (RingHom.Flat.of_bijective e.bijective) (Stacks.Divisors.puncturedSpectrum A)
    (module_finite_sections_of_isCoherent (CommRingCat.of A)
      (Stacks.Divisors.puncturedSpectrum A) h)
  rw [← puncturedSpectrum_eq_preimage_of_ringEquiv e] at hfin
  exact isCoherent_pushforward_structureSheaf_of_module_finite_sections (CommRingCat.of B)
    (Stacks.Divisors.puncturedSpectrum B) hfin

/-- **The hypothesis of `Stacks.LocalCohomology.puncturedSpectrumReduction`, read at a concrete
localization.** Let `Z` be a locally Noetherian scheme, `V` an affine open and `z` a point of `V`.
If the direct image of `𝒪` along the inclusion of the punctured spectrum of the stalk `𝒪_{Z,z}`
is coherent, then so is the corresponding direct image over the punctured spectrum of
`Localization.AtPrime 𝔭`, where `𝔭` is the prime of `Γ(Z, V)` at which `z` sits.

The stalk *is* that localization (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), but only
up to the isomorphism `IsLocalization.algEquiv`; the induction of [Stacks, Tag 0BK1] works on
`Spec Γ(Z, V)` and therefore needs the hypothesis in the second spelling, which
`isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv` supplies. -/
theorem isCoherent_pushforward_structureSheaf_puncturedSpectrum_localization {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] {V : Z.Opens} (hV : IsAffineOpen V) (z : Z) (hz : z ∈ V)
    (h : ((Scheme.Modules.pushforward
        (Stacks.Divisors.puncturedSpectrum (Z.presheaf.stalk z)).ι).obj
      (SheafOfModules.unit.{u} (Stacks.Divisors.puncturedSpectrum
        (Z.presheaf.stalk z)).toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum
        (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)).ι).obj
      (SheafOfModules.unit.{u} (Stacks.Divisors.puncturedSpectrum
        (Localization.AtPrime
          (hV.primeIdealOf ⟨z, hz⟩).asIdeal)).toScheme.ringCatSheaf)).IsCoherent := by
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : Algebra (ToType Γ(Z, V)) (ToType (Z.presheaf.stalk z)) :=
    Z.presheaf.algebra_section_stalk (U := V) ⟨z, hz⟩
  have hloc : IsLocalization.AtPrime (ToType (Z.presheaf.stalk z))
      (hV.primeIdealOf ⟨z, hz⟩).asIdeal := hV.isLocalization_stalk ⟨z, hz⟩
  have : IsNoetherianRing (ToType (Z.presheaf.stalk z)) :=
    IsLocalization.isNoetherianRing (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl _ inferInstance
  exact isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
      (ToType (Z.presheaf.stalk z))).symm.toRingEquiv h

/-! ### The case in which the open contains the closed point -/

/-- **An open of the spectrum of a local ring containing the closed point is everything.** The
closed point lies in the closure of every point, so an open missing some point also misses the
closed point.

This is the case in which the induction of [Stacks, Tag 0BK1] terminates at once: at a prime `𝔭`
of the affine chart for which the open still contains the closed point of `Spec A_𝔭`, there is
nothing left to shrink. -/
theorem eq_univ_of_isOpen_of_closedPoint_mem {A : Type u} [CommRing A] [IsLocalRing A]
    {V : Set (PrimeSpectrum A)} (hV : IsOpen V) (h : closedPoint A ∈ V) : V = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_contra hx
  have hsub : closure ({x} : Set (PrimeSpectrum A)) ⊆ Vᶜ :=
    hV.isClosed_compl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  exact hsub ((PrimeSpectrum.le_iff_mem_closure x (closedPoint A)).mp
    (le_maximalIdeal x.isPrime.ne_top)) h

/-- `eq_univ_of_isOpen_of_closedPoint_mem` read on the opens of the scheme `Spec A`. -/
theorem eq_top_of_closedPoint_mem {A : Type u} [CommRing A] [IsLocalRing A]
    (V : (Spec (CommRingCat.of A)).Opens)
    (h : closedPoint A ∈ (V : Set (Spec (CommRingCat.of A)))) : V = ⊤ :=
  TopologicalSpace.Opens.ext (eq_univ_of_isOpen_of_closedPoint_mem V.isOpen h)

/-- The global sections of an affine scheme are a finite module over themselves: for `U = ⊤` the
structure map `R ⟶ Γ(Spec R, ⊤)` is `(Scheme.ΓSpecIso R).inv`, which is an isomorphism. -/
theorem module_finite_sections_top (R : CommRingCat.{u}) :
    Module.Finite (ToType R) Γ(Spec R, (⊤ : (Spec R).Opens)) := by
  have hid : (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op =
      Quiver.Hom.op (CategoryStruct.id (⊤ : (Spec R).Opens)) :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hsurj : Function.Surjective
      (algebraMap (ToType R) Γ(Spec R, (⊤ : (Spec R).Opens))) := by
    rw [IsAffineOpen.algebraMap_Spec_obj, hid]
    simpa using (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2
  exact Module.Finite.of_surjective (Algebra.linearMap (ToType R) _) hsurj

/-- **The direct image of the structure sheaf along the inclusion of the whole space is
coherent**, over a Noetherian affine base. This is the conclusion the induction of
[Stacks, Tag 0BK1] reaches at a prime whose punctured open is already everything, by
`eq_top_of_closedPoint_mem`. -/
theorem isCoherent_pushforward_structureSheaf_top (R : CommRingCat.{u}) [IsNoetherianRing R] :
    ((Scheme.Modules.pushforward (⊤ : (Spec R).Opens).ι).obj
      (SheafOfModules.unit.{u} (⊤ : (Spec R).Opens).toScheme.ringCatSheaf)).IsCoherent :=
  isCoherent_pushforward_structureSheaf_of_module_finite_sections R ⊤
    (module_finite_sections_top R)

end Stacks.LocalCohomology

end
