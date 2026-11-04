module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Descent
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CompletedLocalObstruction
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Steps of the coherence criterion of Stacks 51.8.4

Let `X` be an integral locally Noetherian scheme, `j : U ⟶ X` the inclusion of a nonempty open
subscheme, and suppose that for every point `z` outside `U` every associated prime `𝔭` of the
completed local ring `𝒪^∧_{X,z}` satisfies `2 ≤ dim(𝒪^∧_{X,z}/𝔭)`. [Stacks, Tag 0BK1] asserts
that `j_*𝒪_U` is then coherent.

This file proves three steps of the argument of that tag. The tag itself is
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_completion_associatedPrime_dim`,
in `StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumCoherentPushforward`.

* The hypothesis forces the complement of `U` to have codimension at least two, which is what
  rules out the base cases `dim = 0` and `dim = 1` of the induction on `dim 𝒪_{X,z}` that the
  tag runs.
* Over an affine Noetherian base, coherence of the direct image of the structure sheaf of an open
  is *equivalent* to finiteness of the sections over that open; the tag's reduction to the affine
  case consumes this direction, and `Stacks.LocalCohomology.module_finite_sections_of_isCoherent`
  is the other.
* Coherence of such a direct image descends along a faithfully flat map of affine schemes, which
  is the tag's last step: it proves coherence after completing the local ring and descends it.

The body of the induction is `Stacks.LocalCohomology.puncturedSpectrumReduction`, in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumReductionInduction`. Its four
inputs are the reduction of the tag to the case of a Noetherian local domain with the complement
equal to the closed point ([Stacks, Tag 0AW9] as
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_forall_localization`, and
[Stacks, Tag 0BK0] through
`Stacks.LocalCohomology.module_finite_sections_zeroLocusCompl_iff`), the extension of a section
after multiplying by a power of a function ([Stacks, Tag 01YB] as
`Stacks.AlgebraicGeometry.PrincipalIdealExtension.exists_hom_app_eq_overApp_smul_pow_basicOpen`,
assembled into the tag's inductive step as
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_basicOpen_le`), and the
criterion over a Nagata universally catenary scheme ([Stacks, Tag 0AWA] as
`Stacks.LocalCohomology.isCoherent_pushforward_of_isNagataScheme`) which is applied to the
completion. The recursion that chains the step is described in the module docstring of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumReductionSteps`.

## Main results

* `Stacks.LocalCohomology.isAssociatedPrimeStacks_of_mem_associatedPrimes`: over a Noetherian
  ring the Stacks Project's notion of an associated prime of the ring itself agrees with
  Mathlib's, in the direction complementary to
  `Stacks.LocalCohomology.mem_associatedPrimes_of_isAssociatedPrimeStacks`.
* `Stacks.LocalCohomology.exists_isAssociatedPrimeStacks`: a nontrivial Noetherian ring has an
  associated prime in the Stacks sense.
* `Stacks.LocalCohomology.le_ringKrullDim_of_forall_isAssociatedPrimeStacks`: a lower bound valid
  for `dim(R/𝔭)` at every associated prime `𝔭` of a nontrivial Noetherian ring `R` is a lower
  bound for `dim R`.
* `Stacks.LocalCohomology.le_ringKrullDim_of_forall_isAssociatedPrimeStacks_adicCompletion`: the
  same bound read on a Noetherian local ring rather than on its completion.
* `Stacks.LocalCohomology.le_ringKrullDim_stalk_of_forall_isAssociatedPrimeStacks`: the bound at
  a point of a locally Noetherian scheme.
* `Stacks.LocalCohomology.two_le_ringKrullDim_stalk_of_notMem_range`: **the first step of
  [Stacks, Tag 0BK1]** — under the hypothesis of that tag, every point outside the open
  subscheme has a local ring of Krull dimension at least two.
* `Stacks.LocalCohomology.isFiniteType_of_moduleFinite_qc`: a quasi-coherent module on an affine
  scheme with finite global sections is of finite type, the converse of
  `AlgebraicGeometry.moduleFinite_of_isFiniteType_qc`.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_module_finite_sections`: the
  degree-zero clause of [Stacks, Tag 0BK0] in the direction [Stacks, Tag 0BK1] consumes — over an
  affine Noetherian base, finiteness of the sections over an open makes the direct image of its
  structure sheaf coherent.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_flat_surjective`: **the last
  step of [Stacks, Tag 0BK1]** — coherence of such a direct image descends along a flat
  surjective map of affine schemes.
* `Stacks.LocalCohomology.flat_specMap_adicCompletion` and
  `Stacks.LocalCohomology.surjective_specMap_adicCompletion`: the two hypotheses of that descent
  hold at the completion map of a Noetherian local ring, which is the one morphism
  [Stacks, Tag 0BK1] applies it to.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_adicCompletion`: the last step
  instantiated there — coherence of the direct image descends from the completion.

## Implementation notes

No `@[stacks 0BK1]` attribute is attached anywhere in this file: the tag's conclusion is not
proved here. See the module docstring of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion` for the
complementary bound, used by [Stacks, Tag 0BK3] in the opposite direction.

Associated primes are taken in the Stacks Project's sense (`IsAssociatedPrimeStacks`, the
annihilator of a single element), which over a Noetherian ring is Mathlib's `associatedPrimes`
without the radical; `Submodule.colon_span` is the only discrepancy between the two spellings,
the Stacks definition taking the colon of the span of a singleton and Mathlib's that of the
singleton itself.

Krull dimensions live in `WithBot ℕ∞`, so the bounds are stated for an arbitrary element `n` of
that type rather than for a natural number.

## References

* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 05AZ](https://stacks.math.columbia.edu/tag/05AZ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.LocalCohomology

/-! ### Associated primes in the Stacks sense exist -/

/-- Over a Noetherian ring, a prime which is associated to the ring in Mathlib's sense is
associated to it in the Stacks Project's sense.

This is the converse of `Stacks.LocalCohomology.mem_associatedPrimes_of_isAssociatedPrimeStacks`,
which holds over any commutative ring. -/
theorem isAssociatedPrimeStacks_of_mem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {p : Ideal R} (hp : p ∈ associatedPrimes R R) :
    IsAssociatedPrimeStacks R R p := by
  obtain ⟨hprime, m, hm⟩ := isAssociatedPrime_iff.mp hp
  exact ⟨hprime, m, by simpa [Submodule.colon_span] using hm.symm⟩

/-- A nontrivial Noetherian ring has an associated prime in the Stacks Project's sense. -/
theorem exists_isAssociatedPrimeStacks (R : Type*) [CommRing R] [IsNoetherianRing R]
    [Nontrivial R] : ∃ p : Ideal R, IsAssociatedPrimeStacks R R p := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R R
  exact ⟨p, isAssociatedPrimeStacks_of_mem_associatedPrimes hp⟩

/-! ### From the associated components to the ring -/

/-- **A bound on the associated components bounds the dimension.** If `n ≤ dim(R/𝔭)` for every
associated prime `𝔭` of a nontrivial Noetherian ring `R`, then `n ≤ dim R`. -/
theorem le_ringKrullDim_of_forall_isAssociatedPrimeStacks {R : Type*} [CommRing R]
    [IsNoetherianRing R] [Nontrivial R] {n : WithBot ℕ∞}
    (h : ∀ p : Ideal R, IsAssociatedPrimeStacks R R p → n ≤ ringKrullDim (R ⧸ p)) :
    n ≤ ringKrullDim R := by
  obtain ⟨p, hp⟩ := exists_isAssociatedPrimeStacks R
  exact (h p hp).trans (ringKrullDim_quotient_le p)

/-- **A bound on the associated components of the completion bounds the dimension of the ring.**
If `n ≤ dim(Â/𝔭)` for every associated prime `𝔭` of the completion `Â` of a Noetherian local
ring `A` at its maximal ideal, then `n ≤ dim A`. -/
theorem le_ringKrullDim_of_forall_isAssociatedPrimeStacks_adicCompletion {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {n : WithBot ℕ∞}
    (h : ∀ p : Ideal (AdicCompletion (maximalIdeal A) A),
      IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal A) A) p →
      n ≤ ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p)) :
    n ≤ ringKrullDim A := by
  rw [ringKrullDim_adicCompletion_maximalIdeal (A := A)]
  exact le_ringKrullDim_of_forall_isAssociatedPrimeStacks h

/-- **The bound at a point of a locally Noetherian scheme.** If `n ≤ dim(𝒪^∧_{X,z}/𝔭)` for every
associated prime `𝔭` of the completed local ring of `X` at `z`, then `n ≤ dim 𝒪_{X,z}`. -/
theorem le_ringKrullDim_stalk_of_forall_isAssociatedPrimeStacks {X : Scheme.{u}}
    [IsLocallyNoetherian X] (z : X) {n : WithBot ℕ∞}
    (h : ∀ p : Ideal (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z)),
      IsAssociatedPrimeStacks
        (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z))
        (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z)) p →
      n ≤ ringKrullDim (AdicCompletion (maximalIdeal (X.presheaf.stalk z))
        (X.presheaf.stalk z) ⧸ p)) :
    n ≤ ringKrullDim (X.presheaf.stalk z) :=
  le_ringKrullDim_of_forall_isAssociatedPrimeStacks_adicCompletion h

/-! ### The first step of [Stacks, Tag 0BK1] -/

/-- **The complement has codimension at least two.** Let `j : U ⟶ X` be a morphism into a locally
Noetherian scheme satisfying the hypothesis of [Stacks, Tag 0BK1]: every associated prime `𝔭` of
the completed local ring `𝒪^∧_{X,z}` at a point `z` outside the image of `j` has
`2 ≤ dim(𝒪^∧_{X,z}/𝔭)`. Then `2 ≤ dim 𝒪_{X,z}` at every such point.

This is the step of [Stacks, Tag 0BK1] which excludes the base cases `d ≤ 1` of the induction on
`d = dim 𝒪_{X,z}`. -/
theorem two_le_ringKrullDim_stalk_of_notMem_range {U X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X)
    (hdim : ∀ z : X, z ∉ Set.range j.base →
      ∀ p : Ideal (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z)),
        IsAssociatedPrimeStacks
          (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z))
          (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z)) p →
        (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion (maximalIdeal (X.presheaf.stalk z))
          (X.presheaf.stalk z) ⧸ p))
    {z : X} (hz : z ∉ Set.range j.base) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk z) :=
  le_ringKrullDim_stalk_of_forall_isAssociatedPrimeStacks z (hdim z hz)

/-! ### Reading coherence of an open pushforward off the sections, over an affine base -/

/-- **A quasi-coherent module on an affine scheme whose global sections are a finite module is of
finite type.** This is the converse of `AlgebraicGeometry.moduleFinite_of_isFiniteType_qc`. -/
theorem isFiniteType_of_moduleFinite_qc (R : CommRingCat.{u}) (F : (Spec R).Modules)
    [F.IsQuasicoherent] (h : Module.Finite (ToType R) Γ(F, (⊤ : (Spec R).Opens))) :
    F.IsFiniteType := by
  have htilde : (AlgebraicGeometry.tilde ((AlgebraicGeometry.modulesSpecToSheaf.obj F).presheaf.obj
      (Opposite.op (⊤ : (Spec R).Opens)))).IsFiniteType :=
    (AlgebraicGeometry.tilde_isFiniteType_iff _).mpr h
  exact AlgebraicGeometry.isFiniteType_of_scheme_iso (asIso F.fromTildeΓ)

/-- The direct image of the structure sheaf of an open of an affine Noetherian scheme is coherent
as soon as it is of finite type, given its quasi-coherence. -/
private theorem isCoherent_pushforward_structureSheaf_of_isFiniteType (R : CommRingCat.{u})
    [IsNoetherianRing R] (V : (Spec R).Opens)
    (h : ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsQuasicoherent →
      ((Scheme.Modules.pushforward V.ι).obj
        (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsFiniteType) :
    ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsCoherent := by
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit V.toScheme
  have hqc := Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs V.ι
    (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)
  have := h hqc
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **Finiteness of the sections over an open of an affine Noetherian scheme makes the direct
image of its structure sheaf coherent.** For `V` an open of `Spec R` with `R` Noetherian, if
`Γ(Spec R, V)` is a finite `R`-module then `(V ⟶ Spec R)_*𝒪_V` is coherent.

This is the degree-zero clause of [Stacks, Tag 0BK0] in the direction that [Stacks, Tag 0BK1]
consumes, and the exact converse of
`Stacks.LocalCohomology.module_finite_sections_of_isCoherent`; together the two say that
coherence of the direct image is *equivalent* to finiteness of the sections. -/
@[ega "IV 7.2.4" "(e)"]
theorem isCoherent_pushforward_structureSheaf_of_module_finite_sections (R : CommRingCat.{u})
    [IsNoetherianRing R] (V : (Spec R).Opens) (h : Module.Finite (ToType R) Γ(Spec R, V)) :
    ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsCoherent := by
  refine isCoherent_pushforward_structureSheaf_of_isFiniteType R V fun _ => ?_
  exact isFiniteType_of_moduleFinite_qc R
    ((Scheme.Modules.pushforward V.ι).obj (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf))
    (Module.Finite.equiv (sectionsTopPushforwardOpensLinearEquiv R V).symm)

/-! ### The last step of [Stacks, Tag 0BK1]: faithfully flat descent -/

/-- **Coherence of an open pushforward descends along a faithfully flat map of affine schemes.**
Let `φ : A ⟶ B` be a ring map with `A` Noetherian such that `Spec φ` is flat and surjective, and
let `V` be an open of `Spec A`. If the direct image of the structure sheaf of the preimage of `V`
along its inclusion into `Spec B` is coherent, then so is the direct image of `𝒪_V` along
`V ⟶ Spec A`.

This is the last step of the argument of [Stacks, Tag 0BK1], where `φ` is the completion map of a
Noetherian local ring: the tag proves coherence after completing and descends it. -/
@[ega "IV 5.9.5" "special case"]
theorem isCoherent_pushforward_structureSheaf_of_flat_surjective {A B : CommRingCat.{u}}
    [IsNoetherianRing A] {φ : A ⟶ B} (hflat : Flat (Spec.map φ))
    (hsurj : Surjective (Spec.map φ)) (V : (Spec A).Opens)
    (h : ((Scheme.Modules.pushforward (Spec.map φ ⁻¹ᵁ V).ι).obj
      (SheafOfModules.unit.{u} (Spec.map φ ⁻¹ᵁ V).toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsCoherent := by
  have := hflat
  have := hsurj
  refine isCoherent_pushforward_structureSheaf_of_isFiniteType A V fun _ => ?_
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit V.toScheme
  have hpb := AlgebraicGeometry.isPullback_morphismRestrict (Spec.map φ) V
  have : ((Scheme.Modules.pushforward (Spec.map φ ⁻¹ᵁ V).ι).obj
      (AlgebraicGeometry.Scheme.unitModule (Spec.map φ ⁻¹ᵁ V).toScheme)).IsFiniteType :=
    h.isFiniteType
  have : ((Scheme.Modules.pushforward (Spec.map φ ⁻¹ᵁ V).ι).obj
      ((Scheme.Modules.pullback (Spec.map φ ∣_ V)).obj
        (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf))).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.pushforward (Spec.map φ ⁻¹ᵁ V).ι).mapIso
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (Spec.map φ ∣_ V))).symm
  have := Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine hpb
    (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)
  exact Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_flat_surjective_of_isAffine
    (Spec.map φ) ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf))
    (Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (asIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange hpb.w
        (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf))).symm)

/-! ### The last step at the completion map of a Noetherian local ring -/

/-- **The completion of a Noetherian local ring is faithfully flat over it.** -/
@[ega "0 7.3.3" "special case",
  ega "IV 8.11.4" "partial",
  sga "1 IV 3.1" "special case",
  sga "3 VIIB 5.5.2" "partial"]
theorem faithfullyFlat_adicCompletion_maximalIdeal (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- **Spec of the completion map of a Noetherian local ring is flat and surjective.** The two
hypotheses of `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_flat_surjective`
hold at the completion map `A ⟶ Â` of a Noetherian local ring. -/
@[ega "IV 8.11.4" "partial"]
theorem flat_and_surjective_specMap_adicCompletion (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    Flat (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A)))) ∧
      Surjective (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A)))) :=
  (AlgebraicGeometry.flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr (faithfullyFlat_adicCompletion_maximalIdeal A))

/-- `Spec` of the completion map of a Noetherian local ring is flat. -/
theorem flat_specMap_adicCompletion (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    Flat (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (maximalIdeal A) A)))) :=
  (flat_and_surjective_specMap_adicCompletion A).1

/-- `Spec` of the completion map of a Noetherian local ring is surjective. -/
@[ega "IV 8.11.4" "partial"]
theorem surjective_specMap_adicCompletion (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (maximalIdeal A) A)))) :=
  (flat_and_surjective_specMap_adicCompletion A).2

/-- **Coherence of an open pushforward descends from the completion of a Noetherian local ring.**
Let `A` be a Noetherian local ring, `Â` its completion at the maximal ideal, `c : Spec Â ⟶ Spec A`
the induced morphism, and `V` an open of `Spec A`. If the direct image of the structure sheaf of
`c ⁻¹ᵁ V` along its inclusion into `Spec Â` is coherent, then so is the direct image of `𝒪_V`
along `V ⟶ Spec A`.

This is `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_flat_surjective` at the
one morphism [Stacks, Tag 0BK1] applies it to. -/
theorem isCoherent_pushforward_structureSheaf_of_adicCompletion (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (V : (Spec (CommRingCat.of A)).Opens)
    {U : (Spec (CommRingCat.of (AdicCompletion (maximalIdeal A) A))).Opens}
    (hU : U = Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (maximalIdeal A) A))) ⁻¹ᵁ V)
    (h : ((Scheme.Modules.pushforward U.ι).obj
      (SheafOfModules.unit.{u} U.toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsCoherent := by
  subst hU
  exact isCoherent_pushforward_structureSheaf_of_flat_surjective
    (flat_specMap_adicCompletion A) (surjective_specMap_adicCompletion A) V h

end Stacks.LocalCohomology

end
