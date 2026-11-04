module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.Depth
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ComplementSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections over the punctured spectrum of a ring of depth at least two

Let `R` be a Noetherian ring and `I ⊆ R` a proper ideal with `depth_I(R) ≥ 2`, and let
`U = Spec R ∖ V(I)`. Then the restriction map `R ⟶ Γ(U, 𝒪_U)` on global functions is bijective.

This is the input that [Stacks, Tag 0EY9] quotes from Local Cohomology: for a Noetherian local
ring `A` of depth at least two the punctured spectrum has the same functions as `Spec A` itself.
The proof here is the source's: the four-term exact sequence

  `0 ⟶ H⁰_I(R) ⟶ R ⟶ Γ(U, 𝒪_U) ⟶ H¹_I(R) ⟶ 0`

of [Stacks, Tag 0DWR] has its two outer terms zero, because local cohomology with support in
`V(I)` vanishes in every degree below `depth_I(R)`.

## Main results

* `Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth` — local cohomology in
  the coreflection model of [Stacks, Tag 0A6Q] vanishes below the depth. This is
  `Stacks.LocalCohomology.subsingleton_localCohomologyWithSupportIn_of_lt_depth` transported
  along the comparison of the two models.
* `Stacks.LocalCohomology.bijective_complementTopScalars_of_depth_ge_two` — the restriction map
  `R ⟶ Γ(U, 𝒪_U)` is bijective when `depth_I(R) ≥ 2`.
* `Stacks.LocalCohomology.bijective_appTop_of_punctured_of_depth_ge_two` — the same statement for
  an arbitrary open immersion into `Spec R` whose range is the punctured spectrum of a Noetherian
  local ring `R` of depth at least two, read on `Γ(-, ⊤)`.

## Implementation notes

No `@[stacks]` attribute is placed. The clause of [Stacks, Tag 0BK0] quoted by [Stacks, Tag 0EY9]
is the four-term exact sequence, which is carried where it is proved, in
`StacksFrontier/RingTheory/LocalCohomology/LowDegree/CechSectionsComparison.lean`; the statements
below are consequences of it together with the vanishing of local cohomology below the depth
([Stacks, Tag 0AVZ]), not clauses of either tag.

The two models of local cohomology both occur: the depth vanishing is proved for
`Stacks.LocalCohomology.localCohomologyWithSupportIn`, the derived-supported-sections model at a
specialization-stable subset, while the exact sequence is stated with
`Stacks.LocalCohomology.localCohomologyModule`, the coreflection model. Over a Noetherian ring
they agree degreewise, which is
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`.

Passing from the canonical open `Stacks.LocalCohomology.complementZeroLocus`, at which the
restriction map is stated, to an arbitrary open immersion with the same image goes through
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` rather than through
`AlgebraicGeometry.Scheme.Hom.appIso`: the two open immersions have the same range, so they
differ by an isomorphism of the sources, and `Γ(-, ⊤)` of that isomorphism is invertible. For the
inclusion of an open subscheme `AlgebraicGeometry.Scheme.Opens.ι_appTop` already identifies
`Γ(-, ⊤)` with a restriction map of the ambient structure sheaf, so nothing else is needed.

## References

* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **Local cohomology vanishes below the depth, in the coreflection model.** For a finite module
`M` over a Noetherian ring `R` with `IM ≠ M` and `i < depth_I(M)`, the local cohomology module
`H^i_I(M)` of [Stacks, Tag 0A6Q] is zero.

This is `Stacks.LocalCohomology.subsingleton_localCohomologyWithSupportIn_of_lt_depth`, which is
[Stacks, Tag 0AVZ] in the derived-supported-sections model, transported along the degreewise
comparison of the two models. -/
@[sga "2 XII 1.5" "more general"]
public theorem subsingleton_localCohomologyModule_of_lt_depth (R : Type u) [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I.FG) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) (i : ℕ) (hi : (i : ℕ∞) < Module.depth R I M) :
    Subsingleton (localCohomologyModule R I hI M (i : ℤ)) :=
  have : Subsingleton (localCohomologyWithSupportIn.{u, u} R
      (PrimeSpectrum.zeroLocus (I : Set R))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (i : ℤ)) :=
    subsingleton_localCohomologyWithSupportIn_of_lt_depth.{u, u} R I M hIM i hi
  Function.Injective.subsingleton
    (localCohomologyWithSupportInIsoLocalCohomologyModule R I hI M
      (i : ℤ)).symm.toLinearEquiv.injective

/-- **Functions on the complement of a zero locus of depth at least two.** Let `R` be a
Noetherian ring and `I ⊆ R` a proper ideal with `depth_I(R) ≥ 2`. Then the restriction map
`R ⟶ Γ(U, 𝒪_U)` on global functions, `U = Spec R ∖ V(I)`, is bijective.

Both halves are read off the four-term exact sequence of [Stacks, Tag 0DWR] at the module `R`,
whose restriction map is `Stacks.LocalCohomology.complementTopScalars` by
`Stacks.LocalCohomology.restrictionToComplement_ring_apply`: injectivity is exactness at `R`
together with `H⁰_I(R) = 0`, and surjectivity is exactness at `Γ(U, 𝒪_U)` together with
`H¹_I(R) = 0`. Both vanishings come from
`Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth`, since `0` and `1` are
below `2 ≤ depth_I(R)`. -/
@[ega "IV 19.9.8" "special case",
  sga "2 III 3.4" "(1)⇒(2)",
  sga "2 III 3.5" "(1) ⇒ (2), special case"]
public theorem bijective_complementTopScalars_of_depth_ge_two (R : Type u) [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hIne : I ≠ ⊤)
    (hdepth : (2 : ℕ∞) ≤ Module.depth R I R) :
    Function.Bijective (complementTopScalars I) := by
  classical
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  have hIM : I • (⊤ : Submodule R (ModuleCat.of R R)) ≠ ⊤ := by simpa using hIne
  have hsub : ∀ i : ℕ, (i : ℕ∞) < 2 →
      Subsingleton (localCohomologyModule R I hI (ModuleCat.of R R) (i : ℤ)) := fun i hi =>
    subsingleton_localCohomologyModule_of_lt_depth R I hI (ModuleCat.of R R) hIM i
      (hi.trans_le hdepth)
  have h0 := hsub 0 (by norm_num)
  have h1 := hsub 1 (by norm_num)
  obtain ⟨D, hD⟩ := lowDegreeExactSequence.{u} R I hI
  obtain ⟨-, hexR, hexU, -⟩ := hD (ModuleCat.of R R)
    (SheafOfModules.unit (complementZeroLocus R I : Scheme).ringCatSheaf)
    (complementTildeRingIsoUnit R I).symm
  set ρ := restrictionToComplement D (ModuleCat.of R R)
    (SheafOfModules.unit (complementZeroLocus R I : Scheme).ringCatSheaf)
    (complementTildeRingIsoUnit R I).symm
  have hfun : ∀ a : R, ρ a = complementTopScalars I a :=
    restrictionToComplement_ring_apply R I hI D
  have hρ : Function.Bijective ρ := by
    refine ⟨(injective_iff_map_eq_zero ρ).mpr fun x hx => ?_, fun s => ?_⟩
    · obtain ⟨a, ha⟩ := (hexR x).mp hx
      rw [← ha, Subsingleton.elim a 0, map_zero]
    · exact (hexU s).mp (Subsingleton.elim _ _)
  rwa [show (ρ : R → _) = complementTopScalars I from funext hfun] at hρ

/-- The punctured spectrum of a local ring is the complement of the zero locus of its maximal
ideal: a prime contains the maximal ideal exactly when it is the closed point. -/
@[ega "I 2.4.1" "partial"]
private theorem complementZeroLocus_maximalIdeal (R : Type u) [CommRing R] [IsLocalRing R] :
    (complementZeroLocus R (IsLocalRing.maximalIdeal R) : Set (Spec (.of R))) =
      {IsLocalRing.closedPoint R}ᶜ := by
  have hzero : PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) =
      {IsLocalRing.closedPoint R} := by
    ext p
    change IsLocalRing.maximalIdeal R ≤ p.asIdeal ↔ p = IsLocalRing.closedPoint R
    refine ⟨fun h => PrimeSpectrum.ext (le_antisymm
      (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h), by rintro rfl; rfl⟩
  change (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R))ᶜ = _
  exact congrArg (fun s : Set (Spec (.of R)) => sᶜ) hzero

/-- **Sections of the structure sheaf over the punctured spectrum of a ring of depth at least
two.** Let `R` be a Noetherian local ring with `depth_𝔪(R) ≥ 2` and let `f : X ⟶ Spec R` be an
open immersion whose range is the punctured spectrum. Then the composite
`R ≅ Γ(Spec R, 𝒪) ⟶ Γ(X, 𝒪_X)` is bijective.

`f` and the inclusion of the open `U = Spec R ∖ V(𝔪)` have the same range, so they differ by an
isomorphism `X ≅ U` of their sources, whose global sections are invertible. On `U` the map is
`Stacks.LocalCohomology.complementTopScalars`, handled by
`Stacks.LocalCohomology.bijective_complementTopScalars_of_depth_ge_two`. -/
@[sga "2 III 3.4" "(1)⇒(2)"]
public theorem bijective_appTop_of_punctured_of_depth_ge_two (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsOpenImmersion f] (hf : Set.range f.base = {IsLocalRing.closedPoint R}ᶜ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) R) :
    Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) := by
  set U := complementZeroLocus R (IsLocalRing.maximalIdeal R)
  have hrange : Set.range f.base = Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, hf, complementZeroLocus_maximalIdeal R]
  let e : X ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq f U.ι hrange
  have : IsIso e.hom.appTop := _root_.Stacks.AlgebraicGeometry.isIso_appTop_of_isIso e.hom
  rw [← IsOpenImmersion.isoOfRangeEq_hom_fac f U.ι hrange, Scheme.Hom.comp_appTop, ← Category.assoc]
  exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
    (bijective_complementTopScalars_of_depth_ge_two R (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top hdepth)

end Stacks.LocalCohomology

end
