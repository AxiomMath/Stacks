module

public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasiAffineInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic

/-!
# [Stacks, Tag 0AYM] in general: every invertible module is a difference of two divisors

Let `X` be a Noetherian scheme carrying an ample invertible module `ℒ`, and let `𝒩` be an
invertible `𝒪_X`-module. [Stacks, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM) asserts
that `𝒩 ≅ 𝒪_X(D - D') = 𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}` for effective Cartier divisors `D`, `D'`, and
that for any prescribed finite `E ⊆ X` both may be chosen to miss `E`. The quasi-affine clause,
`D' = ∅`, is `AlgebraicGeometry.exists_effectiveCartierDivisor_invertibleSheaf_of_isQuasiAffine`;
this file proves the general clause.

## The source's proof, and where each step is

Write `T = E ∪ {associated points of X}`, a finite set ([Stacks, Tag 05AF]).

1. **An affine nonvanishing open containing `T`.** Ampleness gives `m ≥ 1` and
   `s ∈ Γ(X, ℒ^{⊗ m})` with `X_s` affine and `T ⊆ X_s`: [Stacks, Tag 09NV],
   `Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite`.
2. **The quasi-affine case on `X_s`.** `X_s` is affine, hence quasi-affine, so [Stacks, Tag 0F20]
   applied to the restriction `X_s.ι^* 𝒩` produces a global section of it on `X_s.toScheme`
   nonvanishing at every point of `T` above `X_s`. Read back as a section `t` of `𝒩` over the
   open `X_s` of `X` by `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`, with its
   nonvanishing locus over `X_s` computed by
   `Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection`.
   This is `AlgebraicGeometry.InvertibleSheafGeneral.exists_section_nonvanishing_of_isAffineOpen`.
3. **Extension.** [Stacks, Tag 01PW],
   `Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple`, produces `p`, a
   global section `σ` of `ℒ^{⊗ p}` with `X_σ = X_s`, and a global section `τ` of
   `𝒩 ⊗ ℒ^{⊗ p}` restricting on `X_s` to the product `t ⊗ σ|_{X_s}`.
4. **Both global sections avoid `T`.** For `σ` this is `T ⊆ X_s = X_σ`; for `τ` it is the
   [Stacks, Tag 01CY] remark `X_{m ⊗ n} = X_m ∩ X_n` at the germ, in the form
   `Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq` written for exactly this
   consumer.
5. **Two divisors.** A global section of an invertible module nonvanishing at every associated
   point of `X` is regular ([Stacks, Tag 0AYL]) and its zero scheme is an effective Cartier
   divisor `D` with the module isomorphic to `𝒪_X(D)` ([Stacks, Tag 01X0]); the divisor misses
   `E` because the section is a unit there. Applied to `τ` and to `σ` this gives
   `𝒩 ⊗ ℒ^{⊗ p} ≅ 𝒪_X(D)` and `ℒ^{⊗ p} ≅ 𝒪_X(D')`, whence
   `𝒩 ⊗ 𝒪_X(D') ≅ 𝒩 ⊗ ℒ^{⊗ p} ≅ 𝒪_X(D)`.

## The conclusion is stated multiplicatively

`AlgebraicGeometry.InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf`
concludes

```
Nonempty ((𝒩 ⊗ 𝒪_X(D') : X.Modules) ≅ 𝒪_X(D))
```

rather than `𝒩 ≅ 𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}`. The two are the same assertion: `𝒪_X(D')` is
invertible ([Stacks, Tag 01WX], `Stacks.Divisors.invertibleSheaf_isInvertible`), so tensoring
with it is an equivalence of `X.Modules` and the displayed isomorphism exists exactly when
`𝒩 ≅ 𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}` does. The multiplicative form is the one proved because the
construction delivers it directly, and because it mentions no inverse: the repository's integer
tensor powers are indexed by `Stacks.Ample.tensorPowModule`, whose addition law
`Stacks.Ample.tensorPowModuleAddIso` is stated at the `tensorSheaf` spelling of [Stacks, Tag
05NA] rather than at the monoidal `⊗`, so writing the conclusion with `𝒪_X(D')^{⊗ -1}` would
interpose a spelling transport that says nothing about divisors.

## Main results

* `AlgebraicGeometry.InvertibleSheafGeneral.exists_section_nonvanishing_of_isAffineOpen`:
  **the quasi-affine clause read on an affine open of `X`.** An invertible module on a scheme has
  a section over an affine open `U` nonvanishing at every point of a prescribed finite subset
  of `U`.
* `AlgebraicGeometry.InvertibleSheafGeneral.exists_effectiveCartierDivisor_of_nonvanishingLocus`:
  `AlgebraicGeometry.exists_effectiveCartierDivisor_of_nonvanishing` in the vocabulary the ample
  cluster produces its sections in.
* `AlgebraicGeometry.InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf`
  — **[Stacks, Tag 0AYM] in general.**

## Implementation notes

**Two spellings of a nonvanishing section.** The divisor is cut out by
`AlgebraicGeometry.exists_effectiveCartierDivisor_of_nonvanishing`, which is stated over
`M.sections` and the ringed-space nonvanishing locus, whereas the ample cluster produces its
sections over `Γ(M, ⊤)` and `Stacks.Ample.nonvanishingLocus`. The passage between the two is
`Stacks.NonvanishingSpelling.sectionsEquiv` and
`Stacks.NonvanishingSpelling.nonvanishingLocus_symm_eq`, packaged here once as
`exists_effectiveCartierDivisor_of_nonvanishingLocus`.

**Quasi-coherence of an invertible module is derived, not found.** [Stacks, Tag 01PW] is stated
for a quasi-coherent module; an invertible module is finite locally free of rank one ([Stacks, Tag
0B8M], `Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule`) hence
locally free hence quasi-coherent ([Stacks, Tag 01C7]), but no instance chains those, so
`Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule` does it by hand.

**The two spellings of invertibility.** `Stacks.Ample.IsInvertibleModule X M` and
`AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M` are the
same class at definitionally equal indices, but instance search does not pass between them;
`AlgebraicGeometry.InvertibleSheafGeneral.isInvertible_of_isInvertibleModule` is the one-line
transfer, used wherever the divisor API is called.

**The power of a section over an open is not needed.** The companion file
`StacksFrontier/AlgebraicGeometry/Divisors/SectionPowerOpen.lean` supplies
`Stacks.SectionPowerOpen.nonvanishingLocusOn_secPow`,
because the source's own proof multiplies `t` by a power of `s` taken on `X_s`. The repository's
extension theorem is stronger than the source's statement at exactly that point: it returns the
denominator `σ` as a *global* section of `ℒ^{⊗ p}` together with `X_σ = X_s` on the nose, so the
power is already global and no divisibility condition on `p` survives. That is why no `secPow`
appears below.

## References

* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0AYL](https://stacks.math.columbia.edu/tag/0AYL)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample
open Stacks.AmplePullbackPart1 (sectionOfRestrictGlobalSection)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn mem_nonvanishingLocusOn_iff
  mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection)
open Stacks.SectionExtension (resTop)

universe u

namespace AlgebraicGeometry.InvertibleSheafGeneral

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X : Scheme.{u}}

/-! ### Two transfers between spellings -/

/-- **Invertibility in the spelling the divisor API uses.** `Stacks.Ample.IsInvertibleModule X M`
is `AlgebraicGeometry.SheafOfModules.IsInvertible` at the index `X.presheaf`, and the divisor API
is stated at the definitionally equal index `X.sheaf.obj`; instance search does not pass between
them. -/
theorem isInvertible_of_isInvertibleModule (M : X.Modules) [IsInvertibleModule X M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M := ‹_›

/-! ### The quasi-affine clause, read on an affine open of `X` -/

/-- **An invertible module has a section over an affine open nonvanishing at a prescribed finite
set.** `U.toScheme` is affine, hence quasi-affine, so [Stacks, Tag 0F20] applies to the
restriction `U.ι^* M` and gives a global section of it on `U.toScheme` nonvanishing above every
point of `T`; `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` reads that back as a
section of `M` over `U`, and
`Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection`
identifies the two nonvanishing loci.

This is step 2 of the proof of [Stacks, Tag 0AYM]: it is the quasi-affine case of that tag read
on `X_s`, with its conclusion transported from `X_s.toScheme` to `X`. -/
theorem exists_section_nonvanishing_of_isAffineOpen (M : X.Modules) [IsInvertibleModule X M]
    (U : X.Opens) (hU : IsAffineOpen U) {T : Set X} (hT : T.Finite) (hTU : T ⊆ (U : Set X)) :
    ∃ t : Γ(M, U), T ⊆ nonvanishingLocusOn M U t := by
  have _ : IsAffine U.toScheme := hU
  have hfin : (U.ι.base ⁻¹' T).Finite := hT.preimage U.ι.isOpenEmbedding.injective.injOn
  obtain ⟨t, -, hsub, -⟩ :=
    Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite
      (Stacks.AmpleLocallyClosed.pullbackModule U.ι M) hfin ⊤ (fun _ _ => trivial)
  refine ⟨sectionOfRestrictGlobalSection U M t, fun y hy => ?_⟩
  have hyU : y ∈ U := hTU hy
  exact (mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection U M t
      (⟨y, hyU⟩ : U.toScheme)).mp
    (hsub (show U.ι.base (⟨y, hyU⟩ : U.toScheme) ∈ T from hy))

/-! ### From a nonvanishing global section to a divisor -/

/-- `AlgebraicGeometry.exists_effectiveCartierDivisor_of_nonvanishing` in the vocabulary the ample
cluster produces its sections in: over `Γ(M, ⊤)` and `Stacks.Ample.nonvanishingLocus`. -/
theorem exists_effectiveCartierDivisor_of_nonvanishingLocus [IsLocallyNoetherian X]
    (M : X.Modules) [IsInvertibleModule X M] (t : Γ(M, ⊤)) {E : Set X}
    (hE : E ⊆ nonvanishingLocus M t)
    (hAss : Stacks.Divisors.schemeAssociatedPoints X ⊆ nonvanishingLocus M t) :
    ∃ D : X.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      Disjoint E D.supportSet ∧ Nonempty (M ≅ Stacks.Divisors.invertibleSheaf' D) := by
  have := isInvertible_of_isInvertibleModule M
  have h := Stacks.NonvanishingSpelling.nonvanishingLocus_symm_eq X M t
  exact exists_effectiveCartierDivisor_of_nonvanishing M
    ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm t) (h ▸ hE) (h ▸ hAss)

/-! ### The general clause of Tag 0AYM -/

/-- **Stacks Project, Tag 0AYM**, the general clause. On a Noetherian scheme `X` carrying an
ample invertible module `ℒ`, every invertible `𝒪_X`-module `𝒩` is the sheaf `𝒪_X(D - D')` of a
difference of two effective Cartier divisors, and `D` and `D'` may both be chosen disjoint from
any prescribed finite subset `E` of `X`.

`𝒩 ≅ 𝒪_X(D - D') = 𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}` is stated here in the equivalent multiplicative
form `𝒩 ⊗ 𝒪_X(D') ≅ 𝒪_X(D)`; see the module documentation. The case `D' = ∅` for `X`
quasi-affine is
`AlgebraicGeometry.exists_effectiveCartierDivisor_invertibleSheaf_of_isQuasiAffine`. -/
@[stacks 0AYM]
theorem exists_effectiveCartierDivisors_tensor_invertibleSheaf [IsNoetherian X] (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (N : X.Modules) [IsInvertibleModule X N]
    {E : Set X} (hE : E.Finite) :
    ∃ D D' : X.IdealSheafData,
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      Stacks.Divisors.IsEffectiveCartierDivisor D' ∧
      Disjoint E D.supportSet ∧ Disjoint E D'.supportSet ∧
      Nonempty ((N ⊗ Stacks.Divisors.invertibleSheaf' D' : X.Modules) ≅
        Stacks.Divisors.invertibleSheaf' D) := by
  classical
  have := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule N
  -- the associated points of a Noetherian scheme are finite ([Stacks, Tag 05AF])
  have hassoc : (Stacks.Divisors.schemeAssociatedPoints X).Finite := by
    have h := associatedPoints_inter_finite (SheafOfModules.unit X.ringCatSheaf) ⊤
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
    simpa [Stacks.Divisors.schemeAssociatedPoints] using h
  -- step 1: an affine `X_s` containing `E` and every associated point ([Stacks, Tag 09NV])
  obtain ⟨n, hn, s, haff, hTs, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
      (hE.union hassoc) ⊤ (fun _ _ => trivial)
  -- step 2: a section of `N` over `X_s` nonvanishing there ([Stacks, Tag 0F20])
  obtain ⟨t, ht⟩ :=
    exists_section_nonvanishing_of_isAffineOpen N _ haff (hE.union hassoc) hTs
  -- step 3: extend `t ⊗ σ|_{X_s}` to a global section of `N ⊗ L ^⊗ p` ([Stacks, Tag 01PW])
  obtain ⟨p, σ, τ, hUσ, heq⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple L hL N hn s t
  -- step 4a: `σ` is nonvanishing on `E` and at every associated point, since `X_σ = X_s`
  have hσ : E ∪ Stacks.Divisors.schemeAssociatedPoints X ⊆
      nonvanishingLocus (tensorPowModule X L (p : ℤ)) σ := by
    intro y hy
    have h : y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L p σ := hUσ ▸ hTs hy
    rw [Stacks.AmpleTheory.powNonvanishingOpen] at h
    exact (Stacks.NonvanishingOpen.mem_nonvanishingOpen X _ σ y).mp h
  -- step 4b: `τ` is too, by `X_{m ⊗ n} = X_m ∩ X_n` ([Stacks, Tag 01CY])
  have hτ : E ∪ Stacks.Divisors.schemeAssociatedPoints X ⊆
      nonvanishingLocus (N ⊗ tensorPowModule X L (p : ℤ) : X.Modules) τ := by
    intro y hy
    have hyU : y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L n s := hTs hy
    refine (Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq τ t
      (resTop _ σ) heq hyU).mpr ⟨(mem_nonvanishingLocusOn_iff N _ hyU).mp (ht hy), ?_⟩
    have hgerm : ((tensorPowModule X L (p : ℤ)).presheaf.germ
          (Stacks.AmpleTheory.powNonvanishingOpen X L n s) y hyU).hom (resTop _ σ)
        = ((tensorPowModule X L (p : ℤ)).presheaf.Γgerm y).hom σ :=
      TopCat.Presheaf.Γgerm_res_apply (C := Ab.{u})
        (tensorPowModule X L (p : ℤ)).presheaf y hyU σ
    rw [hgerm]
    exact (mem_nonvanishingLocus_iff _ σ y).mp (hσ hy)
  -- step 5: the two divisors ([Stacks, Tags 0AYL and 01X0])
  obtain ⟨D, hD, hDE, ⟨e⟩⟩ := exists_effectiveCartierDivisor_of_nonvanishingLocus _ τ
    (Set.subset_union_left.trans hτ) (Set.subset_union_right.trans hτ)
  obtain ⟨D', hD', hD'E, ⟨e'⟩⟩ := exists_effectiveCartierDivisor_of_nonvanishingLocus _ σ
    (Set.subset_union_left.trans hσ) (Set.subset_union_right.trans hσ)
  exact ⟨D, D', hD, hD', hDE, hD'E, ⟨whiskerLeftIso N e'.symm ≪≫ e⟩⟩

end AlgebraicGeometry.InvertibleSheafGeneral

end
