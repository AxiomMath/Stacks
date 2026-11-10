module

public import StacksFrontier.AlgebraicGeometry.TensorSectionPower.Basic
public import StacksFrontier.AlgebraicGeometry.PartOne.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Annihilator
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The surjectivity half of [Stacks, Tag 01PW] over the *trivializing* cover

`Stacks.SectionExtensionNoAmple.exists_tensorSection_of_quasiCompact_cover` glues the local
extensions of the proof of [Stacks, Tag 01PW] over a cover by affine opens **contained in the
nonvanishing loci of global sections**, which is what
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` supplies. That hypothesis is strictly
stronger than anything Tag 01PW assumes: an invertible module with `Γ(X, M ^⊗ n) = 0` for every
`n ≥ 1` — an anti-ample module on a projective curve — has empty nonvanishing loci in every
positive power, so the hypothesis fails while Tag 01PW still applies.

This file glues over the cover the source actually uses: finitely many affine opens on each of
which `M` is **sectionwise trivial**, which every invertible module admits on a quasi-compact
scheme with no further hypothesis
(`Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover`). **`HasPointwiseNonvanishing` is
gone**, and so is every trace of ampleness: the hypotheses below are quasi-compactness and
quasi-separatedness of `X`, invertibility of `M` and quasi-coherence of `F` — Tag 01PW's own.

## What made this possible, and it is not the cover

The cover is available as
`Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover`, and its own file names the
further step needed: the gluing needs, on each member, a *compatible family of generators* of
the successive tensor powers, and the power law `s ^ (k+1)|_W = f ^ (k+1) · b ^ (k+1)` relating
them to the powers of the global section being inverted.
`Stacks.TensorPowerTrivialize.resTop_sectionPow` is that law only when `b` is the restriction of a
global section — which is the hypothesis being removed, so it cannot be used here.

The way the obstruction is dissolved is to take the powers of the global section with
`Stacks.SectionTensorFormula.tensorSection` rather than with `Stacks.GradedSections.mul`, so that
the power of the global section and the power of the local generator are instances of **one**
operation and the power law is `Stacks.TensorSectionPower.map_secPow` composed with
`Stacks.TensorSectionPower.secPow_smul`. See the module documentation of the sibling file for why
the two products cannot instead be compared: no lemma in either tree mentions both
`Stacks.GradedSections.mulMap` (or `Stacks.TensorSectionNonvanishing.unitMul`) and `tensorSection`,
and supplying one means computing the associator of a localized monoidal structure on sections.

Everything else is the argument of
`Stacks.SectionExtensionNoAmple.exists_tensorSection_of_quasiCompact_cover`, unchanged: the local
extension on an affine chart (`Stacks.ModuleSectionExtension.exists_pow_smul_eq_res`), the
annihilator on the quasi-compact overlaps
(`Stacks.SectionExtensionNoAmple.exists_pow_smul_eq_of_res_eq_of_isCompact`), one exponent raised
to the maximum over the cover, and the sheaf condition. The divisions that produced the ratios
`f i = s / b i` and `w i j = b j / b i` from global sections are now done by the trivializing map
of the chart (`Stacks.NonvanishingOpen.triv`), with
`Stacks.TensorSectionPower.smul_res_basis_injective` for their uniqueness and
`Stacks.NonvanishingOpen.nonvanishingLocus_inter` for `X_s ∩ W i = D(f i)`.

## Main results

* `Stacks.TensorSectionPower.exists_tensorSection_family_of_trivializing_cover`: **the gluing**,
  against a finite family of affine opens trivializing `M` with quasi-compact pairwise
  intersections, and for a finite family of sections of `F` over `X_s` at once — with **one**
  exponent and **one** `σ` for the whole family, which the argument's two maxima over the cover
  give for free, so that a consumer needing a common twist for finitely many sections needs no
  separate degree-equalisation step.
* `Stacks.TensorSectionPower.exists_tensorSection_family_of_compactSpace`: **the deliverable.** For
  `X` quasi-compact and quasi-separated, `M` invertible, `s` a global section of `M` and `F`
  quasi-coherent, every finite family of sections of `F` over `X_s` becomes, after tensoring with
  one positive power of `s`, a family of restrictions of global sections of `F ⊗ M ^⊗ (k+1)`. No
  ampleness, no global section other than `s` itself, and no `HasPointwiseNonvanishing`.
* `Stacks.TensorSectionPower.exists_tensorSection_of_trivializing_cover` and
  `exists_tensorSection_of_compactSpace`: the one-section cases, `I = PUnit`.

## What is not done, and no Stacks attribute is attached

**No `@[stacks]` attribute is attached here, and nothing here is needed for Tag 01PW.** The map
`Γ_*(X, 𝓕, L)_{(s)} → Γ(X_s, 𝓕)` of [Stacks, Tag 0B5L] that Tag 01PW's labels are assertions
about is `Stacks.SheafOfModules.sectionLocalizationMap`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/NonvanishingSections.lean`), and both of the
labels this file is about are **formalized and tagged** in
`StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean`:
`sectionLocalizationMap_injective` carries `@[stacks 01PW "part (1)"]` and
`sectionLocalizationMap_bijective` carries `@[stacks 01PW "part (2)"]`, the latter at
`[CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]`. What is proved here is the same
**surjectivity** content in a different spelling of the tensor power, reached by a different
argument; it is an independent second proof, not an input, and the comparison of the two
spellings named below is not on Tag 01PW's path.

The graded module the map is defined on **does** exist, as of
`Stacks.TwistedSectionModule.twistModule` (`TwistedSectionModule/Monoidal.lean`), with its
`ℤ`-grading in `StacksFrontier/AlgebraicGeometry/TwistedSectionModule/Grading.lean` and the source
`Γ_*(X, 𝓕, L)_{(s)}` of 0B5L's map named over
library vocabulary as `Stacks.TwistedSectionModule.sectionAtNonvanishingOpen`; its degree-`m`
summand is `Stacks.TwistedSectionModule.twistPow F L m`, the **right**-to-left iterate
`(⋯(𝓕 ⊗ L) ⊗ ⋯) ⊗ L`. That is a different bracketing from the `F ⊗ powObj M k` below — the
`𝓕` is innermost there and outermost here — and the two are not definitionally equal, so
composing this file's conclusion with that module is the same associator-on-sections obligation as
the one named above, at one more place.

**The power is `Stacks.TensorSectionPower.powObj M k`, not `Stacks.Ample.tensorPowModule X M k`.**
The consumers of the ample cluster are stated over the latter, and transporting along the
isomorphism between them needs the naturality of `tensorSection` in its module arguments, which is
absent; see the sibling file. So this does not yet discharge an `IsAmple`-flavoured consumer, and
it is not a drop-in replacement for
`Stacks.SectionExtensionNoAmple.exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing` — it is
the same mathematics at weaker hypotheses and in a different spelling of the tensor power.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample
open Stacks.NonvanishingOpen (basis trivTop nonvanishingOpen)
open Stacks.SectionExtension (resTop res_resTop exists_forall_le map_res_res map_res_res_module)
open Stacks.SectionTensorFormula (tensorSection tensorSection_smul_left tensorSection_smul_right
  map_tensorSection)

universe u

namespace Stacks.TensorSectionPower

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X : Scheme.{u}}

/-- **The gluing argument of [Stacks, Tag 01PW] over a trivializing cover, for a finite family of
sections at once and with one exponent for the whole family.**

The hypotheses are a finite family of **affine opens `W i` trivializing `M`** covering `X` and
having quasi-compact pairwise intersections, a global section `s` of `M` with `X_s = U`, and a
finite family `t ν` of sections of the quasi-coherent `F` over `U`. The conclusion is a positive
tensor power `M ^⊗ (k+1)` carrying **one** global section `σ` with `X_σ = U` — it is `s ^ (k+1)` —
and for each `ν` a global section `ρ ν` of `F ⊗ M ^⊗ (k+1)` restricting on `U` to `t ν ⊗ σ|_U`.

There is no ampleness, no `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`, and no global
section other than `s`: the generators of the powers on a chart are the powers of the chart's own
basis section.

**The family costs nothing, and that is why it is the primary statement.** The argument already
takes a maximum over the cover twice — once over the local extension exponents and once over the
annihilator exponents of the pairwise intersections — and the answer `σ` depends only on `s` and
on the resulting exponent. Indexing the sections by `ν` enlarges those two index sets from `ι` and
`ι × ι` to `I × ι` and `I × ι × ι`, and `σ` is then common to the whole family for free. A
consumer needing one common twist for finitely many sections — a finite generating family of a
finite-type module, say — therefore needs no separate "degree equalisation" step. -/
theorem exists_tensorSection_family_of_trivializing_cover (M : X.Modules)
    [IsInvertibleModule X M]
    (s : Γ(M, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} [Finite ι] (W : ι → X.Opens)
    (τ : (i : ι) → Stacks.SheafDescent.Trivialization X.presheaf M.val (W i))
    (hWaff : ∀ i, IsAffineOpen (W i))
    (hqc : ∀ i j, IsCompact ((W i ⊓ W j : X.Opens) : Set X))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, W i)
    (U : X.Opens) (hU : nonvanishingOpen X M s = U)
    {I : Type u} [Finite I] (t : I → Γ(F, U)) :
    ∃ (k : ℕ) (σ : Γ(powObj M k, ⊤)) (ρ : I → Γ(F ⊗ powObj M k, ⊤)),
      U = nonvanishingOpen X (powObj M k) σ ∧
        ∀ ν, resTop U (ρ ν) = tensorSection F (powObj M k) (t ν) (resTop U σ) := by
  classical
  -- the ratio `f i = s / b i` against the basis section of the chart
  obtain ⟨f, hfd⟩ : ∃ f : (i : ι) → Γ(X, W i), ∀ i, f i = trivTop (τ i) s := ⟨_, fun _ => rfl⟩
  have hf : ∀ i, resTop (W i) s = f i • basis (τ i) := fun i => by
    rw [hfd]; exact Stacks.NonvanishingOpen.eq_triv_smul_basis (τ i) (resTop (W i) s)
  -- `X_s ∩ W i = D(f i)`
  have hD : ∀ i, U ⊓ W i = X.basicOpen (f i) := fun i => by
    rw [hfd, ← hU]
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_inf, Stacks.NonvanishingOpen.coe_nonvanishingOpen]
    exact Stacks.NonvanishingOpen.nonvanishingLocus_inter (τ i) s
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i => by rw [← hD i]; exact inf_le_left
  have hDV : ∀ i, X.basicOpen (f i) ≤ W i := fun i => X.basicOpen_le (f i)
  -- the local extension over the affine `W i`, with the exponent raised to a single `k`
  choose e z hz using fun (ν : I) (i : ι) =>
    Stacks.ModuleSectionExtension.exists_pow_smul_eq_res F
      (hWaff i) (f i) (F.presheaf.map (homOfLE (hDU i)).op (t ν))
  obtain ⟨k, hk⟩ := exists_forall_le fun p : I × ι => e p.1 p.2
  obtain ⟨cn, hcn⟩ : ∃ cn : I → (i : ι) → Γ(F, W i), ∀ (ν : I) (i : ι) {S : X.Opens}
      (h : S ≤ X.basicOpen (f i)) (hSV : S ≤ W i) (hSU : S ≤ U),
      F.presheaf.map (homOfLE hSV).op (cn ν i)
        = X.presheaf.map (homOfLE hSV).op (f i) ^ k
            • F.presheaf.map (homOfLE hSU).op (t ν) := by
    refine ⟨fun ν i => f i ^ (k - e ν i) • z ν i, fun ν i S h hSV hSU => ?_⟩
    have h0 : F.presheaf.map (homOfLE (hDV i)).op (z ν i)
        = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ e ν i
          • F.presheaf.map (homOfLE (hDU i)).op (t ν) := (hz ν i).symm
    change F.presheaf.map (homOfLE (h.trans (hDV i))).op (f i ^ (k - e ν i) • z ν i)
      = X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i) ^ k
          • F.presheaf.map (homOfLE (h.trans (hDU i))).op (t ν)
    rw [← map_res_res_module h (hDV i) (f i ^ (k - e ν i) • z ν i)]
    simp only [Scheme.Modules.map_smul, map_pow, h0, map_res_res, map_res_res_module, smul_smul,
      ← pow_add]
    rw [Nat.sub_add_cancel (hk (ν, i))]
  -- the ratio `w i j = b j / b i` of the two basis sections on the overlap `W i ⊓ W j`
  obtain ⟨w, hw⟩ : ∃ w : (i j : ι) → Γ(X, (W i ⊓ W j : X.Opens)), ∀ i j,
      M.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (basis (τ j))
        = w i j • M.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (basis (τ i)) := by
    refine ⟨fun i j => Stacks.NonvanishingOpen.triv (τ i)
      (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))
      (M.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (basis (τ j))),
      fun i j => ?_⟩
    exact Stacks.SectionProduct.eq_triv_smul_res_basis (τ i)
      (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)) _
  obtain ⟨fA, hfA⟩ : ∃ fA : (i j : ι) → Γ(X, (W i ⊓ W j : X.Opens)), ∀ i j,
      fA i j = X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (f i) :=
    ⟨_, fun _ _ => rfl⟩
  -- `f i = f j * w i j` on the overlap: both compute `s` against `b i`
  have hfw : ∀ i j : ι, fA i j
      = X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (f j) * w i j := by
    intro i j
    rw [hfA]
    refine smul_res_basis_injective (τ i) (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)) ?_
    have h1 : M.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (resTop (W i) s)
        = X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (f i)
          • M.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (basis (τ i)) := by
      rw [hf i, Scheme.Modules.map_smul]
    have h2 : M.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (resTop (W j) s)
        = (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (f j) * w i j)
          • M.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (basis (τ i)) := by
      rw [hf j, Scheme.Modules.map_smul, hw i j, smul_smul]
    rw [← h1, ← h2, res_resTop, res_resTop]
  have hBA : ∀ i j : ι, X.basicOpen (fA i j) ≤ W i ⊓ W j := fun i j => X.basicOpen_le _
  have hBD : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f i) := fun i j => by
    rw [hfA, Scheme.basicOpen_res]; exact inf_le_right
  have hBU : ∀ i j : ι, X.basicOpen (fA i j) ≤ U := fun i j => (hBD i j).trans (hDU i)
  have hBD' : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f j) := fun i j => by
    rw [← hD j]
    exact le_inf (hBU i j) ((hBA i j).trans inf_le_right)
  -- the two numerators agree where `s` does not vanish, so a power of `f i` kills the difference
  have hzero : ∀ (ν : I) (i j : ι),
      F.presheaf.map (homOfLE (X.basicOpen_le (fA i j))).op
          (F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (cn ν i))
        = F.presheaf.map (homOfLE (X.basicOpen_le (fA i j))).op
          (w i j ^ k
            • F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (cn ν j)) := by
    intro ν i j
    have hfib : X.presheaf.map (homOfLE ((hBD i j).trans (hDV i))).op (f i)
        = X.presheaf.map (homOfLE ((hBD' i j).trans (hDV j))).op (f j)
            * X.presheaf.map (homOfLE (hBA i j)).op (w i j) := by
      have h := congrArg (X.presheaf.map (homOfLE (hBA i j)).op)
        ((hfA i j).symm.trans (hfw i j))
      rw [map_mul, map_res_res, map_res_res] at h
      exact h
    rw [map_res_res_module, Scheme.Modules.map_smul, map_pow, map_res_res_module,
      hcn ν i (hBD i j) ((hBD i j).trans (hDV i)) (hBU i j),
      hcn ν j (hBD' i j) ((hBD' i j).trans (hDV j)) (hBU i j), hfib, smul_smul, mul_pow]
    ring_nf
  choose m hm using fun (ν : I) (i j : ι) =>
    Stacks.SectionExtensionNoAmple.exists_pow_smul_eq_of_res_eq_of_isCompact F (hqc i j) (fA i j)
      (F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (cn ν i))
      (w i j ^ k • F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (cn ν j))
      (hzero ν i j)
  obtain ⟨q, hq⟩ := exists_forall_le fun p : I × ι × ι => m p.1 p.2.1 p.2.2
  have hm' : ∀ (ν : I) (i j : ι), fA i j ^ (q + 1) •
      (F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (cn ν i))
        = fA i j ^ (q + 1) • (w i j ^ k •
            F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (cn ν j)) := by
    intro ν i j
    have hmq : m ν i j ≤ q := hq (ν, i, j)
    have h : q + 1 = q + 1 - m ν i j + m ν i j := by omega
    rw [h, pow_add, mul_smul, mul_smul, hm ν i j]
  -- the exponent of the answer: `K + 1 = k + (q + 1)`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = k + (q + 1) := ⟨k + q, by omega⟩
  have hK' : K + 1 = q + 1 + k := by omega
  -- the power law, for the global section against the chart's own basis section
  have hσ : ∀ i, resTop (W i) (secPow M s K)
      = f i ^ (K + 1) • secPow M (basis (τ i)) K := by
    intro i
    have h := map_secPow M (homOfLE (le_top : W i ≤ ⊤)) s K
    rw [show M.presheaf.map _ s = _ from hf i, secPow_smul] at h
    exact h
  have hβ : ∀ i j : ι,
      (powObj M K).presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
          (secPow M (basis (τ j)) K)
        = w i j ^ (K + 1) • (powObj M K).presheaf.map
            (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (secPow M (basis (τ i)) K) := by
    intro i j
    rw [map_secPow, map_secPow, hw i j, secPow_smul]
  -- the numerators agree on the overlaps, by the annihilator and `f i = f j * w i j`
  have hγA : ∀ (ν : I) (i j : ι),
      F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (f i ^ (q + 1) • cn ν i)
      = w i j ^ (K + 1) • F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
          (f j ^ (q + 1) • cn ν j) := by
    intro ν i j
    have hscal : fA i j ^ (q + 1) * w i j ^ k
        = w i j ^ (K + 1) *
          X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (f j) ^ (q + 1) := by
      rw [hfw i j, mul_pow, hK]
      ring
    simp only [Scheme.Modules.map_smul, map_pow]
    rw [← hfA i j, hm' ν i j, smul_smul, hscal, smul_smul]
  -- and they compute `t` against the generator over `U ⊓ W i`
  have hγD : ∀ (ν : I) (i : ι),
      F.presheaf.map (homOfLE (hDV i)).op (f i ^ (q + 1) • cn ν i)
      = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) •
          F.presheaf.map (homOfLE (hDU i)).op (t ν) := by
    intro ν i
    rw [Scheme.Modules.map_smul, map_pow, hcn ν i le_rfl (hDV i) (hDU i), smul_smul, ← pow_add,
      ← hK']
  -- the local sections, and their compatibility
  have hcompat : ∀ (ν : I) (i j : ι),
      (F ⊗ powObj M K).presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op
          (tensorSection F (powObj M K) (f i ^ (q + 1) • cn ν i) (secPow M (basis (τ i)) K))
        = (F ⊗ powObj M K).presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
          (tensorSection F (powObj M K) (f j ^ (q + 1) • cn ν j)
            (secPow M (basis (τ j)) K)) := by
    intro ν i j
    rw [map_tensorSection, map_tensorSection, hβ i j, tensorSection_smul_right,
      ← tensorSection_smul_left, hγA ν i j]
  -- one gluing per member of the family, all at the one exponent `K`
  have hglue : ∀ ν : I, ∃ ρ : Γ(F ⊗ powObj M K, ⊤), ∀ i : ι,
      resTop (W i) ρ = tensorSection F (powObj M K) (f i ^ (q + 1) • cn ν i)
        (secPow M (basis (τ i)) K) := by
    intro ν
    obtain ⟨ρ, hρ, -⟩ := TopCat.Sheaf.existsUnique_gluing'
      (⟨(F ⊗ powObj M K).presheaf, (F ⊗ powObj M K).isSheaf⟩ : TopCat.Sheaf Ab X) W ⊤
      (fun _ => homOfLE le_top) hcover _ (hcompat ν)
    exact ⟨ρ, hρ⟩
  choose ρ hρ using hglue
  refine ⟨K, secPow M s K, ρ, ?_, fun ν => ?_⟩
  · rw [← hU]
    exact (nonvanishingOpen_secPow M s K).symm
  · refine TopCat.Presheaf.IsSheaf.section_ext (F ⊗ powObj M K).isSheaf (U := op U) ?_
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover (TopologicalSpace.Opens.mem_top x))
    refine ⟨X.basicOpen (f i), hDU i, ?_, ?_⟩
    · rw [← hD i]; exact ⟨hx, hi⟩
    · have hti : resTop (W i) (ρ ν) = tensorSection F (powObj M K) (f i ^ (q + 1) • cn ν i)
          (secPow M (basis (τ i)) K) := hρ ν i
      have hleft : (F ⊗ powObj M K).presheaf.map (homOfLE (hDU i)).op (resTop U (ρ ν))
          = tensorSection F (powObj M K)
              (X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) •
                F.presheaf.map (homOfLE (hDU i)).op (t ν))
              ((powObj M K).presheaf.map (homOfLE (hDV i)).op (secPow M (basis (τ i)) K)) := by
        rw [res_resTop, ← res_resTop (ρ ν) (hDV i), hti, map_tensorSection, hγD ν i]
      have hright : (F ⊗ powObj M K).presheaf.map (homOfLE (hDU i)).op
            (tensorSection F (powObj M K) (t ν) (resTop U (secPow M s K)))
          = tensorSection F (powObj M K) (F.presheaf.map (homOfLE (hDU i)).op (t ν))
              (X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) •
                (powObj M K).presheaf.map (homOfLE (hDV i)).op
                  (secPow M (basis (τ i)) K)) := by
        rw [map_tensorSection, res_resTop, ← res_resTop (secPow M s K) (hDV i), hσ i,
          Scheme.Modules.map_smul, map_pow]
      rw [hleft, hright, tensorSection_smul_right, ← tensorSection_smul_left]

/-- **The gluing argument of [Stacks, Tag 01PW] over a trivializing cover**, for one section: the
`I = PUnit` case of
`Stacks.TensorSectionPower.exists_tensorSection_family_of_trivializing_cover`. -/
theorem exists_tensorSection_of_trivializing_cover (M : X.Modules) [IsInvertibleModule X M]
    (s : Γ(M, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} [Finite ι] (W : ι → X.Opens)
    (τ : (i : ι) → Stacks.SheafDescent.Trivialization X.presheaf M.val (W i))
    (hWaff : ∀ i, IsAffineOpen (W i))
    (hqc : ∀ i j, IsCompact ((W i ⊓ W j : X.Opens) : Set X))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, W i)
    (U : X.Opens) (hU : nonvanishingOpen X M s = U) (t : Γ(F, U)) :
    ∃ (k : ℕ) (σ : Γ(powObj M k, ⊤)) (ρ : Γ(F ⊗ powObj M k, ⊤)),
      U = nonvanishingOpen X (powObj M k) σ ∧
        resTop U ρ = tensorSection F (powObj M k) t (resTop U σ) := by
  obtain ⟨k, σ, ρ, hloc, heq⟩ := exists_tensorSection_family_of_trivializing_cover M s F W τ
    hWaff hqc hcover U hU (fun _ : PUnit.{u + 1} => t)
  exact ⟨k, σ, ρ PUnit.unit, hloc, heq PUnit.unit⟩

/-- **The surjectivity half of [Stacks, Tag 01PW] at Tag 01PW's own hypotheses.** For `X`
quasi-compact and quasi-separated, `M` an invertible `𝒪_X`-module, `s` a global section of `M` and
`F` a quasi-coherent `𝒪_X`-module, every section `t` of `F` over the nonvanishing open `X_s`
extends, after tensoring with a positive power of `s`, to a global section of
`F ⊗ M ^⊗ (k+1)`: there are `k`, a global section `σ` of `M ^⊗ (k+1)` with `X_σ = X_s` — it is
`s ^ (k+1)` — and a global section `ρ` of `F ⊗ M ^⊗ (k+1)` with `ρ|_{X_s} = t ⊗ σ|_{X_s}`.

Stated for a finite **family** of sections with one common `σ`, which the argument gives for
free; `Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace` is the one-section case.

The cover is `Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover` and the overlaps are
quasi-compact by quasi-separatedness. **There is no ampleness hypothesis and no
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`**: the only global section anywhere in
the argument is `s` itself. -/
theorem exists_tensorSection_family_of_compactSpace [CompactSpace X] [QuasiSeparatedSpace X]
    (M : X.Modules) [IsInvertibleModule X M] (s : Γ(M, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : nonvanishingOpen X M s = U)
    {I : Type u} [Finite I] (t : I → Γ(F, U)) :
    ∃ (k : ℕ) (σ : Γ(powObj M k, ⊤)) (ρ : I → Γ(F ⊗ powObj M k, ⊤)),
      U = nonvanishingOpen X (powObj M k) σ ∧
        ∀ ν, resTop U (ρ ν) = tensorSection F (powObj M k) (t ν) (resTop U σ) := by
  obtain ⟨ι, hι, W, hWaff, hcover, htriv⟩ :=
    Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover M
  have : Finite ι := hι
  have hqc : ∀ i j, IsCompact ((W i ⊓ W j : X.Opens) : Set X) := by
    intro i j
    have h := QuasiSeparatedSpace.inter_isCompact (α := X) (W i : Set X) (W j : Set X)
      (W i).2 (hWaff i).isCompact (W j).2 (hWaff j).isCompact
    rwa [TopologicalSpace.Opens.coe_inf]
  exact exists_tensorSection_family_of_trivializing_cover M s F W (fun i => (htriv i).some) hWaff
    hqc hcover U hU t

/-- **The surjectivity half of [Stacks, Tag 01PW] at Tag 01PW's own hypotheses**, for one
section: the `I = PUnit` case of
`Stacks.TensorSectionPower.exists_tensorSection_family_of_compactSpace`. -/
theorem exists_tensorSection_of_compactSpace [CompactSpace X] [QuasiSeparatedSpace X]
    (M : X.Modules) [IsInvertibleModule X M] (s : Γ(M, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : nonvanishingOpen X M s = U) (t : Γ(F, U)) :
    ∃ (k : ℕ) (σ : Γ(powObj M k, ⊤)) (ρ : Γ(F ⊗ powObj M k, ⊤)),
      U = nonvanishingOpen X (powObj M k) σ ∧
        resTop U ρ = tensorSection F (powObj M k) t (resTop U σ) := by
  obtain ⟨k, σ, ρ, hloc, heq⟩ := exists_tensorSection_family_of_compactSpace M s F U hU
    (fun _ : PUnit.{u + 1} => t)
  exact ⟨k, σ, ρ PUnit.unit, hloc, heq PUnit.unit⟩

end Stacks.TensorSectionPower

end
