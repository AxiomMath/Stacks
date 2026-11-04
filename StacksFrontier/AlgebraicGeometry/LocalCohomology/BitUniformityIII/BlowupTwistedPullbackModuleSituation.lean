module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupFreeCohomology
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupModuleSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupPresentationSequences
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.PullbackCohomology
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A `ModuleSituation` on the blowup, from twisted pullbacks of `A`-modules

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X → Spec(A)` the blowup of `Spec(A)` in
`I`. This file exhibits `Stacks.LocalCohomology.UniformityIII.ModuleSituation`, the data and
standing hypotheses of [Stacks, Tag 0GAA], on that blowup, so that the five clauses of Tag 0GAA
hold there rather than only in the two degenerate witnesses `topModuleSituation` and
`affineModuleSituation`.

The cohomology groups here are those of the twisted pullbacks `𝒪_X(q) ⊗ p^*Ñ` of the `A`-modules
`N` underlying `(A, n, c)`-modules (`Stacks.LocalCohomology.UniformityIII.twistedPullbackFunctor`),
on the Situation `blowupSituationOf` whose `d` is a Čech vanishing degree. The witness
`Stacks.LocalCohomology.UniformityIII.blowupModuleSituation` of
`BitUniformityIII/BlowupModuleSituation.lean` records the same data through the pullback
`thickeningPullback` of `A ⧸ Iⁿ`-modules with integer twists, at `d = d(S)`; the
`TwistedModuleSituation`, `DualSituation` and corrected Tag 0GAD built on this file
(`BitUniformityIII/BlowupTwistedModuleSituation.lean`, …, `BitUniformityIII/BlowupExtension.lean`)
compute with the twisted-pullback model.

## What was already in hand

`BitUniformityIII/BlowupSituation.lean` gives the underlying Situation of [Stacks, Tag 0GA6],
`Stacks.LocalCohomology.UniformityIII.blowupSituationOf`.
`BitUniformityIII/BlowupFreeCohomology.lean` gives the field `freeIso`,
`Stacks.LocalCohomology.UniformityIII.blowupFreeIsoSituationOf`.
`BitUniformityIII/BlowupPresentationSequences.lean` gives the two short exact sequences
`0 → 𝒢 → (𝒪_{Yₙ})^{⊕r}(q) → p^*M(q) → 0` and `0 → ℱ → p^*K(q) → 𝒢 → 0` that the proof of
Tag 0GAA splits a pulled-back presentation into, for an arbitrary short exact sequence of
`A`-modules.

## What is added here

Two things.

* **The quasi-coherence of `𝒢` and of `ℱ`.** These are the fields `vanishing_HG` and
  `vanishing_HF`, which ask for `Hⁱ(X, 𝒢(q)) = Hⁱ(X, ℱ(q)) = 0` above the invariant `d`, and
  `Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH` supplies that for
  every quasi-coherent sheaf at once. `𝒢` and `ℱ` are a kernel and a kernel of a kernel, and the
  kernel of a morphism of quasi-coherent modules is quasi-coherent on an **arbitrary** scheme:
  that is `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, [Stacks, Tag 01LB]
  (kernel half), proved affine-locally from the locality of quasi-coherence. No affineness
  hypothesis is involved, so nothing has to be generalized for the blowup; what carries
  `[IsAffine X]` is the unrelated `Stacks.AffineTilde.isQuasicoherent_kernel`, the affine
  statement [Stacks, Tag 01IC].

* **The presentation of an `(A, n, c)`-module as a short exact sequence of `A`-modules**, which
  is what the two sequences of `BitUniformityIII/BlowupPresentationSequences.lean` are applied
  to, and then the witness itself.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.ANCPresentation.resShortComplex`: a chosen finite free
  presentation of an `(A, n, c)`-module, read as a short complex of `A`-modules.
* `Stacks.LocalCohomology.UniformityIII.blowupModuleSituationOf`: **the witness**, a
  `ModuleSituation` on the blowup extending `blowupSituationOf`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.isQuasicoherent_twistedPullbackImage` and
  `…_twistedPullbackSupported`: **`𝒢` and `ℱ` are quasi-coherent.**
* `Stacks.LocalCohomology.UniformityIII.ANCPresentation.shortExact_resShortComplex`: the chosen
  presentation is short exact over `A`.
* `Stacks.LocalCohomology.UniformityIII.nonempty_moduleSituation`: **`ModuleSituation` is
  inhabited** for every Noetherian ring, every ideal and every pair of exponents `c ≤ n`.
* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupHmodTwistedPullback_top` and
  `…_next`: **clauses (1) and (2) of [Stacks, Tag 0GAA] on the blowup**, i.e. the two clauses
  that `ModuleSituation` discharges, read off the witness and stated about the blowup's own
  cohomology.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### `𝒢` and `ℱ` are quasi-coherent -/

section Quasicoherent

variable {S : ShortComplex (ModuleCat.{u} A)} (q : ℤ)

/-- **The sheaf `𝒢` of the proof of [Stacks, Tag 0GAA] is quasi-coherent.** It is the kernel of
`(𝒪_{Yₙ})^{⊕r}(q) → p^*M(q)`, both of which are quasi-coherent by
`isQuasicoherent_twistedGeometricFactor_obj`, and the kernel of a morphism of quasi-coherent
modules is quasi-coherent on an arbitrary scheme
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, [Stacks, Tag 01LB]). The blowup is
not affine, so the affine statement [Stacks, Tag 01IC] would not serve.

`Stacks.LocalCohomology.UniformityIII.twistedPullbackImage` is `CategoryTheory.ShortComplex.cycles`
rather than `CategoryTheory.Limits.kernel`, so the two limit cones are compared by
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`. -/
instance isQuasicoherent_twistedPullbackImage :
    (twistedPullbackImage I q (S := S)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (blowupScheme I).ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel (S.map (twistedPullbackFunctor I q)).g)
      (S.map (twistedPullbackFunctor I q)).cyclesIsKernel)
    (@Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (blowupScheme I) _ _
      (S.map (twistedPullbackFunctor I q)).g
      (isQuasicoherent_twistedGeometricFactor_obj I q S.X₂)
      (isQuasicoherent_twistedGeometricFactor_obj I q S.X₃))

/-- **The sheaf `ℱ` of the proof of [Stacks, Tag 0GAA] is quasi-coherent.** It is the kernel of
`p^*K(q) → 𝒢`, whose source is quasi-coherent by `isQuasicoherent_twistedGeometricFactor_obj` and
whose target is quasi-coherent by `isQuasicoherent_twistedPullbackImage`. -/
instance isQuasicoherent_twistedPullbackSupported :
    (twistedPullbackSupported I q (S := S)).IsQuasicoherent :=
  @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (blowupScheme I) _ _
    (S.map (twistedPullbackFunctor I q)).toCycles
    (isQuasicoherent_twistedGeometricFactor_obj I q S.X₁)
    (isQuasicoherent_twistedPullbackImage I q)

/-- **`Hⁱ(X, 𝒢(q)) = 0` above the vanishing degree of the blowup.** This is the field
`vanishing_HG` of `Stacks.LocalCohomology.UniformityIII.ModuleSituation` for a witness built on
`blowupSituationOf`, whose `d` is exactly that degree. -/
theorem subsingleton_blowupHmod_twistedPullbackImage [IsNoetherianRing A] (i : ℕ)
    (hi : (exists_forall_subsingleton_blowupH I).choose < i) :
    Subsingleton (blowupHmod I i (twistedPullbackImage I q (S := S))) :=
  subsingleton_blowupHmod I i _
    ((exists_forall_subsingleton_blowupH I).choose_spec _ inferInstance i hi)

/-- **`Hⁱ(X, ℱ(q)) = 0` above the vanishing degree of the blowup**, the field `vanishing_HF`. -/
theorem subsingleton_blowupHmod_twistedPullbackSupported [IsNoetherianRing A] (i : ℕ)
    (hi : (exists_forall_subsingleton_blowupH I).choose < i) :
    Subsingleton (blowupHmod I i (twistedPullbackSupported I q (S := S))) :=
  subsingleton_blowupHmod I i _
    ((exists_forall_subsingleton_blowupH I).choose_spec _ inferInstance i hi)

end Quasicoherent

/-! ### `𝒪_{Y₀} = 0`

`Hⁱ(X, 𝒪_{Y₀}(q)) = 0`, the field `subsingleton_Hdiv_zero`, is
`Stacks.LocalCohomology.UniformityIII.subsingleton_blowupHmod_thickeningTwist_zero` of
`BitUniformityIII/BlowupModuleSituation.lean`. -/

/-! ### A chosen presentation as a short exact sequence of `A`-modules -/

namespace ANCPresentation

variable [IsNoetherianRing A] {I} {n c : ℕ} {M : ANCModule I n c}

/-- **A chosen finite free presentation `0 → K → (A/Iⁿ)^{⊕r} → M → 0` of an `(A, n, c)`-module,
read as a short complex of `A`-modules.** Its three terms are `resModule I n K`,
`ModuleCat.of A (Fin r → A ⧸ Iⁿ)` and `resModule I n M`, the last being the `A`-module underlying
`M`; the two maps are the presentation's own, which are `A`-linear because the `A`-module
structures factor through `A → A ⧸ Iⁿ`.

This is what the two short exact sequences of
`BitUniformityIII/BlowupPresentationSequences.lean` are applied to: the twisted pullback is a
functor out of `ModuleCat A`, so the presentation has to be read over `A` before it can be pulled
back. -/
def resShortComplex (P : ANCPresentation I n c M) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map (ModuleCat.ofHom P.incl))
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map (ModuleCat.ofHom P.proj))
    (by
      ext x
      exact (P.range_incl_eq_ker_proj.le ⟨x, rfl⟩ : _))

omit [IsNoetherianRing A] in
/-- The middle term of `resShortComplex` is the free module `(A ⧸ Iⁿ)^{⊕r}` over `A`, which is
the module `Stacks.LocalCohomology.UniformityIII.blowupFreeIso` computes the cohomology of the
twisted pullback of. -/
@[simp] theorem resShortComplex_X₂ (P : ANCPresentation I n c M) :
    P.resShortComplex.X₂ = ModuleCat.of A (Fin P.rank → A ⧸ I ^ n) := rfl

/-- The first term of `resShortComplex` is the `A`-module underlying the kernel of the chosen
presentation, which is again an `(A, n, c)`-module (`ANCPresentation.kernelANC`). -/
@[simp] theorem resShortComplex_X₁ (P : ANCPresentation I n c M) :
    P.resShortComplex.X₁ = resModule I n P.kernelANC.1 := rfl

omit [IsNoetherianRing A] in
/-- The last term of `resShortComplex` is the `A`-module underlying `M`. -/
@[simp] theorem resShortComplex_X₃ (P : ANCPresentation I n c M) :
    P.resShortComplex.X₃ = resModule I n M.1 := rfl

omit [IsNoetherianRing A] in
/-- **The chosen presentation is short exact over `A`.** Restriction of scalars does not change
the underlying maps, so injectivity, surjectivity and exactness in the middle are the
presentation's own three fields. -/
theorem shortExact_resShortComplex (P : ANCPresentation I n c M) :
    P.resShortComplex.ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact P.range_incl_eq_ker_proj.ge hx
  mono_f := (ModuleCat.mono_iff_injective _).2 P.incl_injective
  epi_g := (ModuleCat.epi_iff_surjective _).2 P.proj_surjective

end ANCPresentation

/-! ### The witness -/

section Witness

variable [IsNoetherianRing A]

/-- The presentation of an `(A, n, c)`-module chosen once and for all, which is the field `pres`
of `Stacks.LocalCohomology.UniformityIII.ModuleSituation`. One exists by
`nonempty_ANCPresentation`, so this is a genuine choice and not a further hypothesis. -/
def blowupANCPres (n c : ℕ) (M : ANCModule I n c) : ANCPresentation I n c M :=
  (nonempty_ANCPresentation M).some

/-- The chosen presentation of an `(A, n, c)`-module as a short exact sequence of `A`-modules,
`0 → K → (A/Iⁿ)^{⊕r} → M → 0`. This is the short complex the two sequences of
`BitUniformityIII/BlowupPresentationSequences.lean` are applied to. -/
abbrev blowupPresShortComplex (n c : ℕ) (M : ANCModule I n c) :
    ShortComplex (ModuleCat.{u} A) :=
  (blowupANCPres I n c M).resShortComplex

/-- **A `ModuleSituation` on the blowup**: the data and standing hypotheses of
[Stacks, Tag 0GAA] hold for the blowup of `Spec(A)` in `I`, for a Noetherian ring `A`, any ideal
`I`, any `q₀` with the defining property of `q(S)` and any exponents `c ≤ n`. In particular the
two clauses of Tag 0GAA that `ModuleSituation` carries — `subsingleton_H_top` (clause (1)) and
`subsingleton_H_next` (clause (2)) — hold on the blowup.

Each of the four cohomology families is the blowup's own `blowupHmod`, taken at: the twisted
pullback of `M` (`H`); the twisted pullback of the free module `(A ⧸ Iⁿ)^{⊕r}` of the chosen
presentation (`Hfree`); the kernel `𝒢` of `(𝒪_{Yₙ})^{⊕r}(q) → p^*M(q)`
(`HG`, `twistedPullbackImage`); and the kernel `ℱ` of `p^*K(q) → 𝒢`
(`HF`, `twistedPullbackSupported`).

The comparison maps and their exactness are the long exact sequences of `blowupDeltaMod` at
`shortExact_twistedPullbackFreeSequence` and `shortExact_twistedPullbackKernelSequence`. The
three vanishing fields are `exists_forall_subsingleton_blowupH` applied to three quasi-coherent
sheaves — the third and fourth through `isQuasicoherent_twistedPullbackImage` and
`isQuasicoherent_twistedPullbackSupported`. `freeIso` is `blowupFreeIsoSituationOf` and
`subsingleton_Hdiv_zero` is `subsingleton_blowupHmod_thickeningTwist_zero`. -/
def blowupModuleSituationOf (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    ModuleSituation A I n c where
  toSituation := blowupSituationOf I q₀ h
  exponent_le := hcn
  pres := blowupANCPres I n c
  H M i q := blowupHmodTwistedPullback I (resModule I n M.1) i q
  Hfree M i q := blowupHmodTwistedPullback I
    (ModuleCat.of A (Fin (blowupANCPres I n c M).rank → A ⧸ I ^ n)) i q
  HG M i q := blowupHmod I i (twistedPullbackImage I q (S := blowupPresShortComplex I n c M))
  HF M i q := blowupHmod I i (twistedPullbackSupported I q (S := blowupPresShortComplex I n c M))
  freeIso M i q := blowupFreeIsoSituationOf I q₀ h n (blowupANCPres I n c M).rank i q
  subsingleton_Hdiv_zero i q := subsingleton_blowupHmod_thickeningTwist_zero I i q
  vanishing_H M i q hi := subsingleton_blowupHmodTwistedPullback_blowupSituationOf I q₀ h
    (resModule I n M.1) i q hi
  vanishing_HG _M i q hi := subsingleton_blowupHmod_twistedPullbackImage I q i hi
  vanishing_HF _M i q hi := subsingleton_blowupHmod_twistedPullbackSupported I q i hi
  freeToPullback M i q := (blowupHmodMap I i
    ((twistedPullbackFunctor I q).map (blowupPresShortComplex I n c M).g)).hom
  pullbackToImage M i q := ((blowupDeltaMod I).δ (shortExact_twistedPullbackFreeSequence I q
    (blowupANCPres I n c M).shortExact_resShortComplex) i).hom
  exact_pullback M i q := exact_blowupHmodMap_δ I _ _ _
    (shortExact_twistedPullbackFreeSequence I q
      (blowupANCPres I n c M).shortExact_resShortComplex) i
  kernelToImage M i q := (blowupHmodMap I i
    ((blowupPresShortComplex I n c M).map (twistedPullbackFunctor I q)).toCycles).hom
  imageToSupported M i q := ((blowupDeltaMod I).δ (shortExact_twistedPullbackKernelSequence I q
    (blowupANCPres I n c M).shortExact_resShortComplex) i).hom
  exact_image M i q := exact_blowupHmodMap_δ I _ _ _
    (shortExact_twistedPullbackKernelSequence I q
      (blowupANCPres I n c M).shortExact_resShortComplex) i

/-- **`Stacks.LocalCohomology.UniformityIII.ModuleSituation` is inhabited for every Noetherian
ring, every ideal and every pair of exponents `c ≤ n`**, by the blowup: `blowupModuleSituationOf`
at the integer `qS I`. -/
theorem nonempty_moduleSituation (n c : ℕ) (hcn : c ≤ n) :
    Nonempty (ModuleSituation A I n c) :=
  ⟨blowupModuleSituationOf I (qS I) (isBaseThreshold_qS I) n c hcn⟩

/-! ### The two clauses of Tag 0GAA that the witness discharges on the blowup -/

/-- **[Stacks, Tag 0GAA], clause (1), on the blowup.** For an `(A, n, c)`-module `M` with
`c ≤ n`, and for `q ≥ q₀` and `d ≥ 1` with `d` the vanishing degree of
`exists_forall_subsingleton_blowupH`, the top cohomology `H^d(X, 𝒪_X(q) ⊗ p^*M̃)` vanishes.

This is `ModuleSituation.subsingleton_H_top` at `blowupModuleSituationOf`; the point is that the
statement is now about the blowup's own cohomology rather than about an abstract witness. -/
theorem subsingleton_blowupHmodTwistedPullback_top (q₀ : ℕ) (h : IsBaseThreshold I q₀)
    (n c : ℕ) (hcn : c ≤ n) (M : ANCModule I n c) {q : ℤ}
    (hd : 1 ≤ (exists_forall_subsingleton_blowupH I).choose) (hq : (q₀ : ℤ) ≤ q) :
    Subsingleton (blowupHmodTwistedPullback I (resModule I n M.1)
      (exists_forall_subsingleton_blowupH I).choose q) :=
  (blowupModuleSituationOf I q₀ h n c hcn).subsingleton_H_top M hd hq

/-- **[Stacks, Tag 0GAA], clause (2), on the blowup.** In the next degree down,
`H^{d-1}(X, 𝒪_X(q) ⊗ p^*M̃) = 0` for `q ≥ q₀`, provided `d - 1 ≥ 1`. The hypothesis `i = d - 1`
is written `i + 1 = d` to avoid a truncated subtraction. -/
theorem subsingleton_blowupHmodTwistedPullback_next (q₀ : ℕ) (h : IsBaseThreshold I q₀)
    (n c : ℕ) (hcn : c ≤ n) (M : ANCModule I n c) {i : ℕ} {q : ℤ} (hi : 1 ≤ i)
    (hid : i + 1 = (exists_forall_subsingleton_blowupH I).choose) (hq : (q₀ : ℤ) ≤ q) :
    Subsingleton (blowupHmodTwistedPullback I (resModule I n M.1) i q) :=
  (blowupModuleSituationOf I q₀ h n c hcn).subsingleton_H_next M hi hid hq

end Witness

end Stacks.LocalCohomology.UniformityIII

end
