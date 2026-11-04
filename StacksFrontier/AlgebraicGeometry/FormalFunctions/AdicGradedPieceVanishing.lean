module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorExceptionalCohomology
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorExceptionalImmersion
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorIdealGenerated
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Vanishing
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicGradedPieceGenerated
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowGeneratingSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientCohomologyBound
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.EquationsBaseChange
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorProper
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafExactAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H¹` vanishing on the graded pieces of the `𝓘`-adic filtration

Let `Y` be a scheme, `𝓘` a quasi-coherent sheaf of ideals on it and `ℱ` a sheaf of modules. The
inverse-limit induction of [Stacks, Tag 0EXD] proved in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AdicGradedPieceShortExact.lean` asks for the
vanishing of `H¹(Y, 𝓘 ᵐ ℱ / 𝓘 ⁿ ℱ)` for **every** pair `m ≤ n`. This file turns the two inputs
the source actually provides into that hypothesis:

* the *consecutive* pieces `𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ` are annihilated by `𝓘`, hence live on the
  exceptional line `E = Proj (exceptionalGrading A f₁ f₂) = 𝐏¹_Z`, where global generation kills
  `H¹` unconditionally
  (`Stacks.AlmostBlowUp.isZero_cohomology_one_exceptional_of_generatingSections`); and
* a general piece `𝓘 ᵐ ℱ / 𝓘 ⁿ ℱ` is built from consecutive ones by the short exact sequences
  `0 ⟶ 𝓘 ⁿ⁻¹ ℱ / 𝓘 ⁿ ℱ ⟶ 𝓘 ᵐ ℱ / 𝓘 ⁿ ℱ ⟶ 𝓘 ᵐ ℱ / 𝓘 ⁿ⁻¹ ℱ ⟶ 0` of a nested chain of
  submodules, along which `H¹` vanishing propagates.

Both bullets are proved here outright. The general statements keep the module `𝒢ₖ` on `E` and the
isomorphism `i_* 𝒢ₖ ≅ 𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ` as explicit data, since they are stated for an arbitrary
closed immersion out of the exceptional line; for the two-generator square itself every piece of
that data is constructed below, and the final corollary carries nothing about the square.

## Main results

* `Stacks.Cohomology.FormalFunctions.shortExact_nestedQuotient`: **the quotients of a nested
  chain `N₃ ≤ N₂ ≤ N₁` of subsheaves sit in a short exact sequence**
  `0 ⟶ N₂/N₃ ⟶ N₁/N₃ ⟶ N₁/N₂ ⟶ 0`, with the composite inclusion presented by a variable.
* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_nestedQuotient`: `H¹(N₁/N₃)`
  vanishes once `H¹(N₂/N₃)` and `H¹(N₁/N₂)` do.
* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_adicGradedPiece_of_consecutive`:
  **`H¹` vanishes on every graded piece `𝓘 ᵐ ℱ / 𝓘 ⁿ ℱ` as soon as it vanishes on the
  consecutive pieces.** No hypothesis beyond that.
* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_exceptional_of_generatingSections`:
  the exceptional-line vanishing in Mathlib's `ℕ`-indexing.
* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_gradedPiece_of_generatingSections`:
  **`H¹(Y, 𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ) = 0`** for a graded piece presented as the direct image of a
  globally generated quasi-coherent module on the exceptional line.
* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_gradedPiece_of_pullback`: the same,
  with the generating sections produced from global generation of `𝓘 ᵏ` and `ℱ / 𝓘 ℱ` on `Y`.
* `Stacks.Cohomology.FormalFunctions.idealPowerMultiple_one_adicGradedPieceModule_eq_bot`:
  **the consecutive graded piece `𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ` is annihilated by `𝓘`.**
* `Stacks.Cohomology.FormalFunctions.annihilatedByKer_adicGradedPieceModule`: the same read over
  *every* open as annihilation by the sections killed by a closed immersion with ideal sheaf `𝓘`.
* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_gradedPiece_of_ker`:
  **`H¹(Y, 𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ) = 0` with no presentation carried**, for a closed immersion of the
  exceptional line whose ideal sheaf is `𝓘`.
* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_of_exceptional`:
  **the hypothesis `hz` of
  `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_of_isZero_gradedPiece` is
  discharged** from the exceptional-line data, one module per consecutive piece.
* `Stacks.Cohomology.FormalFunctions.comap_centerIdealSheaf_eq_baseIdealSheaf`: the ideal sheaf
  of the exceptional divisor of the two-generator square is `(f₁,f₂) 𝒪_{X'}`.
* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_twoGenerator`: **the
  inverse-limit induction for the two-generator almost blowup square, with `hz` discharged
  outright** — nothing about the exceptional line is carried.

## Implementation notes

**How the exceptional-line data is constructed.** Three identifications used to be carried; all
three are now discharged, and the general statements keep them only because they are stated for
an arbitrary closed immersion out of the exceptional line.

1. *The closed immersion `i : E ⟶ X'`.*
   `Stacks.AlmostBlowUp.isClosedImmersion_exceptionalToModification` is the instance, from the
   square being cartesian.
2. *The presentation `i_* 𝒢 ≅ 𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ`.* Taking `𝒢 = i ^* (𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ)`, it is the
   inverse of the unit of `i ^* ⊣ i_*`, an isomorphism by
   `Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero` as soon as the ideal of `i`
   annihilates the graded piece section by section. That annihilation is
   `annihilatedByKer_adicGradedPieceModule`, which combines
   `idealPowerMultiple_one_adicGradedPieceModule_eq_bot` with
   `Stacks.AlmostBlowUp.ker_exceptionalToModification`, the identification of the exceptional
   line as the zero locus of `𝓘`. Going through the unit rather than through
   `Stacks.Cohomology.ClosedImmersion.exists_isCoherent_pushforward_iso_isZero_of_smul_eq_zero`
   avoids needing the graded piece to be coherent and `X'` to be locally Noetherian.
3. *The counit `i^* i_* 𝒢 ≅ 𝒢`.* With `𝒢` taken to be `i ^* (𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ)` the counit is
   not needed at all: the isomorphism `i ^* (𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ) ≅ 𝒢` that
   `isZero_rightDerived_one_gradedPiece_of_pullback` asks for is `Iso.refl`, and global
   generation travels from `X'` to `E` along
   `Stacks.AlgebraicGeometry.FlatBaseChange.pullbackGeneratingSections` with nothing to transport.

**The affine-to-all-opens reduction is reused, not restated.**
`Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal` already performs it, including the
`AlgebraicGeometry.Scheme.Hom.ker_apply` step; `annihilatedByKer_adicGradedPieceModule` is that
lemma applied to the affine-local annihilation, and the ideal sheaf of the immersion is rewritten
at the `Scheme.IdealSheafData` level rather than open by open. In particular
`Stacks.AlmostBlowUp.ker_app_exceptionalToModification` is not needed here: it is the same
`ker_apply` rewrite, performed one level further down.

**What the final corollary still assumes, and why it must.** Coherence of `ℳ`, which
[Stacks, Tag 0EXD] assumes throughout, and global generation of `ℳ / 𝓘 ℳ`, which is what step
(a) of the source arranges by twisting; both are hypotheses about the module, not about the
square. They are *not* hypotheses about the exceptional data: both are conditions on `ℳ` alone,
each of them one of the source's own standing assumptions on the sheaf it starts from, and
neither constrains `A`, `f₁` or `f₂`. The vanishing for non-consecutive exponents is supplied by
`isZero_rightDerived_one_adicGradedPiece_of_consecutive`, which assumes nothing — a corollary
assuming exceptional data for every pair `(m, n)` would be assuming something false for
`n - m ≥ 2`, where the graded piece is not annihilated by `𝓘` and does not live on the line.

**The two coherence classes.** `Stacks.SheafOfModules.IsCoherent` is the `Prop` that
`surjective_adicCohomologyProj_of_isZero_gradedPiece` takes as a hypothesis, while
`_root_.SheafOfModules.IsCoherent` is the class that
`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent` needs in order
to produce quasi-coherence. The two have the same two fields, so the conversion is the anonymous
constructor; inside the `Stacks.*` namespace the short name resolves to the former, and the
latter has to be written `_root_.SheafOfModules.IsCoherent`.

**The composite inclusion of the nested chain is a variable.** `submoduleInclusion h₃₂ ≫
submoduleInclusion h₂₁` is `submoduleInclusion (h₃₂.trans h₂₁)` only propositionally
(`Stacks.Cohomology.FormalFunctions.submoduleInclusion_comp`), and the induction needs the
cokernel of the composite to *be* the graded piece named by the proof `h : m ≤ n` that the
hypothesis supplies. Rather than transport along `cokernelIsoOfEq`, the composite inclusion is
presented by a variable `h₃₁ : N₃ ≤ N₁` together with the defining equation — the device of
`Stacks.Abelian.shortExact_of_cokernel_desc`, whose hypotheses this is exactly shaped to meet.
Proof irrelevance then makes the conclusion applicable at whichever proof of `N₃ ≤ N₁` the caller
holds.

**The induction runs on the upper exponent, not on the difference.** With `d = n - m` as the
induction variable the step needs `(m + 1) + d` and `m + (d + 1)` to be the same natural number,
which they are not definitionally; the graded pieces at the two spellings are then different
objects and the transport lands under the derived functor. Inducting on `n` with `m` fixed and
splitting on `m = n + 1` versus `m ≤ n` uses the chain `𝓘 ⁿ⁺¹ ℱ ≤ 𝓘 ⁿ ℱ ≤ 𝓘 ᵐ ℱ`, whose three
exponents are already in the right shape, and needs no arithmetic at all.

**The diagonal piece.** `m = n` is in the range of the hypothesis, and there the piece is
the cokernel of an inclusion of a subsheaf into itself, which is the identity by right
cancellation against the monomorphism `N.ι`; an additive functor takes the resulting zero object
to a zero object.

**The two indexings.** The exceptional-line vanishing is stated in the `ℤ`-indexed
`rightDerivedPlus` and the induction consumes Mathlib's `ℕ`-indexed `rightDerived`;
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` crosses between them, and
`HasDerivedCategory.standard` is given the same local priority as in
`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorExceptionalCohomology.lean` so that the
`rightDerivedPlus` of this file is the one that statement was compiled against.

The ambient category is pinned as `(C := Y.Modules)` at every `cokernel`, `cokernel.π` and
`cokernel.desc`: `Y.Modules` is a `def` for `SheafOfModules Y.ringCatSheaf` and the two
presentations carry separately declared category instances.

No `@[stacks]` attribute: Tag 0EXD asserts that
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` is an equivalence, and this is one
step inside the essential-surjectivity half of it.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.Abelian

/-! ### One more cancellation with the composite as a variable -/

section OfEq

variable {D : Type u} [Category.{v} D] [Abelian D] {A B M : D}

/-- **The composite `A ⟶ M ⟶ M / B` vanishes when `A ⟶ M` is presented as `u ≫ v`.** The
companion of `Stacks.Abelian.comp_cokernel_π_eq_zero`, which instead quotients by `w` itself. -/
public lemma comp_cokernel_π_eq_zero_of_comp_eq (u : A ⟶ B) (v : B ⟶ M) {w : A ⟶ M}
    (hw : u ≫ v = w) : w ≫ cokernel.π v = 0 := by
  subst hw
  simp

end OfEq

end Stacks.Abelian

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization

/-! ### The quotients of a nested chain of subsheaves -/

section Chain

variable {Y : Scheme.{u}} {F : Y.Modules} {N₃ N₂ N₁ : SheafOfModules.Submodule F}

/-- **An inclusion of subsheaves is a monomorphism**, because composing it with the inclusion of
the larger one into the ambient sheaf gives the inclusion of the smaller one. -/
public lemma mono_submoduleInclusion (h : N₃ ≤ N₂) : Mono (submoduleInclusion h) := by
  have hm : Mono (submoduleInclusion h ≫
      (N₂.ι : (N₂.toSheafOfModules : Y.Modules) ⟶ F)) := by
    rw [submoduleInclusion_comp_ι]
    infer_instance
  exact mono_of_mono _ (N₂.ι : (N₂.toSheafOfModules : Y.Modules) ⟶ F)

/-- **The inclusion of a subsheaf into itself is the identity**, by right cancellation against
the monomorphism `N.ι`. -/
public lemma submoduleInclusion_refl (N : SheafOfModules.Submodule F) :
    submoduleInclusion (le_refl N) = 𝟙 (N.toSheafOfModules : Y.Modules) :=
  (Scheme.Modules.mono_submodule_ι N).right_cancellation _ _
    ((submoduleInclusion_comp_ι (le_refl N)).trans (Category.id_comp _).symm)

/-- The inclusion of a subsheaf into itself is an epimorphism. -/
public lemma epi_submoduleInclusion_refl (N : SheafOfModules.Submodule F) :
    Epi (submoduleInclusion (le_refl N)) := by
  rw [submoduleInclusion_refl]
  infer_instance

/-- **The quotient of a subsheaf by itself is zero.** -/
public lemma isZero_cokernel_submoduleInclusion_refl (N : SheafOfModules.Submodule F) :
    IsZero (cokernel (C := Y.Modules) (submoduleInclusion (le_refl N))) :=
  let := epi_submoduleInclusion_refl N
  isZero_cokernel_of_epi (submoduleInclusion (le_refl N))

variable (h₃₂ : N₃ ≤ N₂) (h₂₁ : N₂ ≤ N₁) {h₃₁ : N₃ ≤ N₁}
  (hc : submoduleInclusion h₃₂ ≫ submoduleInclusion h₂₁ = submoduleInclusion h₃₁)

/-- **The map `N₂ / N₃ ⟶ N₁ / N₃`** induced by the inclusion of `N₂` into `N₁`, for a chain whose
composite inclusion is presented by the variable `h₃₁`. -/
public noncomputable def nestedQuotientIncl :
    cokernel (C := Y.Modules) (submoduleInclusion h₃₂) ⟶
      cokernel (C := Y.Modules) (submoduleInclusion h₃₁) :=
  cokernel.desc (C := Y.Modules) _
    (submoduleInclusion h₂₁ ≫ cokernel.π (C := Y.Modules) (submoduleInclusion h₃₁))
    (Stacks.Abelian.comp_cokernel_π_eq_zero _ _ hc)

/-- `N₂ / N₃ ⟶ N₁ / N₃` is the map determined by the universal property of the cokernel. -/
public lemma π_comp_nestedQuotientIncl :
    cokernel.π (C := Y.Modules) (submoduleInclusion h₃₂) ≫ nestedQuotientIncl h₃₂ h₂₁ hc =
      submoduleInclusion h₂₁ ≫ cokernel.π (C := Y.Modules) (submoduleInclusion h₃₁) :=
  cokernel.π_desc (C := Y.Modules) _ _ _

/-- **The exponent drop `N₁ / N₃ ⟶ N₁ / N₂`**, for a chain whose composite inclusion is
presented by the variable `h₃₁`. -/
public noncomputable def nestedQuotientDrop :
    cokernel (C := Y.Modules) (submoduleInclusion h₃₁) ⟶
      cokernel (C := Y.Modules) (submoduleInclusion h₂₁) :=
  cokernel.desc (C := Y.Modules) _ (cokernel.π (C := Y.Modules) (submoduleInclusion h₂₁))
    (Stacks.Abelian.comp_cokernel_π_eq_zero_of_comp_eq _ _ hc)

/-- The drop `N₁ / N₃ ⟶ N₁ / N₂` commutes with the two quotient projections. -/
public lemma π_comp_nestedQuotientDrop :
    cokernel.π (C := Y.Modules) (submoduleInclusion h₃₁) ≫ nestedQuotientDrop h₃₂ h₂₁ hc =
      cokernel.π (C := Y.Modules) (submoduleInclusion h₂₁) :=
  cokernel.π_desc (C := Y.Modules) _ _ _

/-- The composite `N₂ / N₃ ⟶ N₁ / N₃ ⟶ N₁ / N₂` vanishes. -/
public lemma nestedQuotientIncl_comp_nestedQuotientDrop :
    nestedQuotientIncl h₃₂ h₂₁ hc ≫ nestedQuotientDrop h₃₂ h₂₁ hc = 0 :=
  Stacks.Abelian.comp_eq_zero_of_cokernel_desc (submoduleInclusion h₃₂)
    (submoduleInclusion h₂₁) hc (π_comp_nestedQuotientIncl h₃₂ h₂₁ hc)
    (π_comp_nestedQuotientDrop h₃₂ h₂₁ hc)

/-- **The quotients of a nested chain `N₃ ≤ N₂ ≤ N₁` of subsheaves sit in a short exact
sequence** `0 ⟶ N₂ / N₃ ⟶ N₁ / N₃ ⟶ N₁ / N₂ ⟶ 0`.

This is `Stacks.Abelian.shortExact_of_cokernel_desc` at the two inclusions, with the composite
inclusion kept as the variable `h₃₁` so that the middle term is the quotient named by whichever
proof of `N₃ ≤ N₁` the caller holds. -/
public lemma shortExact_nestedQuotient :
    (ShortComplex.mk (nestedQuotientIncl h₃₂ h₂₁ hc) (nestedQuotientDrop h₃₂ h₂₁ hc)
      (nestedQuotientIncl_comp_nestedQuotientDrop h₃₂ h₂₁ hc)).ShortExact := by
  have := mono_submoduleInclusion h₃₂
  have := mono_submoduleInclusion h₂₁
  exact Stacks.Abelian.shortExact_of_cokernel_desc (submoduleInclusion h₃₂)
    (submoduleInclusion h₂₁) hc (π_comp_nestedQuotientIncl h₃₂ h₂₁ hc)
    (π_comp_nestedQuotientDrop h₃₂ h₂₁ hc)
    (nestedQuotientIncl_comp_nestedQuotientDrop h₃₂ h₂₁ hc)

include hc in
/-- **`H¹(N₁ / N₃)` vanishes once `H¹(N₂ / N₃)` and `H¹(N₁ / N₂)` do**: the window
`R¹Q X₁ ⟶ R¹Q X₂ ⟶ R¹Q X₃` of the long exact sequence of
`Stacks.Cohomology.FormalFunctions.shortExact_nestedQuotient`. -/
public theorem isZero_rightDerived_one_nestedQuotient
    (h₁ : IsZero (((moduleGlobalSections Y).rightDerived 1).obj
      (cokernel (C := Y.Modules) (submoduleInclusion h₃₂))))
    (h₃ : IsZero (((moduleGlobalSections Y).rightDerived 1).obj
      (cokernel (C := Y.Modules) (submoduleInclusion h₂₁)))) :
    IsZero (((moduleGlobalSections Y).rightDerived 1).obj
      (cokernel (C := Y.Modules) (submoduleInclusion h₃₁))) :=
  Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂
    (shortExact_nestedQuotient h₃₂ h₂₁ hc) (moduleGlobalSections Y) 1 h₁ h₃

end Chain

/-! ### Global generation across a pullback presentation -/

/-- **Global generating sections of a module presented as a pullback.** A family of global
generating sections of `M` on `Y` gives one of any module on `Z` isomorphic to `p ^* M`.

The `Epi` witness is passed by position: it is proved at the `Z.Modules` spelling of the category
of sheaves of modules and instance search does not find it at the
`SheafOfModules Z.ringCatSheaf` spelling that `SheafOfModules.GeneratingSections.ofEpi` is stated
in. -/
public noncomputable def generatingSectionsOfPullbackIso {Y Z : Scheme.{u}} (p : Z ⟶ Y)
    (M : Y.Modules) (G : Z.Modules) (c : (Scheme.Modules.pullback p).obj M ≅ G)
    (τ : SheafOfModules.GeneratingSections M) : SheafOfModules.GeneratingSections G :=
  @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _
    (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackGeneratingSections p M τ) c.hom
    (IsIso.epi_of_iso c.hom)

/-! ### From the consecutive graded pieces to all of them -/

section Adic

variable {Y : Scheme.{u}} (J : Y.IdealSheafData) (F : Y.Modules)

/-- **`H¹` of the diagonal graded piece `𝓘 ᵐ ℱ / 𝓘 ᵐ ℱ` vanishes**, that piece being the zero
sheaf. The proof `h : m ≤ m` is an explicit argument because the induction's hypothesis supplies one;
by proof irrelevance it does not matter which. -/
public theorem isZero_rightDerived_one_adicGradedPiece_self (m : ℕ) (h : m ≤ m) :
    IsZero (((moduleGlobalSections Y).rightDerived 1).obj
      (cokernel (C := Y.Modules) (submoduleInclusion (idealPowerMultiple_antitone J F h)))) :=
  Functor.map_isZero _
    (isZero_cokernel_submoduleInclusion_refl (idealPowerMultiple J m F))

/-- **`H¹` vanishes on every graded piece `𝓘 ᵐ ℱ / 𝓘 ⁿ ℱ` of the `𝓘`-adic filtration as soon as
it vanishes on the consecutive pieces `𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ`.**

The induction is on `n` with `m` fixed: either `m = n + 1`, and the piece is the zero sheaf, or
`m ≤ n`, and the chain `𝓘 ⁿ⁺¹ ℱ ≤ 𝓘 ⁿ ℱ ≤ 𝓘 ᵐ ℱ` puts the piece in the middle of a short exact
sequence whose outer terms are a consecutive piece and the piece at `(m, n)`. -/
public theorem isZero_rightDerived_one_adicGradedPiece_of_consecutive
    (hcons : ∀ k : ℕ, IsZero (((moduleGlobalSections Y).rightDerived 1).obj
      (cokernel (C := Y.Modules)
        (submoduleInclusion (idealPowerMultiple_antitone J F (Nat.le_succ k))))))
    {m n : ℕ} (h : m ≤ n) :
    IsZero (((moduleGlobalSections Y).rightDerived 1).obj
      (cokernel (C := Y.Modules) (submoduleInclusion (idealPowerMultiple_antitone J F h)))) := by
  induction n, h using Nat.le_induction with
  | base => exact isZero_rightDerived_one_adicGradedPiece_self J F m le_rfl
  | succ n hmn ih =>
    exact isZero_rightDerived_one_nestedQuotient
      (idealPowerMultiple_antitone J F (Nat.le_succ n))
      (idealPowerMultiple_antitone J F hmn)
      (submoduleInclusion_comp _ _) (hcons n) ih

end Adic

/-! ### The consecutive graded piece is annihilated by the ideal -/

section Annihilation

variable {Y : Scheme.{u}} (J : Y.IdealSheafData) (F : Y.Modules)

/-- **The consecutive graded piece `𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ` is annihilated by `𝓘`.**

Over an affine open `V` the quotient projection `𝓘 ᵏ ℱ ⟶ 𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ` is surjective on
sections, both modules being quasi-coherent
(`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`); the sections of `𝓘 ᵏ ℱ` over `V` are
`𝓘(V) ᵏ Γ(ℱ, V)` by
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen`; and multiplying one of
those by a section of `𝓘(V)` lands in `𝓘(V) ᵏ⁺¹ Γ(ℱ, V)`, which the projection kills. This is
the statement that the graded pieces of the `𝓘`-adic filtration live on the closed subscheme cut
out by `𝓘`, in the affine-local form that
`Stacks.Algebraization.affine_sections_annihilated_of_idealPowerMultiple_eq_bot` reads off.

The lifted section is produced twice, once as a section `yg` of the subsheaf `𝓘 ᵏ ℱ` and once as
a section `yv` of `ℱ` with the equation identifying the two: `Γ(𝒪_Y, V)` is not found as a scalar
for the `ModuleCat` spelling of the sections of a subsheaf, the device of
`Stacks.AlgebraicGeometry.IdealPowerColimit.smulToModule_app_toTensorSheafSection`. -/
@[ega "IV 6.10.1" "partial"]
public theorem idealPowerMultiple_one_adicGradedPieceModule_eq_bot [F.IsQuasicoherent] (k : ℕ) :
    idealPowerMultiple J 1 (adicGradedPieceModule J F k) = ⊥ := by
  let : (adicGradedPieceModule J F k).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun V a ha x => ?_
  obtain ⟨y, hy⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen Y
    (cokernel.π (C := Y.Modules) (adicGradedPieceInclusion J F k)) V.1 V.2 x
  obtain ⟨yg, hyg⟩ : ∃ z : Γ(Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul J k F, V.1),
      (cokernel.π (C := Y.Modules) (adicGradedPieceInclusion J F k)).app V.1 z = x := ⟨y, hy⟩
  obtain ⟨yv, hyv⟩ : ∃ z : Γ(F, V.1), z = yg.1 := ⟨yg.1, rfl⟩
  have hy1 : yv ∈ J.ideal V ^ k • (⊤ : Submodule Γ(Y, V.1) Γ(F, V.1)) := by
    rw [hyv]
    exact (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen J k F V).le yg.2
  have ha1 : a ∈ J.ideal V := by simpa using ha
  have hmem : a • yv ∈ (idealPowerMultiple J (k + 1) F).toSubmodule.obj (op V.1) := by
    refine (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen J (k + 1)
      F V).ge ?_
    have h1 : a • yv ∈ J.ideal V • (J.ideal V ^ k • (⊤ : Submodule Γ(Y, V.1) Γ(F, V.1))) :=
      Submodule.smul_mem_smul ha1 hy1
    rwa [← Submodule.mul_smul, ← pow_succ'] at h1
  have hz : (cokernel.π (C := Y.Modules) (adicGradedPieceInclusion J F k)).app V.1
      ((adicGradedPieceInclusion J F k).app V.1 ⟨a • yv, hmem⟩) = 0 := by
    have h2 : (adicGradedPieceInclusion J F k ≫
        cokernel.π (C := Y.Modules) (adicGradedPieceInclusion J F k)).app V.1
          ⟨a • yv, hmem⟩ = 0 := by
      rw [cokernel.condition]
      rfl
    exact h2
  have hincl : (adicGradedPieceInclusion J F k).app V.1 ⟨a • yv, hmem⟩ = a • yg :=
    Subtype.ext (congrArg (fun z : Γ(F, V.1) => a • z) hyv)
  have happ : (cokernel.π (C := Y.Modules) (adicGradedPieceInclusion J F k)).app V.1
      (a • yg) = 0 :=
    (congrArg (fun w => (cokernel.π (C := Y.Modules)
      (adicGradedPieceInclusion J F k)).app V.1 w) hincl).symm.trans hz
  exact (congrArg (fun z => a • z) hyg.symm).trans
    ((Scheme.Modules.Hom.app_smul _ a yg).symm.trans happ)

/-- **A section of `𝒪_Y` killed by the comorphism of a closed immersion kills the consecutive
graded piece**, for a closed immersion whose ideal sheaf is `𝓘`, over *every* open and not only
over the affine ones.

That reduction is `Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal`: annihilation of a
section is a local condition and the affine opens form a basis, so the condition over all opens
follows from the condition over the affine opens, where
`AlgebraicGeometry.Scheme.Hom.ker_apply` identifies the kernel of the comorphism with the ideal
of `AlgebraicGeometry.Scheme.Hom.ker`. The affine-local input is
`Stacks.Cohomology.FormalFunctions.idealPowerMultiple_one_adicGradedPieceModule_eq_bot`.

This is the hypothesis of
`Stacks.ClosedImmersion.exists_isCoherent_pushforward_iso_of_smul_eq_zero` and of
`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`. -/
public theorem annihilatedByKer_adicGradedPieceModule {E : Scheme.{u}} (i : E ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion i] [F.IsQuasicoherent] (hker : i.ker = J) (k : ℕ) :
    Stacks.ClosedImmersion.AnnihilatedByKer i (adicGradedPieceModule J F k) := by
  rw [Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal]
  intro V a ha m
  rw [hker] at ha
  exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot
    (idealPowerMultiple_one_adicGradedPieceModule_eq_bot J F k) V (by simpa using ha) m

end Annihilation

/-! ### The exceptional line of the two-generator almost blowup square -/

section Exceptional

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- **`H¹(E, 𝒢) = 0` for a globally generated quasi-coherent module on the exceptional line of
the two-generator almost blowup square, in Mathlib's `ℕ`-indexing.** This is
`Stacks.AlmostBlowUp.isZero_cohomology_one_exceptional_of_generatingSections`, crossed from the
`ℤ`-indexed `rightDerivedPlus` by `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`. -/
public theorem isZero_rightDerived_one_exceptional_of_generatingSections
    (G : (AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)).Modules)
    [G.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections G) :
    IsZero (((moduleGlobalSections
      (AlgebraicGeometry.Proj
        (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂))).rightDerived 1).obj G) :=
  (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ Nat.cast_one.symm G).mp
    (Stacks.AlmostBlowUp.isZero_cohomology_one_exceptional_of_generatingSections A f₁ f₂ G σ)

variable {Z : Scheme.{u}}
  (i : AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂) ⟶ Z)

/-- **`H¹(Z, ℳ) = 0` for a module on `Z` which is the direct image, along a closed immersion of
the exceptional line, of a globally generated quasi-coherent module.** The composite of the
exceptional-line vanishing with
`Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_of_isZero_pushforward`. -/
public theorem isZero_rightDerived_one_of_pushforward_exceptional
    [AlgebraicGeometry.IsClosedImmersion i] {M : Z.Modules}
    (G : (AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)).Modules)
    [G.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections G)
    (e : (Scheme.Modules.pushforward i).obj G ≅ M) :
    IsZero (((moduleGlobalSections Z).rightDerived 1).obj M) :=
  Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_of_isZero_pushforward i G e 1
    (isZero_rightDerived_one_exceptional_of_generatingSections A f₁ f₂ G σ)

variable [AlgebraicGeometry.IsClosedImmersion i] (J : Z.IdealSheafData) (M : Z.Modules) (k : ℕ)

/-- **`H¹(Z, 𝓘 ᵏ ℳ / 𝓘 ᵏ⁺¹ ℳ) = 0`** for a graded piece of the `𝓘`-adic filtration presented as
the direct image of a globally generated quasi-coherent module on the exceptional line.

This is the cohomological half of step (b) of [Stacks, Tag 0EXD]: the graded piece is
annihilated by `𝓘` and so lives on `E = 𝐏¹_Z`, where global generation makes `H¹` vanish. What
the statement carries is the presentation itself; see the implementation notes. -/
public theorem isZero_rightDerived_one_gradedPiece_of_generatingSections
    (G : (AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)).Modules)
    [G.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections G)
    (e : (Scheme.Modules.pushforward i).obj G ≅ adicGradedPieceModule J M k) :
    IsZero (((moduleGlobalSections Z).rightDerived 1).obj (adicGradedPieceModule J M k)) :=
  isZero_rightDerived_one_of_pushforward_exceptional A f₁ f₂ i G σ e

/-- **`H¹(Z, 𝓘 ᵏ ℳ / 𝓘 ᵏ⁺¹ ℳ) = 0` from global generation on `Z` itself**, which is what
`Stacks.Cohomology.FormalFunctions.generatingSectionsAdicGradedPiece` delivers: the graded piece
is globally generated as soon as `𝓘 ᵏ` and `ℳ / 𝓘 ℳ` are, and global generation travels to the
exceptional line along the pullback, the counit isomorphism `i ^* i_* 𝒢 ≅ 𝒢` being carried. -/
public theorem isZero_rightDerived_one_gradedPiece_of_pullback [M.IsQuasicoherent]
    (G : (AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)).Modules)
    [G.IsQuasicoherent]
    (hI : (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow J k).GeneratingSections)
    (hQ : (idealPowerQuotient J 1 M).GeneratingSections)
    (c : (Scheme.Modules.pullback i).obj (adicGradedPieceModule J M k) ≅ G)
    (e : (Scheme.Modules.pushforward i).obj G ≅ adicGradedPieceModule J M k) :
    IsZero (((moduleGlobalSections Z).rightDerived 1).obj (adicGradedPieceModule J M k)) :=
  isZero_rightDerived_one_gradedPiece_of_generatingSections A f₁ f₂ i J M k G
    (generatingSectionsOfPullbackIso i (adicGradedPieceModule J M k) G c
      (generatingSectionsAdicGradedPiece J M k hI hQ)) e

/-- **`H¹(Z, 𝓘 ᵏ ℳ / 𝓘 ᵏ⁺¹ ℳ) = 0` with no presentation carried**, for a closed immersion of
the exceptional line into `Z` whose ideal sheaf is `𝓘`: the only inputs are the global generation
of `𝓘 ᵏ` and of `ℳ / 𝓘 ℳ` on `Z` itself.

The module on the exceptional line is taken to be `i ^* (𝓘 ᵏ ℳ / 𝓘 ᵏ⁺¹ ℳ)`, which makes the
counit isomorphism of
`Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_gradedPiece_of_pullback` the identity
and the presentation `i_* 𝒢 ≅ 𝓘 ᵏ ℳ / 𝓘 ᵏ⁺¹ ℳ` the inverse of the adjunction unit, which is an
isomorphism precisely because the graded piece is annihilated by the ideal of `i`
(`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero` at
`Stacks.Cohomology.FormalFunctions.annihilatedByKer_adicGradedPieceModule`). No coherence and no
Noetherian hypothesis is needed: [Stacks, Tag 087T] is used only through that unit. -/
public theorem isZero_rightDerived_one_gradedPiece_of_ker [M.IsQuasicoherent] (hker : i.ker = J)
    (hI : (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow J k).GeneratingSections)
    (hQ : (idealPowerQuotient J 1 M).GeneratingSections) :
    IsZero (((moduleGlobalSections Z).rightDerived 1).obj (adicGradedPieceModule J M k)) := by
  let : (adicGradedPieceModule J M k).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _
  have := Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i
    (adicGradedPieceModule J M k) (annihilatedByKer_adicGradedPieceModule J M i hker k)
  let : ((Scheme.Modules.pullback i).obj (adicGradedPieceModule J M k)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback i _ inferInstance
  exact isZero_rightDerived_one_gradedPiece_of_pullback A f₁ f₂ i J M k
    ((Scheme.Modules.pullback i).obj (adicGradedPieceModule J M k)) hI hQ (Iso.refl _)
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (adicGradedPieceModule J M k))).symm

end Exceptional

/-! ### Discharging the hypothesis of the inverse-limit induction -/

section Discharge

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (f₁ f₂ : A) {Z : Scheme.{u}}
  (i : AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂) ⟶ Z)
  [AlgebraicGeometry.IsClosedImmersion i] (J : Z.IdealSheafData) (M : Z.Modules)
  (G : ℕ → (AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)).Modules)
  (hq : ∀ k, (G k).IsQuasicoherent) (σ : ∀ k, SheafOfModules.GeneratingSections (G k))
  (e : ∀ k, (Scheme.Modules.pushforward i).obj (G k) ≅ adicGradedPieceModule J M k)

include hq σ e in
/-- **`H¹` vanishes on every graded piece `𝓘 ᵐ ℳ / 𝓘 ⁿ ℳ`**, given one globally generated
quasi-coherent module on the exceptional line per consecutive piece. The consecutive pieces are
handled on the line and the rest by the nested-chain induction. -/
public theorem isZero_rightDerived_one_adicGradedPiece_of_exceptional {m n : ℕ} (h : m ≤ n) :
    IsZero (((moduleGlobalSections Z).rightDerived 1).obj
      (cokernel (C := Z.Modules) (submoduleInclusion (idealPowerMultiple_antitone J M h)))) :=
  isZero_rightDerived_one_adicGradedPiece_of_consecutive J M
    (fun k ↦ let := hq k
      isZero_rightDerived_one_gradedPiece_of_generatingSections A f₁ f₂ i J M k (G k) (σ k) (e k))
    h

end Discharge

section DischargeInduction

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {Z : Scheme.{u}}
  (g : Z ⟶ Spec (.of R)) (I : Ideal R) (M : Z.Modules)
  (A : Type u) [CommRing A] (f₁ f₂ : A)
  (i : AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂) ⟶ Z)
  [AlgebraicGeometry.IsClosedImmersion i]
  (G : ℕ → (AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)).Modules)
  (hq : ∀ k, (G k).IsQuasicoherent) (σ : ∀ k, SheafOfModules.GeneratingSections (G k))
  (e : ∀ k, (Scheme.Modules.pushforward i).obj (G k) ≅
    adicGradedPieceModule (baseIdealSheaf R I g) M k)

include hq σ e in
/-- **The `𝓘`-adic inverse-limit induction of [Stacks, Tag 0EXD], with its `H¹` hypothesis
discharged on the exceptional line.** For a proper `g : Z ⟶ Spec R` over a Noetherian ring, a
coherent `ℳ`, and one globally generated quasi-coherent module on
`E = Proj (exceptionalGrading A f₁ f₂)` presenting each consecutive graded piece of the
`𝓘`-adic filtration, `H⁰(Z, ℳ) ⟶ H⁰(Z, ℳ / 𝓘 ⁿ ℳ)` is surjective for every `n`.

This is `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_of_isZero_gradedPiece`
with its hypothesis `hz` supplied. -/
public theorem surjective_adicCohomologyProj_of_exceptional
    (hZ : AlgebraicGeometry.IsProper g) (hM : Stacks.SheafOfModules.IsCoherent M) (n : ℕ) :
    Function.Surjective (adicCohomologyProj R g I M 0 n) :=
  surjective_adicCohomologyProj_of_isZero_gradedPiece R g I M hZ hM
    (fun _ _ h ↦ isZero_rightDerived_one_adicGradedPiece_of_exceptional A f₁ f₂ i
      (baseIdealSheaf R I g) M G hq σ e h) n

end DischargeInduction

/-! ### The two-generator almost blowup square, with nothing carried -/

section TwoGenerator

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- **The ideal sheaf of the exceptional divisor is the extension of `(f₁,f₂)` to the
modification.** Both sides are the ideal sheaf generated by the image of `(f₁,f₂)` under
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X', 𝒪_{X'})`: the left-hand side computes it as the inverse image of the
ideal sheaf of the centre and the right-hand side as the extension along the modification, and
`Stacks.IdealSheaf.comap_ofIdealTop` identifies the two. -/
public theorem comap_centerIdealSheaf_eq_baseIdealSheaf :
    letI := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
    (Stacks.AlmostBlowUp.centerIdealSheaf A f₁ f₂).comap
        (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) =
      baseIdealSheaf A (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂)
        (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) := by
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  rw [Stacks.AlmostBlowUp.centerIdealSheaf, Stacks.IdealSheaf.comap_ofIdealTop,
    baseIdealSheaf, baseIdeal, Ideal.map_map, CommRingCat.hom_comp]

/-- **The `𝓘`-adic inverse-limit induction of [Stacks, Tag 0EXD] for the two-generator almost
blowup square, with its `H¹` hypothesis discharged outright.**

Let `A` be a Noetherian ring, `f₁, f₂ ∈ A`, and let
`b : X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) ⟶ Spec A` be the modification of the two-generator square,
with `𝓘 = (f₁,f₂) 𝒪_{X'}` the ideal sheaf of its exceptional divisor. For a coherent `ℳ` on `X'`
whose quotient `ℳ / 𝓘 ℳ` is generated by global sections,
`H⁰(X', ℳ) ⟶ H⁰(X', ℳ / 𝓘 ⁿ ℳ)` is surjective for every `n`.

Nothing about the exceptional line is carried. The closed immersion is
`Stacks.AlmostBlowUp.exceptionalToModification`, a closed immersion by
`Stacks.AlmostBlowUp.isClosedImmersion_exceptionalToModification` and with ideal sheaf `𝓘` by
`Stacks.AlmostBlowUp.ker_exceptionalToModification`; the module on the line and the presentation
of the graded piece as its direct image come from
`Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_gradedPiece_of_ker`; and the global
generation of every power `𝓘 ᵏ` comes from
`Stacks.AlmostBlowUp.generatingSections_comap_centerIdealSheaf` through
`AlgebraicGeometry.idealPowGeneratingSections`. The two surviving hypotheses are about `ℳ`, not
about the square: coherence, which [Stacks, Tag 0EXD] assumes throughout, and the global
generation of `ℳ / 𝓘 ℳ`, which is what step (a) of the source arranges by twisting.

The graded pieces at non-consecutive exponents are *not* annihilated by `𝓘` and do not live on
the exceptional line; they are handled by
`Stacks.Cohomology.FormalFunctions.isZero_rightDerived_one_adicGradedPiece_of_consecutive`,
which needs no hypothesis at all. -/
public theorem surjective_adicCohomologyProj_twoGenerator [IsNoetherianRing A]
    (M : (letI := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.modificationGrading A f₁ f₂)).Modules)
    (hM : Stacks.SheafOfModules.IsCoherent M)
    (hQ : (idealPowerQuotient (baseIdealSheaf A (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂)
      (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂)) 1 M).GeneratingSections)
    (n : ℕ) :
    Function.Surjective (adicCohomologyProj A (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂)
      (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂) M 0 n) := by
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  let : _root_.SheafOfModules.IsCoherent M := ⟨hM.isFiniteType, hM.kernel_isFiniteType⟩
  let : M.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  have hker : (Stacks.AlmostBlowUp.exceptionalToModification A f₁ f₂).ker =
      baseIdealSheaf A (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂)
        (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) :=
    (Stacks.AlmostBlowUp.ker_exceptionalToModification A f₁ f₂).trans
      (comap_centerIdealSheaf_eq_baseIdealSheaf A f₁ f₂)
  have hI : (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow
      (baseIdealSheaf A (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂)
        (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂)) 1).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso
      (eqToIso (congrArg (fun L => Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow L 1)
        (comap_centerIdealSheaf_eq_baseIdealSheaf A f₁ f₂)))
      (Stacks.AlmostBlowUp.generatingSections_comap_centerIdealSheaf A f₁ f₂)
  refine surjective_adicCohomologyProj_of_isZero_gradedPiece A
    (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂)
    (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂) M
    (Stacks.AlmostBlowUp.isProper_modificationToBase A f₁ f₂) hM (fun m n' h => ?_) n
  exact isZero_rightDerived_one_adicGradedPiece_of_consecutive _ M
    (fun k => isZero_rightDerived_one_gradedPiece_of_ker A f₁ f₂
      (Stacks.AlmostBlowUp.exceptionalToModification A f₁ f₂) _ M k hker
      (AlgebraicGeometry.idealPowGeneratingSections _ hI k) hQ) h

end TwoGenerator

end Stacks.Cohomology.FormalFunctions

end
