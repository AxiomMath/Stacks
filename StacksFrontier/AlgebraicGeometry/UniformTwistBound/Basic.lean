module

public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Devissage
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjGradedRing.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A uniform vanishing bound for all twists on Proj of a Noetherian graded ring

Stacks Tag 0B5Q, label `eventual_higher_cohomology_vanishing`, asserts that for a Noetherian
graded ring `𝒜`, a coherent sheaf `ℱ` on `Proj 𝒜` and each `p > 0`, the cohomology
`Hᵖ(Proj 𝒜, ℱ(d))` vanishes for all sufficiently large `d`.

The reduction of that label to two hypotheses is already available, as
`Stacks.AlgebraicGeometry.ProjTwistFunctor.exists_isZero_hgroup_twist_of_descending_devissage`,
whose conclusion at `U = ⊤` is the tagged statement verbatim (its ring sheaf is the
`sheafCompose … structureSheaf 𝒜`, which is exactly
`Stacks.AlgebraicGeometry.ProjTwistFunctor.projRingSheaf`, and its twist has the
equivalent `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`, tagged 01MN part (2)).
Its two hypotheses are

* `hbound`: a degree `e` above which `Hᵖ(⊤, ℱ(d))` vanishes **for every `d` and every `ℱ` in the
  class**, and
* `step`: a dévissage presenting each `ℱ` as the quotient of an eventually acyclic module.

This file does the work for `hbound` on the **relative** side: it instantiates the uniform
vanishing of Tag 01XJ at the structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)`, where the bound is uniform
in the module and therefore uniform over all twists at once, and it supplies the quasi-coherence
of a twist that any such instantiation needs.

## Main results

All names below live in the namespace `Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound`.

* `isQuasicoherent_twistingSheaf`, `isQuasicoherent_twistSheafOfModules`: the twisting sheaf, and
  the twist of a quasi-coherent sheaf, are quasi-coherent.
* `isProper_toSpecZero`, `quasiCompact_toSpecZero`, `quasiSeparated_toSpecZero`: for `𝒜` a graded
  ring whose underlying ring is Noetherian, the structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)` is
  proper, quasi-compact and quasi-separated.
* `exists_isZero_rightDerivedPlus_pushforward_toSpecZero`: a single degree above which every
  higher direct image along `Proj 𝒜 ⟶ Spec (𝒜 0)` of every quasi-coherent sheaf vanishes.
* `exists_isZero_rightDerivedPlus_twist`: the same bound, applied to every twist of every
  quasi-coherent sheaf — the relative form of Tag 0B5Q's `hbound`.
* `exists_isCoherent_rightDerivedPlus_pushforward_toSpecZero`: a single degree above which every
  higher direct image of every quasi-coherent sheaf is coherent, with no Noetherian hypothesis
  used beyond the one that makes the morphism proper.

## What this does and does not close

**Done here.** Every scheme-theoretic hypothesis of the Tag 01XJ machinery is discharged at `Proj`:
`Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing` turns `IsNoetherianRing A` into
`Algebra.FiniteType (𝒜 0) A`, which is exactly the hypothesis under which pinned Mathlib's
`AlgebraicGeometry.Proj` instances give properness and quasi-compactness of the structure
morphism; quasi-separatedness comes from the separatedness instance, which needs no finiteness; and
`CompactSpace (Spec (𝒜 0))` is automatic. Nothing in either tree had applied the 01XJ machinery to
a `Proj` before this file.

**The one remaining link for `hbound`, named.** Tag 01XJ is about
`(Scheme.Modules.pushforward f).rightDerivedPlus p`, the *relative* higher direct image, while
`hbound` is about `Hgroup`, the derived global sections. The two are connected by
`Stacks.SchemeCohomology.Hfunctor_eq_rightDerived_comp`, which says — by `rfl` — that `Hgroup` is
the right derived functor of the **composite** `pushforward f ⋙ secF`, and that is not the
composite of the two derived functors: the comparison is the Leray spectral sequence. Over the
affine base `Spec (𝒜 0)` that sequence degenerates, because the higher cohomology of a
quasi-coherent sheaf on an affine scheme vanishes
(`Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine`) and the higher direct images here are
quasi-coherent (`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`,
an instance) — but **that degeneration is absent** from the library, in both available forms: the Leray collapse
`Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages` demands that *all*
positive higher direct images vanish, which is what one is trying to prove, and the
affine-morphism collapse `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso` demands
`IsAffineHom f`, which `Proj.toSpecZero 𝒜` is not. The relative Leray spectral sequence is available
as an existence statement (`Stacks.RelativeLeray.exists_spectralSequence_relativeLeray`) and
nothing degenerates it over an affine base or identifies its `E₂^{0,p}` with `Hgroup`.

**The other hypothesis, `step`, is a genuinely open theorem.** It is Tag 0B5Q part (1) — every
coherent sheaf on `Proj 𝒜` is a quotient of a finite direct sum of twists — and this is not
available: none of Tags 01XQ, 01XS, 01YR and 01YS is formalized in the library.  Tag 0AG5
*is* attached, and unconditionally:
`Stacks.AlgebraicGeometry.ProjTwistComparisonCompact.isIso_integerComparison` proves that the
Tag 0B5I comparison `M̃ ⟶ ℱ` is an isomorphism for `Proj 𝒜` quasi-compact and `ℱ` quasi-coherent.
That is Tag 0B5Q's *input*, not its conclusion: it recovers a quasi-coherent sheaf from its
twisted global sections and says nothing about a finite direct sum of twists surjecting onto a
coherent one, so it does not supply `step`.  The only statement of that shape in either tree is
for an **ample invertible module**,
`Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists`, not for the twisting sheaf of an
arbitrary graded ring. So Tag 0B5Q's eventual-vanishing label is two steps from done, and this
file closes neither of them outright; it makes the first one a bridge rather than a theorem.

## Implementation notes

**Instance spellings are pinned in the binders, never left to search.** Quasi-coherence of a
module on `Proj 𝒜` is stated three ways in this repository — at `projRingSheaf 𝒜`, at
`(Proj 𝒜).ringCatSheaf` and at `structureSheafRing
  (Proj 𝒜).toRingedSpace` — and
all three are the same term up to `rfl`
(`Stacks.AlgebraicGeometry.ProjTrivialization.ringCatSheaf_eq`), while instance **search** crosses
none of them, `AlgebraicGeometry.Scheme.Modules` being a `def`. So quasi-coherence appears as an
ordinary hypothesis and is handed to the library results by explicit `@`-application, where it is
checked by unification at default transparency. This is what makes
`isQuasicoherent_twistSheafOfModules` two lines: Tag 01CE's instance
`AlgebraicGeometry.tensorSheaf_isQuasicoherent` applies to the twist on the nose, and only the
instance arguments had to be supplied by hand.

**No attribute is attached.** The label `eventual_higher_cohomology_vanishing` is not proved here;
the other 0B5Q label live in the tree, `proj_noetherian`, is untouched. Tag 01XJ, 01CE and 01MB
are all already attached where they belong, and nothing here is a new covering set for them.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Quasi-coherence of the twists -/

/-- **The `d`-th twisting sheaf on `Proj 𝒜` is quasi-coherent.** It is the sheaf associated to the
shifted grading, so this is Tag 01MB's instance
`AlgebraicGeometry.associatedModuleSheaf_isQuasicoherent`, named here at the `projRingSheaf`
spelling that the twist constructions and the Tag 0B5Q dévissage are stated over. -/
theorem isQuasicoherent_twistingSheaf (d : ℤ) :
    SheafOfModules.IsQuasicoherent (R := projRingSheaf 𝒜) (twistingSheaf 𝒜 d) :=
  inferInstance

/-- **The `d`-th twist of a quasi-coherent sheaf on `Proj 𝒜` is quasi-coherent.** The twist is the
sheafified tensor product with the twisting sheaf, so this is Tag 01CE — the tensor product of two
quasi-coherent modules on a ringed space is quasi-coherent — applied on the nose, with both
instance arguments supplied explicitly because instance search does not cross between the
`projRingSheaf 𝒜` and `structureSheafRing (Proj
  𝒜).toRingedSpace` spellings of the
same sheaf of rings.

Nothing in either tree stated this before; what existed was the general tensor instance one
spelling away. -/
theorem isQuasicoherent_twistSheafOfModules (F : SheafOfModules.{u} (projRingSheaf 𝒜))
    (hF : SheafOfModules.IsQuasicoherent (R := projRingSheaf 𝒜) F) (d : ℤ) :
    SheafOfModules.IsQuasicoherent (R := projRingSheaf 𝒜) (twistSheafOfModules 𝒜 F d) :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent.{u}
    (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace F (twistingSheaf 𝒜 d) hF
    (isQuasicoherent_twistingSheaf 𝒜 d)

/-! ### The structure morphism of Proj of a Noetherian graded ring -/

section Noetherian

variable [IsNoetherianRing A]

/-- **For a Noetherian graded ring the structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)` is proper.**
`Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing` supplies
`Algebra.FiniteType (𝒜 0) A`, which is the hypothesis of pinned Mathlib's properness instance for
`AlgebraicGeometry.Proj.toSpecZero`. -/
@[ega "II 2.7.1" "special case"]
theorem isProper_toSpecZero : IsProper (Proj.toSpecZero 𝒜) := by
  have : Algebra.FiniteType (𝒜 0) A :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒜
  infer_instance

/-- The structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)` of a Noetherian graded ring is quasi-compact.
This is one of the two hypotheses of the Tag 01XJ uniform vanishing. -/
theorem quasiCompact_toSpecZero : QuasiCompact (Proj.toSpecZero 𝒜) := by
  have := isProper_toSpecZero 𝒜
  infer_instance

/-- The structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)` of a Noetherian graded ring is quasi-separated.
This is the other hypothesis of the Tag 01XJ uniform vanishing; it is in fact available without
any finiteness, since `AlgebraicGeometry.Proj.isSeparated` is unconditional. -/
theorem quasiSeparated_toSpecZero : QuasiSeparated (Proj.toSpecZero 𝒜) := by
  have := isProper_toSpecZero 𝒜
  infer_instance

/-! ### The uniform vanishing bound -/

/-- **Tag 01XJ's uniform vanishing, at `Proj 𝒜` for a Noetherian graded ring.** There is a single
degree `n` above which the higher direct image along `Proj 𝒜 ⟶ Spec (𝒜 0)` of **every**
quasi-coherent sheaf vanishes.

The content is entirely
`Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward`; what is
new is that its hypotheses hold here, which is the three results above together with the
compactness of an affine spectrum. The design point of that theorem is what makes this useful for
Tag 0B5Q: the bound sits inside the induction predicate as an existential, so it does not depend
on the module, and the quantifier `∀ F` can therefore be instantiated at every twist at once. -/
theorem exists_isZero_rightDerivedPlus_pushforward_toSpecZero :
    ∃ n : ℤ, ∀ p : ℤ, n ≤ p → ∀ (F : (_root_.AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent],
      IsZero (((Scheme.Modules.pushforward (Proj.toSpecZero 𝒜)).rightDerivedPlus p).obj F) := by
  have := quasiCompact_toSpecZero 𝒜
  have := quasiSeparated_toSpecZero 𝒜
  exact Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward
    (Proj.toSpecZero 𝒜)

/-- **The relative form of Tag 0B5Q's `hbound`.** There is a single degree `n` above which, for
every quasi-coherent sheaf `F` on `Proj 𝒜` and **every** twist index `d`, the higher direct image
of `F(d)` along `Proj 𝒜 ⟶ Spec (𝒜 0)` vanishes.

Uniformity in `d` is not an extra argument: the bound of
`exists_isZero_rightDerivedPlus_pushforward_toSpecZero` is independent of the module, and `F(d)` is
quasi-coherent by `isQuasicoherent_twistSheafOfModules`, so the one bound serves every twist. This
is exactly the shape Tag 0B5Q's dévissage asks of `hbound`, with the derived global sections
`Hgroup` replaced by the relative higher direct image; see the module docstring for the bridge
between the two, which is the one thing this file does not supply. -/
theorem exists_isZero_rightDerivedPlus_twist :
    ∃ n : ℤ, ∀ p : ℤ, n ≤ p → ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜),
      SheafOfModules.IsQuasicoherent (R := projRingSheaf 𝒜) F → ∀ d : ℤ,
        IsZero (((Scheme.Modules.pushforward (Proj.toSpecZero 𝒜)).rightDerivedPlus p).obj
          (twistSheafOfModules 𝒜 F d)) := by
  obtain ⟨n, hn⟩ := exists_isZero_rightDerivedPlus_pushforward_toSpecZero 𝒜
  exact ⟨n, fun p hp F hF d ↦
    @hn p hp (twistSheafOfModules 𝒜 F d) (isQuasicoherent_twistSheafOfModules 𝒜 F hF d)⟩

/-- **Eventual coherence of the higher direct images on `Proj 𝒜`.** Above the same degree every
higher direct image of every quasi-coherent sheaf is coherent, because it vanishes. This is
`AlgebraicGeometry.ProperCoherentFiniteType.exists_isCoherent_rightDerivedPlus_of_le` at the
structure morphism; no Noetherian hypothesis enters beyond the one making that morphism proper, the
coherence being obtained from the weak Serre class rather than from finiteness. -/
theorem exists_isCoherent_rightDerivedPlus_pushforward_toSpecZero :
    ∃ n : ℤ, ∀ p : ℤ, n ≤ p → ∀ F : (_root_.AlgebraicGeometry.Proj 𝒜).Modules, F.IsQuasicoherent →
      (((Scheme.Modules.pushforward (Proj.toSpecZero 𝒜)).rightDerivedPlus p).obj F).IsCoherent := by
  have := quasiCompact_toSpecZero 𝒜
  have := quasiSeparated_toSpecZero 𝒜
  exact AlgebraicGeometry.ProperCoherentFiniteType.exists_isCoherent_rightDerivedPlus_of_le
    (Proj.toSpecZero 𝒜)

end Noetherian

end Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound

end
