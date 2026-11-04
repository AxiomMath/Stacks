module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Pair
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 01PF: extending a finite type quasi-coherent submodule from a quasi-compact open

This file closes [Stacks, Tag 01PF] at module level: on a quasi-compact and quasi-separated
scheme, a quasi-coherent submodule of finite type of the restriction of a quasi-coherent module
to a quasi-compact open extends to a quasi-coherent submodule of finite type of the module
itself, with that restriction.

What is here is the recursion. The affine case in the form it needs is
`StacksFrontier/AlgebraicGeometry/AffineExtend/Basic.lean` and the two-member step
`X = U ∪ V` with `V` affine is
`StacksFrontier/AlgebraicGeometry/AffineExtend/Pair.lean`; this file supplies the finite
affine covering, iterates the step along it, and discharges the two topological hypotheses the
step left named.

## Main results

* `exists_isFiniteType_submodule_restrictTo_eq_of_qcqs`: **[Stacks, Tag 01PF]**, tagged.
* `exists_submodule_obj_eq_of_qcqs`: the same in the sections currency — the extension is
  controlled by `N.obj (op Z) = N₀.obj (op Z)` for the opens `Z` inside `U` rather than by an
  equality of restrictions, which is the form the recursion produces.
* `exists_submodule_obj_eq_of_finset`: **the recursion**, over an arbitrary finite family of
  affine opens and with no hypothesis on the scheme beyond quasi-separatedness.
* `quasiCompact_ι`: the inclusion of a quasi-compact open of a quasi-separated space is a
  quasi-compact morphism — the fact that discharges both hypotheses of the two-member step.
* `isQuasicoherent_of_restrict_top`, `isFiniteType_of_restrict_top`: the two properties over `⊤`
  are the two properties.
* `exists_finset_affineOpens_iSup_eq_top`: a quasi-compact scheme has a finite affine covering,
  as a `Finset` of `X.affineOpens`.

## The covering set, and clause 2

The tag is attached to `exists_isFiniteType_submodule_restrictTo_eq_of_qcqs` alone: [Stacks, Tag
01PF] has a single, unlabelled assertion, and that theorem is it. Its elaborated binder list is

```
∀ {X : Scheme} {F : X.Modules} [CompactSpace ↥X] [QuasiSeparatedSpace ↥X]
  [SheafOfModules.IsQuasicoherent F] {U : X.Opens}, IsCompact ↑U →
  ∀ (G : SheafOfModules.Submodule (F.restrict U.ι)),
    G.toSheafOfModules.IsQuasicoherent → G.toSheafOfModules.IsFiniteType →
    ∃ N, N.toSheafOfModules.IsQuasicoherent ∧ N.toSheafOfModules.IsFiniteType ∧
      restrictTo U.ι N = G
```

— quasi-compact and quasi-separated `X`, quasi-coherent `F`, quasi-compact open `U`, and `G`
quasi-coherent of finite type, which is the tag's hypothesis list and nothing more. Nothing on
the route needs the scheme to be affine, Noetherian or separated, and the conclusion is an
**equality** of submodules, `G'|_U = G`, which is how the source states it.

A submodule is spelled as a concrete `SheafOfModules.Submodule` rather than as a categorical
`Subobject`. The two notions are identified in both directions in this tree —
`Stacks.AlgebraicGeometry.SubmodulePrimitives.ofSubobject` with `ofSubobjectIso`, and
`SheafOfModules.Submodule.toSubobject` with `toSubobjectIso` in
`StacksFrontier/AlgebraicGeometry/AffineExtend/Basic.lean` — so the choice is a spelling and not a
weakening. The
subobject-shaped restatement is **not** written here: it would have to compare
`(G' : X.Modules).restrict U.ι` with `(G : U.toScheme.Modules)` through two equalities of objects,
hence through `eqToHom`, and carry that through the commuting square with `G.arrow`; the concrete
form needs none of it.

## Implementation notes

**Two `whnf` timeouts, both the same cause and neither a budget problem.** The identity
`Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules` is `rfl` in the file it
is stated in and is **not affordable as a defeq check** here: letting it be found by unification
when applying `isQuasicoherent_of_restrict_top` to a hypothesis in the `restrictTo` spelling is a
deterministic timeout at 200000 heartbeats, and so is instantiating
`AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens` by unifying its implicit open
against a coercion. Both compile at the default budget once the term is pinned — the equation
applied explicitly with `▸`, and the open passed as a named argument. Zero compiler options in
this directory.

`isQuasicoherent_of_restrict_top` goes through `X.topIso.symm` and not through `(⊤ : X.Opens).ι`
directly, and its hypothesis has to be re-stated at `X.topIso.symm.inv` before the instance for
the iterated restriction is found: `AlgebraicGeometry.Scheme.topIso_hom` is a simp lemma, not an
`rfl` instance search will apply.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01PFAffineExtend

open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.AlgebraicGeometry.SubmoduleRestrict
open Stacks.AlgebraicGeometry.SubmoduleGlueOpens Stacks.AlgebraicGeometry.SubmoduleAgree
open Stacks.AlgebraicGeometry.SubmoduleRelativeLocality

variable {X : Scheme.{u}} {F : X.Modules}

/-! ### The two topological facts -/

/-- **The inclusion of a quasi-compact open of a quasi-separated space is a quasi-compact
morphism.** -/
theorem quasiCompact_ι [QuasiSeparatedSpace X] {W : X.Opens} (hW : IsCompact (W : Set X)) :
    QuasiCompact W.ι :=
  quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hW.isRetrocompact W.2))

/-! ### Transporting the two properties from the top open to the whole scheme -/

/-- **Quasi-coherence over `⊤` is quasi-coherence.** -/
theorem isQuasicoherent_of_restrict_top (M : X.Modules)
    (hqc : (Scheme.Modules.restrict M (⊤ : X.Opens).ι).IsQuasicoherent) : M.IsQuasicoherent :=
  have h1 : (Scheme.Modules.restrict M X.topIso.symm.inv).IsQuasicoherent := hqc
  have := h1
  isQuasicoherent_of_iso (CoherentTFAE.restrictIsoSelf X.topIso.symm M) inferInstance

/-- **Finite type over `⊤` is finite type.** -/
theorem isFiniteType_of_restrict_top (M : X.Modules)
    (hft : (Scheme.Modules.restrict M (⊤ : X.Opens).ι).IsFiniteType) : M.IsFiniteType :=
  have h1 : (Scheme.Modules.restrict M X.topIso.symm.inv).IsFiniteType := hft
  AlgebraicGeometry.Modules.isFiniteType_of_iso (CoherentTFAE.restrictIsoSelf X.topIso.symm M)
    (AlgebraicGeometry.Modules.isFiniteType_restrict X.topIso.symm.hom _ h1)

/-! ### The recursion -/

/-- **The recursion of [Stacks, Tag 01PF].** Along any finite family of affine opens, the
two-member step iterates: a submodule quasi-coherent and of finite type over a quasi-compact
open `U` extends to one quasi-coherent and of finite type over `U` together with the family,
with its sections over the opens inside `U` unchanged. -/
theorem exists_submodule_obj_eq_of_finset [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    (s : Finset X.affineOpens) : ∀ U : X.Opens, IsCompact (U : Set X) → ∀ N₀ : F.Submodule,
      ((restrictTo U.ι N₀).toSheafOfModules : U.toScheme.Modules).IsQuasicoherent →
      ((restrictTo U.ι N₀).toSheafOfModules : U.toScheme.Modules).IsFiniteType →
      ∃ N : F.Submodule,
        ((restrictTo (U ⊔ ⨆ V ∈ s, (V : X.Opens)).ι N).toSheafOfModules :
          (U ⊔ ⨆ V ∈ s, (V : X.Opens)).toScheme.Modules).IsQuasicoherent ∧
        ((restrictTo (U ⊔ ⨆ V ∈ s, (V : X.Opens)).ι N).toSheafOfModules :
          (U ⊔ ⨆ V ∈ s, (V : X.Opens)).toScheme.Modules).IsFiniteType ∧
        ∀ Z : X.Opens, Z ≤ U → N.obj (op Z) = N₀.obj (op Z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U hU N₀ hqc hft
    have heq : U ⊔ (⨆ V ∈ (∅ : Finset X.affineOpens), (V : X.Opens)) = U := by simp
    rw [heq]
    exact ⟨N₀, hqc, hft, fun _ _ => rfl⟩
  | @insert V s _ ih =>
    intro U hU N₀ hqc hft
    have hqcV : QuasiCompact V.1.ι := quasiCompact_ι V.2.isCompact
    have : IsAffine V.1.toScheme := V.2
    have hcpt : IsCompact (((V.1.ι ⁻¹ᵁ U) : V.1.toScheme.Opens) : Set V.1.toScheme) :=
      V.1.ι.isCompact_preimage hU
    obtain ⟨N₁, hN₁qc, hN₁ft, hN₁⟩ :=
      exists_submodule_obj_eq_sup U V.1 V.2 hcpt (quasiCompact_ι hcpt) N₀ hqc hft
    have hUV : IsCompact ((U ⊔ V.1 : X.Opens) : Set X) := by
      rw [Opens.coe_sup]
      exact hU.union V.2.isCompact
    obtain ⟨N, hNqc, hNft, hN⟩ := ih (U ⊔ V.1) hUV N₁ hN₁qc hN₁ft
    have heq : (U ⊔ V.1) ⊔ (⨆ V' ∈ s, (V' : X.Opens)) =
        U ⊔ (⨆ V' ∈ insert V s, (V' : X.Opens)) := by
      rw [Finset.iSup_insert, sup_assoc]
    rw [← heq]
    exact ⟨N, hNqc, hNft,
      fun Z hZ => (hN Z (hZ.trans le_sup_left)).trans (hN₁ Z hZ)⟩

/-! ### Tag 01PF -/

/-- A finite family of affine opens covering a quasi-compact scheme. -/
theorem exists_finset_affineOpens_iSup_eq_top [CompactSpace X] :
    ∃ s : Finset X.affineOpens, (⨆ V ∈ s, (V : X.Opens)) = ⊤ := by
  classical
  have htopcpt : IsCompact ((⊤ : X.Opens) : Set X) := by
    rw [Opens.coe_top]; exact isCompact_univ
  obtain ⟨s, hsfin, hcov⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp htopcpt
  refine ⟨hsfin.toFinset, ?_⟩
  have h1 : (⨆ V ∈ hsfin.toFinset, (V : X.Opens)) = ⨆ V ∈ s, (V : X.Opens) := by
    simp only [Set.Finite.mem_toFinset]
  rw [h1, ← hcov]

/-- **[Stacks, Tag 01PF] in the sections currency.** The extension is controlled over the opens
inside `U` section by section rather than by an equality of restrictions; this is what the
recursion produces, and `restrictTo_eq_of_obj_eq` converts it. -/
theorem exists_submodule_obj_eq_of_qcqs [CompactSpace X] [QuasiSeparatedSpace X]
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsCompact (U : Set X)) (N₀ : F.Submodule)
    (hqc : ((restrictTo U.ι N₀).toSheafOfModules : U.toScheme.Modules).IsQuasicoherent)
    (hft : ((restrictTo U.ι N₀).toSheafOfModules : U.toScheme.Modules).IsFiniteType) :
    ∃ N : F.Submodule, (N.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (N.toSheafOfModules : X.Modules).IsFiniteType ∧
      ∀ Z : X.Opens, Z ≤ U → N.obj (op Z) = N₀.obj (op Z) := by
  obtain ⟨s, hs⟩ := exists_finset_affineOpens_iSup_eq_top (X := X)
  obtain ⟨N, hNqc, hNft, hN⟩ := exists_submodule_obj_eq_of_finset s U hU N₀ hqc hft
  have htop : U ⊔ (⨆ V ∈ s, (V : X.Opens)) = ⊤ := by rw [hs, sup_top_eq]
  rw [htop] at hNqc hNft
  have e := restrictTo_toSheafOfModules (⊤ : X.Opens).ι N
  exact ⟨N, isQuasicoherent_of_restrict_top _ (e ▸ hNqc),
    isFiniteType_of_restrict_top _ (e ▸ hNft), hN⟩

/-- **Stacks Project, Tag 01PF.** Let `X` be a quasi-compact and quasi-separated scheme, let
`U ⊆ X` be a quasi-compact open, let `F` be a quasi-coherent `𝒪_X`-module and let `G ⊆ F|_U` be a
quasi-coherent `𝒪_U`-submodule which is of finite type. Then there exists a quasi-coherent
submodule `G' ⊆ F` which is of finite type such that `G'|_U = G`. -/
@[stacks 01PF, ega "I 9.4.6" "qcqs case", ega "I 9.4.3" "qcqs scheme", ega "I 9.4.7" "(b)"]
theorem exists_isFiniteType_submodule_restrictTo_eq_of_qcqs
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact (U : Set X)) (G : (F.restrict U.ι).Submodule)
    (hqc : (G.toSheafOfModules : U.toScheme.Modules).IsQuasicoherent)
    (hft : (G.toSheafOfModules : U.toScheme.Modules).IsFiniteType) :
    ∃ N : F.Submodule, (N.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (N.toSheafOfModules : X.Modules).IsFiniteType ∧ restrictTo U.ι N = G := by
  obtain ⟨N, hNqc, hNft, hN⟩ := exists_submodule_obj_eq_of_qcqs hU (coRestrict U.ι G)
    (by rwa [restrictTo_coRestrict]) (by rwa [restrictTo_coRestrict])
  exact ⟨N, hNqc, hNft,
    (restrictTo_eq_of_obj_eq (W := U) hN).trans (restrictTo_coRestrict U.ι G)⟩

end Stacks.AlgebraicGeometry.Tag01PFAffineExtend

end
