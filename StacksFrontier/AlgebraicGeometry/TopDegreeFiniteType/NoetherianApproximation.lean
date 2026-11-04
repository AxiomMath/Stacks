module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Limits.ProperFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationColimit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeRightExact
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.AffineModuleFinite
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Noetherian approximation of a proper morphism with bounded fibres

[Stacks, Tag 0EX4] and [Stacks, Tag 0EX5] both begin by replacing a proper morphism by a proper
morphism **of finite presentation**. The source does this with the limit presentation of
[Stacks, Tag 09ZR] — `X = lim X_i` with `X_i ⟶ Y` proper and of finite presentation and all the
transition morphisms and projections closed immersions — and then picks out a stage whose fibres
still satisfy the dimension bound, by [Stacks, Tag 05M5]. Since `X ⟶ X_i` is a closed immersion,
the higher direct images along `f` and along `X_i ⟶ Y` of the corresponding modules agree, by
[Stacks, Tag 30.2.3] and Leray; so the conclusion for `f` follows from the conclusion at the
stage.

The single stage is
`…TopDegreeBaseChange.exists_isClosedImmersion_isProper_finitePresentation_fiber_dim_le`: a proper
morphism onto a quasi-compact quasi-separated base all of whose fibres have dimension at most `d`
factors as a closed immersion followed by a proper morphism **of finite presentation** all of
whose fibres still have dimension at most `d`. This file reads off from it the finite-type
conclusion of [Stacks, Tag 0EX4] for `f` as soon as it holds for every proper morphism of finite
presentation onto the same base with the same bound on its fibres, and then assembles the rest
of the source's proof around the remaining inputs.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeFiniteType`.

* `isFiniteType_rightDerived_of_finitePresentation_case`: the finite-type conclusion of
  [Stacks, Tag 0EX4] for a proper `f`, from the case of a proper morphism of finite
  presentation.
* `isFiniteType_rightDerived_of_isFinitePresentation_case`: **the middle paragraph of the
  source's proof** — given the vanishing above `d`, the finite-type conclusion for modules of
  finite presentation gives it for quasi-coherent modules of finite type.
* `isFiniteType_rightDerived_of_model_of_baseChange`: **the last paragraph of the source's
  proof** — the finite-presentation case over an affine base, from a Noetherian model of the pair
  and the top-degree base change.
* `isFiniteType_rightDerived_of_isAffine_of_noetherianInputs` and
  `isFiniteType_rightDerived_of_noetherianInputs`: **the finite-type conclusion of
  [Stacks, Tag 0EX4]** over an affine base and over an arbitrary base, from the vanishing above
  `d` and the case of a proper morphism of finite presentation with a module of finite
  presentation.
* `isQuasicoherent_isFiniteType_rightDerived_of_noetherianInputs`: **both clauses of
  [Stacks, Tag 0EX4]** from the same two inputs.

## Implementation notes

**No `@[stacks 0EX4]` attribute is attached**: every statement here carries the
finite-presentation case or the vanishing above `d` as an argument, which
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/Unconditional.lean` supplies.

**Why the pushforward along the closed immersion is handled by
`…ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso` and not by a spectral sequence.**
That isomorphism is `R ⁿ (ι ≫ g)_* ≅ ι_* ⋙ R ⁿ g_*` for a closed immersion `ι`, which is the
degenerate case of the relative Leray spectral sequence the source cites, and it is already
proved. It is stated for Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, which is
the indexing [Stacks, Tag 0EX4] uses, so no comparison of indexings is needed here.

**The derived-category model is pinned.** `CategoryTheory.HasDerivedCategory.standard` is a local
instance at priority 2000, because the imports also carry a global
`CategoryTheory.HasDerivedCategory.{u}` instance for `X.Modules`
(`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`) and the statements of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/` used here are elaborated at `standard`.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry hiding moduleGlobalSections
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### The reduction to a morphism of finite presentation -/

/-- **The finite-type conclusion of [Stacks, Tag 0EX4] for a proper morphism, from the case of a
proper morphism of finite presentation.** The closed immersion `ι : X ⟶ X'` of
`…TopDegreeBaseChange.exists_isClosedImmersion_isProper_finitePresentation_fiber_dim_le` is a
finite morphism, so `ι_* F` is again quasi-coherent of finite type, and
`R ᵈ f_* F = R ᵈ g_* (ι_* F)` by `…ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso`.

No `@[stacks 0EX4]` attribute: `hfp` is a hypothesis the tag discharges. -/
theorem isFiniteType_rightDerived_of_finitePresentation_case
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (d : ℕ) (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hfp : ∀ (X' : Scheme.{u}) (g : X' ⟶ Y), IsProper g →
      AlgebraicGeometry.FinitePresentation g →
      (∀ y : Y, topologicalKrullDim (g.fiber y) ≤ (d : WithBot ℕ∞)) →
        ∀ G : X'.Modules, G.IsQuasicoherent → G.IsFiniteType →
          (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFiniteType) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType := by
  obtain ⟨X', g, ι, hgpr, hgfp, hιcl, hcomp, hgdim⟩ :=
    TopDegreeBaseChange.exists_isClosedImmersion_isProper_finitePresentation_fiber_dim_le
      f d hdim
  subst hcomp
  have hstage := hfp X' g hgpr hgfp hgdim ((Scheme.Modules.pushforward ι).obj F)
    inferInstance (isFiniteType_pushforward_of_isFinite ι F)
  have := hstage
  exact Stacks.SheafOfModules.isFiniteType_of_iso
    (M := ((Scheme.Modules.pushforward g).rightDerived d).obj
      ((Scheme.Modules.pushforward ι).obj F))
    ((ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso ι g d).app F).symm

/-! ### From modules of finite presentation to modules of finite type -/

/-- **The middle paragraph of the proof of [Stacks, Tag 0EX4].** For `f : X ⟶ Y` proper onto a
quasi-compact quasi-separated base, all of whose higher direct images vanish above `d`, the
finite-type conclusion in degree `d` for every `𝒪_X`-module of **finite presentation** gives it
for every quasi-coherent `𝒪_X`-module of finite type.

A quasi-coherent module of finite type on a quasi-compact quasi-separated scheme is a quotient of
one of finite presentation ([Stacks, Tag 086M],
`AlgebraicGeometry.exists_finitePresentation_epi`); in degree `d` the induced map on `R ᵈ f_*` is
then surjective, because `R ᵈ ⁺ ¹ f_*` of the kernel vanishes
(`…TopDegreeBaseChange.epi_rightDerivedPlus_pushforward_map_of_vanishes`); and a quotient of a
module of finite type is of finite type.

No `@[stacks 0EX4]` attribute: `hvan` and `hFP` are hypotheses the tag discharges. -/
theorem isFiniteType_rightDerived_of_isFinitePresentation_case
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj G))
    (hFP : ∀ G : X.Modules, G.IsFinitePresentation →
      (((Scheme.Modules.pushforward f).rightDerived d).obj G).IsFiniteType)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨A, hA, φ, hφ⟩ := AlgebraicGeometry.exists_finitePresentation_epi X F
  have := hA
  have := hφ
  have : A.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation A
  have hepi := TopDegreeBaseChange.epi_rightDerivedPlus_pushforward_map_of_vanishes f d
    (ShortComplex.shortExact_mk_kernel_ι φ) inferInstance hvan
  have hnat := (Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward f) d).hom.naturality φ
  have heq : ((Scheme.Modules.pushforward f).rightDerived d).map φ =
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) d).hom.app A ≫
        ((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map φ ≫
          (Stacks.DerivedIndexing.rightDerivedIso
            (Scheme.Modules.pushforward f) d).inv.app F := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have : Epi (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map φ) := hepi
  have hepi₂ : Epi (((Scheme.Modules.pushforward f).rightDerived d).map φ) := by
    rw [heq]; infer_instance
  exact @Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} _ _ _ _ _ _ _ _ _
    (((Scheme.Modules.pushforward f).rightDerived d).map φ) hepi₂ (hFP A hA)


/-- The vanishing above `d` for a proper morphism onto an affine base, from the family of
vanishing statements for global sections. -/
private theorem isZero_rightDerivedPlus_pushforward_of_hvanFamily (d : ℕ)
    (hvanFamily : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] [IsAffine Y]
    (hdim : ∀ s : Y, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) :
    ∀ i : ℤ, (d : ℤ) < i → ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G) :=
  fun i hi G hG =>
    TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing d
      hvanFamily g inferInstance inferInstance hdim i hi G hG

/-! ### The finite-type conclusion over an affine base -/

/-- **The finite-type conclusion of [Stacks, Tag 0EX4] over an affine base**, from the two
residues of the source's proof: the vanishing above `d` over an affine base, and the conclusion
for a proper morphism of finite presentation and a module of finite presentation.

The first reduction is [Stacks, Tag 09ZR] with [Stacks, Tag 05M5]
(`isFiniteType_rightDerived_of_finitePresentation_case`), which replaces `f` by a proper morphism
of finite presentation; the second is [Stacks, Tag 086M] with top-degree right exactness
(`isFiniteType_rightDerived_of_isFinitePresentation_case`), which replaces `F` by a module of
finite presentation.

No `@[stacks 0EX4]` attribute: both inputs are hypotheses. -/
theorem isFiniteType_rightDerived_of_isAffine_of_noetherianInputs (d : ℕ)
    (hvanFamily : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    (hFPcase : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g →
      AlgebraicGeometry.FinitePresentation g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ G : X₀.Modules, G.IsFinitePresentation →
        (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFiniteType)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType := by
  refine isFiniteType_rightDerived_of_finitePresentation_case f d hdim F ?_
  intro X' g hg hgfp hgdim G hG hGft
  have := hg
  have := hG
  have := hGft
  exact isFiniteType_rightDerived_of_isFinitePresentation_case g d
    (isZero_rightDerivedPlus_pushforward_of_hvanFamily d hvanFamily g hgdim)
    (fun G' hG' => hFPcase g hg hgfp inferInstance hgdim G' hG') G


/-! ### The tag over an arbitrary base -/

/-- **The finite-type conclusion of [Stacks, Tag 0EX4] over an arbitrary base**, from the same
two inputs as `isFiniteType_rightDerived_of_isAffine_of_noetherianInputs`. The question is local
on `Y` (`isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase`), and
the fibre bound transports to the restricted morphism, so the affine case suffices.

No `@[stacks 0EX4]` attribute: both inputs are hypotheses. -/
theorem isFiniteType_rightDerived_of_noetherianInputs (d : ℕ)
    (hvanFamily : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    (hFPcase : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g →
      AlgebraicGeometry.FinitePresentation g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ G : X₀.Modules, G.IsFinitePresentation →
        (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFiniteType)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase f d hdim F
    fun X₀ Y₀ g hg hY₀ hgdim G hG hGft => by
      have := hg
      have := hY₀
      have := hG
      have := hGft
      exact isFiniteType_rightDerived_of_isAffine_of_noetherianInputs d hvanFamily hFPcase g
        hgdim G


/-- **Both clauses of [Stacks, Tag 0EX4] over an arbitrary base, from the two inputs.** The
quasi-coherence clause is already proved and is found by instance search — a proper morphism is
quasi-compact and quasi-separated, which is all [Stacks, Tag 01XJ] needs — and the finite-type
clause is `isFiniteType_rightDerived_of_noetherianInputs`.

The source prints the conclusion as a statement about an `𝒪_X`-module; `R ᵈ f_* F` is a sheaf on
`Y`, and the `𝒪_Y`-reading is the one the source's own proof supports and the one Lean's types
force.

No `@[stacks 0EX4]` attribute: both inputs are hypotheses. -/
theorem isQuasicoherent_isFiniteType_rightDerived_of_noetherianInputs (d : ℕ)
    (hvanFamily : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    (hFPcase : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g →
      AlgebraicGeometry.FinitePresentation g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ G : X₀.Modules, G.IsFinitePresentation →
        (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFiniteType)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsQuasicoherent ∧
      (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  ⟨inferInstance, isFiniteType_rightDerived_of_noetherianInputs d hvanFamily hFPcase f hdim F⟩


/-! ### The finite-presentation case from a Noetherian model and the top-degree base change -/

/-- **The last paragraph of the proof of [Stacks, Tag 0EX4].** For a proper morphism of finite
presentation onto an affine base with fibres of dimension at most `d`, and an `𝒪_X`-module of
finite presentation, the finite-type conclusion in degree `d` follows from a Noetherian model of
the pair together with the top-degree base change.

Over the affine Noetherian base `Y₀` the model `G₀` of `G` is of finite presentation on the
locally Noetherian `X₀`, hence coherent; the base change identifies `H ᵈ (X, G)` with
`H ᵈ (X₀, G₀) ⊗ Γ(Y, ⊤)`, which is a finite `Γ(Y, ⊤)`-module because `H ᵈ (X₀, G₀)` is a finite
`Γ(Y₀, ⊤)`-module by [Stacks, Tag 02O6]; and over an affine base finiteness of the cohomology
module is finiteness of type of `R ᵈ f_* G`
(`…TopDegreeFiniteType.isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine`).

No `@[stacks 0EX4]` attribute: all three inputs are hypotheses. -/
theorem isFiniteType_rightDerived_of_model_of_baseChange (d : ℕ)
    (hvanFamily : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    (hmodelMod : ∀ {X₁ Y₁ : Scheme.{u}} (g : X₁ ⟶ Y₁), IsProper g →
      AlgebraicGeometry.FinitePresentation g → IsAffine Y₁ →
      (∀ s : Y₁, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ G : X₁.Modules, G.IsFinitePresentation →
      ∃ (X₀ Y₀ : Scheme.{u}) (g₀ : X₀ ⟶ Y₀) (u : Y₁ ⟶ Y₀) (h : X₁ ⟶ X₀) (G₀ : X₀.Modules),
        IsAffine Y₀ ∧ IsLocallyNoetherian Y₀ ∧ IsProper g₀ ∧
          (∀ s : Y₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) ∧
          G₀.IsFinitePresentation ∧ IsPullback h g g₀ u ∧
          Nonempty (G ≅ (Scheme.Modules.pullback h).obj G₀))
    (hBC : ∀ {X₀ Y₀ X₁ Y₁ : Scheme.{u}} (g₀ : X₀ ⟶ Y₀), IsProper g₀ → IsAffine Y₀ →
      IsLocallyNoetherian Y₀ →
      (∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus i).obj G)) →
      ∀ G₀ : X₀.Modules, G₀.IsCoherent → IsAffine Y₁ →
      ∀ (h : X₁ ⟶ X₀) (g : X₁ ⟶ Y₁) (u : Y₁ ⟶ Y₀), IsPullback h g g₀ u →
      ∀ G : X₁.Modules, (G ≅ (Scheme.Modules.pullback h).obj G₀) →
        Module.Finite Γ(Y₁, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X₁).rightDerived d).obj G))) :
    ∀ {X₁ Y₁ : Scheme.{u}} (g : X₁ ⟶ Y₁), IsProper g →
      AlgebraicGeometry.FinitePresentation g → IsAffine Y₁ →
      (∀ s : Y₁, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ G : X₁.Modules, G.IsFinitePresentation →
        (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFiniteType := by
  intro X₁ Y₁ g hg hgfp hY₁ hgdim G hG
  have := hg
  have := hY₁
  have := hG
  obtain ⟨X₀, Y₀, g₀, u, h, G₀, hY₀, hY₀N, hg₀, hg₀dim, hG₀, hsq, ⟨e⟩⟩ :=
    hmodelMod g hg hgfp hY₁ hgdim G hG
  have := hY₀
  have := hY₀N
  have := hg₀
  have := hG₀
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian g₀
  have hfin := hBC g₀ hg₀ hY₀ hY₀N
    (isZero_rightDerivedPlus_pushforward_of_hvanFamily d hvanFamily g₀ hg₀dim) G₀
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation G₀ hG₀)
    hY₁ h g u hsq G e
  have hGqc : G.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation G
  have := hGqc
  exact isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine g G d hfin


end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
