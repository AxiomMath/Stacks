module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.BaseChangeFinite
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.NoetherianModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0EX4: the inputs of the limit argument discharged

`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianApproximation.lean` reduces the
finite-type conclusion of [Stacks, Tag 0EX4] to three inputs: the vanishing of the cohomology
above `d` over an affine base, a **Noetherian model** of a proper morphism of finite
presentation together with a module of finite presentation over an affine base, and the
**top-degree base change**.

This file discharges all three. The vanishing is
`…TopDegreeBaseChange.cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le`, the model is
`…TopDegreeFiniteType.exists_noetherianModel`, and the top-degree base change is
`…TopDegreeFiniteType.moduleFinite_cohomology_of_isPullback_of_isQuasicoherent`. With them
[Stacks, Tag 0EX4] holds with no hypothesis beyond the source's.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeFiniteType`.

* `isFiniteType_rightDerived_of_baseChange`: the Noetherian model eliminated from the hypotheses
  of `…NoetherianApproximation.isFiniteType_rightDerived_of_model_of_baseChange`.
* `isFiniteType_rightDerived_of_baseChange'`: the finite-type conclusion of [Stacks, Tag 0EX4]
  over an arbitrary base, with the top-degree base change as its only hypothesis.
* `isZero_rightDerivedPlus_pushforward_of_forall_topologicalKrullDim_fiber_le`: the vanishing of
  the higher direct image sheaves above `d`, in the shape the proof of [Stacks, Tag 0EX5] uses.
* `isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le`: the finite-type
  clause of [Stacks, Tag 0EX4], that hypothesis discharged.
* `isQuasicoherent_isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le`:
  **[Stacks, Tag 0EX4]**, both clauses, over an arbitrary base.

## Implementation notes

**`@[stacks 0EX4]` is attached once**, to
`isQuasicoherent_isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le`,
which states both clauses of the tag under exactly its hypotheses. The finite-type clause on its
own, and the intermediate statements that still take the top-degree base change as an argument,
carry no attribute. The quasi-coherence clause alone also carries
`@[stacks 0EX4 "quasi-coherence"]` in `StacksFrontier/AlgebraicGeometry/ProperQcoh/Basic.lean`.

**The derived-category model is pinned.** `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`
installs a global `CategoryTheory.HasDerivedCategory.{u}` instance for `X.Modules`, while the
statements imported from `NoetherianApproximation.lean` and from
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/` are elaborated at
`CategoryTheory.HasDerivedCategory.standard`, which is `.{u + 1}`. The two `rightDerivedPlus`
functors are different constants and do not unify, so `standard` is pinned at local priority
2000, as it is in `…TopDegreeBaseChange/AffineBaseVanishing.lean`.

**The existential binders are reordered.** `…NoetherianModel.exists_noetherianModel` returns the
base before the source, `∃ (Y₀ X₀ : Scheme.{u}) …`, while the hypothesis of
`…NoetherianApproximation.isFiniteType_rightDerived_of_model_of_baseChange` asks for the source
first. The anonymous constructor below is that permutation and nothing else.

**`open AlgebraicGeometry hiding moduleGlobalSections`.** The imports bring
`AlgebraicGeometry.moduleGlobalSections` into scope alongside
`Stacks.Cohomology.AffineBase.moduleGlobalSections`; the two have the same type and every
statement here means the second.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry hiding moduleGlobalSections
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### The finite-presentation case over an affine base -/

/-- **The finite-type conclusion for a proper morphism of finite presentation and a module of
finite presentation over an affine base, from the top-degree base change.** The Noetherian model
that `isFiniteType_rightDerived_of_model_of_baseChange` asks for is
`exists_noetherianModel`. -/
theorem isFiniteType_rightDerived_of_baseChange (d : ℕ)
    (hvanFamily : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
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
        (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFiniteType :=
  isFiniteType_rightDerived_of_model_of_baseChange d hvanFamily
    (fun g hg hgfp hY hgdim G hG => by
      have := hg
      have := hY
      have := hG
      obtain ⟨Y₀, X₀, g₀, u, h, G₀, hY₀, hY₀N, hg₀, hg₀dim, hG₀, hpb, he⟩ :=
        exists_noetherianModel g hgfp d hgdim G
      exact ⟨X₀, Y₀, g₀, u, h, G₀, hY₀, hY₀N, hg₀, hg₀dim, hG₀, hpb, he⟩)
    hBC

/-! ### The tag, conditional only on the top-degree base change -/

/-- **The finite-type conclusion of [Stacks, Tag 0EX4] over an arbitrary base**, with the
top-degree base change as the only remaining hypothesis: the vanishing above `d` is
`…TopDegreeBaseChange.cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le` and the
Noetherian model is
`…NoetherianModel.exists_noetherianModel`. -/
theorem isFiniteType_rightDerived_of_baseChange' (d : ℕ)
    (hBC : ∀ {X₀ Y₀ X₁ Y₁ : Scheme.{u}} (g₀ : X₀ ⟶ Y₀), IsProper g₀ → IsAffine Y₀ →
      IsLocallyNoetherian Y₀ →
      (∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus i).obj G)) →
      ∀ G₀ : X₀.Modules, G₀.IsCoherent → IsAffine Y₁ →
      ∀ (h : X₁ ⟶ X₀) (g : X₁ ⟶ Y₁) (u : Y₁ ⟶ Y₀), IsPullback h g g₀ u →
      ∀ G : X₁.Modules, (G ≅ (Scheme.Modules.pullback h).obj G₀) →
        Module.Finite Γ(Y₁, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X₁).rightDerived d).obj G)))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_noetherianInputs d
    (TopDegreeBaseChange.cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le d)
    (isFiniteType_rightDerived_of_baseChange d
      (TopDegreeBaseChange.cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le d) hBC)
    f hdim F


/-! ### The vanishing in the shape the finite-presentation analogue consumes -/

/-- **The vanishing above `d` as [Stacks, Tag 0E7D] clause (2) is consumed**: the higher direct
image **sheaf** `R ʲ g₀_* G'` vanishes for every `j > d`, every quasi-coherent `G'`, and every
proper `g₀` onto an affine Noetherian base whose fibres all have dimension at most `d`.

This is `…TopDegreeBaseChange.cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le` read
through
`…TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`, which over an
affine base turns the vanishing of `H ʲ (X₀, G')` into the vanishing of the sheaf.

The Noetherian hypothesis on the base is **inert** — the binder is named `_hSN` for that reason.
The vanishing holds over an arbitrary affine base, so this statement is strictly weaker
than what is available; it is phrased with the hypothesis because that is the shape
[Stacks, Tag 0EX5]'s limit argument asks for, where the base of the stage is Noetherian anyway. -/
@[ega "III 4.2.2" "special case"]
theorem isZero_rightDerivedPlus_pushforward_of_forall_topologicalKrullDim_fiber_le (d : ℕ) :
    ∀ (X₀ S₀ : Scheme.{u}) (g₀ : X₀ ⟶ S₀), IsProper g₀ → IsAffine S₀ →
      IsNoetherian S₀ → (∀ s : S₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ j : ℤ, (d : ℤ) < j → ∀ G' : X₀.Modules, G'.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus j).obj G') := by
  intro X₀ S₀ g₀ hg hS _hSN hdim j hj G' hG'
  exact TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing d
    (TopDegreeBaseChange.cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le d) g₀ hg hS
    hdim j hj G' hG'


/-! ### Tag 0EX4 -/

/-- **[Stacks, Tag 0EX4], the finite-type clause.** Let `f : X ⟶ Y` be a morphism of schemes, let
`d ≥ 0`, and let `F` be an `𝒪_X`-module. Assume

* `f` is a proper morphism all of whose fibres have dimension at most `d`, and
* `F` is a quasi-coherent `𝒪_X`-module of finite type.

Then `R ᵈ f_* F` is of finite type.

**There is no hypothesis on `Y`.** It is an arbitrary scheme — not affine, not locally
Noetherian — and `d` is arbitrary. This is the source's own statement.

The proof is the source's, in four steps. The question is local on `Y`, so `Y` may be taken affine
(`…AffineBase.isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase`, the
fibre bound transported to the restriction by [Stacks, Tag 02FY]). Over an affine base `f` is
replaced by a proper morphism of finite presentation, by the limit presentation of
[Stacks, Tag 09ZR] with the fibre bound preserved at a stage by [Stacks, Tag 05M5], the two higher
direct images agreeing because `X ⟶ X_i` is a closed immersion
(`…NoetherianApproximation.isFiniteType_rightDerived_of_finitePresentation_case`). Then `F` is
replaced by a module of finite presentation: it is a quotient of one by [Stacks, Tag 086M], and in
degree `d` the induced map is surjective because `R ᵈ ⁺ ¹ f_*` of the kernel vanishes
(`…NoetherianApproximation.isFiniteType_rightDerived_of_isFinitePresentation_case`, the vanishing
being `…TopDegreeBaseChange.cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le`). Finally
that situation is descended to an affine Noetherian base
(`…NoetherianModel.exists_noetherianModel`) and the top-degree base change of
[Stacks, Tag 0EX3] (b) identifies `H ᵈ (X, F)` with `H ᵈ (X₀, F₀) ⊗ Γ(Y, ⊤)`, which is finite
because `H ᵈ (X₀, F₀)` is, by [Stacks, Tag 02O6].

The quasi-coherence clause of the tag is
`…ProperQcoh.isQuasicoherent_rightDerived_of_isProper`; the two clauses are stated together, and
registered, in
`isQuasicoherent_isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le`. -/
theorem isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_baseChange' d
    (fun g₀ hg₀ hY₀ hY₀N hvan G₀ hG₀ hY₁ h g u hsq G e => by
      have := hg₀
      have := hY₀
      have := hY₀N
      have := hG₀
      have := hY₁
      exact moduleFinite_cohomology_of_isPullback_of_isQuasicoherent g₀ d hvan G₀
        (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G₀).1
        h g u hsq G e)
    f hdim F

/-- **[Stacks, Tag 0EX4].** For `f : X ⟶ Y` proper all of whose fibres have dimension at most
`d`, and `F` a quasi-coherent `𝒪_X`-module of finite type, the `𝒪_Y`-module `R ᵈ f_* F` is
quasi-coherent of finite type. The base is arbitrary.

The source prints the conclusion as an `𝒪_X`-module; `R ᵈ f_* F` is a sheaf on `Y`, and the
`𝒪_Y`-reading is the one the source's own proof uses.

Both clauses of the tag in one statement: quasi-coherence is
`…ProperQcoh.isQuasicoherent_rightDerived_of_isProper`, found by instance search because a proper
morphism is quasi-compact and quasi-separated, and finite type is
`isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le`. -/
@[stacks 0EX4 "both clauses at an ARBITRARY base, every d; the conclusion read as the 𝒪_Y-module \
R ᵈ f_* F, the source's 𝒪_X being a typo"]
theorem isQuasicoherent_isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsQuasicoherent ∧
      (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  ⟨inferInstance,
    isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le f d hdim F⟩


end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
