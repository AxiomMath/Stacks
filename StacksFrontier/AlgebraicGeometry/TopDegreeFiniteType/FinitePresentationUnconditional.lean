module

public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.FinitePresentationAffineBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.FinitePresentationNoetherianModel

/-!
# Tag 0EX5 over an arbitrary base, assembled

[Stacks, Tag 0EX5] asserts that `R ᵈ f_* F` is of finite presentation for `f` proper and of
finite presentation with all fibres of dimension at most `d` and `F` of finite presentation.
Its proof is the proof of [Stacks, Tag 0EX4] with the third paragraph skipped, and this file is
the last step of that proof: the reduction to an affine base
(`…isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase`) fed
with the affine case, which is the Noetherian model of
`…NoetherianModel.exists_noetherianModel` followed by top-degree base change.

## Main results

* `…TopDegreeFiniteType.isFinitePresentation_rightDerived_affineBase_of_baseChange`: the affine
  case of the tag, granted the two inputs named below.
* `…TopDegreeFiniteType.isFinitePresentation_rightDerived_of_baseChange`: the tag over an
  arbitrary base, granted the same two inputs.

## Implementation notes

**The two carried hypotheses, and why they are carried here.** `hvan` is [Stacks, Tag 0E7D] for
a general `d` — the vanishing of `R ʲ (g₀)_* G` above the fibre dimension — and `hbc` is the
top-degree base change along the model. Neither is a hypothesis of [Stacks, Tag 0EX5], so the
statement below carries no attribute: it is the shape of the assembly, isolated
so that the plumbing of the Noetherian model is checked independently of the two inputs.

What the assembly does is small and entirely about matching the model to the base-change
statement: `exists_noetherianModel` produces the cartesian square and an isomorphism
`G ≅ p^* G₀`, the base-change input is applied to the square, and the isomorphism is transported
through `R ᵈ g_*` by `CategoryTheory.ObjectProperty.prop_of_iso`.

## References

* [Stacks Project, Tag 0EX5](https://stacks.math.columbia.edu/tag/0EX5)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The affine case of [Stacks, Tag 0EX5], granted the vanishing above the fibre dimension and
top-degree base change along a Noetherian model.**

`hvan` is [Stacks, Tag 0E7D] for a general `d`: for a proper morphism onto an affine Noetherian
base all of whose fibres have dimension at most `d`, the higher direct images vanish above
degree `d`. `hbc` is the top-degree base change: finite presentation of `R ᵈ g_* (p^* G₀)` for a
cartesian square over such a stage.

No `@[stacks 0EX5]` attribute: `hvan` and `hbc` are hypotheses the tag does not carry, and
`IsAffine Y` is a hypothesis too. -/
theorem isFinitePresentation_rightDerived_affineBase_of_baseChange
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] (hfp : AlgebraicGeometry.FinitePresentation g)
    [IsAffine Y] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (g.fiber y) ≤ (d : WithBot ℕ∞))
    (G : X.Modules) [G.IsFinitePresentation]
    (hvan : ∀ (X₀ S₀ : Scheme.{u}) (g₀ : X₀ ⟶ S₀), IsProper g₀ → IsAffine S₀ →
      IsNoetherian S₀ → (∀ s : S₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ j : ℤ, (d : ℤ) < j → ∀ G' : X₀.Modules, G'.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus j).obj G'))
    (hbc : ∀ (X₀ S₀ X' Y' : Scheme.{u}) (g₀ : X₀ ⟶ S₀), IsProper g₀ → IsAffine S₀ →
      IsNoetherian S₀ → ∀ G₀ : X₀.Modules, G₀.IsFinitePresentation →
      (∀ j : ℤ, (d : ℤ) < j → ∀ G' : X₀.Modules, G'.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus j).obj G')) →
      ∀ (g' : X' ⟶ Y') (p : X' ⟶ X₀) (v : Y' ⟶ S₀), IsAffine Y' → IsPullback p g' g₀ v →
        (((Scheme.Modules.pushforward g').rightDerived d).obj
          ((Scheme.Modules.pullback p).obj G₀)).IsFinitePresentation) :
    (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFinitePresentation := by
  obtain ⟨X₀, S₀, g₀, hpr, -, haff₀, hnoeth₀, hdim₀, G₀, hG₀, v, p, hsq, ⟨eG⟩⟩ :=
    Stacks.AlgebraicGeometry.NoetherianModel.exists_noetherianModel g hfp d hdim G
  have hres := hbc X₀ S₀ X Y g₀ hpr haff₀ hnoeth₀ G₀ hG₀
    (hvan X₀ S₀ g₀ hpr haff₀ hnoeth₀ hdim₀) g p v inferInstance hsq
  exact (_root_.SheafOfModules.isFinitePresentation.{u, u, u} Y.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward g).rightDerived d).mapIso eG).symm hres

/-- **[Stacks, Tag 0EX5] over an arbitrary base, granted the same two inputs.** The reduction to
an affine base is
`…isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase`, which
`…forall_isFinitePresentation_rightDerived_iff_forall_isAffineBase` shows loses nothing;
the affine case is the statement above.

No `@[stacks 0EX5]` attribute: `hvan` and `hbc` are hypotheses the tag does not carry. Once
[Stacks, Tag 0E7D] is available at a general `d` and top-degree base change is proved, both
arguments are discharged and the attribute moves onto the resulting unconditional statement. -/
theorem isFinitePresentation_rightDerived_of_baseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (hfp : AlgebraicGeometry.FinitePresentation f)
    (d : ℕ) (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsFinitePresentation]
    (hvan : ∀ (X₀ S₀ : Scheme.{u}) (g₀ : X₀ ⟶ S₀), IsProper g₀ → IsAffine S₀ →
      IsNoetherian S₀ → (∀ s : S₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ j : ℤ, (d : ℤ) < j → ∀ G' : X₀.Modules, G'.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus j).obj G'))
    (hbc : ∀ (X₀ S₀ X' Y' : Scheme.{u}) (g₀ : X₀ ⟶ S₀), IsProper g₀ → IsAffine S₀ →
      IsNoetherian S₀ → ∀ G₀ : X₀.Modules, G₀.IsFinitePresentation →
      (∀ j : ℤ, (d : ℤ) < j → ∀ G' : X₀.Modules, G'.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus j).obj G')) →
      ∀ (g' : X' ⟶ Y') (p : X' ⟶ X₀) (v : Y' ⟶ S₀), IsAffine Y' → IsPullback p g' g₀ v →
        (((Scheme.Modules.pushforward g').rightDerived d).obj
          ((Scheme.Modules.pullback p).obj G₀)).IsFinitePresentation) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation := by
  refine isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase
    f hfp d hdim F fun X₀ Y₀ g hg hgfp hY₀ hgdim G hG => ?_
  have := hg
  have := hY₀
  have := hG
  exact isFinitePresentation_rightDerived_affineBase_of_baseChange g hgfp d hgdim G hvan hbc

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
