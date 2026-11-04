module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
/-!
# Descent of a morphism of modules over one affine chart of a stage

[Stacks Project, Tag 01ZR] (2) is proved for a cofiltered diagram of *affine* schemes by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine'`, and the
general quasi-compact quasi-separated case is deduced from it by Zariski glueing.  This file
carries out the first step of that deduction: the restriction of the given morphism to the
preimage of one *affine open* `V` of the stage descends, because the diagram of preimages of `V`
is a cofiltered diagram of affine schemes with limit the preimage of `V` in `c.pt`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen`: for an affine open `V`
  of the stage `D.obj i`, the restriction of `φ` to the preimage of `V` in `c.pt` is, up to the
  canonical comparisons, pulled back from a morphism over the preimage of `V` at some stage over
  `i`.

## Implementation notes

The affine case is applied to the diagram `AlgebraicGeometry.EventualLimit.preimageDiagram D i V`
indexed by `CategoryTheory.Over i`, whose stages are affine by
`AlgebraicGeometry.EventualLimit.isAffine_preimageDiagram_obj` and whose limit cone is
`AlgebraicGeometry.EventualLimit.isLimitPreimageCone`.  Only affineness of the *stages* is used
here; the hypothesis that the transition morphisms of the diagram of preimages are affine —
`AlgebraicGeometry.EventualLimit.preimageDiagram_isAffineHom` — is not needed for this step.

Two bookkeeping points are inherited verbatim from
`StacksFrontier/AlgebraicGeometry/ModuleLimits/EventualMapEq.lean`.  The base object of `Over i`
is `Over.mk (𝟙 i)`, whose value under `preimageDiagram D i V` is `D.map (𝟙 i) ⁻¹ᵁ V` and not `V`
itself; the argument is run with that open throughout and only `Prop`-valued comparisons with `V`
are needed.  And `Stacks.Modules.restrictPullbackIso` is used in its
`AlgebraicGeometry.Scheme.Hom.resLE` form, which makes its restricted morphism literally
`(AlgebraicGeometry.EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i))`; that is what lets
the restriction of `φ` be fed to the affine case without any further transport.

The index category of the diagram of preimages is `Over i`, whose objects live in the universe
`max u v` for `[Category.{v} I]`; since the affine case requires an index category in the universe
of the schemes, this file is stated with `[Category.{u} I]`.  The unrestricted form is obtained,
as elsewhere in this directory, by passing to `CategoryTheory.Functor.FullImage`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **Stacks Project, Tag 01ZR (2) over one affine chart of the stage.**  Let `c` be a limit cone
on a cofiltered diagram `D` of schemes with affine transition morphisms, let `V` be an affine open
of the stage `D.obj i`, and let `φ` be a morphism between the pullbacks to `c.pt` of two finitely
presented modules `F`, `G` on `D.obj i`.  Then the restriction of `φ` to the preimage of `V` in
`c.pt` — transported to the preimage diagram by `Stacks.Modules.restrictPullbackIso` — is pulled
back from a morphism at some stage over `i`, compatibly with the canonical comparisons.

This is `exists_map_of_pullback_canonical_of_isAffine'` for the diagram of preimages of `V`, whose
stages are affine. -/
theorem exists_over_map_of_isAffineOpen (hc : IsLimit c) (i : I)
    {V : (D.obj i).Opens} (hV : IsAffineOpen V)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : Over i) (e : j ⟶ Over.mk (𝟙 i))
      (φj : (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i V).map e)).obj
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
          (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i V).map e)).obj
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G)),
      (Scheme.Modules.pullback ((EventualLimit.preimageCone D c i V).π.app j)).map φj ≫
          canHom ((EventualLimit.preimageCone D c i V).π.app j)
            ((EventualLimit.preimageDiagram D i V).map e)
            ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
            ((EventualLimit.preimageCone D c i V).w e)
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) =
        canHom ((EventualLimit.preimageCone D c i V).π.app j)
            ((EventualLimit.preimageDiagram D i V).map e)
            ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
            ((EventualLimit.preimageCone D c i V).w e)
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ≫
          ((Stacks.Modules.restrictPullbackIso (c.π.app i)
              (Scheme.Hom.preimage_mono (c.π.app i)
                (show V ≤ D.map (𝟙 i) ⁻¹ᵁ V by simp))).app F).inv ≫
            (Scheme.Modules.restrictFunctor (c.π.app i ⁻¹ᵁ V).ι).map φ ≫
            ((Stacks.Modules.restrictPullbackIso (c.π.app i)
              (Scheme.Hom.preimage_mono (c.π.app i)
                (show V ≤ D.map (𝟙 i) ⁻¹ᵁ V by simp))).app G).hom := by
  have haff : ∀ j : Over i, IsAffine ((EventualLimit.preimageDiagram D i V).obj j) :=
    EventualLimit.isAffine_preimageDiagram_obj D i hV
  have hdl : IsLimit (EventualLimit.preimageCone D c i V) :=
    EventualLimit.isLimitPreimageCone D c hc i V
  have hFfp : ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj
      F).IsFinitePresentation := isFinitePresentation_restrict _ F
  have hGfp : ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj
      G).IsFinitePresentation := isFinitePresentation_restrict _ G
  exact @exists_map_of_pullback_canonical_of_isAffine' (Over i) _ _
    (EventualLimit.preimageDiagram D i V) (EventualLimit.preimageCone D c i V) haff hdl
    (Over.mk (𝟙 i)) _ _ hFfp hGfp
    (((Stacks.Modules.restrictPullbackIso (c.π.app i)
          (Scheme.Hom.preimage_mono (c.π.app i)
            (show V ≤ D.map (𝟙 i) ⁻¹ᵁ V by simp))).app F).inv ≫
      (Scheme.Modules.restrictFunctor (c.π.app i ⁻¹ᵁ V).ι).map φ ≫
      ((Stacks.Modules.restrictPullbackIso (c.π.app i)
          (Scheme.Hom.preimage_mono (c.π.app i)
            (show V ≤ D.map (𝟙 i) ⁻¹ᵁ V by simp))).app G).hom)

end Stacks.AlgebraicGeometry.ModuleLimits

end
