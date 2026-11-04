module

public import StacksFrontier.Algebra.Homology.Resolution.MapInjectiveResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationInDegreeZero

/-!
# [Stacks, Tag 01E5] read at the chosen injective resolutions on both sides

`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_injectiveResolution` computes
[Stacks, Tag 01E5] on an **arbitrary** triple: an injective resolution `I` of `M` on `X`, an
injective resolution `J` of its restriction to `f⁻¹(V)`, and a comparison `φ` of the second into
the image of the first descending the identity. That is the form the clause has to take, because
there is no canonical map between two unrelated resolutions.

A comparison between [Stacks, Tag 01E5] and a statement about `Stacks.Cohomology.AffineBase`
`.rightDerivedCompNatIso` has to be made at the resolutions **that comparison** is computed on,
and those are the *chosen* ones: `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app`
prints its component through `CategoryTheory.injectiveResolution (E.obj Z)`, which on the open
subscheme is the chosen resolution of the restricted module and on the ambient space the chosen
resolution of the module itself. This file supplies the triple at which the two meet: the two
chosen resolutions, and the comparison between them that
`CategoryTheory.InjectiveResolution.mapOfPreservesInjectives` makes available.

The ingredient that makes the comparison exist is that **restriction to an open preserves
injective objects**, `ExtensionByZeroModules.preservesInjectiveObjects_jStar`, which applies to
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` because the latter is
`ExtensionByZeroModules.jStar` at the structure sheaf. Restriction is also exact, so the image of
a resolution is a resolution, and `CategoryTheory.InjectiveResolution.desc` descends the chosen
one into it.

## Main results

* `…HigherDirectImage.restrictChosenResolutionComparison`: **the comparison of the two chosen
  resolutions.** The chosen injective resolution of `M|_{f⁻¹(V)}` descends into the restriction of
  the chosen injective resolution of `M`, along the identity of `M|_{f⁻¹(V)}`.
* `…HigherDirectImage.higherDirectImageRestrictIso_chosenResolution`: **[Stacks, Tag 01E5] at the
  chosen resolutions.** The comparison of [Stacks, Tag 01E5] in degree `p` at `M`, followed by the
  restriction to `V` of the computation of `Rᵖ f_* M` on the chosen resolution of `M`, is the
  computation of `Rᵖ (f ∣ V)_* (M|_{f⁻¹V})` on the chosen resolution of `M|_{f⁻¹V}`, then the
  degree-`p` homology of `(f ∣ V)_*` of the comparison of resolutions, then of the identification
  of the two composites of pushforwards, and then
  `CategoryTheory.ShortComplex.mapHomologyIso` for restriction to `V`.

  **Nothing is assumed** of `f`, of `V`, of `M` or of `p`.

The last factor is the one worth naming: `CategoryTheory.ShortComplex.mapHomologyIso` on the
degree-`p` short complex of the image under `f_*` of the chosen resolution of `M` is exactly the
middle factor of `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app` at the pair
`(f_*, Γ(V, -))`, so a square comparing Grothendieck's collapse at the ambient pair with the one
on the open subscheme meets [Stacks, Tag 01E5] here and nowhere else.

## Implementation notes

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 01E5] carries its own where the comparison is
built and where its injective-resolution clause is proved; this is that clause instantiated.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction (modulePushforward)

universe u

namespace Stacks.Cohomology.HigherDirectImage

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)
  (M : SheafOfModules.{u} (structureSheafRing X))

/-- **The comparison of the two chosen injective resolutions across restriction to an open.** The
chosen injective resolution of `M|_{f⁻¹(V)}` descends, along the identity of `M|_{f⁻¹(V)}`, into
the restriction to `f⁻¹(V)` of the chosen injective resolution of `M`.

The target is an injective resolution by
`CategoryTheory.InjectiveResolution.mapOfPreservesInjectives`: restriction to an open is exact and
preserves injective objects, the latter by
`ExtensionByZeroModules.preservesInjectiveObjects_jStar`. **Nothing is assumed** of `f`, of `V` or
of `M`. -/
def restrictChosenResolutionComparison :
    (injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M)).cocomplex ⟶
      ((moduleRestriction X (preimageOpen f V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution M).cocomplex :=
  InjectiveResolution.desc (𝟙 _)
    ((injectiveResolution M).mapOfPreservesInjectives
      (moduleRestriction X (preimageOpen f V)))
    (injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M))

/-- **[Stacks, Tag 01E5], compatibility with injective resolutions, at the chosen resolutions on
both sides.** For a morphism of ringed spaces `f : X ⟶ Y`, an open `V ⊆ Y`, a sheaf of modules `M`
on `X` and a degree `p`, the comparison of [Stacks, Tag 01E5] at `M` followed by the restriction to
`V` of the computation of `Rᵖ f_* M` on the chosen injective resolution of `M` is

> the computation of `Rᵖ (f ∣ V)_* (M|_{f⁻¹V})` on the chosen injective resolution of
> `M|_{f⁻¹V}`, then the degree-`p` homology of `(f ∣ V)_*` applied to
> `restrictChosenResolutionComparison`, then of
> `Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, and then
> `CategoryTheory.ShortComplex.mapHomologyIso` for restriction to `V` on the degree-`p` short
> complex of the image under `f_*` of the chosen resolution of `M`.

This is `higherDirectImageRestrictIso_injectiveResolution` at the two chosen resolutions, its
augmentation hypothesis discharged by
`CategoryTheory.InjectiveResolution.desc_mapOfPreservesInjectives_f_zero`. **Nothing is assumed**
of `f`, of `V`, of `M` or of `p`. -/
theorem higherDirectImageRestrictIso_chosenResolution (p : ℕ) :
    (higherDirectImageRestrictIso f V p).hom.app M ≫
        (moduleRestriction Y V).map
          ((injectiveResolution M).isoRightDerivedObj (modulePushforward f) p).hom =
      ((injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M)).isoRightDerivedObj
            (modulePushforward (restrictedMorphism f V)) p).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((modulePushforward (restrictedMorphism f V)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (restrictChosenResolutionComparison f V M)) ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((modulePushforwardRestrictIso f V).hom.mapHomologicalComplex
            (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex) ≫
        (((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex).sc p).mapHomologyIso (moduleRestriction Y V)).hom :=
  higherDirectImageRestrictIso_injectiveResolution f V p M (injectiveResolution M)
    (injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M))
    (restrictChosenResolutionComparison f V M)
    (InjectiveResolution.desc_mapOfPreservesInjectives_f_zero
      (moduleRestriction X (preimageOpen f V)) (injectiveResolution M)
      (injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M)))

end Stacks.Cohomology.HigherDirectImage

end
