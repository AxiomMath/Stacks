module

public import StacksFrontier.Homology.CompositeCollapseChosenResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.RestrictionOfChosenResolutions

/-!
# The source edge of the [Stacks, Tag 01E5] square, at the chosen injective resolutions

`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_chosenResolution` reads
[Stacks, Tag 01E5] at the two chosen injective resolutions: the chosen resolution of `M` on `X`
and the chosen resolution of its restriction to `f⁻¹(V)`, compared by
`Stacks.Cohomology.HigherDirectImage.restrictChosenResolutionComparison`. That statement is one
edge of a square whose other three sides are two Grothendieck collapses and a comparison between
the two *sources* of those collapses — between `R ᵖ (f_* ⋙ P')(M)` read on `X` and
`R ᵖ ((f ∣ V)_* ⋙ P)(M|)` read on `f⁻¹(V)`.

This file supplies that second comparison at the same two chosen resolutions and at the same
comparison between them, which is the only form in which it can be matched against
`higherDirectImageRestrictIso_chosenResolution` componentwise.

## The comparison is not a new construction

It is `Stacks.RightDerivedComp.objIso` — the collapse `R ᵖ (G ⋙ T)(M) ≅ R ᵖ T (G M)` for `G`
additive, left exact and injectives-preserving at a `G`-acyclic `M` — at

> `G :=` restriction of modules to `f⁻¹(V)`, `T :=` the direct image along the restricted
> morphism followed by an arbitrary additive `P`.

Restriction to an open is exact, so its higher right derived functors vanish at **every** module
by `CategoryTheory.Functor.isZero_rightDerived_of_exact` and the acyclicity hypothesis is free;
that is `isZero_rightDerived_moduleRestriction` below. What was missing was not the comparison
but its reading at the chosen resolutions **in the direction the comparison of resolutions
points**: `Stacks.RightDerivedComp.objIso_hom_eq` computes the collapse on a comparison running
*into* an injective resolution of `G M`, while
`CategoryTheory.InjectiveResolution.desc_mapOfPreservesInjectives_f_zero` — and hence
`restrictChosenResolutionComparison` — runs *out of* the chosen one. The mirror is
`Stacks.RightDerivedComp.objIso_inv_eq`, and this file is one application of it.

`P` is left arbitrary. Taking sections over an open is one choice of it, and so is a further
restriction of scalars; keeping it general is what lets the square be stated without committing
to either spelling of the sections functor.

## Main results

* `Stacks.Cohomology.HigherDirectImage.isZero_rightDerived_moduleRestriction`: the higher right
  derived functors of restriction to an open vanish at every sheaf of modules.
* `Stacks.Cohomology.HigherDirectImage.restrictCollapse_inv_eq`: **the source edge at the chosen
  resolutions.** The collapse `R ᵖ (restriction ⋙ (f ∣ V)_* ⋙ P)(M) ≅ R ᵖ ((f ∣ V)_* ⋙ P)(M|)`
  inverted is the computation of the right-hand side on the chosen resolution of `M|`, then the
  degree-`p` homology of `(f ∣ V)_* ⋙ P` applied to `restrictChosenResolutionComparison`, then
  the computation of the left-hand side on the chosen resolution of `M` inverted.

  **Nothing is assumed** of `f`, of `V`, of `M`, of `P` beyond additivity, or of `p`.

Its middle factor is the degree-`p` homology of `restrictChosenResolutionComparison` under
`(f ∣ V)_* ⋙ P`, and the middle factor of
`higherDirectImageRestrictIso_chosenResolution` is the degree-`p` homology of the same comparison
under `(f ∣ V)_*` alone: the two differ by the compatibility of `P` with homology, which is the
`CategoryTheory.ShortComplex.mapHomologyIso` factor that
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app` carries. That is what makes the
square checkable factor by factor.

## Implementation notes

*No `@[stacks …]` attribute is placed.* Nothing here is a statement of a tagged result: it is
Grothendieck's collapse at a particular pair, read on the resolutions [Stacks, Tag 01E5]'s own
clause is read on.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction (modulePushforward)

universe u

namespace Stacks.Cohomology.HigherDirectImage

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)
  (M : SheafOfModules.{u} (structureSheafRing X))

/-- **Restriction to an open has no higher right derived functors.** Restriction of sheaves of
modules to an open is exact, so `R ⁿ (-|_{f⁻¹V}) (M) = 0` for every `M` and every `n > 0`.

This is what makes the acyclicity hypothesis of `Stacks.RightDerivedComp.objIso` free at this
pair. **Nothing is assumed** of `f`, of `V`, of `M` or of `n`. -/
theorem isZero_rightDerived_moduleRestriction (n : ℕ) (hn : 0 < n) :
    IsZero (((moduleRestriction X (preimageOpen f V)).rightDerived n).obj M) :=
  CategoryTheory.Functor.isZero_rightDerived_of_exact _ M n hn

variable {W : Type*} [Category* W] [Abelian W]
  (P : SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V)) ⥤ W) [P.Additive]

/-- **The source edge of the [Stacks, Tag 01E5] square, read at the chosen injective
resolutions.** For a morphism of ringed spaces `f : X ⟶ Y`, an open `V ⊆ Y`, a sheaf of modules
`M` on `X`, an additive functor `P` out of the modules on `V` and a degree `p`, the collapse

> `R ᵖ ((-|_{f⁻¹V}) ⋙ (f ∣ V)_* ⋙ P)(M) ≅ R ᵖ ((f ∣ V)_* ⋙ P)(M|_{f⁻¹V})`

**inverted** is the computation of `R ᵖ ((f ∣ V)_* ⋙ P)` on the chosen injective resolution of
`M|_{f⁻¹V}`, then the degree-`p` homology of `(f ∣ V)_* ⋙ P` applied to
`Stacks.Cohomology.HigherDirectImage.restrictChosenResolutionComparison`, then the computation of
`R ᵖ ((-|_{f⁻¹V}) ⋙ (f ∣ V)_* ⋙ P)` on the chosen injective resolution of `M` inverted.

This is `Stacks.RightDerivedComp.objIso_inv_eq` at that pair, its acyclicity hypothesis supplied
by `isZero_rightDerived_moduleRestriction` and its augmentation clause by
`CategoryTheory.InjectiveResolution.desc_mapOfPreservesInjectives_f_zero`, which is what
`restrictChosenResolutionComparison` was built to make available.

**Nothing is assumed** of `f`, of `V`, of `M`, of `p`, or of `P` beyond additivity. -/
theorem restrictCollapse_inv_eq (p : ℕ) :
    (Stacks.RightDerivedComp.objIso (moduleRestriction X (preimageOpen f V))
        (injectiveResolution M) (isZero_rightDerived_moduleRestriction f V M)
        (modulePushforward (restrictedMorphism f V) ⋙ P) p).inv =
      ((injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M)).isoRightDerivedObj
          (modulePushforward (restrictedMorphism f V) ⋙ P) p).hom ≫
        HomologicalComplex.homologyMap
          (((modulePushforward (restrictedMorphism f V) ⋙ P).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (restrictChosenResolutionComparison f V M)) p ≫
          ((injectiveResolution M).isoRightDerivedObj
            (moduleRestriction X (preimageOpen f V) ⋙
              modulePushforward (restrictedMorphism f V) ⋙ P) p).inv :=
  Stacks.RightDerivedComp.objIso_inv_eq _ _ _ _ _ _ (restrictChosenResolutionComparison f V M)
    (InjectiveResolution.desc_mapOfPreservesInjectives_f_zero _ _ _)

end Stacks.Cohomology.HigherDirectImage

end
