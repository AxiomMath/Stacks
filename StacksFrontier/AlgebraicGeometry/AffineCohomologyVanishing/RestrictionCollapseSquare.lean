module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBaseComposition
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyGlueComplex
public import StacksFrontier.CategoryTheory.CompositeCancellation
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SourceEdgeChosenResolutions

/-!
# Grothendieck's collapse at the ambient pair against the one on the open subscheme

`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` is Grothendieck's comparison
`Rⁿ(G ∘ F) ≅ G ∘ RⁿF` with the homology-preservation hypothesis on `G` asked only pointwise, at
the short complexes of the images under `F` of the chosen injective resolutions. Conclusion (c) of
[Stacks, Tag 0EX3] crosses it at **two** pairs: at `(f_*, (-|_V) ⋙ P)` on the ambient space, and
at `((f ∣ V)_*, P)` after restriction to `f⁻¹V`, the `γ⁺` side reading the one and the `ψ` side
the other. This file proves the square between them.

The four sides are the two collapses, the **source edge**
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` of [Stacks, Tag 01E1] at the pair
`((-|_{f⁻¹V}), (f ∣ V)_* ⋙ P)`, and the **target edge** [Stacks, Tag 01E5]; the two paths are
glued by the derived transport `τ` at `P` along
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso` inverted, which is hoisted onto
a variable with its chosen-resolution reading as its defining hypothesis.

## Main results

* `…AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square`: **the square.** For a
  morphism of ringed spaces `f : X ⟶ Y`, an open `V ⊆ Y`, an index functor `E` into the modules on
  `X`, an additive `P` out of the modules on `V` and a degree `p`, the target edge followed by the
  ambient collapse and by `τ` is the restricted collapse followed by the source edge.

  **Nothing is asked beyond the two pointwise hypotheses `hamb` and `hres` that the two collapses
  carry**: the one further pointwise hypothesis the composition law for
  `CategoryTheory.ShortComplex.mapHomologyIso` needs, at the intermediate short complex
  `((f_*(I)).sc p).map (-|_V)`, is discharged inside the proof from `hamb` by
  `CategoryTheory.ShortComplex.preservesLeftHomologyOf_map`, restriction to an open being exact.
  **Nothing is assumed of `f`**, of `V`, of `E` or of `p`, and nothing of `P` beyond additivity —
  in particular no exactness, which is what makes the statement available where `P` is sections
  over an affine open.

## Implementation notes

*Where each side's chosen-resolution formula comes from.* Both collapses are read by
`…AffineBase.rightDerivedCompNatIso_hom_app`; the source edge by
`Stacks.Cohomology.HigherDirectImage.compRightDerivedNatIso_inv_app_chosenResolution`; the target
edge by `…HigherDirectImage.higherDirectImageRestrictIso_chosenResolution`. Those four are all the
mathematics in this file: after them the two paths differ by one cancellation of a conjugating
`isoRightDerivedObj` pair on each side, the four-fold splitting of `P` applied to the target edge,
and the identity `CategoryTheory.ShortComplex.mapHomologyIso_glue` — the composition law for
`mapHomologyIso` and its naturality composed.

*Why the proof is terms and not `rw`/`simp`.* The target edge writes the degree-`p` short complex
of the image of the chosen resolution under `f_*` **restricted to `V`** as
`((f_*[I]).sc p).map (-|_V)`, while the factor in front of it is the degree-`p` homology of
`((-|_{f⁻¹V}) ⋙ (f ∣ V)_*)[I]`; the two objects are definitionally equal and the goal carrying
both is not type-correct at `implicit` transparency, so `simp only [Functor.map_comp]` on it is
**refused with no progress**. Every step after the four rewrites is therefore a term
application, with the bookkeeping done at variables of an abstract category by
`CategoryTheory.comp_square_cancel` and `CategoryTheory.map_comp₄`, where it is syntactic.

*No `@[stacks …]` attribute is placed.* This is a compatibility of two instantiations of
Grothendieck's collapse, not a statement of a tagged result; [Stacks, Tag 01E5] and
[Stacks, Tag 01E1] carry their own where they are built.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction (modulePushforward)
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.Cohomology.AffineBase

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)
  {Dc : Type*} [Category* Dc] (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X))
  {W : Type*} [Category* W] [Abelian W]
  (P : SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V)) ⥤ W) [P.Additive]
  (p : ℕ)

/-- **Grothendieck's collapse at the ambient pair agrees with the one on the open subscheme,
across [Stacks, Tag 01E5] and [Stacks, Tag 01E1].** Writing `L = (-|_{f⁻¹V})`, `F = f_*`,
`F' = (f ∣ V)_*`, `R = (-|_V)` and `I` for the chosen injective resolution of `E Z`, the two paths
from `P((RᵖF')(L(E Z)))` to `(Rᵖ(L ⋙ F' ⋙ P))(E Z)` agree:

> [Stacks, Tag 01E5] under `P`, then the collapse at `(F, R ⋙ P)`, then the transport `τ`
> along `…HigherDirectImage.modulePushforwardRestrictIso` inverted,

and

> the collapse at `(F', P)` on the open subscheme, then [Stacks, Tag 01E1]'s source edge at
> `(L, F' ⋙ P)` inverted.

`τ` is hoisted onto a variable fixed by `hτ`, its reading on the chosen resolution of `E Z`; a
caller takes `τ` to be that composite, for which `hτ` is `rfl`.

**Nothing is assumed** of `f`, of `V`, of `E`, of `Z` or of `p`, and nothing of `P` beyond
additivity. The two collapses' own pointwise hypotheses `hamb` and `hres` are all that is asked:
the preservation of the left homology of `((F[I]).sc p).map R` by `P`, which the composition law
for `CategoryTheory.ShortComplex.mapHomologyIso` and its naturality need, follows from `hamb` by
`CategoryTheory.ShortComplex.preservesLeftHomologyOf_map`, restriction to an open being exact. -/
theorem rightDerivedCompNatIso_restrictChosenResolution_square
    (hamb : ∀ Z : Dc, (moduleRestriction Y V ⋙ P).PreservesLeftHomologyOf
      ((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (hres : ∀ Z : Dc, P.PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X (preimageOpen f V)).obj Z)).cocomplex).sc p))
    (τ : (modulePushforward f ⋙ moduleRestriction Y V ⋙ P).rightDerived p ⟶
      (moduleRestriction X (preimageOpen f V) ⋙
        modulePushforward (restrictedMorphism f V) ⋙ P).rightDerived p)
    (Z : Dc)
    [(moduleRestriction Y V ⋙ P).PreservesLeftHomologyOf
      ((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)]
    [P.PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X (preimageOpen f V)).obj Z)).cocomplex).sc p)]
    (hτ : τ.app (E.obj Z) =
      ((injectiveResolution (E.obj Z)).isoRightDerivedObj
          (modulePushforward f ⋙ moduleRestriction Y V ⋙ P) p).hom ≫
        (HomologicalComplex.homologyFunctor W (ComplexShape.up ℕ) p).map
          (((Functor.whiskerRight (modulePushforwardRestrictIso f V).inv P).mapHomologicalComplex
            (ComplexShape.up ℕ)).app (injectiveResolution (E.obj Z)).cocomplex) ≫
          ((injectiveResolution (E.obj Z)).isoRightDerivedObj
            (moduleRestriction X (preimageOpen f V) ⋙
              modulePushforward (restrictedMorphism f V) ⋙ P) p).inv) :
    P.map ((higherDirectImageRestrictIso f V p).hom.app (E.obj Z)) ≫
        (rightDerivedCompNatIso E (modulePushforward f) (moduleRestriction Y V ⋙ P) p
          hamb).hom.app Z ≫ τ.app (E.obj Z) =
      (rightDerivedCompNatIso (E ⋙ moduleRestriction X (preimageOpen f V))
          (modulePushforward (restrictedMorphism f V)) P p hres).hom.app Z ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
          (moduleRestriction X (preimageOpen f V))
          (modulePushforward (restrictedMorphism f V) ⋙ P) p).inv.app (E.obj Z) := by
  have := ShortComplex.preservesLeftHomologyOf_map
    ((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj Z)).cocomplex).sc p) (moduleRestriction Y V) P
  have core := ShortComplex.mapHomologyIso_glue_mapHomologicalComplex
    (moduleRestriction X (preimageOpen f V)) (modulePushforward (restrictedMorphism f V))
    (modulePushforward f) (moduleRestriction Y V) P (modulePushforwardRestrictIso f V)
    (ComplexShape.up ℕ) p (injectiveResolution (E.obj Z)).cocomplex
    (injectiveResolution ((moduleRestriction X (preimageOpen f V)).obj (E.obj Z))).cocomplex
    (restrictChosenResolutionComparison f V (E.obj Z))
  rw [hτ, rightDerivedCompNatIso_hom_app, rightDerivedCompNatIso_hom_app,
    compRightDerivedNatIso_inv_app_chosenResolution]
  exact comp_square_cancel _ (Iso.inv_hom_id _) (Iso.inv_hom_id _)
    ((P.map_comp _ _).symm.trans
      ((congrArg P.map (higherDirectImageRestrictIso_chosenResolution f V (E.obj Z) p)).trans
        (map_comp₄ P _ _ _ _))) core

end Stacks.Cohomology.AffineBase

end
