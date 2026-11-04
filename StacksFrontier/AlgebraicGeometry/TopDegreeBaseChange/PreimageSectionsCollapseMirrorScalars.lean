module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.DerivedSectionsModel
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBaseComposition
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.PreimageSectionsCollapseMirror

/-!
# The scalars factor of [Stacks, Tag 089W] is Grothendieck's comparison at the scalars pair

`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` reads
[Stacks, Tag 089W] inverted in the model of derived sections. Printed from that statement, its
**fourth** factor is the crossing of the two models of the classical right derived functor at the
pair `(g_* ⋙ Γ(S, ⊤, -), Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections g ⊤)`,
and its **fifth** is `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso`
inverted — restriction of scalars along `g^♯` pulled out of the right derived functor, built from
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the comparison
`Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop`.

The collapse mirror
`Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp_rightDerivedCompNatIso_inv`
(`PreimageSectionsCollapseMirror.lean`) moves that fourth factor — but it is stated with
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`, Grothendieck's comparison with the
homology-preservation hypothesis taken pointwise, in the `Γ(g⁻¹⊤, -)` spelling of the sections
functor. This file is the dictionary between the two spellings of that one isomorphism, and the
composition of the two factors it makes possible.

## That this is a dictionary and not a second construction

`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_eq_rightDerivedCompIso`
(`AffineCohomologyVanishing/AffineBaseComposition.lean`) already says that for an exact `G` the
pointwise-hypothesis comparison **is** `rightDerivedCompIso` at the identity comparison
`F ⋙ G ≅ F ⋙ G`, whiskered by `E`; restriction of scalars is exact, so it applies here. What it
does not do is cross from `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` at `g⁻¹⊤` to
`Stacks.Cohomology.AffineBase.moduleGlobalSections`, nor from the identity comparison to
`sectionsRestrictionIsoTop`. Both crossings are definitional, and all four of their halves are
`rfl`, each checked separately:

* `Stacks.Cohomology.AffineBase.asRingedSpaceHom g = g.toLRSHom.toShHom`;
* `moduleGlobalSections X = sectionsOverOpen X ((opensMap g).obj ⊤)`, the inverse image of `⊤`
  being `⊤`;
* `ModuleCat.restrictScalars g.appTop.hom = Stacks.EdgeCompat.preimageRestrictScalars g ⊤`, the
  ascription of the source ring that makes exactness synthesisable being invisible to `rfl`;
* `Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop g = Iso.refl _`, that comparison being
  `NatIso.ofComponents (fun _ => Iso.refl _)`.

So nothing is constructed here: the two isomorphisms are one, and the only content is that the
equation between them be available to a chase.

## Implementation notes

*Every crossing is made at the level of isomorphisms, never at a component, and that is what
keeps the file inside the heartbeat budget.* Two other arrangements fail:

* the dictionary stated as an equality of the two **isomorphisms** `(…).app Z = …` and proved by
  `Iso.ext` — `timeout at whnf`. The statement alone elaborates in about five seconds, so the
  crossing is affordable once; `Iso.ext` then unifies the two isomorphism **types** a second time,
  and the budget is already spent.
* the dictionary stated at the `hom` **component** and proved from
  `rightDerivedCompNatIso_hom_app_eq_rightDerivedCompIso` by one `congrArg` — `timeout at whnf`
  too, for the same reason: the statement pays the crossing and the `congrArg`'s result type pays
  it again, at a `whnf` on `.hom.app` of two large terms rather than on the isomorphisms.

What works is to pay the crossing **once**, between two isomorphisms, in
`rightDerivedCompIsoTop_app_eq_restrictScalarsRightDerivedIso` — where it is `rfl` in about a
second — and to reach the component by `congrArg Iso.inv` afterwards,
`rightDerivedCompNatIso_eq_rightDerivedCompIso` supplying the other half at the mirror's own
spelling, where there is no crossing at all. This is the ordering discipline this subtree records:
a definitional crossing is paid in the statement it is written into, so no proof step may be asked
to make it a second time.

## Main results

* `Stacks.EdgeCompat.rightDerivedCompIsoTop_app_eq_restrictScalarsRightDerivedIso`: **the one
  crossing.** `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the pair
  `(Γ(g⁻¹⊤, -), res_{g^♯})` and the identity comparison, evaluated at a module, **is**
  `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso g M n`.
* `Stacks.EdgeCompat.rightDerivedCompNatIsoTop_inv_app_eq_restrictScalarsRightDerivedIso`:
  **the dictionary**, in the direction [Stacks, Tag 089W] inverted carries it: the component of
  Grothendieck's comparison at that pair, inverted, is `restrictScalarsRightDerivedIso` inverted.
* `Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp`
  `_restrictScalarsRightDerivedIso_inv`: **the last two factors of [Stacks, Tag 089W] inverted,
  composed.** Factor (4) of `cohomologyIsoPushforward_inv_eq_lerayComparison` followed by its
  factor (5) is the degree-`n` cohomology of `Stacks.EdgeCompat.preimageSectionsModelComparison`
  at `(E Z)[0]`, then the edge morphism of restriction of scalars at `RΓ(g⁻¹⊤, (E Z)[0])`, then
  restriction of scalars applied to the crossing of the two models of `RΓ(g⁻¹⊤, -)` at `E Z` —
  the place the `γ⁺` side reads, with the scalars **outside** the right derived functor.

Nothing is assumed of `g`, of the degree or of the object, and in particular no affineness: the
affineness [Stacks, Tag 089W] carries sits in its other three factors, not in these two. The
mirror's pointwise homology-preservation hypothesis is discharged by `inferInstance` throughout,
restriction of scalars being exact, so it appears in none of the statements.

No `@[stacks …]` attribute is placed: [Stacks, Tag 089W] carries its own where it is proved, and
conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.AffineBase (rightDerivedCompNatIso moduleGlobalSections)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)

universe u

namespace Stacks.EdgeCompat

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (g : X ⟶ S) (n : ℕ)

/-- **The one crossing, made between two isomorphisms.** For a morphism of schemes `g : X ⟶ S`, a
module `M` upstairs and a degree `n`, `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at
the pair `(Γ(g⁻¹⊤, -), restriction of scalars along g^♯)` and the identity comparison
`F ⋙ G ≅ F ⋙ G`, evaluated at `M`, **is**
`Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso g M n`.

Both sides are the same application of `rightDerivedCompIso`: the four spellings between them —
`Stacks.Cohomology.AffineBase.asRingedSpaceHom g` against `g.toLRSHom.toShHom`,
`moduleGlobalSections` against `sectionsOverOpen` at `g⁻¹⊤ = ⊤`, `ModuleCat.restrictScalars
g.appTop.hom` against the ascribed `preimageRestrictScalars g ⊤`, and
`Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop g` against `Iso.refl` — are each `rfl`.

Nothing is assumed of `g`, of `M` or of `n`. -/
theorem rightDerivedCompIsoTop_app_eq_restrictScalarsRightDerivedIso
    (M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
        (sectionsOverOpen X.toSheafedSpace ((opensMap g.toLRSHom.toShHom).obj ⊤))
        (preimageRestrictScalars g.toLRSHom.toShHom ⊤)
        (sectionsOverOpen X.toSheafedSpace ((opensMap g.toLRSHom.toShHom).obj ⊤) ⋙
          preimageRestrictScalars g.toLRSHom.toShHom ⊤)
        (Iso.refl _) n).app M =
      Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso g M n := rfl

variable {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))

/-- **The dictionary, in the direction [Stacks, Tag 089W] inverted carries it.** The component at
`Z` of `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` at the pair
`(Γ(g⁻¹⊤, -), res_{g^♯})`, inverted, is
`Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso g (E.obj Z) n` inverted —
which is the fifth factor of
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison`.

It is `rightDerivedCompNatIso_eq_rightDerivedCompIso`, which needs restriction of
scalars to be exact and nothing else, followed by the one crossing above; no step crosses a
spelling twice, which is what the implementation notes record as deciding the shape.

Nothing is assumed of `g`, of `n`, of `E` or of `Z`. -/
theorem rightDerivedCompNatIsoTop_inv_app_eq_restrictScalarsRightDerivedIso
    (hpl : ∀ Z : Dc, (preimageRestrictScalars g.toLRSHom.toShHom ⊤).PreservesLeftHomologyOf
      ((((sectionsOverOpen X.toSheafedSpace
        ((opensMap g.toLRSHom.toShHom).obj ⊤)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (Z : Dc) :
    (rightDerivedCompNatIso E
        (sectionsOverOpen X.toSheafedSpace ((opensMap g.toLRSHom.toShHom).obj ⊤))
        (preimageRestrictScalars g.toLRSHom.toShHom ⊤) n hpl).inv.app Z =
      (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso g (E.obj Z) n).inv :=
  (congrArg
      (fun i : E ⋙ (sectionsOverOpen X.toSheafedSpace
            ((opensMap g.toLRSHom.toShHom).obj ⊤)).rightDerived n ⋙
            preimageRestrictScalars g.toLRSHom.toShHom ⊤ ≅
          E ⋙ (sectionsOverOpen X.toSheafedSpace ((opensMap g.toLRSHom.toShHom).obj ⊤) ⋙
            preimageRestrictScalars g.toLRSHom.toShHom ⊤).rightDerived n =>
        i.inv.app Z)
      (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_eq_rightDerivedCompIso E
        (sectionsOverOpen X.toSheafedSpace ((opensMap g.toLRSHom.toShHom).obj ⊤))
        (preimageRestrictScalars g.toLRSHom.toShHom ⊤) n hpl)).trans
    (congrArg Iso.inv (rightDerivedCompIsoTop_app_eq_restrictScalarsRightDerivedIso g n (E.obj Z)))

/-- **The last two factors of [Stacks, Tag 089W] inverted, composed.** Printed from
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison`, its fourth
factor is the crossing of the two models of `Rⁿ(Γ(S, ⊤, -) ∘ g_*)` and its fifth is
`Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso` inverted. Their composite is

> the degree-`n` cohomology of `Stacks.EdgeCompat.preimageSectionsModelComparison` at `(E Z)[0]`,
> then the edge morphism of restriction of scalars along `g^♯` at `RΓ(g⁻¹⊤, (E Z)[0])`, then
> restriction of scalars applied to the crossing of the two models of `RΓ(g⁻¹⊤, -)` at `E Z`,

which is where the `γ⁺` side reads the same place: the scalars are **outside** the right derived
functor, and the crossing left standing is the one on `X` alone — the one brick (i)'s
instantiation at an open subscheme moves.

This is the collapse mirror
`singleCompDerivedPreimageSectionsComp_hom_app_comp_rightDerivedCompNatIso_inv` with its
Grothendieck factor rewritten by the dictionary above. The mirror's pointwise
homology-preservation hypothesis is `fun _ => inferInstance`, restriction of scalars being exact,
so it does not appear here.

Nothing is assumed of `g`, of `n`, of `E` or of `Z`; in particular no affineness, the affineness
[Stacks, Tag 089W] carries sitting in its other three factors. -/
theorem singleCompDerivedPreimageSectionsComp_hom_app_comp_restrictScalarsRightDerivedIso_inv
    (Z : Dc) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (modulePushforward g.toLRSHom.toShHom ⋙ sectionsOverOpen S.toSheafedSpace ⊤)
            (derivedPreimageSections g.toLRSHom.toShHom ⊤)
            (derivedPreimageSectionsUnit g.toLRSHom.toShHom ⊤)
            (exists_quasiIso_isKInjective X.toSheafedSpace) n).hom.app (E.obj Z) ≫
        (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso g (E.obj Z) n).inv =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).map
          ((preimageSectionsModelComparison g.toLRSHom.toShHom ⊤).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj (E.obj Z))) ≫
        (derivedHomologyComparison (preimageRestrictScalars g.toLRSHom.toShHom ⊤)
              (preimageRestrictScalars g.toLRSHom.toShHom ⊤).mapDerivedCategory
              (preimageRestrictScalars g.toLRSHom.toShHom ⊤).mapDerivedCategoryFactorsh.inv
              (exists_quasiIso_isKInjective_preimageSectionsRing
                g.toLRSHom.toShHom ⊤) (n : ℤ)).app
            ((derivedSectionsOverOpen X.toSheafedSpace
                ((opensMap g.toLRSHom.toShHom).obj ⊤)).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj (E.obj Z))) ≫
          (preimageRestrictScalars g.toLRSHom.toShHom ⊤).map
            ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (sectionsOverOpen X.toSheafedSpace ((opensMap g.toLRSHom.toShHom).obj ⊤))
              (derivedSectionsOverOpen X.toSheafedSpace ((opensMap g.toLRSHom.toShHom).obj ⊤))
              (derivedSectionsOverOpenUnit X.toSheafedSpace
                ((opensMap g.toLRSHom.toShHom).obj ⊤))
              (exists_quasiIso_isKInjective X.toSheafedSpace) n).hom.app (E.obj Z)) :=
  (congrArg
      (fun z => (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (modulePushforward g.toLRSHom.toShHom ⋙ sectionsOverOpen S.toSheafedSpace ⊤)
          (derivedPreimageSections g.toLRSHom.toShHom ⊤)
          (derivedPreimageSectionsUnit g.toLRSHom.toShHom ⊤)
          (exists_quasiIso_isKInjective X.toSheafedSpace) n).hom.app (E.obj Z) ≫ z)
      (rightDerivedCompNatIsoTop_inv_app_eq_restrictScalarsRightDerivedIso g n E
        (fun _ => inferInstance) Z).symm).trans
    (singleCompDerivedPreimageSectionsComp_hom_app_comp_rightDerivedCompNatIso_inv
      g.toLRSHom.toShHom ⊤ E n (fun _ => inferInstance) Z)

end Stacks.EdgeCompat

end
