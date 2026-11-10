module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkCommRingNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.EtaleLocalSolutionComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.TerminalGermTransport
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The coefficients of the two solution sets of step (3) of Stacks 04I6 agree

Step (3) of the proof of [Stacks Project, Tag 04I6] compares the solutions of the system `P`
presenting an affine étale chart `V` of an affine `Y` in the two étale local rings
`𝒪^{ét}_{Y,ȳ}` and `𝒪^{ét}_{X,x̄}`.  [Stacks Project, Tag 04GX], applied in
`AlgebraicGeometry.bijOn_etaleLocalSolutions_etaleLocalRingHom`, gives a bijection onto the
solutions over the coefficient map `φ ∘ γ_Y`; the set of lifts of `x̄` to `X ×_Y V`, computed by
`AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions`, is the solutions over
`γ_X ∘ f^♯`.  This file proves that those two coefficient maps are the same:

`φ ∘ γ_Y = γ_X ∘ φ_glob`.

That is clause (i) of the third identification which step (3) of the source owed.

## The argument

The homomorphism `φ = AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso` is built out of an
*arbitrary* isomorphism `e` of geometric stalk functors, of which no description on germs is
available, so the only possible argument is naturality.  It runs in three parts, and only the
first is about `e`.

* The germ calculus of `φ` is in
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/EtaleLocalRingFiber.lean`:
  `AlgebraicGeometry.etaleLocalRingEquivInverseImageFiber_toPresheafFiber` reduces `φ` on a germ
  to a single application of `e.hom.app`.
* `MorphismOfTopoi.germ_globalSections_of_sheafFiberIso` does the `e`-step, for an arbitrary
  morphism of topoi: the germ of a *global* section is a germ of a morphism out of the terminal
  sheaf, and `CategoryTheory.GrothendieckTopology.Point.eq_of_isTerminal` pins down the value of
  `e` there without any formula.
* `Stacks.Sheaves.StalkTransport.commRingFiber_map_ringStalkComparison` moves the ring-valued
  fibre of the structure map into the set-valued world where the previous step applies, and
  `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` identifies that map with
  the adjunct the previous step consumes.

The one genuinely missing statement was that the structure morphism of the terminal chart is the
identity, so that `AlgebraicGeometry.etaleCoefficientGerm` is simply the germ there; it is proved
below as `AlgebraicGeometry.SmallEtale.schemeStructureHom_final`.

## Main results

* `AlgebraicGeometry.SmallEtale.schemeStructureHom_final` and
  `AlgebraicGeometry.etaleCoefficientGerm_eq_etaleLocalRingGerm` — the terminal chart's structure
  morphism is the identity, so the coefficient germ is the germ at the terminal chart.
* `AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm` — **the
  coefficient compatibility**.

## What this does not do

Nothing here carries a `@[stacks 04I6]` tag.  Clause (ii) of the third identification — that the
fibre at `x̄` of `AlgebraicGeometry.comparisonSheafHom` is the solution-set map — is
`AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom`, and the tag
itself is `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.StalkInverseImage
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.StalkTransport

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (x : GeometricPoint X.obj) (y : GeometricPoint Y.obj)
  (e : (geometricPointSitePoint B Y.obj Y.property y).sheafFiber (A := Type u) ≅
    g.toToposHom.inverseImage ⋙
      (geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))

/-- **The structure morphism of the terminal chart of the small étale site is the identity.**  The
terminal chart is `S / S` with identity structure morphism by the very definition of
`AlgebraicGeometry.SmallEtale.final`, so this is functoriality of the inclusion of the big étale
site into schemes.

It is recorded because nothing in the tree said it:
`AlgebraicGeometry.SmallEtale.toScheme_map_from_final` is about the morphisms *to* the terminal
chart, not about its structure map, and the coefficient germ
`AlgebraicGeometry.etaleCoefficientGerm` is defined with that structure map in front. -/
theorem SmallEtale.schemeStructureHom_final (S : Scheme.{u}) (hS : B.Contains S) :
    schemeStructureHom B S hS (SmallEtale.final B S hS) = CategoryStruct.id S := by
  change B.inclusion.map (CategoryStruct.id (B.obj S hS)) = _
  exact B.inclusion.map_id (B.obj S hS)

/-- The structure morphism of the terminal chart induces the identity on global functions. -/
theorem SmallEtale.appTop_schemeStructureHom_final (S : Scheme.{u}) (hS : B.Contains S) :
    (schemeStructureHom B S hS (SmallEtale.final B S hS)).appTop.hom = RingHom.id _ := by
  rw [SmallEtale.schemeStructureHom_final, Scheme.Hom.id_appTop]
  rfl

/-- **The coefficient germ is the germ at the terminal chart.**
`AlgebraicGeometry.etaleCoefficientGerm` is by definition the germ at the terminal chart
precomposed with the ring map on global functions of that chart's structure morphism, and that
structure morphism is the identity
(`AlgebraicGeometry.SmallEtale.schemeStructureHom_final`). -/
theorem etaleCoefficientGerm_eq_etaleLocalRingGerm (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    etaleCoefficientGerm B S hS s =
      etaleLocalRingGerm B S hS s (SmallEtale.final B S hS)
        (SmallEtale.finalLift B S hS s) := by
  rw [etaleCoefficientGerm, SmallEtale.appTop_schemeStructureHom_final]
  exact RingHom.comp_id _

/-- `AlgebraicGeometry.etaleCoefficientGerm_eq_etaleLocalRingGerm` on an element, in the
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber` spelling that the germ lemmas of
`EtaleLocalRingFiber.lean` are stated in. -/
theorem etaleCoefficientGerm_apply (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) (t : Γ(S, ⊤)) :
    etaleCoefficientGerm B S hS s t =
      (((geometricPointSitePoint B S hS s).toPresheafFiber (SmallEtale.final B S hS)
        (SmallEtale.finalLift B S hS s) (SmallEtale.structureSheaf B S hS).obj)).hom t :=
  DFunLike.congr_fun (etaleCoefficientGerm_eq_etaleLocalRingGerm B S hS s) t

/-- **The coefficient compatibility of step (3) of Stacks 04I6, at an arbitrary pair of lifts of
the two geometric points to the terminal charts.**  The homomorphism `φ` of étale local rings
carries the germ at `(Y / Y, u)` of a global function `b` on `Y` to the germ at `(X / X, v)` of
`AlgebraicGeometry.RingedToposHom.globalSectionsMap g b`.

The lifts are left as variables because none of the argument uses that they are the chosen ones:
`MorphismOfTopoi.germ_globalSections_of_sheafFiberIso` holds at any pair of lifts, and keeping
them general is also what lets the rewrites see the fibre of the site point rather than
`AlgebraicGeometry.geometricPointFiber`. -/
theorem etaleLocalRingHomOfSheafFiberIso_toPresheafFiber_final
    (u : (geometricPointSitePoint B Y.obj Y.property y).fiber.obj
      (SmallEtale.final B Y.obj Y.property))
    (v : (geometricPointSitePoint B X.obj X.property x).fiber.obj
      (SmallEtale.final B X.obj X.property)) (b : Γ(Y.obj, ⊤)) :
    etaleLocalRingHomOfSheafFiberIso B g x y e
        ((((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber
          (SmallEtale.final B Y.obj Y.property) u
          (SmallEtale.structureSheaf B Y.obj Y.property).obj)).hom b) =
      (((geometricPointSitePoint B X.obj X.property x).toPresheafFiber
        (SmallEtale.final B X.obj X.property) v
        (SmallEtale.structureSheaf B X.obj X.property).obj)).hom
        ((g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
          (SmallEtale.finalIsTerminal B Y.obj Y.property)).hom b) := by
  change etaleCommRingFiberEquiv B X.obj X.property x
      ((((geometricPointSitePoint B X.obj X.property x).sheafFiber
        (A := CommRingCat.{u})).map g.fSharpInverseImage).hom
        (etaleLocalRingEquivInverseImageFiber B g x y e _)) = _
  rw [etaleLocalRingEquivInverseImageFiber_toPresheafFiber B g x y e
    (SmallEtale.final B Y.obj Y.property) u b]
  refine Eq.trans (congrArg (etaleCommRingFiberEquiv B X.obj X.property x)
    (commRingFiber_map_ringStalkComparison (geometricPointSitePoint B X.obj X.property x)
      g.fSharpInverseImage _)) ?_
  have hA : (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
        ((RingedSite.toRingedTopos
          (smallEtaleRingedSite B X.obj X.property)).forgetRing.map g.fSharpInverseImage))
        (e.hom.app ((RingedSite.toRingedTopos
            (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.obj
            (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O)
          (((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber
            (SmallEtale.final B Y.obj Y.property) u
            ((RingedSite.toRingedTopos
              (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.obj
              (RingedSite.toRingedTopos
                (smallEtaleRingedSite B Y.obj Y.property)).O).obj).hom b)) =
      (((geometricPointSitePoint B X.obj X.property x).toPresheafFiber
        (SmallEtale.final B X.obj X.property) v
        (CategoryTheory.Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).O)).obj)).hom
        ((g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
          (SmallEtale.finalIsTerminal B Y.obj Y.property)).hom b) := by
    simp only [RingedToposHom.fSharpInverseImage_forget_homEquiv]
    exact MorphismOfTopoi.germ_globalSections_of_sheafFiberIso g.toToposHom
      (geometricPointSitePoint B X.obj X.property x)
      (geometricPointSitePoint B Y.obj Y.property y) e
      (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property)
      ((RingedSite.toRingedTopos
        (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.map g.fSharp) u v b
  refine Eq.trans (congrArg (fun z => etaleCommRingFiberEquiv B X.obj X.property x
      ((Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
          (RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).O.obj).ringCatIsoToRingEquiv
        (ringStalkComparison (geometricPointSitePoint B X.obj X.property x)
          (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).O) z))) hA) ?_
  refine Eq.trans (congrArg (fun z => etaleCommRingFiberEquiv B X.obj X.property x
      ((Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
          (RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).O.obj).ringCatIsoToRingEquiv z))
    (ringStalkComparison_ringGerm (geometricPointSitePoint B X.obj X.property x)
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.toRingedTopos
        (smallEtaleRingedSite B X.obj X.property)).O)
      (SmallEtale.final B X.obj X.property) v
      ((g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
        (SmallEtale.finalIsTerminal B Y.obj Y.property)).hom b))) ?_
  refine Eq.trans (congrArg (etaleCommRingFiberEquiv B X.obj X.property x)
    (ConcreteCategory.congr_hom
      ((geometricPointSitePoint B X.obj X.property x).toPresheafFiber_presheafFiberCompIso_hom_app
        (F := forget₂ CommRingCat.{u} RingCat.{u}) (SmallEtale.final B X.obj X.property) v
        (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).O.obj)
      ((g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
        (SmallEtale.finalIsTerminal B Y.obj Y.property)).hom b))) ?_
  exact etaleCommRingFiberEquiv_toPresheafFiber B X.obj X.property x
    (SmallEtale.final B X.obj X.property) v
    ((g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property)).hom b)

/-- **The coefficient compatibility of step (3) of [Stacks Project, Tag 04I6].**  For a morphism
`(g, g^♯)` of the small étale ringed topoi of `X` and `Y`, a geometric point `x̄` of `X`, a
geometric point `ȳ` of `Y` and an identification `e` of the geometric stalk functor at `ȳ` with
`g⁻¹` followed by that at `x̄`,

`φ ∘ γ_Y = γ_X ∘ φ_glob`,

where `φ = AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso` is the homomorphism of étale local
rings, `γ` is `AlgebraicGeometry.etaleCoefficientGerm` on each side and `φ_glob` is the ring map
on global functions `AlgebraicGeometry.RingedToposHom.globalSectionsMap` of the source's first
paragraph.

This is clause (i) of the third identification which step (3) owed.  Taken with
`AlgebraicGeometry.bijOn_etaleLocalSolutions_etaleLocalRingHom` — [Stacks Project, Tag 04GX] for
the two étale local rings — it says that the target of that bijection *is* the set of lifts of
`x̄` to `X ×_Y V` which `AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions` computes,
whose coefficient map is `γ_X ∘ f^♯`.

Nothing here carries a `@[stacks 04I6]` tag: this is one clause of one step.  Clause (ii), that
the fibre of `AlgebraicGeometry.comparisonSheafHom` is the solution-set map, is
`AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom`. -/
theorem etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm :
    (etaleLocalRingHomOfSheafFiberIso B g x y e).comp
        (etaleCoefficientGerm B Y.obj Y.property y) =
      (etaleCoefficientGerm B X.obj X.property x).comp
        (g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
          (SmallEtale.finalIsTerminal B Y.obj Y.property)).hom := by
  refine RingHom.ext fun b => ?_
  refine Eq.trans (congrArg (etaleLocalRingHomOfSheafFiberIso B g x y e)
    (etaleCoefficientGerm_apply B Y.obj Y.property y b)) ?_
  refine Eq.trans (etaleLocalRingHomOfSheafFiberIso_toPresheafFiber_final B g x y e
    (SmallEtale.finalLift B Y.obj Y.property y) (SmallEtale.finalLift B X.obj X.property x) b) ?_
  exact (etaleCoefficientGerm_apply B X.obj X.property x _).symm

end AlgebraicGeometry

end
