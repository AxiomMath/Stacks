module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareSndLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FactorComparisonCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisStalkDegeneracies
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekStalkMap

/-!
# The comparison out of the intersection is invertible on the stalk at a point of the open part

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` and let `F` be a sheaf of `𝒪_X`-modules.  The fifth and last stalk
degeneracy of the Mayer–Vietoris sequence is that the comparison

`j_{P!}(F|_P) ⟶ j_{V!}(F|_V)`

is invertible on the stalk at a geometric point of `U`.  It is *not* a formal consequence of the
compatibility of that comparison with the counits: with the counit from `U` invertible on stalks,
exactness in the middle is equivalent to invertibility of this comparison, and a geometric point
of `U` with two or more lifts along `j_V` admits maps compatible with the counits that are not
invertible.  So the comparison has to be identified, and it is:

* `CategoryTheory.Adjunction.factorLeftAdjointComparison_app` writes it as the canonical
  isomorphism of left adjoints followed by `j_{V!}` applied to the counit of the extension by
  zero along the second projection `P ⟶ V`, read through the composition comparison of
  restrictions;
* Equation 08GU turns the stalk of `j_{V!}` of a map into the direct sum of the stalks of that
  map at the lifts of the point to `V`;
* and each of those is invertible because a lift to `V` of a point of `U` lifts uniquely to `P`,
  which is `AlgebraicGeometry.Space.unique_geometricPointLift_edsSnd_of_mem`.

## Main results

* `AlgebraicGeometry.Space.isIso_edsModuleStalk_edsShriekEtaleComparison_of_mem`: **the
  comparison out of the intersection is invertible on the stalk at a geometric point of the open
  subspace.**

## Implementation notes

The auxiliary adjunction fed to
`CategoryTheory.Adjunction.factorLeftAdjointComparison_app` is the chosen one of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZero` along the second projection;
it is free in that lemma, so taking it canonical costs nothing and makes Tag 0798 applicable to
it.  The data `adjV` and `adjP` of the square itself stay arbitrary: the isomorphism of left
adjoints absorbs `adjP`, and `adjV` is moved to the canonical extension by zero by the naturality
of `CategoryTheory.Adjunction.leftAdjointUniq`.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The map on the étale algebraic space of the square whose extension by zero is the comparison
out of the intersection: the composition comparison of restrictions, extended by zero along the
second projection, followed by the counit of that extension by zero. -/
abbrev edsEtaleComparisonFactor (F : Modules.{u, u} B S hS W.1 W.2) :
    (etaleModuleLowerShriek B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).obj
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj F) ⟶
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj F :=
  (etaleModuleLowerShriek B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).map
      ((edsFactorIsoEtale B S hS hsq).inv.app F) ≫
    (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).counit.app
      ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj F)

/-- **At a lift to the étale algebraic space of a geometric point of the open subspace, the
counit of the extension by zero along the second projection is invertible on stalks**: that lift
lifts uniquely to the intersection. -/
theorem isIso_sheafFiber_edsSnd_counit_of_mem
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))
    (t : GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x) :
    IsIso ((liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
        ((etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).counit.app
          ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).obj F)))) := by
  have huniq : Unique (GeometricPointLift B S hS (edsSnd B S hS hsq).hom
      (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t)) :=
    unique_geometricPointLift_edsSnd_of_mem B S hS hsq
      (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t)
      (by rw [geometricPointMap_liftGeometricPoint]; exact hx)
  exact isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS (edsSnd B S hS hsq)
    (isEtale_edsSnd B S hS hsq) (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t)
    ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj F)
    (EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq) (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t) _)

/-- **At a lift to the étale algebraic space of a geometric point of the open subspace, the map
whose extension by zero is the comparison out of the intersection is invertible on stalks.** -/
theorem isIso_sheafFiber_edsSnd_factor_of_mem
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))
    (t : GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x) :
    IsIso ((liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
        ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
              (isEtale_edsSnd B S hS hsq)).map
            ((edsFactorIsoEtale B S hS hsq).inv.app F) ≫
          (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).counit.app
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
              (isEtale_edsEtaleHom B S hS hsq)).obj F)))) := by
  have h1 : IsIso ((liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
        ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).map
          ((edsFactorIsoEtale B S hS hsq).inv.app F)))) :=
    Iso.isIso_hom
      (((liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber
        (A := AddCommGrpCat.{u})).mapIso
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).mapIso
          ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).mapIso
            ((edsFactorIsoEtale B S hS hsq).app F).symm)))
  have h2 := isIso_sheafFiber_edsSnd_counit_of_mem B S hS hsq F x hx t
  have hsplit : (liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
          ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
                (isEtale_edsSnd B S hS hsq)).map
              ((edsFactorIsoEtale B S hS hsq).inv.app F) ≫
            (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
              (isEtale_edsSnd B S hS hsq)).counit.app
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).obj F))) =
      (liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
          ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
            ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
              (isEtale_edsSnd B S hS hsq)).map
              ((edsFactorIsoEtale B S hS hsq).inv.app F))) ≫
        (liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
          ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
            ((etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
              (isEtale_edsSnd B S hS hsq)).counit.app
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).obj F))) :=
    (congrArg ((liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber
        (A := AddCommGrpCat.{u})).map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map_comp _ _)).trans
      (((liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber
        (A := AddCommGrpCat.{u})).map_comp _ _)
  rw [hsplit]
  exact IsIso.comp_isIso
    (f := (liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
        ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).map
          ((edsFactorIsoEtale B S hS hsq).inv.app F))))
    (h := (liftSitePoint B S hS (edsEtaleHom B S hS hsq) t).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).map
        ((etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).counit.app
          ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).obj F))))

/-- **The extension by zero along the étale morphism of the square of the map of
`AlgebraicGeometry.Space.edsEtaleComparisonFactor` is invertible on the stalk at a geometric
point of the open subspace.** -/
theorem isIso_edsModuleStalk_edsEtale_shriek_factor_of_mem
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((edsModuleStalk B S hS x).map
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).map
        (edsEtaleComparisonFactor B S hS hsq F))) := by
  refine isIso_edsModuleStalk_of_isIso_sheafFiber B S hS _ x ?_
  exact isIso_sheafFiber_toSheaf_etaleModuleShriek_map_of_lifts B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) x
    (edsEtaleComparisonFactor B S hS hsq F)
    fun t => isIso_sheafFiber_edsSnd_factor_of_mem B S hS hsq F x hx t

section Comparison

variable
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))

/-- The same for an arbitrary extension by zero along the étale morphism of the square: the
canonical isomorphism of left adjoints moves the statement from the chosen one. -/
theorem isIso_edsModuleStalk_shriekV_factor_of_mem
    (adj : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((edsModuleStalk B S hS x).map
      (shriekV.map (edsEtaleComparisonFactor B S hS hsq F))) := by
  have hcan := isIso_edsModuleStalk_edsEtale_shriek_factor_of_mem B S hS hsq F x hx
  have hwR : IsIso ((edsModuleStalk B S hS x).map
      ((Adjunction.leftAdjointUniq adj
        (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq))).hom.app
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj F))) :=
    Iso.isIso_hom ((edsModuleStalk B S hS x).mapIso
      ((Adjunction.leftAdjointUniq adj
        (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq))).app
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj F)))
  have hwL : IsIso ((edsModuleStalk B S hS x).map
      ((Adjunction.leftAdjointUniq adj
        (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq))).hom.app
        ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).obj
          ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq)).obj F)))) :=
    Iso.isIso_hom ((edsModuleStalk B S hS x).mapIso
      ((Adjunction.leftAdjointUniq adj
        (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq))).app
        ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).obj
          ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq)).obj F))))
  have hnat := (Adjunction.leftAdjointUniq adj
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))).hom.naturality
    (edsEtaleComparisonFactor B S hS hsq F)
  have hnat' := (Functor.map_comp (edsModuleStalk B S hS x) _ _).symm.trans
    ((congrArg (edsModuleStalk B S hS x).map hnat).trans
      (Functor.map_comp (edsModuleStalk B S hS x) _ _))
  have hrhs : IsIso ((edsModuleStalk B S hS x).map
        ((Adjunction.leftAdjointUniq adj
          (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq))).hom.app
          ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).obj
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).obj F))) ≫
      (edsModuleStalk B S hS x).map
        ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).map
          (edsEtaleComparisonFactor B S hS hsq F))) :=
    IsIso.comp_isIso
      (f := (edsModuleStalk B S hS x).map
        ((Adjunction.leftAdjointUniq adj
          (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq))).hom.app
          ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).obj
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).obj F))))
      (h := (edsModuleStalk B S hS x).map
        ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).map
          (edsEtaleComparisonFactor B S hS hsq F)))
  exact IsIso.of_isIso_fac_right hnat'

/-- **The comparison out of the intersection of an elementary distinguished square is invertible
on the stalk at a geometric point of the open subspace.** -/
theorem isIso_edsModuleStalk_edsShriekEtaleComparison_of_mem
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((edsModuleStalk B S hS x).map
      ((edsShriekEtaleComparison B S hS hsq adjV adjP).app F)) := by
  have hfac := isIso_edsModuleStalk_shriekV_factor_of_mem B S hS hsq adjV F x hx
  have hA : (edsShriekEtaleComparison B S hS hsq adjV adjP).app F =
      (Adjunction.leftAdjointUniq adjP (Adjunction.factorComposed
          (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq))
          (edsFactorIsoEtale B S hS hsq) adjV
          (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)))).hom.app
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj F) ≫
      shriekV.map (edsEtaleComparisonFactor B S hS hsq F) :=
    Adjunction.factorLeftAdjointComparison_app
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
      (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq))
      (edsFactorIsoEtale B S hS hsq) adjP adjV
      (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)) F
  have hu : IsIso ((edsModuleStalk B S hS x).map
      ((Adjunction.leftAdjointUniq adjP (Adjunction.factorComposed
          (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq))
          (edsFactorIsoEtale B S hS hsq) adjV
          (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)))).hom.app
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj F))) :=
    Iso.isIso_hom ((edsModuleStalk B S hS x).mapIso
      ((Adjunction.leftAdjointUniq adjP (Adjunction.factorComposed
          (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq))
          (edsFactorIsoEtale B S hS hsq) adjV
          (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)))).app
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj F)))
  have hsplit := (congrArg (edsModuleStalk B S hS x).map hA).trans
    (Functor.map_comp (edsModuleStalk B S hS x) _ _)
  rw [hsplit]
  exact IsIso.comp_isIso
    (f := (edsModuleStalk B S hS x).map
      ((Adjunction.leftAdjointUniq adjP (Adjunction.factorComposed
          (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq))
          (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq))
          (edsFactorIsoEtale B S hS hsq) adjV
          (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)))).hom.app
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj F)))
    (h := (edsModuleStalk B S hS x).map
      (shriekV.map (edsEtaleComparisonFactor B S hS hsq F)))

end Comparison

end AlgebraicGeometry.Space

end
