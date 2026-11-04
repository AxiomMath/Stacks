module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelColimitPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineLimitEtaleCohomology

/-!
# The hypotheses of the transport at the canonical site system of Stacks 0EYL

At the canonical site system `Stacks.EtaleCohomology.AffineLimitCohomology.sys` the hypotheses of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelLimitTransport.lean` hold: the levels
and the functors to the limit are continuous, restriction from Mathlib's small étale sites to the
levels and to the raised site of the limit are equivalences (every functor involved is the
inclusion of a dense subsite), and inverse image to the raised site of the limit is left exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.AffineLimitCohomology

universe v u

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Sites.InverseSystem
  InverseSystemOfFiniteSites Stacks.WeakSites.ExtColimit Stacks.WeakSites.ColimitSiteCohomology
  Stacks.EtaleCohomology.TransitionBaseChange

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- The functors from the levels to the raised site of the limit are continuous. -/
theorem isContinuous_levelToLimit (i : (sys D c B hD hX hc).I) :
    (levelToLimit (affineEtaleSiteColimit D c B hD hX hc) i).IsContinuous
      ((sys D c B hD hX hc).J i) (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck :=
  Stacks.WeakSites.ColimitMorphismOfSites.isContinuous_toColimitSite (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc) (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX) (mem_limitSitePrecoverage_iff D c B hD hX hc) i

/-- The functors from the levels to the raised site of the limit are morphisms of sites. -/
theorem isMorphismOfSites_levelToLimit (i : (sys D c B hD hX hc).I) :
    (levelToLimit (affineEtaleSiteColimit D c B hD hX hc) i).IsMorphismOfSites
      ((sys D c B hD hX hc).J i) (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck :=
  Stacks.WeakSites.ColimitMorphismOfSites.isMorphismOfSites_toColimitSite (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc) (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX) (mem_limitSitePrecoverage_iff D c B hD hX hc) i

attribute [local instance] isContinuous_levelEtale isContinuous_levelToLimit
  isContinuous_levelMathlib isDenseSubsite_levelFunctor
  Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion

/-- Restriction from Mathlib's small étale site of a stage to the level is an equivalence. -/
theorem isEquivalence_levelMathlibRestrict (i : (sys D c B hD hX hc).I) :
    (levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) i).IsEquivalence := by
  show ((AlgebraicGeometry.SmallEtale.toEtaleSite B (levelScheme D c B hD hX hc i)
      (hD (levelIndex D c B hD hX hc i))).sheafPushforwardContinuous Ab.{max u v + 1}
        (AlgebraicGeometry.SmallEtale.topology B _ _) (smallEtaleTopology _) ⋙
      (AlgebraicGeometry.SmallAffineEtale.inclusion B _ _).sheafPushforwardContinuous
        Ab.{max u v + 1} (AlgebraicGeometry.SmallAffineEtale.topology B _ _)
        (AlgebraicGeometry.SmallEtale.topology B _ _) ⋙
      restrictToLevel D c B hD hX hc i).IsEquivalence
  infer_instance

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The raise `AsSmall.down` is continuous. -/
theorem isContinuous_asSmallDown :
    (AsSmall.down : limitSiteRaised (c := c) (hX := hX) ⥤ _).IsContinuous
      (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) := by
  have : (AsSmall.down : limitSiteRaised (c := c) (hX := hX) ⥤ _).IsDenseSubsite
      (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) :=
    AsSmall.isDenseSubsite_down _
  infer_instance

attribute [local instance] isContinuous_asSmallDown

/-- The equivalence of abelian sheaf categories along the affine inclusion of Stacks 04HR. -/
def affineSheafEquiv :
    Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) Ab.{max u v + 1} ≌
      Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) Ab.{max u v + 1} :=
  @Functor.asEquivalence _ _ _ _ _
    (Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale_isEquivalence B c.pt hX)

/-- The raise followed by its inverse, read in Mathlib's small étale site, is the reading of the
small affine étale site. -/
def upLimitSmallMathlibIso :
    (AsSmall.up : _ ⥤ limitSiteRaised (c := c) (hX := hX)) ⋙ limitSmallMathlib (c := c) (hX := hX) ≅
      limitMathlib (c := c) (hX := hX) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

attribute [local instance] isContinuous_limitSmallMathlib

section LimitEquivalence

variable (hX : B.Contains c.pt)

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The raise `AsSmall.down` is the inclusion of a dense subsite. -/
theorem isDenseSubsite_down' :
    (AsSmall.down : limitSiteRaised (c := c) (hX := hX) ⥤ _).IsDenseSubsite
      (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) :=
  AsSmall.isDenseSubsite_down _

attribute [local instance] isDenseSubsite_down'

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Restriction along the raise `AsSmall.down` is an equivalence. -/
theorem isEquivalence_asSmallDown_restrict :
    ((AsSmall.down : limitSiteRaised (c := c) (hX := hX) ⥤ _).sheafPushforwardContinuous
        Ab.{max u v + 1} (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck
        (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX)).IsEquivalence := by
  have : ∀ X, HasLimitsOfShape (StructuredArrow X
      (AsSmall.down : limitSiteRaised (c := c) (hX := hX) ⥤ _).op) Ab.{max u v + 1} :=
    fun _ => inferInstance
  infer_instance

attribute [local instance]
  Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The reading of the small affine étale site of the limit in Mathlib's site is continuous. -/
theorem isContinuous_limitMathlib' :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX ⋙
      AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).IsContinuous
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) (smallEtaleTopology c.pt) :=
  have := AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite B c.pt hX
  Functor.isContinuous_comp _ _ _ (AlgebraicGeometry.SmallEtale.topology B c.pt hX) _

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The embedding of the bounded small étale site of the limit is continuous. -/
theorem isContinuous_toEtaleSite' :
    (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).IsContinuous
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (smallEtaleTopology c.pt) :=
  AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite B c.pt hX

attribute [local instance] isContinuous_limitMathlib' isContinuous_toEtaleSite'
  isContinuous_limitSmallMathlib

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Restriction from Mathlib's small étale site of the limit to the raised site is an
equivalence. -/
theorem isEquivalence_limitMathlibRestrict :
    (limitMathlibRestrict (c := c) (hX := hX)).IsEquivalence := by
  have := isEquivalence_asSmallDown_restrict D c B hX
  have : ((AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).sheafPushforwardContinuous
      Ab.{max u v + 1} (AlgebraicGeometry.SmallEtale.topology B _ _)
      (smallEtaleTopology _)).IsEquivalence :=
    (AlgebraicGeometry.SmallEtale.sheafEquiv B c.pt hX Ab.{max u v + 1}).symm.isEquivalence_functor
  have : ((AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX).sheafPushforwardContinuous
      Ab.{max u v + 1} (AlgebraicGeometry.SmallAffineEtale.topology B _ _)
      (AlgebraicGeometry.SmallEtale.topology B _ _)).IsEquivalence :=
    Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale_isEquivalence B c.pt hX
  let e₁ := Functor.sheafPushforwardContinuousComp
      (AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX)
      (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX) Ab.{max u v + 1}
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX)
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (smallEtaleTopology c.pt)
  let e₂ := Functor.sheafPushforwardContinuousComp
      (AsSmall.down : limitSiteRaised (c := c) (hX := hX) ⥤ _)
      (AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX) Ab.{max u v + 1}
      (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) (smallEtaleTopology c.pt)
  have : ((AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX ⋙
      AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).sheafPushforwardContinuous
      Ab.{max u v + 1} (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX)
      (smallEtaleTopology c.pt)).IsEquivalence := Functor.isEquivalence_of_iso e₁
  exact Functor.isEquivalence_of_iso e₂

end LimitEquivalence

end Stacks.EtaleCohomology.AffineLimitCohomology

end
