module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelSystemTransport
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.Pretopology.AsSmallSite
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ColimitPresentationOfIsoLegs
public import StacksFrontier.Homology.Ext.MapExactFunctorTransport

/-!
# The limit of the levels of Stacks 0EYL read in Mathlib's small étale site

The colimit site of the site system of Stacks 0EYL is the small affine étale site of the limit
`Y = c.pt`, raised by `CategoryTheory.AsSmall`. Reading it in Mathlib's small étale site of `Y`
(`limitSmallMathlib`), restriction of abelian sheaves along it (`limitMathlibRestrict`) commutes
with the direct images to the levels (`limitMathlibSquare`), and the inverse images `π_i⁻¹ 𝓜` of a
sheaf on the vertex of a cocone carry legs to the restriction of `p⁻¹ 𝓜`, for `p : Y ⟶ d.pt` the
common composite (`levelLeg`), compatible with the transitions of `levelSystem`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.TransitionBaseChange

universe v u

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Sites.InverseSystem
  InverseSystemOfFiniteSites Stacks.WeakSites.ExtColimit

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX) (d : Cocone D)
  (p : c.pt ⟶ d.pt) (hp : ∀ i : E.system.I, p = coneProj E i ≫ stageProj E d i)

/-- **The transpose of the comparison of left adjoints along a composite** is the transpose of the
unit of the composite adjunction followed by the comparison of right adjoints. -/
theorem homEquiv_leftAdjointCompIso_hom_app {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) {L₂ : C₁ ⥤ C₂}
    {R₂ : C₂ ⥤ C₁} (adj₂ : L₂ ⊣ R₂) {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj : L ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) (X : C₀) :
    adj₂.homEquiv _ _ ((Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).hom.app X) =
      (adj₁.homEquiv _ _).symm (adj.unit.app X ≫ e.inv.app (L.obj X)) := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  refine (cancel_epi ((Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).inv.app X)).1 ?_
  rw [Iso.inv_hom_id_app]
  have h := leftAdjointCompIso_inv_homEquiv_symm adj₁ adj₂ adj e (adj₁.unit.app X)
    ((adj₁.homEquiv _ _).symm (adj.unit.app X ≫ e.inv.app (L.obj X)))
  have h2 : adj₁.unit.app X ≫ R₁.map ((adj₁.homEquiv _ _).symm
      (adj.unit.app X ≫ e.inv.app (L.obj X))) = adj.unit.app X ≫ e.inv.app (L.obj X) := by
    have := (adj₁.homEquiv X _).apply_symm_apply (adj.unit.app X ≫ e.inv.app (L.obj X))
    rw [Adjunction.homEquiv_unit] at this
    exact this
  simp only [Functor.id_obj] at h h2
  rw [Adjunction.homEquiv_symm_unit, CategoryTheory.Functor.map_id, reassoc_of% h2,
    Iso.inv_hom_id_app] at h
  simp only [Category.comp_id, Adjunction.homEquiv_symm_unit] at h
  exact h.symm.trans (congrArg (_ ≫ ·) (Category.id_comp _))

/-- The raised small affine étale site of the limit. -/
abbrev limitSiteRaised : Type (max u v + 1) :=
  AsSmall.{max u v + 1} (AlgebraicGeometry.SmallAffineEtale B c.pt hX)

/-- Its precoverage. -/
abbrev limitPrecoverageRaised : Precoverage (limitSiteRaised (c := c) (hX := hX)) :=
  (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX).comap AsSmall.down

/-- The functor from a level to the raised site of the limit. -/
abbrev levelToLimit (i : E.system.I) : E.system.C i ⥤ limitSiteRaised (c := c) (hX := hX) :=
  E.toLimit i ⋙ AsSmall.up

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- `levelToLimit` is compatible with the transition functors of the site system. -/
theorem levelToLimit_transition {i j : E.system.I} (a : i ⟶ j) :
    E.system.u a ⋙ levelToLimit E i = levelToLimit E j :=
  (Functor.assoc _ _ _).symm.trans (congrArg (· ⋙ AsSmall.up) (E.toLimit_transition a))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Abelian sheaves on the raised site of the limit admit sheafification. -/
theorem hasSheafify_limitSiteRaised :
    HasSheafify (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck
      AddCommGrpCat.{max u v + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v + 1, max u v + 1,
    max u v + 1} _


/-- The raised site of the limit read in Mathlib's small étale site. -/
abbrev limitSmallMathlib : limitSiteRaised (c := c) (hX := hX) ⥤ c.pt.Etale :=
  AsSmall.down ⋙ limitMathlib (c := c) (hX := hX)

/-- `limitSmallMathlib` is continuous for the étale topologies. -/
theorem isContinuous_limitSmallMathlib :
    (limitSmallMathlib (c := c) (hX := hX)).IsContinuous
      (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck (smallEtaleTopology c.pt) := by
  have := AsSmall.isDenseSubsite_down (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX)
  have := Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion
    B c.pt hX
  have := AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite B c.pt hX
  have : (limitMathlib (c := c) (hX := hX)).IsContinuous
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) (smallEtaleTopology c.pt) :=
    Functor.isContinuous_comp _ _ _ (AlgebraicGeometry.SmallEtale.topology B c.pt hX) _
  exact Functor.isContinuous_comp _ _ _
    (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX).toGrothendieck _

attribute [local instance] isContinuous_limitSmallMathlib

/-- `limitMathlibIso` for the raised site. -/
def limitSmallMathlibIso (i : E.system.I) :
    levelToLimit E i ⋙ limitSmallMathlib (c := c) (hX := hX) ≅
      levelMathlib E i ⋙ smallEtaleBaseChange (coneProj E i) :=
  limitMathlibIso E i

/-- The components of `limitSmallMathlibIso` are those of `limitMathlibIso`. -/
theorem limitSmallMathlibIso_hom_app (i : E.system.I) (Y : E.system.C i) :
    (limitSmallMathlibIso E i).hom.app Y = (limitMathlibIso E i).hom.app Y := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The cone condition at a level. -/
theorem coneProj_eq {i j : E.system.I} (a : i ⟶ j) :
    coneProj E j = coneProj E i ≫ stageMor E a :=
  (c.w (E.indexEquiv.functor.map a)).symm

/-- The legs `π_j⁻¹ 𝓜 ⟶ (c_j)_* p⁻¹ 𝓜`, in the direct-image direction. -/
def legFlat (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) (j : E.system.I) :
    (smallEtalePullbackAb (stageProj E d j)).obj 𝓜 ⟶
      (smallEtalePushforwardAb (coneProj E j)).obj ((smallEtalePullbackAb p).obj 𝓜) :=
  ((smallEtaleAdjunctionAb (stageProj E d j)).homEquiv _ _).symm
    ((smallEtaleAdjunctionAb p).unit.app 𝓜 ≫
      (smallEtalePushforwardAbCompIso' (coneProj E j) (stageProj E d j) p (hp j)).inv.app _)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transpose of `legFlat` is the unit of `p` followed by the comparison of direct images. -/
theorem homEquiv_legFlat (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (j : E.system.I) :
    (smallEtaleAdjunctionAb (stageProj E d j)).homEquiv _ _ (legFlat E d p hp 𝓜 j) =
      (smallEtaleAdjunctionAb p).unit.app 𝓜 ≫
        (smallEtalePushforwardAbCompIso' (coneProj E j) (stageProj E d j) p (hp j)).inv.app _ :=
  Equiv.apply_symm_apply _ _

/-- **The legs are compatible with the transitions.** -/
theorem legFlat_transition (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    {i j : E.system.I} (a : i ⟶ j) :
    legFlat E d p hp 𝓜 j =
      transitionFlat E d 𝓜 a ≫ (smallEtalePushforwardAb (stageMor E a)).map (legFlat E d p hp 𝓜 i) ≫
        (smallEtalePushforwardAbCompIso' (coneProj E i) (stageMor E a) (coneProj E j)
          (coneProj_eq E a)).hom.app _ := by
  apply ((smallEtaleAdjunctionAb (stageProj E d j)).homEquiv _ _).injective
  have hcoc := smallEtalePushforwardComp'_inv_app_cocycle (coneProj E i) (stageMor E a)
    (stageProj E d j) (coneProj E j) (coneProj_eq E a) (stageProj E d i) (stageProj_eq E d a) p
    (hp j) (hp i) Ab.{max u v + 1} ((smallEtalePullbackAb p).obj 𝓜)
  change (smallEtalePushforwardAbCompIso' _ _ _ (hp j)).inv.app _ ≫
      (smallEtalePushforwardAb (stageProj E d j)).map
        ((smallEtalePushforwardAbCompIso' _ _ _ (coneProj_eq E a)).inv.app _) =
    (smallEtalePushforwardAbCompIso' _ _ _ (hp i)).inv.app _ ≫
      (projPushComp E d a).inv.app _ at hcoc
  have hnat := (projPushComp E d a).inv.naturality (legFlat E d p hp 𝓜 i)
  have htr : (smallEtaleAdjunctionAb (stageProj E d j)).homEquiv _ _ (transitionFlat E d 𝓜 a) =
      (smallEtaleAdjunctionAb (stageProj E d i)).unit.app 𝓜 ≫
        (projPushComp E d a).inv.app ((smallEtalePullbackAb (stageProj E d i)).obj 𝓜) :=
    PushforwardCocone.homEquiv_transitionPushforward
      (P := fun {i j : E.system.I} (a : i ⟶ j) => smallEtalePushforwardAb (stageMor E a))
      (fun i => smallEtaleAdjunctionAb (stageProj E d i)) (fun a => projPushComp E d a) 𝓜 a
  rw [homEquiv_legFlat, Adjunction.homEquiv_naturality_right, htr]
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map] at hnat ⊢
  have hl : (smallEtaleAdjunctionAb (stageProj E d i)).unit.app 𝓜 ≫
      (smallEtalePushforwardAb (stageProj E d i)).map (legFlat E d p hp 𝓜 i) =
      (smallEtaleAdjunctionAb p).unit.app 𝓜 ≫
        (smallEtalePushforwardAbCompIso' (coneProj E i) (stageProj E d i) p (hp i)).inv.app _ := by
    rw [← homEquiv_legFlat, Adjunction.homEquiv_unit]
  rw [← reassoc_of% hnat]
  have step : (smallEtaleAdjunctionAb p).unit.app 𝓜 ≫
      (smallEtalePushforwardAbCompIso' (coneProj E j) (stageProj E d j) p (hp j)).inv.app _ =
      ((smallEtaleAdjunctionAb p).unit.app 𝓜 ≫
        (smallEtalePushforwardAbCompIso' (coneProj E i) (stageProj E d i) p (hp i)).inv.app _) ≫
        (projPushComp E d a).inv.app _ ≫ (smallEtalePushforwardAb (stageProj E d j)).map
          ((smallEtalePushforwardAbCompIso' (coneProj E i) (stageMor E a) (coneProj E j)
            (coneProj_eq E a)).hom.app _) := by
    rw [Category.assoc, ← reassoc_of% hcoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← hl] at step
  exact step.trans (Category.assoc _ _ _)

/-! ### Restriction to the raised site of the limit -/

section Restrict

variable [hcont : ∀ i : E.system.I,
    (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]
  [hcontL : ∀ i : E.system.I, (levelToLimit E i).IsContinuous (E.system.J i)
    (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck]

attribute [local instance] isContinuous_levelMathlib

omit hcont in
/-- The composite of `levelToLimit` and `limitSmallMathlib` is continuous. -/
theorem isContinuous_levelToLimit_comp (i : E.system.I) :
    (levelToLimit E i ⋙ limitSmallMathlib (c := c) (hX := hX)).IsContinuous (E.system.J i)
      (smallEtaleTopology c.pt) :=
  Functor.isContinuous_comp _ _ _ (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck _

omit hcontL in
/-- The composite of `levelMathlib` and base change along the cone projection is continuous. -/
theorem isContinuous_levelMathlib_comp_coneProj (i : E.system.I) :
    (levelMathlib E i ⋙ smallEtaleBaseChange (coneProj E i)).IsContinuous (E.system.J i)
      (smallEtaleTopology c.pt) :=
  Functor.isContinuous_comp _ _ _ (smallEtaleTopology (D.obj (stage E i))) _

attribute [local instance] isContinuous_levelToLimit_comp isContinuous_levelMathlib_comp_coneProj

/-- **Restriction of abelian sheaves from Mathlib's small étale site of the limit to the raised
small affine étale site.** -/
abbrev limitMathlibRestrict :
    Sheaf (smallEtaleTopology c.pt) Ab.{max u v + 1} ⥤
      Sheaf (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck Ab.{max u v + 1} :=
  (limitSmallMathlib (c := c) (hX := hX)).sheafPushforwardContinuous Ab.{max u v + 1}
    (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck (smallEtaleTopology c.pt)

/-- **Restriction to the limit and direct image to a level commute.** -/
def limitMathlibSquare (i : E.system.I) :
    limitMathlibRestrict (c := c) (hX := hX) ⋙
        colimitPushforward.{v, v, max u v + 1} E.system (levelToLimit E)
          (limitPrecoverageRaised (c := c) (hX := hX)) i ≅
      smallEtalePushforwardAb (coneProj E i) ⋙ levelMathlibRestrict E i :=
  Functor.sheafPushforwardContinuousIso (limitSmallMathlibIso E i) Ab.{max u v + 1}
    (E.system.J i) (smallEtaleTopology c.pt)

/-- The sections of the components of the inverse of `limitMathlibSquare`. -/
theorem limitMathlibSquare_inv_app_hom_app (i : E.system.I)
    (M : Sheaf (smallEtaleTopology c.pt) Ab.{max u v + 1}) (V : (E.system.C i)ᵒᵖ) :
    ((limitMathlibSquare E i).inv.app M).hom.app V =
      M.obj.map ((limitMathlibIso E i).hom.app V.unop).op :=
  rfl

/-- The legs of `levelSystem` to the restriction of `p⁻¹ 𝓜`, in the direct-image direction. -/
def levelLeg (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) (j : E.system.I) :
    (levelMathlibRestrict E j).obj ((smallEtalePullbackAb (stageProj E d j)).obj 𝓜) ⟶
      (colimitPushforward.{v, v, max u v + 1} E.system (levelToLimit E)
        (limitPrecoverageRaised (c := c) (hX := hX)) j).obj
          ((limitMathlibRestrict (c := c) (hX := hX)).obj ((smallEtalePullbackAb p).obj 𝓜)) :=
  (levelMathlibRestrict E j).map (legFlat E d p hp 𝓜 j) ≫ (limitMathlibSquare E j).inv.app _

/-- A rearrangement in an arbitrary category. -/
theorem rearrange₅ {𝒞 : Type*} [Category 𝒞] {P Q R S T U W Z : 𝒞} (t : P ⟶ Q) (l : Q ⟶ R)
    (c' : R ⟶ S) (m : S ⟶ T) (g : Q ⟶ U) (l' : U ⟶ W) (q : R ⟶ W) (n : W ⟶ Z)
    (e : Z ⟶ T) (hnat : g ≫ l' = l ≫ q) (hkey : c' ≫ m = q ≫ n ≫ e) :
    (t ≫ l ≫ c') ≫ m = (t ≫ g) ≫ (l' ≫ n) ≫ e := by
  simp only [Category.assoc, hkey, reassoc_of% hnat]

/-- The presheaf component of `levelLeg`. -/
theorem levelLeg_hom_app (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) (j : E.system.I)
    (V : E.system.C j) :
    (levelLeg E d p hp 𝓜 j).hom.app (Opposite.op V) =
      (legFlat E d p hp 𝓜 j).hom.app (Opposite.op ((levelMathlib E j).obj V)) ≫
        ((smallEtalePullbackAb p).obj 𝓜).obj.map ((limitMathlibIso E j).hom.app V).op :=
  rfl

omit hcontL in
/-- The presheaf component of `levelTransitionFlat`. -/
theorem levelTransitionFlat_hom_app (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    {i j : E.system.I} (a : i ⟶ j) (V : E.system.C j) :
    (levelTransitionFlat E d 𝓜 a).hom.app (Opposite.op V) =
      (transitionFlat E d 𝓜 a).hom.app (Opposite.op ((levelMathlib E j).obj V)) ≫
        ((smallEtalePullbackAb (stageProj E d i)).obj 𝓜).obj.map
          ((levelMathlibIso E a (stageMor E a) (inclusion_map_stageMap E a)).hom.app V).op :=
  rfl

/-- **The legs are compatible with the transitions of `levelSystem`**, on sections. -/
theorem levelLeg_transition_app (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    {i j : E.system.I} (a : i ⟶ j) (V : E.system.C j) :
    (levelLeg E d p hp 𝓜 j).hom.app (Opposite.op V) =
      (levelTransitionFlat E d 𝓜 a).hom.app (Opposite.op V) ≫
        (levelLeg E d p hp 𝓜 i).hom.app (Opposite.op ((E.system.u a).obj V)) ≫
          ((smallEtalePullbackAb p).obj 𝓜).obj.map
            ((limitMathlib (c := c) (hX := hX)).map
              (eqToHom (Functor.congr_obj (E.toLimit_transition a) V).symm)).op := by
  have key0 : (limitMathlibIso E j).hom.app V ≫
      (smallEtaleBaseChangeComp' (coneProj E i) (stageMor E a) (coneProj E j)
        (coneProj_eq E a)).hom.app ((levelMathlib E j).obj V) =
      (limitMathlib (c := c) (hX := hX)).map
          (eqToHom (Functor.congr_obj (E.toLimit_transition a) V).symm) ≫
        (limitMathlibIso E i).hom.app ((E.system.u a).obj V) ≫
          (smallEtaleBaseChange (coneProj E i)).map
            ((levelMathlibIso E a (stageMor E a) (inclusion_map_stageMap E a)).hom.app V) := by
    rw [limitMathlibIso_hom_app_transition E a (stageMor E a) (inclusion_map_stageMap E a)
      (coneProj_eq E a) V]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (_ ≫ _ ≫ ·) (Category.comp_id _)
  have hnat := (legFlat E d p hp 𝓜 i).hom.naturality
    ((levelMathlibIso E a (stageMor E a) (inclusion_map_stageMap E a)).hom.app V).op
  have hl := congrArg (fun f => f.hom.app (Opposite.op ((levelMathlib E j).obj V)))
    (legFlat_transition E d p hp 𝓜 a)
  have hkey := congrArg (fun f => ((smallEtalePullbackAb p).obj 𝓜).obj.map f.op) key0
  simp only [op_comp, Functor.map_comp] at hkey
  rw [levelLeg_hom_app, levelLeg_hom_app, levelTransitionFlat_hom_app]
  refine (congrArg (· ≫ ((smallEtalePullbackAb p).obj 𝓜).obj.map
    ((limitMathlibIso E j).hom.app V).op) hl).trans ?_
  exact rearrange₅ _ _ _ _ _ _ _ _ _ hnat hkey

/-- The legs of `levelSystem`, as a family of maps of presheaves. -/
abbrev levelLegFamily (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) (j : E.system.I) :
    ((levelSystem E d 𝓜).obj j).obj ⟶ (levelToLimit E j).op ⋙
      ((limitMathlibRestrict (c := c) (hX := hX)).obj ((smallEtalePullbackAb p).obj 𝓜)).obj :=
  (levelLeg E d p hp 𝓜 j).hom

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **The legs of `levelSystem` form a compatible family**, in the sense of Stacks 09YP. -/
theorem levelLeg_isCompatible (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) :
    IsCompatible.{v, v, max v (max u v + 1), max u v + 1} E.system (levelToLimit E)
      (levelToLimit_transition E) (levelSystem E d 𝓜)
      ((limitMathlibRestrict (c := c) (hX := hX)).obj ((smallEtalePullbackAb p).obj 𝓜)).obj
      (fun j => (levelLeg E d p hp 𝓜 j).hom) := by
  intro j k a
  have ht : transition.{v, v, max v (max u v + 1), max u v + 1} E.system (levelSystem E d 𝓜) a =
      (levelTransitionFlat E d 𝓜 a).hom :=
    transition_systemOfDirectImageMaps _ _ _ _ _ a
  rw [ht]
  ext V : 2
  induction V using Opposite.rec with | op V => ?_
  rw [levelLeg_transition_app E d p hp 𝓜 a V]
  congr 2
  simp only [eqToHom_map, eqToHom_op, eqToHom_app]
  exact eqToHom_map _ _

/-- The transpose of `levelLeg` to the raised site of the limit. -/
def legTranspose (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) (j : E.system.I) :
    (colimitPullback.{v, v, max u v + 1} E.system (levelToLimit E)
        (limitPrecoverageRaised (c := c) (hX := hX)) j).obj
        ((levelMathlibRestrict E j).obj ((smallEtalePullbackAb (stageProj E d j)).obj 𝓜)) ⟶
      (limitMathlibRestrict (c := c) (hX := hX)).obj ((smallEtalePullbackAb p).obj 𝓜) :=
  by
    let adj := colimitAdj.{v, v, max u v + 1} E.system (levelToLimit E)
      (limitPrecoverageRaised (c := c) (hX := hX)) j
    let f := levelLeg E d p hp 𝓜 j
    exact (adj.homEquiv _ _).symm f

/-- The transpose of `legTranspose` is `levelLeg`. -/
theorem homEquiv_legTranspose (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (j : E.system.I) :
    (colimitAdj.{v, v, max u v + 1} E.system (levelToLimit E)
      (limitPrecoverageRaised (c := c) (hX := hX)) j).homEquiv _ _ (legTranspose E d p hp 𝓜 j) =
      levelLeg E d p hp 𝓜 j :=
  Equiv.apply_symm_apply _ _

end Restrict

/-! ### The transposes are invertible -/

section Transposes

variable [hcont : ∀ i : E.system.I,
    (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]
  [hcontL : ∀ i : E.system.I, (levelToLimit E i).IsContinuous (E.system.J i)
    (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck]
  [hequiv : ∀ i : E.system.I, (levelMathlibRestrict E i).IsEquivalence]
  [hequivL : (limitMathlibRestrict (c := c) (hX := hX)).IsEquivalence]

attribute [local instance] isContinuous_levelMathlib isContinuous_transition

/-- A morphism whose image under a left adjoint, followed by the counit, is invertible up to
invertible factors, is invertible, when the right adjoints are equivalences. -/
theorem isIso_of_square_counit {𝒞₁ 𝒞₂ 𝒟₁ 𝒟₂ : Type*} {_ : Category 𝒞₁} {_ : Category 𝒞₂}
    {_ : Category 𝒟₁} {_ : Category 𝒟₂} {P : 𝒞₁ ⥤ 𝒞₂} {Q : 𝒟₁ ⥤ 𝒟₂} {L₁ : 𝒟₁ ⥤ 𝒞₁} {E₁ : 𝒞₁ ⥤ 𝒟₁}
    (adj₁ : L₁ ⊣ E₁) {L₂ : 𝒟₂ ⥤ 𝒞₂} {E₂ : 𝒞₂ ⥤ 𝒟₂} (adj₂ : L₂ ⊣ E₂) [E₁.IsEquivalence]
    [E₂.IsEquivalence] {G₁ : 𝒞₁} {G₂ : 𝒞₂} (b : P.obj G₁ ≅ G₂)
    (θ : Q ⋙ L₂ ≅ L₁ ⋙ P) {b' : Q.obj (E₁.obj G₁) ⟶ E₂.obj G₂}
    (h : θ.inv.app (E₁.obj G₁) ≫ L₂.map b' ≫ adj₂.counit.app G₂ =
      P.map (adj₁.counit.app G₁) ≫ b.hom) : IsIso b' := by
  have : IsIso (θ.inv.app (E₁.obj G₁) ≫ L₂.map b' ≫ adj₂.counit.app G₂) := by
    rw [h]
    infer_instance
  have : IsIso (L₂.map b' ≫ adj₂.counit.app G₂) :=
    IsIso.of_isIso_comp_left (θ.inv.app (E₁.obj G₁)) _
  have : IsIso (L₂.map b') := IsIso.of_isIso_comp_right _ (adj₂.counit.app G₂)
  have := adj₂.isEquivalence_left_of_isEquivalence_right
  exact isIso_of_reflects_iso b' L₂

/-- **A transported map is invertible** when it is the transpose of an invertible map read through
a square of right adjoints, the vertical right adjoints being equivalences. -/
theorem isIso_of_transpose_square {𝒞₁ 𝒞₂ 𝒟₁ 𝒟₂ : Type*} {_ : Category 𝒞₁} {_ : Category 𝒞₂}
    {_ : Category 𝒟₁} {_ : Category 𝒟₂} {P : 𝒞₁ ⥤ 𝒞₂} {P' : 𝒞₂ ⥤ 𝒞₁} (adjP : P ⊣ P')
    {Q : 𝒟₁ ⥤ 𝒟₂} {Q' : 𝒟₂ ⥤ 𝒟₁} (adjQ : Q ⊣ Q') {E₁ : 𝒞₁ ⥤ 𝒟₁} (hE₁ : E₁.IsEquivalence)
    {E₂ : 𝒞₂ ⥤ 𝒟₂} (hE₂ : E₂.IsEquivalence)
    (σ : E₂ ⋙ Q' ≅ P' ⋙ E₁) {G₁ : 𝒞₁} {G₂ : 𝒞₂} (b : P.obj G₁ ≅ G₂)
    (b' : Q.obj (E₁.obj G₁) ⟶ E₂.obj G₂)
    (hb' : adjQ.homEquiv _ _ b' = E₁.map (adjP.homEquiv _ _ b.hom) ≫ σ.inv.app G₂) :
    IsIso b' :=
  have := hE₁
  have := hE₂
  isIso_of_square_counit (Adjunction.ofIsRightAdjoint E₁) (Adjunction.ofIsRightAdjoint E₂) b
    (Stacks.Homology.squareIso adjP adjQ (Adjunction.ofIsRightAdjoint E₁)
      (Adjunction.ofIsRightAdjoint E₂) σ)
    (Stacks.Homology.squareIso_inv_app_comp_map_comp_counit adjP adjQ
      (Adjunction.ofIsRightAdjoint E₁) (Adjunction.ofIsRightAdjoint E₂) σ b.hom b' hb')

omit hcont hcontL hequiv in
/-- The transpose of `transitionFlat` is the comparison of inverse images. -/
theorem homEquiv_smallEtalePullbackAbCompIso'_hom_app
    (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) {i j : E.system.I} (a : i ⟶ j) :
    (smallEtaleAdjunctionAb (stageMor E a)).homEquiv _ _
        ((smallEtalePullbackAbCompIso' (stageMor E a) (stageProj E d j) (stageProj E d i)
          (stageProj_eq E d a)).hom.app 𝓜) =
      transitionFlat E d 𝓜 a :=
  homEquiv_leftAdjointCompIso_hom_app _ _ _ _ 𝓜

omit [Nonempty I] [IsDirected I (· ≤ ·)] hcont hcontL hequiv in
/-- The transpose of `legFlat` is the comparison of inverse images. -/
theorem homEquiv_smallEtalePullbackAbCompIso'_hom_app_leg
    (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) (j : E.system.I) :
    (smallEtaleAdjunctionAb (coneProj E j)).homEquiv _ _
        ((smallEtalePullbackAbCompIso' (coneProj E j) (stageProj E d j) p (hp j)).hom.app 𝓜) =
      legFlat E d p hp 𝓜 j :=
  homEquiv_leftAdjointCompIso_hom_app _ _ _ _ 𝓜

omit hcontL in
/-- **The transitions of `levelSystem` are isomorphisms.** -/
theorem isIso_levelSystem_map (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    {i j : E.system.I} (a : i ⟶ j) : IsIso ((levelSystem E d 𝓜).map a) :=
  isIso_of_transpose_square (smallEtaleAdjunctionAb (stageMor E a))
    (abelianSheafAdjunction E.system a) (hequiv j) (hequiv i) (levelMathlibSquare E a)
    ((smallEtalePullbackAbCompIso' (stageMor E a) (stageProj E d j) (stageProj E d i)
      (stageProj_eq E d a)).app 𝓜) ((levelSystem E d 𝓜).map a) (by
        rw [Iso.app_hom, homEquiv_smallEtalePullbackAbCompIso'_hom_app]
        exact Equiv.apply_symm_apply _ _)

omit hequiv in
/-- The transpose of `legTranspose`, written through the comparison of inverse images. -/
theorem homEquiv_legTranspose_eq (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (j : E.system.I) :
    (colimitAdj.{v, v, max u v + 1} E.system (levelToLimit E)
      (limitPrecoverageRaised (c := c) (hX := hX)) j).homEquiv _ _
        (legTranspose E d p hp 𝓜 j) = (levelMathlibRestrict E j).map
      ((smallEtaleAdjunctionAb (coneProj E j)).homEquiv _ _
        ((smallEtalePullbackAbCompIso' (coneProj E j) (stageProj E d j) p (hp j)).app 𝓜).hom) ≫
        (limitMathlibSquare E j).inv.app _ :=
  (homEquiv_legTranspose E d p hp 𝓜 j).trans (congrArg (fun z => (levelMathlibRestrict E j).map z ≫
    (limitMathlibSquare E j).inv.app _)
      (homEquiv_smallEtalePullbackAbCompIso'_hom_app_leg E d p hp 𝓜 j).symm)

/-- **The legs of `levelSystem`, transposed to the raised site of the limit, are isomorphisms.** -/
theorem isIso_legTranspose (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (j : E.system.I) : IsIso (legTranspose E d p hp 𝓜 j) := by
  let adjQ := colimitAdj.{v, v, max u v + 1} E.system (levelToLimit E)
      (limitPrecoverageRaised (c := c) (hX := hX)) j
  let σ := limitMathlibSquare E j
  let b := (smallEtalePullbackAbCompIso' (coneProj E j) (stageProj E d j) p (hp j)).app 𝓜
  let b' := legTranspose E d p hp 𝓜 j
  let h₁ := hequiv j
  let h₂ := hequivL
  let hb' := homEquiv_legTranspose_eq E d p hp 𝓜 j
  exact isIso_of_transpose_square (smallEtaleAdjunctionAb (coneProj E j)) adjQ h₁ h₂ σ b b' hb'

end Transposes

end Stacks.EtaleCohomology.TransitionBaseChange

end
