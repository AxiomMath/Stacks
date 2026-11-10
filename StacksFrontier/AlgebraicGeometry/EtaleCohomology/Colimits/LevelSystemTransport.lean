module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelMathlibComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.SystemTransitionCalculus
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InverseImagesOfASingleSheaf

/-!
# Inverse images of one sheaf, transported to the levels of Stacks 0EYL

Let `d` be a cocone on an inverse system of schemes `D` and `𝓜` an abelian sheaf on Mathlib's small
étale site of its vertex. The inverse images `π_i⁻¹ 𝓜` along the legs carry transition maps in the
direct-image direction (`transitionFlat`), the transposes of the comparison of inverse images along
`π_i = (X_i ⟶ X_j) ≫ π_j`, with an identity and a composition law. Restricting them to the levels
of the site system of Stacks 0EYL along `levelMathlib` and reading the transitions through
`levelMathlibIso` gives a system of abelian sheaves on the levels (`levelSystem`), whose sheaf at a
level is the restriction of `π_i⁻¹ 𝓜`.

## Main definitions

* `Stacks.EtaleCohomology.TransitionBaseChange.transitionFlat` — the transitions of `π_i⁻¹ 𝓜`,
  in the direct-image direction, with `transitionFlat_id` and `transitionFlat_comp`.
* `Stacks.EtaleCohomology.TransitionBaseChange.levelSystem` — the system on the levels.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.TransitionBaseChange

universe v u

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Sites.InverseSystem
  InverseSystemOfFiniteSites

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX) (d : Cocone D)

/-- The transition morphism `X_i ⟶ X_j` of schemes attached to an arrow of the levels. -/
abbrev stageMor {i j : E.system.I} (a : i ⟶ j) : D.obj (stage E i) ⟶ D.obj (stage E j) :=
  D.map (E.indexEquiv.functor.map a)

/-- The leg of the cocone `d` at the stage of a level. -/
abbrev stageProj (i : E.system.I) : D.obj (stage E i) ⟶ d.pt := d.ι.app (stage E i)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The leg at a level factors as the transition to a later level followed by the leg there. -/
theorem stageProj_eq {i j : E.system.I} (a : i ⟶ j) :
    stageProj E d i = stageMor E a ≫ stageProj E d j :=
  (d.w _).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition morphism of an identity arrow is the identity. -/
theorem stageMor_id (i : E.system.I) : stageMor E (𝟙 i) = 𝟙 _ := by
  simp [stageMor]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition morphism of a composite arrow is the composite of the transition morphisms. -/
theorem stageMor_comp {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    stageMor E (a ≫ b) = stageMor E a ≫ stageMor E b := by
  simp [stageMor]

/-- The comparison `(X_i ⟶ X_j)_* ⋙ (π_j)_* ≅ (π_i)_*`. -/
def projPushComp {i j : E.system.I} (a : i ⟶ j) :
    smallEtalePushforwardAb (stageMor E a) ⋙ smallEtalePushforwardAb (stageProj E d j) ≅
      smallEtalePushforwardAb (stageProj E d i) :=
  smallEtalePushforwardAbCompIso' _ _ _ (stageProj_eq E d a)

/-- Direct image along the transition at an identity arrow is the identity. -/
def stagePushId (i : E.system.I) :
    𝟭 (Sheaf (smallEtaleTopology (D.obj (stage E i))) Ab.{max u v + 1}) ≅
      smallEtalePushforwardAb (stageMor E (𝟙 i)) :=
  (Functor.sheafPushforwardContinuousId Ab.{max u v + 1} _).symm ≪≫
    (Functor.sheafPushforwardContinuousIso
      (smallEtaleBaseChangeIdOf (stageMor E (𝟙 i)) (stageMor_id E i)) Ab.{max u v + 1} _ _).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The components of `stagePushId` are restrictions along the identification of the base change
along the identity transition with the identity. -/
theorem stagePushId_hom_app_hom_app (i : E.system.I)
    (M : Sheaf (smallEtaleTopology (D.obj (stage E i))) Ab.{max u v + 1})
    (W : ((D.obj (stage E i)).Etale)ᵒᵖ) :
    ((stagePushId E i).hom.app M).hom.app W =
      M.obj.map ((smallEtaleBaseChangeIdOf (stageMor E (𝟙 i)) (stageMor_id E i)).hom.app
        W.unop).op :=
  Category.id_comp _

/-- Direct image along a composite transition is the composite of the direct images. -/
def stagePushComp {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    smallEtalePushforwardAb (stageMor E a) ⋙ smallEtalePushforwardAb (stageMor E b) ≅
      smallEtalePushforwardAb (stageMor E (a ≫ b)) :=
  smallEtalePushforwardAbCompIso' _ _ _ (stageMor_comp E a b)

/-- **The transition maps of the inverse images `π_i⁻¹ 𝓜`, in the direct-image direction.** -/
def transitionFlat (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) {i j : E.system.I}
    (a : i ⟶ j) :
    (smallEtalePullbackAb (stageProj E d j)).obj 𝓜 ⟶
      (smallEtalePushforwardAb (stageMor E a)).obj
        ((smallEtalePullbackAb (stageProj E d i)).obj 𝓜) :=
  PushforwardCocone.transitionPushforward
    (P := fun {i j : E.system.I} (a : i ⟶ j) => smallEtalePushforwardAb (stageMor E a))
    (fun i => smallEtaleAdjunctionAb (stageProj E d i)) (fun a => projPushComp E d a) 𝓜 a

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- At an identity arrow, the inverse of `projPushComp` is the direct image of `stagePushId`. -/
theorem projPushComp_id_inv_app (i : E.system.I)
    (Z : Sheaf (smallEtaleTopology (D.obj (stage E i))) Ab.{max u v + 1}) :
    (projPushComp E d (𝟙 i)).inv.app Z =
      (smallEtalePushforwardAb (stageProj E d i)).map ((stagePushId E i).hom.app Z) := by
  apply Sheaf.hom_ext
  ext U : 2
  have hu := smallEtaleBaseChangeComp'_id_left_hom_app (stageMor E (𝟙 i)) (stageMor_id E i)
    (stageProj E d i) (stageProj_eq E d (𝟙 i)) U.unop
  change Z.obj.map ((smallEtaleBaseChangeComp' (stageMor E (𝟙 i)) (stageProj E d i)
    (stageProj E d i) (stageProj_eq E d (𝟙 i))).inv.app U.unop).op =
      𝟙 _ ≫ Z.obj.map ((smallEtaleBaseChangeIdOf (stageMor E (𝟙 i)) (stageMor_id E i)).hom.app
        ((smallEtaleBaseChange (stageProj E d i)).obj U.unop)).op
  rw [Category.id_comp, ← Iso.app_inv, ← Iso.app_hom, ← Iso.symm_inv]
  congr 3
  exact Iso.ext hu

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The inverse of `projPushComp` at a composite arrow is the composite of its inverses at the
factors, followed by the direct image of `stagePushComp`. -/
theorem projPushComp_comp_inv_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (Z : Sheaf (smallEtaleTopology (D.obj (stage E i))) Ab.{max u v + 1}) :
    (projPushComp E d (a ≫ b)).inv.app Z =
      (projPushComp E d a).inv.app Z ≫ (projPushComp E d b).inv.app _ ≫
        (smallEtalePushforwardAb (stageProj E d k)).map ((stagePushComp E a b).hom.app Z) := by
  have h := smallEtalePushforwardComp'_inv_app_cocycle (stageMor E a) (stageMor E b)
    (stageProj E d k) (stageMor E (a ≫ b)) (stageMor_comp E a b) (stageProj E d j)
    (stageProj_eq E d b) (stageProj E d i) ((stageProj_eq E d (a ≫ b)))
    (stageProj_eq E d a) Ab.{max u v + 1} Z
  change (projPushComp E d (a ≫ b)).inv.app Z ≫ (smallEtalePushforwardAb (stageProj E d k)).map
    ((stagePushComp E a b).inv.app Z) = (projPushComp E d a).inv.app Z ≫
      (projPushComp E d b).inv.app _ at h
  rw [← reassoc_of% h, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition of `transitionFlat` at an identity arrow is given by `stagePushId`. -/
theorem transitionFlat_id (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (i : E.system.I) :
    transitionFlat E d 𝓜 (𝟙 i) = (stagePushId E i).hom.app _ :=
  PushforwardCocone.transitionPushforward_id
    (P := fun {i j : E.system.I} (a : i ⟶ j) => smallEtalePushforwardAb (stageMor E a))
    (fun i => smallEtaleAdjunctionAb (stageProj E d i)) (fun i => stagePushId E i)
    (fun a => projPushComp E d a) (projPushComp_id_inv_app E d) 𝓜 i

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition of `transitionFlat` at a composite arrow is the composite of the transitions
at the factors, followed by `stagePushComp`. -/
theorem transitionFlat_comp (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    transitionFlat E d 𝓜 (a ≫ b) =
      transitionFlat E d 𝓜 b ≫ (smallEtalePushforwardAb (stageMor E b)).map
        (transitionFlat E d 𝓜 a) ≫ (stagePushComp E a b).hom.app _ :=
  PushforwardCocone.transitionPushforward_comp
    (P := fun {i j : E.system.I} (a : i ⟶ j) => smallEtalePushforwardAb (stageMor E a))
    (fun i => smallEtaleAdjunctionAb (stageProj E d i)) (fun a b => stagePushComp E a b)
    (fun a => projPushComp E d a) (fun a b Z => projPushComp_comp_inv_app E d a b Z) 𝓜 a b

/-! ### Restriction to the levels -/

section Levels

variable
  [hcont : ∀ i : E.system.I, (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]

attribute [local instance] isContinuous_transition

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- `levelMathlib` is continuous. -/
theorem isContinuous_levelMathlib (i : E.system.I) :
    (levelMathlib E i).IsContinuous (E.system.J i) (smallEtaleTopology (D.obj (stage E i))) :=
  have := AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite B (D.obj (stage E i))
    (hD (stage E i))
  Functor.isContinuous_comp _ _ _ (stageTopology E i) _

attribute [local instance] isContinuous_levelMathlib

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The composite of the transition functor of the levels with `levelMathlib` is continuous. -/
theorem isContinuous_transition_comp_levelMathlib {i j : E.system.I} (a : i ⟶ j) :
    (E.system.u a ⋙ levelMathlib E i).IsContinuous (E.system.J j)
      (smallEtaleTopology (D.obj (stage E i))) :=
  Functor.isContinuous_comp _ _ _ (E.system.J i) _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The composite of `levelMathlib` with base change along a transition morphism is continuous. -/
theorem isContinuous_levelMathlib_comp_baseChange {i j : E.system.I} (a : i ⟶ j) :
    (levelMathlib E j ⋙ smallEtaleBaseChange (stageMor E a)).IsContinuous (E.system.J j)
      (smallEtaleTopology (D.obj (stage E i))) :=
  Functor.isContinuous_comp _ _ _ (smallEtaleTopology (D.obj (stage E j))) _

attribute [local instance] isContinuous_transition_comp_levelMathlib
  isContinuous_levelMathlib_comp_baseChange

/-- Restriction of abelian sheaves from Mathlib's small étale site of `X_i` to the level `i`. -/
abbrev levelMathlibRestrict (i : E.system.I) :
    Sheaf (smallEtaleTopology (D.obj (stage E i))) Ab.{max u v + 1} ⥤
      Sheaf (E.system.J i) Ab.{max u v + 1} :=
  (levelMathlib E i).sheafPushforwardContinuous Ab.{max u v + 1} (E.system.J i)
    (smallEtaleTopology (D.obj (stage E i)))

/-- **Restriction to a level and direct image along a transition commute**: restriction along
`levelMathlibIso`. -/
def levelMathlibSquare {i j : E.system.I} (a : i ⟶ j) :
    levelMathlibRestrict E i ⋙
        abelianSheafPushforward.{v, v, max v (max u v + 1), max u v + 1} E.system a ≅
      smallEtalePushforwardAb (stageMor E a) ⋙ levelMathlibRestrict E j :=
  Functor.sheafPushforwardContinuousIso
    (levelMathlibIso E a (stageMor E a) (inclusion_map_stageMap E a)) Ab.{max u v + 1}
    (E.system.J j) (smallEtaleTopology (D.obj (stage E i)))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The components of the inverse of `levelMathlibSquare` are restrictions along
`levelMathlibIso`. -/
theorem levelMathlibSquare_inv_app_hom_app {i j : E.system.I} (a : i ⟶ j)
    (M : Sheaf (smallEtaleTopology (D.obj (stage E i))) Ab.{max u v + 1})
    (V : (E.system.C j)ᵒᵖ) :
    ((levelMathlibSquare E a).inv.app M).hom.app V =
      M.obj.map ((levelMathlibIso E a (stageMor E a) (inclusion_map_stageMap E a)).hom.app
        V.unop).op :=
  rfl

/-- The transitions of the system on the levels, in the direct-image direction. -/
def levelTransitionFlat (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) {i j : E.system.I}
    (a : i ⟶ j) :
    (levelMathlibRestrict E j).obj ((smallEtalePullbackAb (stageProj E d j)).obj 𝓜) ⟶
      (abelianSheafPushforward.{v, v, max v (max u v + 1), max u v + 1} E.system a).obj
        ((levelMathlibRestrict E i).obj ((smallEtalePullbackAb (stageProj E d i)).obj 𝓜)) :=
  (levelMathlibRestrict E j).map (transitionFlat E d 𝓜 a) ≫
    (levelMathlibSquare E a).inv.app _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition of `levelTransitionFlat` at an identity arrow is the identification of the
direct image along the identity with the identity. -/
theorem levelTransitionFlat_id (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (i : E.system.I) :
    levelTransitionFlat E d 𝓜 (𝟙 i) =
      (abelianSheafPushforwardIdIso.{v, v, max v (max u v + 1), max u v + 1} E.system i).hom.app
        _ := by
  apply Sheaf.hom_ext
  ext V : 2
  rw [Stacks.WeakSites.ColimitSiteCohomology.abelianSheafPushforwardIdIso_hom_app_hom_app]
  change ((transitionFlat E d 𝓜 (𝟙 i)).hom.app _ ≫ _) = _
  rw [transitionFlat_id, stagePushId_hom_app_hom_app, levelMathlibSquare_inv_app_hom_app]
  have key := congrArg (fun f => ((smallEtalePullbackAb (stageProj E d i)).obj 𝓜).obj.map f.op)
    (levelMathlibIso_id_hom_app E i (stageMor E (𝟙 i)) (inclusion_map_stageMap E (𝟙 i))
      (stageMor_id E i) V.unop)
  simp only [op_comp, Functor.map_comp] at key
  refine key.trans ?_
  change _ = ((smallEtalePullbackAb (stageProj E d i)).obj 𝓜).obj.map
    ((levelMathlib E i).op.map (eqToHom _))
  simp only [eqToHom_map, eqToHom_op]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The composition law of `levelMathlibSquare`.** -/
theorem levelMathlibSquare_comp_inv_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (M : Sheaf (smallEtaleTopology (D.obj (stage E i))) Ab.{max u v + 1}) :
    (levelMathlibRestrict E k).map ((stagePushComp E a b).hom.app M) ≫
        (levelMathlibSquare E (a ≫ b)).inv.app M =
      (levelMathlibSquare E b).inv.app ((smallEtalePushforwardAb (stageMor E a)).obj M) ≫
        (abelianSheafPushforward.{v, v, max v (max u v + 1), max u v + 1} E.system b).map
          ((levelMathlibSquare E a).inv.app M) ≫
          (abelianSheafPushforwardCompIso.{v, v, max v (max u v + 1), max u v + 1} E.system a
            b).hom.app ((levelMathlibRestrict E i).obj M) := by
  apply Sheaf.hom_ext
  ext V : 2
  induction V using Opposite.rec with | op V => ?_
  have key0 : (levelMathlibIso E (a ≫ b) (stageMor E (a ≫ b))
        (inclusion_map_stageMap E (a ≫ b))).hom.app V ≫
      (smallEtaleBaseChangeComp' (stageMor E a) (stageMor E b) (stageMor E (a ≫ b))
        (stageMor_comp E a b)).hom.app ((levelMathlib E k).obj V) =
      (levelMathlib E i).map (eqToHom (Functor.congr_obj (E.system.comp a b) V)) ≫
        (levelMathlibIso E a (stageMor E a) (inclusion_map_stageMap E a)).hom.app
          ((E.system.u b).obj V) ≫
        (smallEtaleBaseChange (stageMor E a)).map
          ((levelMathlibIso E b (stageMor E b) (inclusion_map_stageMap E b)).hom.app V) := by
    rw [levelMathlibIso_comp_hom_app E a b (stageMor E a) (inclusion_map_stageMap E a)
      (stageMor E b) (inclusion_map_stageMap E b) (stageMor E (a ≫ b))
      (inclusion_map_stageMap E (a ≫ b)) (stageMor_comp E a b) V]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (_ ≫ _ ≫ ·) (Category.comp_id _)
  change _ = _ ≫ _ ≫ ((abelianSheafPushforwardCompIso.{v, v, max v (max u v + 1), max u v + 1}
    E.system a b).hom.app _).hom.app (Opposite.op V)
  rw [Stacks.WeakSites.ColimitSiteCohomology.abelianSheafPushforwardCompIso_hom_app_hom_app]
  change M.obj.map ((smallEtaleBaseChangeComp' (stageMor E a) (stageMor E b) (stageMor E (a ≫ b))
      (stageMor_comp E a b)).hom.app ((levelMathlib E k).obj V)).op ≫
      M.obj.map ((levelMathlibIso E (a ≫ b) (stageMor E (a ≫ b))
        (inclusion_map_stageMap E (a ≫ b))).hom.app V).op =
    M.obj.map ((smallEtaleBaseChange (stageMor E a)).map
        ((levelMathlibIso E b (stageMor E b) (inclusion_map_stageMap E b)).hom.app V)).op ≫
      M.obj.map ((levelMathlibIso E a (stageMor E a) (inclusion_map_stageMap E a)).hom.app
        ((E.system.u b).obj V)).op ≫
      M.obj.map ((levelMathlib E i).op.map (eqToHom _))
  rw [← Functor.map_comp, ← op_comp, key0]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  congr 2
  simp only [eqToHom_map, eqToHom_op]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition of `levelTransitionFlat` at a composite arrow is the composite of the
transitions at the factors, followed by the comparison of direct images along a composite. -/
theorem levelTransitionFlat_comp (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    levelTransitionFlat E d 𝓜 (a ≫ b) =
      levelTransitionFlat E d 𝓜 b ≫
        (abelianSheafPushforward.{v, v, max v (max u v + 1), max u v + 1} E.system b).map
          (levelTransitionFlat E d 𝓜 a) ≫
          (abelianSheafPushforwardCompIso.{v, v, max v (max u v + 1), max u v + 1} E.system a
            b).hom.app _ := by
  have hnat := (levelMathlibSquare E b).inv.naturality (transitionFlat E d 𝓜 a)
  simp only [Functor.comp_map] at hnat
  simp only [levelTransitionFlat, transitionFlat_comp, Functor.map_comp, Category.assoc,
    levelMathlibSquare_comp_inv_app]
  rw [← reassoc_of% hnat]

/-- **The system of inverse images `π_i⁻¹ 𝓜` on the levels of Stacks 0EYL.** -/
def levelSystem (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) :
    AbelianSheafSystem.{v, v, max v (max u v + 1), max u v + 1} E.system :=
  Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps.{v, v, max v (max u v + 1),
      max u v + 1} E.system
    (fun i => (levelMathlibRestrict E i).obj ((smallEtalePullbackAb (stageProj E d i)).obj 𝓜))
    (fun a => levelTransitionFlat E d 𝓜 a) (fun i => levelTransitionFlat_id E d 𝓜 i)
    (fun a b => levelTransitionFlat_comp E d 𝓜 a b)

end Levels

end Stacks.EtaleCohomology.TransitionBaseChange

end
