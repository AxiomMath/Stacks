module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelVanishing
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitSystemFirstVariable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian

/-!
# The `Ext` diagram of the levels, read in Mathlib's small étale sites

At the canonical site system of Stacks 0EYL, let `d` be a cocone on the system of schemes with
vertex `S`, `p : X ⟶ S` compatible with its legs, and `𝓝`, `𝓜` abelian sheaves on `S_étale`. The
inverse images `π_j⁻¹ 𝓝` restricted to the levels form a system presenting `p⁻¹ 𝓝` by invertible
legs, hence a first variable `𝒜(𝓝)` at every index
(`Stacks.EtaleCohomology.AffineLimitCohomology.levelFirstVariable`). This file

* proves the `Ext` colimit property for `𝒜(ℤ)` at a quasi-compact quasi-separated level
  (`Stacks.EtaleCohomology.AffineLimitCohomology.nonempty_isColimit_levelFirstVariable`), from the
  Mayer–Vietoris theorem `mvColimit_levelConstant` through `nonempty_isColimit_of_topIso`;
* identifies the groups `Ext^n(𝒜(𝓝)_A, 𝒜(𝓜)_A)` of the `Ext` diagram with the groups
  `Ext^n(π_A⁻¹ 𝓝, π_A⁻¹ 𝓜)` of Mathlib's small étale site of the level, through the inverse of
  the restriction equivalence (`Stacks.EtaleCohomology.AffineLimitCohomology.levelExtCompare`),
  and shows that the transitions become the canonical restriction maps: `Ext` along the inverse
  image of schemes followed by the composition comparisons of inverse images
  (`Stacks.EtaleCohomology.AffineLimitCohomology.levelExtCompare_extTransition`), and likewise
  for the legs (`Stacks.EtaleCohomology.AffineLimitCohomology.levelExtCompare_extLeg`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.EtaleCohomology.AffineLimitCohomology

universe v u

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Sites.InverseSystem
  InverseSystemOfFiniteSites Stacks.WeakSites.ExtColimit Stacks.WeakSites.ColimitSiteCohomology
  Stacks.EtaleCohomology.TransitionBaseChange Stacks.Homology

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  (d : Cocone D) (p : c.pt ⟶ d.pt)
  (hp : ∀ i : (sys D c B hD hX hc).I,
    p = coneProj (affineEtaleSiteColimit D c B hD hX hc) i ≫
      stageProj (affineEtaleSiteColimit D c B hD hX hc) d i)

attribute [local instance] isContinuous_levelEtale isContinuous_levelToLimit
  isContinuous_levelMathlib
  enoughInjectives_level hasExt_level hasExt_limitSite enoughInjectives_limitSite
  Stacks.EtaleCohomology.LimitSiteBridge.toLimitSmall_isContinuous
  preservesFiniteLimits_colimitPullback_sys
  isEquivalence_levelMathlibRestrict isContinuous_limitSmallMathlib
  isContinuous_limitSmallMathlib_site

/-! ### The first variable of the inverse images of one sheaf -/

/-- The legs of the inverse images of `𝓝`, at the spelling of the canonical system. -/
def levelLegSite (𝓝 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (j : (sys D c B hD hX hc).I) :
    ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝).obj j).obj ⟶
      (toLimitSmall D c B hD hX hc j).op ⋙
        ((limitRestrict D c B hX).obj ((smallEtalePullbackAb p).obj 𝓝)).obj :=
  (levelLeg (affineEtaleSiteColimit D c B hD hX hc) d p hp 𝓝 j).hom

include hp in
/-- The legs `levelLegSite` are compatible with the transitions of the system of levels. -/
theorem levelLeg_isCompatible_site (𝓝 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) :
    IsCompatible.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝)
      ((limitRestrict D c B hX).obj ((smallEtalePullbackAb p).obj 𝓝)).obj
      (levelLegSite D c B hD hX hc d p hp 𝓝) :=
  @levelLeg_isCompatible _ _ _ _ _ _ _ _ _ (affineEtaleSiteColimit D c B hD hX hc) d p hp _ _ 𝓝

/-- The system leg at level `j` built from `levelLegSite` is an isomorphism. -/
theorem isIso_systemLeg_levelLeg_site (𝓝 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (j : (sys D c B hD hX hc).I) :
    IsIso (systemLeg.{v, v, max u v + 1} (D := sys D c B hD hX hc)
      (uC := toLimitSmall D c B hD hX hc)
      (K := limitSitePrecoverage D c B hX)
      (F := levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝)
      (𝒢 := (limitRestrict D c B hX).obj ((smallEtalePullbackAb p).obj 𝓝))
      (levelLegSite D c B hD hX hc d p hp 𝓝) j) :=
  isIso_legTranspose (hequivL := isEquivalence_limitMathlibRestrict D c B hX)
    (affineEtaleSiteColimit D c B hD hX hc) d p hp 𝓝 j

/-- **The first variable `𝒜(𝓝)`**: the inverse images `π_A⁻¹ 𝓝`, restricted to the levels below
`i₀`, with the restriction of `p⁻¹ 𝓝` on the site of the limit. -/
def levelFirstVariable (𝓝 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})
    (i₀ : (sys D c B hD hX hc).I) :
    FirstVariable.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) i₀ :=
  by
    have hP : ∀ {j k : (sys D c B hD hX hc).I} (a : j ⟶ k),
        IsIso ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝).map a) := fun a =>
      isIso_levelSystem_map (hequivL := isEquivalence_limitMathlibRestrict D c B hX)
        (affineEtaleSiteColimit D c B hD hX hc) d 𝓝 a
    have hκ := @levelLeg_isCompatible_site _ _ _ _ D c B hD hX hc _ d p hp 𝓝
    have hκiso := isIso_systemLeg_levelLeg_site D c B hD hX hc d p hp 𝓝
    exact systemFirstVariable.{v, v, max u v + 1} hP _ _ hκ hκiso i₀

include hp in
/-- The inverse images `π_j⁻¹ 𝓜` restricted to the levels, with the legs `levelLegSite`, form a
colimit presentation of the restriction of `p⁻¹ 𝓜` to the site of the limit. -/
theorem isColimitPresentation_levelLegSite (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) :
    IsColimitPresentation.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (limitSitePrecoverage D c B hX) (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜)
      ((limitRestrict D c B hX).obj ((smallEtalePullbackAb p).obj 𝓜))
      (levelLegSite D c B hD hX hc d p hp 𝓜) :=
  isColimitPresentation_levelLeg_site D c B hD hX hc d p hp 𝓜

/-- The constant sheaf `ℤ` of the small étale site of a scheme. -/
abbrev constZ (Y : Scheme.{max u v}) : Sheaf (smallEtaleTopology Y) Ab.{max u v + 1} :=
  (constantSheaf (smallEtaleTopology Y) Ab.{max u v + 1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- **The `Ext` colimit for the first variable `𝒜(ℤ)` at a quasi-compact quasi-separated level**,
at the colimit presentation of `p⁻¹ 𝓜` by the transported levels, in every degree. -/
theorem nonempty_isColimit_levelFirstVariable (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)]
    (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) (n : ℕ) :
    Nonempty (IsColimit (extCocone
      (levelFirstVariable D c B hD hX hc d p hp (constZ.{v, u} d.pt) i₀)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜)
      (levelLegSite D c B hD hX hc d p hp 𝓜) n
      (isColimitPresentation_levelLegSite D c B hD hX hc d p hp 𝓜).1)) := by
  let E := affineEtaleSiteColimit D c B hD hX hc
  have hpres := isColimitPresentation_levelLegSite D c B hD hX hc d p hp 𝓜
  have h₁ := nonempty_isColimit_extCocone_of_presentation.{v, v, max u v + 1}
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc) (mem_limitSitePrecoverage_iff D c B hD hX hc)
    (pullbackFirstVariable.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX)
      (levelConstant D c B hD hX hc i₀)) n (levelSystem E d 𝓜) _ hpres
    (mvColimit_levelConstant D c B hD hX hc i₀ n (levelSystem E d 𝓜))
  obtain ⟨e⟩ := nonempty_smallEtalePullbackAb_constant_iso (stageProj E d i₀)
  have e' : (levelFirstVariable D c B hD hX hc d p hp (constZ.{v, u} d.pt) i₀).obj
        (FirstVariable.topObj.{v, v, max u v + 1} i₀) ≅
      (pullbackFirstVariable.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX)
        (levelConstant D c B hD hX hc i₀)).obj (FirstVariable.topObj.{v, v, max u v + 1} i₀) :=
    (levelMathlibRestrict E i₀).mapIso e ≪≫
      ((abelianSheafPullbackIdIso.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc) i₀).app
        (levelConstant D c B hD hX hc i₀)).symm
  exact FirstVariable.nonempty_isColimit_of_topIso _ _ _ _ e' h₁

/-! ### The `Ext` groups of the levels read in Mathlib's small étale sites -/

section Compare

variable (𝓝 𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})

/-- The left adjoint of restriction to a level, with its adjunction. -/
abbrev levelAdj (j : (sys D c B hD hX hc).I) :=
  Adjunction.ofIsRightAdjoint (levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) j)

/-- The counit of `levelAdj` is an isomorphism. -/
theorem isIso_levelAdj_counit (j : (sys D c B hD hX hc).I) :
    IsIso (levelAdj D c B hD hX hc j).counit := by
  have := (levelAdj D c B hD hX hc j).isEquivalence_left_of_isEquivalence_right
  infer_instance

attribute [local instance] isIso_levelAdj_counit

/-- The left adjoint of restriction to a level is additive and preserves finite limits and finite
colimits. -/
theorem exact_levelAdj_left (j : (sys D c B hD hX hc).I) :
    (Functor.leftAdjoint (levelMathlibRestrict
        (affineEtaleSiteColimit D c B hD hX hc) j)).Additive ∧
      PreservesFiniteLimits (Functor.leftAdjoint (levelMathlibRestrict
        (affineEtaleSiteColimit D c B hD hX hc) j)) ∧
      PreservesFiniteColimits (Functor.leftAdjoint (levelMathlibRestrict
        (affineEtaleSiteColimit D c B hD hX hc) j)) := by
  let L := Functor.leftAdjoint (levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) j)
  have : L.IsEquivalence := (levelAdj D c B hD hX hc j).isEquivalence_left_of_isEquivalence_right
  have : PreservesLimitsOfSize.{0, 0} L := Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimitsOfSize.{0, 0} L := Adjunction.isEquivalence_preservesColimits _
  have : PreservesFiniteLimits L := ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteColimits L := ⟨fun _ _ _ => inferInstance⟩
  have : L.IsLeftAdjoint := ⟨_, ⟨levelAdj D c B hD hX hc j⟩⟩
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- The left adjoint of restriction to a level is additive. -/
theorem additive_levelAdj_left (j : (sys D c B hD hX hc).I) :
    (Functor.leftAdjoint (levelMathlibRestrict
      (affineEtaleSiteColimit D c B hD hX hc) j)).Additive :=
  (exact_levelAdj_left D c B hD hX hc j).1

/-- The left adjoint of restriction to a level preserves finite limits. -/
theorem preservesFiniteLimits_levelAdj_left (j : (sys D c B hD hX hc).I) :
    PreservesFiniteLimits (Functor.leftAdjoint (levelMathlibRestrict
      (affineEtaleSiteColimit D c B hD hX hc) j)) :=
  (exact_levelAdj_left D c B hD hX hc j).2.1

/-- The left adjoint of restriction to a level preserves finite colimits. -/
theorem preservesFiniteColimits_levelAdj_left (j : (sys D c B hD hX hc).I) :
    PreservesFiniteColimits (Functor.leftAdjoint (levelMathlibRestrict
      (affineEtaleSiteColimit D c B hD hX hc) j)) :=
  (exact_levelAdj_left D c B hD hX hc j).2.2

attribute [local instance] additive_levelAdj_left preservesFiniteLimits_levelAdj_left
  preservesFiniteColimits_levelAdj_left

/-- The comparison `π_a⁻¹ π_k⁻¹ 𝓝 ≅ π_j⁻¹ 𝓝` along a transition `a : j ⟶ k`. -/
abbrev stageComp {j k : (sys D c B hD hX hc).I} (a : j ⟶ k) :
    (smallEtalePullbackAb (stageMor (affineEtaleSiteColimit D c B hD hX hc) a)).obj
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d k)).obj 𝓝) ≅
      (smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓝 :=
  (smallEtalePullbackAbCompIso' (stageMor (affineEtaleSiteColimit D c B hD hX hc) a)
    (stageProj (affineEtaleSiteColimit D c B hD hX hc) d k)
    (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)
    (stageProj_eq (affineEtaleSiteColimit D c B hD hX hc) d a)).app 𝓝

/-- **The restriction map** `Ext^n(π_k⁻¹𝓝, π_k⁻¹𝓜) ⟶ Ext^n(π_j⁻¹𝓝, π_j⁻¹𝓜)` along a transition. -/
def stageExtTransition {j k : (sys D c B hD hX hc).I} (a : j ⟶ k) (n : ℕ)
    (y : Abelian.Ext.{max u v + 1}
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d k)).obj 𝓝)
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d k)).obj 𝓜) n) :
    Abelian.Ext.{max u v + 1}
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓝)
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓜) n :=
  extConj (stageComp D c B hD hX hc d 𝓝 a).inv (stageComp D c B hD hX hc d 𝓜 a).hom
    (y.mapExactFunctor (smallEtalePullbackAb (stageMor (affineEtaleSiteColimit D c B hD hX hc) a)))

/-- **The comparison of the `Ext` groups of a level with those of Mathlib's small étale site**,
through the left adjoint of the restriction and its counit. -/
def levelExtCompare (j : (sys D c B hD hX hc).I) (n : ℕ)
    (x : Abelian.Ext.{max u v + 1} ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝).obj j)
      ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜).obj j) n) :
    Abelian.Ext.{max u v + 1}
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓝)
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓜) n :=
  extConj (inv ((levelAdj D c B hD hX hc j).counit.app _))
    ((levelAdj D c B hD hX hc j).counit.app _)
    (x.mapExactFunctor (Functor.leftAdjoint (levelMathlibRestrict
      (affineEtaleSiteColimit D c B hD hX hc) j)))

/-- Under the adjunction of a transition `a : j ⟶ k`, the transition map of the system of levels
corresponds to the restriction to level `k` of the adjoint of `stageComp`, followed by the
comparison square `levelMathlibSquare`. -/
theorem homEquiv_levelSystem_map {j k : (sys D c B hD hX hc).I} (a : j ⟶ k) :
    (abelianSheafAdjunction.{v, v, max v (max u v + 1), max u v + 1}
        (sys D c B hD hX hc) a).homEquiv
        _ _ ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝).map a) =
      (levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) k).map
        ((smallEtaleAdjunctionAb (stageMor (affineEtaleSiteColimit D c B hD hX hc) a)).homEquiv _ _
          (stageComp D c B hD hX hc d 𝓝 a).hom) ≫
        (levelMathlibSquare (affineEtaleSiteColimit D c B hD hX hc) a).inv.app _ := by
  rw [Iso.app_hom, homEquiv_smallEtalePullbackAbCompIso'_hom_app
    (E := affineEtaleSiteColimit D c B hD hX hc)
    (hequivL := isEquivalence_limitMathlibRestrict D c B hX)]
  exact Equiv.apply_symm_apply _ _

include hp in
/-- The map of `levelFirstVariable` along `f : A₁ ⟶ A₂` is the inverse of the transition map of the
system of levels along `f.left`. -/
theorem levelFirstVariable_map (i₀ : (sys D c B hD hX hc).I) {A₁ A₂ : Over i₀} (f : A₁ ⟶ A₂) :
    (levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀).map f =
      @inv _ _ _ _ ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝).map f.left)
        (isIso_levelSystem_map (hequivL := isEquivalence_limitMathlibRestrict D c B hX)
          (affineEtaleSiteColimit D c B hD hX hc) d 𝓝 f.left) := by
  dsimp only [FirstVariable.map, FirstVariable.ψ, levelFirstVariable, systemFirstVariable,
    pushforwardTransition]
  simp only [Equiv.symm_apply_apply]

/-- **The transitions of the `Ext` diagram are the restriction maps of the levels.** -/
theorem levelExtCompare_extTransition (i₀ : (sys D c B hD hX hc).I) {A₁ A₂ : Over i₀} (f : A₁ ⟶ A₂)
    (n : ℕ) (x : Abelian.Ext.{max u v + 1}
      ((levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀).obj A₂)
      ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜).obj A₂.left) n) :
    levelExtCompare D c B hD hX hc d 𝓝 𝓜 A₁.left n
        (extTransition (levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀)
          (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜) n f x) =
      stageExtTransition D c B hD hX hc d 𝓝 𝓜 f.left n
        (levelExtCompare D c B hD hX hc d 𝓝 𝓜 A₂.left n x) := by
  rw [extTransition_apply, levelFirstVariable_map]
  have key := extConj_mapExactFunctor_squareIso
    (smallEtalePullbackAb (stageMor (affineEtaleSiteColimit D c B hD hX hc) f.left))
    (smallEtaleAdjunctionAb (stageMor (affineEtaleSiteColimit D c B hD hX hc) f.left))
    (pb.{v, v, max u v + 1} (sys D c B hD hX hc) f.left)
    (abelianSheafAdjunction.{v, v, max v (max u v + 1), max u v + 1} (sys D c B hD hX hc) f.left)
    (levelAdj D c B hD hX hc A₂.left) (levelAdj D c B hD hX hc A₁.left)
    (levelMathlibSquare (affineEtaleSiteColimit D c B hD hX hc) f.left)
    (stageComp D c B hD hX hc d 𝓝 f.left).hom inferInstance
    (stageComp D c B hD hX hc d 𝓜 f.left).hom
    ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓝).map f.left)
    (isIso_levelSystem_map (hequivL := isEquivalence_limitMathlibRestrict D c B hX)
      (affineEtaleSiteColimit D c B hD hX hc) d 𝓝 f.left)
    ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜).map f.left)
    (homEquiv_levelSystem_map D c B hD hX hc d 𝓝 f.left)
    (homEquiv_levelSystem_map D c B hD hX hc d 𝓜 f.left) x
  simp only [IsIso.Iso.inv_hom] at key
  exact key

/-! ### The legs -/

attribute [local instance] isEquivalence_limitRestrict hasSheafify_limitSite


/-- Restriction to the limit and direct image to a level commute, at the spelling of the canonical
system. -/
def limitSquareSite (j : (sys D c B hD hX hc).I) :
    limitRestrict D c B hX ⋙ colimitPushforward.{v, v, max u v + 1} (sys D c B hD hX hc)
        (toLimitSmall D c B hD hX hc) (limitSitePrecoverage D c B hX) j ≅
      smallEtalePushforwardAb (coneProj (affineEtaleSiteColimit D c B hD hX hc) j) ⋙
        levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) j :=
  limitMathlibSquare (affineEtaleSiteColimit D c B hD hX hc) j

/-- The left adjoint of restriction to the limit, with its adjunction. -/
abbrev limitAdj := Adjunction.ofIsRightAdjoint (limitRestrict D c B hX)

/-- The counit of `limitAdj` is an isomorphism. -/
theorem isIso_limitAdj_counit : IsIso (limitAdj D c B hX).counit := by
  have := (limitAdj D c B hX).isEquivalence_left_of_isEquivalence_right
  infer_instance

attribute [local instance] isIso_limitAdj_counit

/-- The left adjoint of restriction to the limit is additive and preserves finite limits and
finite colimits. -/
theorem exact_limitAdj_left :
    (Functor.leftAdjoint (limitRestrict D c B hX)).Additive ∧
      PreservesFiniteLimits (Functor.leftAdjoint (limitRestrict D c B hX)) ∧
      PreservesFiniteColimits (Functor.leftAdjoint (limitRestrict D c B hX)) := by
  let L := Functor.leftAdjoint (limitRestrict D c B hX)
  have : L.IsEquivalence := (limitAdj D c B hX).isEquivalence_left_of_isEquivalence_right
  have : PreservesLimitsOfSize.{0, 0} L := Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimitsOfSize.{0, 0} L := Adjunction.isEquivalence_preservesColimits _
  have : PreservesFiniteLimits L := ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteColimits L := ⟨fun _ _ _ => inferInstance⟩
  have : L.IsLeftAdjoint := ⟨_, ⟨limitAdj D c B hX⟩⟩
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- The left adjoint of restriction to the limit is additive. -/
theorem additive_limitAdj_left : (Functor.leftAdjoint (limitRestrict D c B hX)).Additive :=
  (exact_limitAdj_left D c B hX).1

/-- The left adjoint of restriction to the limit preserves finite limits. -/
theorem preservesFiniteLimits_limitAdj_left :
    PreservesFiniteLimits (Functor.leftAdjoint (limitRestrict D c B hX)) :=
  (exact_limitAdj_left D c B hX).2.1

/-- The left adjoint of restriction to the limit preserves finite colimits. -/
theorem preservesFiniteColimits_limitAdj_left :
    PreservesFiniteColimits (Functor.leftAdjoint (limitRestrict D c B hX)) :=
  (exact_limitAdj_left D c B hX).2.2

attribute [local instance] additive_limitAdj_left preservesFiniteLimits_limitAdj_left
  preservesFiniteColimits_limitAdj_left

/-- The comparison `(X ⟶ X_j)⁻¹ π_j⁻¹ 𝓝 ≅ p⁻¹ 𝓝` along the leg of the limit cone. -/
abbrev legComp (j : (sys D c B hD hX hc).I) :
    (smallEtalePullbackAb (coneProj (affineEtaleSiteColimit D c B hD hX hc) j)).obj
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓝) ≅
      (smallEtalePullbackAb p).obj 𝓝 :=
  (smallEtalePullbackAbCompIso' (coneProj (affineEtaleSiteColimit D c B hD hX hc) j)
    (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j) p (hp j)).app 𝓝

/-- **The restriction map to the limit** `Ext^n(π_j⁻¹𝓝, π_j⁻¹𝓜) ⟶ Ext^n(p⁻¹𝓝, p⁻¹𝓜)`. -/
def stageExtLeg (j : (sys D c B hD hX hc).I) (n : ℕ)
    (y : Abelian.Ext.{max u v + 1}
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓝)
      ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓜) n) :
    Abelian.Ext.{max u v + 1} ((smallEtalePullbackAb p).obj 𝓝) ((smallEtalePullbackAb p).obj 𝓜) n :=
  extConj (legComp D c B hD hX hc d p hp 𝓝 j).inv (legComp D c B hD hX hc d p hp 𝓜 j).hom
    (y.mapExactFunctor (smallEtalePullbackAb (coneProj (affineEtaleSiteColimit D c B hD hX hc) j)))

include hp in
/-- Under the adjunction `colimitAdj` at level `j`, the system leg built from `levelLegSite`
corresponds to the restriction to level `j` of the adjoint of `legComp`, followed by the
comparison square `limitSquareSite`. -/
theorem homEquiv_levelLegSite (j : (sys D c B hD hX hc).I) :
    (colimitAdj.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (limitSitePrecoverage D c B hX) j).homEquiv _ _
        (systemLeg.{v, v, max u v + 1} (D := sys D c B hD hX hc)
          (uC := toLimitSmall D c B hD hX hc) (K := limitSitePrecoverage D c B hX)
          (levelLegSite D c B hD hX hc d p hp 𝓝) j) =
      (levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) j).map
        ((smallEtaleAdjunctionAb (coneProj (affineEtaleSiteColimit D c B hD hX hc) j)).homEquiv _ _
          (legComp D c B hD hX hc d p hp 𝓝 j).hom) ≫
        (limitSquareSite D c B hD hX hc j).inv.app _ :=
  homEquiv_legTranspose_eq (hequivL := isEquivalence_limitMathlibRestrict D c B hX)
    (affineEtaleSiteColimit D c B hD hX hc) d p hp 𝓝 j

include hp in
/-- The leg of `levelFirstVariable` at `A` is the inverse of the system leg built from
`levelLegSite` at `A.left`. -/
theorem levelFirstVariable_leg (i₀ : (sys D c B hD hX hc).I) (A : Over i₀) :
    (levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀).leg A =
      @inv _ _ _ _ (systemLeg.{v, v, max u v + 1} (D := sys D c B hD hX hc)
          (uC := toLimitSmall D c B hD hX hc) (K := limitSitePrecoverage D c B hX)
          (levelLegSite D c B hD hX hc d p hp 𝓝) A.left)
        (isIso_systemLeg_levelLeg_site D c B hD hX hc d p hp 𝓝 A.left) := rfl

/-- **The legs of the `Ext` cocone are the restriction maps to the limit.** -/
theorem levelExtCompare_extLeg (i₀ : (sys D c B hD hX hc).I) (A : Over i₀) (n : ℕ)
    (x : Abelian.Ext.{max u v + 1} ((levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀).obj A)
      ((levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜).obj A.left) n) :
    extCompareAlong (limitAdj D c B hX) ((smallEtalePullbackAb p).obj 𝓝)
        ((smallEtalePullbackAb p).obj 𝓜)
        (extLeg (levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀)
          (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜)
          (levelLegSite D c B hD hX hc d p hp 𝓜) n A x) =
      stageExtLeg D c B hD hX hc d p hp 𝓝 𝓜 A.left n
        (levelExtCompare D c B hD hX hc d 𝓝 𝓜 A.left n x) := by
  rw [extLeg_apply, levelFirstVariable_leg]
  have key := extConj_mapExactFunctor_squareIso
    (smallEtalePullbackAb (coneProj (affineEtaleSiteColimit D c B hD hX hc) A.left))
    (smallEtaleAdjunctionAb (coneProj (affineEtaleSiteColimit D c B hD hX hc) A.left))
    (colimitPullback.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (limitSitePrecoverage D c B hX) A.left)
    (colimitAdj.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (limitSitePrecoverage D c B hX) A.left)
    (levelAdj D c B hD hX hc A.left) (limitAdj D c B hX)
    (limitSquareSite D c B hD hX hc A.left)
    (legComp D c B hD hX hc d p hp 𝓝 A.left).hom inferInstance
    (legComp D c B hD hX hc d p hp 𝓜 A.left).hom
    (systemLeg.{v, v, max u v + 1} (D := sys D c B hD hX hc)
      (uC := toLimitSmall D c B hD hX hc) (K := limitSitePrecoverage D c B hX)
      (levelLegSite D c B hD hX hc d p hp 𝓝) A.left)
    (isIso_systemLeg_levelLeg_site D c B hD hX hc d p hp 𝓝 A.left)
    (systemLeg.{v, v, max u v + 1} (D := sys D c B hD hX hc)
      (uC := toLimitSmall D c B hD hX hc) (K := limitSitePrecoverage D c B hX)
      (levelLegSite D c B hD hX hc d p hp 𝓜) A.left)
    (homEquiv_levelLegSite D c B hD hX hc d p hp 𝓝 A.left)
    (homEquiv_levelLegSite D c B hD hX hc d p hp 𝓜 A.left) x
  simp only [IsIso.Iso.inv_hom] at key
  exact key

end Compare

end Stacks.EtaleCohomology.AffineLimitCohomology

end
