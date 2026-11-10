module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelExtComparison

/-!
# The colimit of the `Ext` groups of the levels, in Mathlib's small étale sites

At the canonical site system of Stacks 0EYL with a cocone `d` on the system of schemes, the groups
`Ext^n(π_j⁻¹ 𝓝, π_j⁻¹ 𝓜)` of Mathlib's small étale sites of the levels, with the restriction maps
`stageExtTransition`, form a diagram over the opposite of the index, and the restriction maps
`stageExtLeg` to `Ext^n(p⁻¹ 𝓝, p⁻¹ 𝓜)` form a cocone on it. For `𝓝 = ℤ` and a quasi-compact
quasi-separated level the cocone is a colimit: through the comparisons `levelExtCompare` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelExtComparison.lean`, it is the `Ext`
colimit of `nonempty_isColimit_levelFirstVariable` over the arrows into the chosen level, which
are cofinal.

## Main definitions

* `Stacks.EtaleCohomology.AffineLimitCohomology.stageExtDiagram`: The diagram of the groups
  `Ext^n(π_j⁻¹ 𝓝, π_j⁻¹ 𝓜)` with the restriction maps.
* `Stacks.EtaleCohomology.AffineLimitCohomology.stageExtCocone`: The cocone of the restriction
  maps to `Ext^n(p⁻¹ 𝓝, p⁻¹ 𝓜)`.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.nonempty_isColimit_stageExtCocone`: For a
  quasi-compact quasi-separated level, the cocone `stageExtCocone` with `𝓝 = ℤ` is a colimit.
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
  (𝓝 𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1})

attribute [local instance] isContinuous_levelEtale isContinuous_levelToLimit
  isContinuous_levelMathlib enoughInjectives_level hasExt_level hasExt_limitSite
  enoughInjectives_limitSite Stacks.EtaleCohomology.LimitSiteBridge.toLimitSmall_isContinuous
  preservesFiniteLimits_colimitPullback_sys isEquivalence_levelMathlibRestrict
  isContinuous_limitSmallMathlib isContinuous_limitSmallMathlib_site
  isIso_levelAdj_counit additive_levelAdj_left preservesFiniteLimits_levelAdj_left
  preservesFiniteColimits_levelAdj_left isEquivalence_limitRestrict hasSheafify_limitSite
  isIso_limitAdj_counit additive_limitAdj_left preservesFiniteLimits_limitAdj_left
  preservesFiniteColimits_limitAdj_left

attribute [local instance high] hasSheafify_smallEtaleTopology_succ

/-- The arrow `a : j ⟶ k` as an object of `Over k`. -/
abbrev overOf {j k : (sys D c B hD hX hc).I} (a : j ⟶ k) : Over k := Over.mk a

/-- The comparison `levelExtCompare` of `Ext` groups at a level is surjective. -/
theorem surjective_levelExtCompare (j : (sys D c B hD hX hc).I) (n : ℕ) :
    Function.Surjective (levelExtCompare D c B hD hX hc d 𝓝 𝓜 j n) := by
  have : IsIso (levelAdj D c B hD hX hc j).unit := by
    have := (levelAdj D c B hD hX hc j).isEquivalence_left_of_isEquivalence_right
    infer_instance
  exact (bijective_extCompareAlong.{max u v + 1, max u v + 1} (levelAdj D c B hD hX hc j) _ _ n).2

/-- The restriction map `stageExtTransition` as a morphism of groups. -/
def stageExtTransitionHom {j k : (sys D c B hD hX hc).I} (a : j ⟶ k) (n : ℕ) :
    AddCommGrpCat.of (Abelian.Ext.{max u v + 1}
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d k)).obj 𝓝)
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d k)).obj 𝓜) n) ⟶
      AddCommGrpCat.of (Abelian.Ext.{max u v + 1}
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓝)
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓜) n) :=
  AddCommGrpCat.ofHom ((extConjHom (stageComp D c B hD hX hc d 𝓝 a).inv
    (stageComp D c B hD hX hc d 𝓜 a).hom n).comp
      ((smallEtalePullbackAb (stageMor (affineEtaleSiteColimit D c B hD hX hc) a)).mapExtAddHom
        _ _ n))

/-- `stageExtTransitionHom` acts on elements as `stageExtTransition`. -/
theorem stageExtTransitionHom_apply {j k : (sys D c B hD hX hc).I} (a : j ⟶ k) (n : ℕ) (y) :
    stageExtTransitionHom D c B hD hX hc d 𝓝 𝓜 a n y =
      stageExtTransition D c B hD hX hc d 𝓝 𝓜 a n y := rfl

include hp in
/-- The restriction map along the identity of a level is the identity. -/
theorem stageExtTransition_id (j : (sys D c B hD hX hc).I) (n : ℕ) (y) :
    stageExtTransition D c B hD hX hc d 𝓝 𝓜 (𝟙 j) n y = y := by
  obtain ⟨x, rfl⟩ := surjective_levelExtCompare D c B hD hX hc d 𝓝 𝓜 j n y
  exact (levelExtCompare_extTransition D c B hD hX hc d p hp 𝓝 𝓜 j (𝟙 (Over.mk (𝟙 j))) n
    x).symm.trans (congrArg (levelExtCompare D c B hD hX hc d 𝓝 𝓜 j n)
    (extTransition_id (levelFirstVariable D c B hD hX hc d p hp 𝓝 j)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜) n (Over.mk (𝟙 j)) x))

include hp in
/-- The restriction map along a composite `a ≫ b` is the composite of the restriction maps
along `b` and along `a`. -/
theorem stageExtTransition_comp {j k l : (sys D c B hD hX hc).I} (a : j ⟶ k) (b : k ⟶ l) (n : ℕ)
    (y) : stageExtTransition D c B hD hX hc d 𝓝 𝓜 (a ≫ b) n y =
      stageExtTransition D c B hD hX hc d 𝓝 𝓜 a n
        (stageExtTransition D c B hD hX hc d 𝓝 𝓜 b n y) := by
  obtain ⟨x, rfl⟩ := surjective_levelExtCompare D c B hD hX hc d 𝓝 𝓜 l n y
  let f₁ : overOf D c B hD hX hc (a ≫ b) ⟶ overOf D c B hD hX hc b := Over.homMk a
  let f₂ : overOf D c B hD hX hc b ⟶ overOf D c B hD hX hc (𝟙 l) := Over.homMk b
  have h₁ := levelExtCompare_extTransition D c B hD hX hc d p hp 𝓝 𝓜 l (f₁ ≫ f₂) n x
  have h₂ := levelExtCompare_extTransition D c B hD hX hc d p hp 𝓝 𝓜 l f₁ n
    (extTransition (levelFirstVariable D c B hD hX hc d p hp 𝓝 l)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜) n f₂ x)
  have h₃ := levelExtCompare_extTransition D c B hD hX hc d p hp 𝓝 𝓜 l f₂ n x
  have h₄ := congrArg (levelExtCompare D c B hD hX hc d 𝓝 𝓜 j n)
    (extTransition_comp (levelFirstVariable D c B hD hX hc d p hp 𝓝 l)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜) n f₁ f₂ x)
  exact h₁.symm.trans (h₄.trans (h₂.trans (congrArg
    (stageExtTransition D c B hD hX hc d 𝓝 𝓜 a n) h₃)))

/-- The map from the limit to the vertex of `d` through any level. -/
def throughLevel : c.pt ⟶ d.pt :=
  coneProj (affineEtaleSiteColimit D c B hD hX hc)
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj
        (Opposite.op (Classical.arbitrary I))) ≫
    stageProj (affineEtaleSiteColimit D c B hD hX hc) d
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj
        (Opposite.op (Classical.arbitrary I)))

/-- The map `throughLevel` is the composite of the projection to any level `j` with the leg of
`d` at `j`. -/
theorem throughLevel_spec (j : (sys D c B hD hX hc).I) :
    throughLevel D c B hD hX hc d =
      coneProj (affineEtaleSiteColimit D c B hD hX hc) j ≫
        stageProj (affineEtaleSiteColimit D c B hD hX hc) d j := by
  let E := affineEtaleSiteColimit D c B hD hX hc
  have key : ∀ {m k : (sys D c B hD hX hc).I} (a : m ⟶ k),
      coneProj E k ≫ stageProj E d k = coneProj E m ≫ stageProj E d m := by
    intro m k a
    rw [coneProj_eq E a, stageProj_eq E d a, Category.assoc]
  obtain ⟨m, ⟨a⟩, ⟨b⟩⟩ := system_I_cofiltered E
    (E.indexEquiv.inverse.obj (Opposite.op (Classical.arbitrary I))) j
  exact (key a).trans (key b).symm

/-- The restriction map along the identity of a level is the identity. -/
theorem stageExtTransition_id' (j : (sys D c B hD hX hc).I) (n : ℕ) (y) :
    stageExtTransition D c B hD hX hc d 𝓝 𝓜 (𝟙 j) n y = y :=
  stageExtTransition_id D c B hD hX hc d _ (throughLevel_spec D c B hD hX hc d) 𝓝 𝓜 j n y

/-- The restriction map along a composite `a ≫ b` is the composite of the restriction maps
along `b` and along `a`. -/
theorem stageExtTransition_comp' {j k l : (sys D c B hD hX hc).I} (a : j ⟶ k) (b : k ⟶ l)
    (n : ℕ) (y) : stageExtTransition D c B hD hX hc d 𝓝 𝓜 (a ≫ b) n y =
      stageExtTransition D c B hD hX hc d 𝓝 𝓜 a n (stageExtTransition D c B hD hX hc d 𝓝 𝓜 b n y) :=
  stageExtTransition_comp D c B hD hX hc d _ (throughLevel_spec D c B hD hX hc d) 𝓝 𝓜 a b n y

/-- **The diagram of the `Ext` groups of the levels**, with the restriction maps. -/
def stageExtDiagram (n : ℕ) : (sys D c B hD hX hc).Iᵒᵖ ⥤ Ab.{max u v + 1} where
  obj j := AddCommGrpCat.of (Abelian.Ext.{max u v + 1}
    ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j.unop)).obj 𝓝)
    ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j.unop)).obj 𝓜) n)
  map a := stageExtTransitionHom D c B hD hX hc d 𝓝 𝓜 a.unop n
  map_id j := by
    ext y
    exact stageExtTransition_id' D c B hD hX hc d 𝓝 𝓜 j.unop n y
  map_comp a b := by
    ext y
    exact stageExtTransition_comp' D c B hD hX hc d 𝓝 𝓜 b.unop a.unop n y

/-- The map of `stageExtDiagram` at `a` acts on elements as `stageExtTransition` along
`a.unop`. -/
theorem stageExtDiagram_map_apply (n : ℕ) {j k : (sys D c B hD hX hc).Iᵒᵖ} (a : j ⟶ k) (y) :
    (stageExtDiagram D c B hD hX hc d 𝓝 𝓜 n).map a y =
      stageExtTransition D c B hD hX hc d 𝓝 𝓜 a.unop n y := rfl

/-- The restriction map to the limit as a morphism of groups. -/
def stageExtLegHom (j : (sys D c B hD hX hc).I) (n : ℕ) :
    AddCommGrpCat.of (Abelian.Ext.{max u v + 1}
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓝)
        ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓜) n) ⟶
      AddCommGrpCat.of (Abelian.Ext.{max u v + 1} ((smallEtalePullbackAb p).obj 𝓝)
        ((smallEtalePullbackAb p).obj 𝓜) n) :=
  AddCommGrpCat.ofHom ((extConjHom (legComp D c B hD hX hc d p hp 𝓝 j).inv
    (legComp D c B hD hX hc d p hp 𝓜 j).hom n).comp
      ((smallEtalePullbackAb (coneProj (affineEtaleSiteColimit D c B hD hX hc) j)).mapExtAddHom
        _ _ n))

/-- `stageExtLegHom` acts on elements as `stageExtLeg`. -/
theorem stageExtLegHom_apply (j : (sys D c B hD hX hc).I) (n : ℕ) (y) :
    stageExtLegHom D c B hD hX hc d p hp 𝓝 𝓜 j n y =
      stageExtLeg D c B hD hX hc d p hp 𝓝 𝓜 j n y := rfl

/-- The restriction maps to the limit are compatible with the restriction maps along the
transitions. -/
theorem stageExtLeg_transition {j k : (sys D c B hD hX hc).I} (a : j ⟶ k) (n : ℕ) (y) :
    stageExtLeg D c B hD hX hc d p hp 𝓝 𝓜 j n (stageExtTransition D c B hD hX hc d 𝓝 𝓜 a n y) =
      stageExtLeg D c B hD hX hc d p hp 𝓝 𝓜 k n y := by
  obtain ⟨x, rfl⟩ := surjective_levelExtCompare D c B hD hX hc d 𝓝 𝓜 k n y
  let f : overOf D c B hD hX hc a ⟶ overOf D c B hD hX hc (𝟙 k) := Over.homMk a
  have h₁ := levelExtCompare_extTransition D c B hD hX hc d p hp 𝓝 𝓜 k f n x
  have h₂ := levelExtCompare_extLeg D c B hD hX hc d p hp 𝓝 𝓜 k (overOf D c B hD hX hc a) n
    (extTransition (levelFirstVariable D c B hD hX hc d p hp 𝓝 k)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜) n f x)
  have h₃ := levelExtCompare_extLeg D c B hD hX hc d p hp 𝓝 𝓜 k (overOf D c B hD hX hc (𝟙 k)) n x
  rw [extLeg_transition (levelFirstVariable D c B hD hX hc d p hp 𝓝 k)
      (levelLegSite D c B hD hX hc d p hp 𝓜) n
      (isColimitPresentation_levelLegSite D c B hD hX hc d p hp 𝓜).1 f x] at h₂
  exact (congrArg (stageExtLeg D c B hD hX hc d p hp 𝓝 𝓜 j n) h₁.symm).trans (h₂.symm.trans h₃)

/-- **The cocone of restrictions to the limit.** -/
def stageExtCocone (n : ℕ) : Cocone (stageExtDiagram D c B hD hX hc d 𝓝 𝓜 n) where
  pt := AddCommGrpCat.of (Abelian.Ext.{max u v + 1} ((smallEtalePullbackAb p).obj 𝓝)
    ((smallEtalePullbackAb p).obj 𝓜) n)
  ι :=
    { app j := stageExtLegHom D c B hD hX hc d p hp 𝓝 𝓜 j.unop n
      naturality j k a := by
        ext y
        exact stageExtLeg_transition D c B hD hX hc d p hp 𝓝 𝓜 a.unop n y }

/-- The leg of `stageExtCocone` at `j` acts on elements as `stageExtLeg` at `j.unop`. -/
theorem stageExtCocone_ι_app (n : ℕ) (j : (sys D c B hD hX hc).Iᵒᵖ) (y) :
    (stageExtCocone D c B hD hX hc d p hp 𝓝 𝓜 n).ι.app j y =
      stageExtLeg D c B hD hX hc d p hp 𝓝 𝓜 j.unop n y := rfl

/-! ### The colimit -/

section Colimit

variable (i₀ : (sys D c B hD hX hc).I) (n : ℕ)

/-- The comparison at an arrow into `i₀`, as an isomorphism of groups. -/
def levelExtCompareIso (A : Over i₀) :
    (extDiagram (levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜) n).obj (op A) ≅
      ((Over.forget i₀).op ⋙ stageExtDiagram D c B hD hX hc d 𝓝 𝓜 n).obj (op A) := by
  haveI : IsIso (levelAdj D c B hD hX hc A.left).unit := by
    have := (levelAdj D c B hD hX hc A.left).isEquivalence_left_of_isEquivalence_right
    infer_instance
  exact (AddEquiv.ofBijective (extCompareAlongHom.{max u v + 1, max u v + 1}
    (levelAdj D c B hD hX hc A.left) _ _ n)
    (bijective_extCompareAlong.{max u v + 1, max u v + 1} (levelAdj D c B hD hX hc A.left)
      _ _ n)).toAddCommGrpIso

/-- The isomorphism `levelExtCompareIso` acts on elements as `levelExtCompare`. -/
theorem levelExtCompareIso_hom_apply (A : Over i₀) (x) :
    (levelExtCompareIso D c B hD hX hc d p hp 𝓝 𝓜 i₀ n A).hom x =
      levelExtCompare D c B hD hX hc d 𝓝 𝓜 A.left n x := rfl

/-- **The comparison of the diagrams**, a natural isomorphism. -/
def levelExtDiagramIso :
    extDiagram (levelFirstVariable D c B hD hX hc d p hp 𝓝 i₀)
      (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜) n ≅
      (Over.forget i₀).op ⋙ stageExtDiagram D c B hD hX hc d 𝓝 𝓜 n :=
  NatIso.ofComponents (fun A => levelExtCompareIso D c B hD hX hc d p hp 𝓝 𝓜 i₀ n A.unop)
    (fun {A A'} f => by
      ext x
      exact levelExtCompare_extTransition D c B hD hX hc d p hp 𝓝 𝓜 i₀ f.unop n x)

/-- The comparison of the vertices, an isomorphism of groups. -/
def limitExtCompareIso :
    AddCommGrpCat.of (Abelian.Ext.{max u v + 1}
        ((limitRestrict D c B hX).obj ((smallEtalePullbackAb p).obj 𝓝))
        ((limitRestrict D c B hX).obj ((smallEtalePullbackAb p).obj 𝓜)) n) ≅
      (stageExtCocone D c B hD hX hc d p hp 𝓝 𝓜 n).pt := by
  haveI : IsIso (limitAdj D c B hX).unit := by
    have := (limitAdj D c B hX).isEquivalence_left_of_isEquivalence_right
    infer_instance
  exact (AddEquiv.ofBijective (extCompareAlongHom.{max u v + 1, max u v + 1}
    (𝒞 := Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (𝒟 := Sheaf (limitSitePrecoverage D c B hX).toGrothendieck AddCommGrpCat.{max u v + 1})
    (limitAdj D c B hX) _ _ n)
    (bijective_extCompareAlong.{max u v + 1, max u v + 1}
      (𝒞 := Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{max u v + 1})
      (𝒟 := Sheaf (limitSitePrecoverage D c B hX).toGrothendieck AddCommGrpCat.{max u v + 1})
      (limitAdj D c B hX) _ _ n)).toAddCommGrpIso

/-- **Stacks 09YP for the étale cohomology of the levels, in Mathlib's small étale sites**: for a
quasi-compact quasi-separated level `i₀`, `Ext^n(p⁻¹ ℤ, p⁻¹ 𝓜) = colim_j Ext^n(π_j⁻¹ ℤ, π_j⁻¹ 𝓜)`,
the restriction maps forming a colimit cocone. -/
theorem nonempty_isColimit_stageExtCocone (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)] (n : ℕ) :
    Nonempty (IsColimit (stageExtCocone D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 n)) := by
  obtain ⟨hcol⟩ := nonempty_isColimit_levelFirstVariable D c B hD hX hc d p hp i₀ 𝓜 n
  let α := levelExtDiagramIso D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 i₀ n
  let c₂ := (stageExtCocone D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 n).whisker
    (Over.forget i₀).op
  have e : (Cocone.precompose α.hom).obj c₂ ≅
      extCocone (levelFirstVariable D c B hD hX hc d p hp (constZ.{v, u} d.pt) i₀)
        (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜)
        (levelLegSite D c B hD hX hc d p hp 𝓜) n
        (isColimitPresentation_levelLegSite D c B hD hX hc d p hp 𝓜).1 :=
    Cocone.ext (limitExtCompareIso D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 n).symm
      (fun A => by
        ext x
        have key :=
          levelExtCompare_extLeg D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 i₀ A.unop n x
        change (limitExtCompareIso D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 n).inv
          (stageExtLeg D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 A.unop.left n
            (levelExtCompare D c B hD hX hc d (constZ.{v, u} d.pt) 𝓜 A.unop.left n x)) = _
        rw [← key]
        exact Iso.hom_inv_id_apply
          (limitExtCompareIso D c B hD hX hc d p hp (constZ.{v, u} d.pt) 𝓜 n) _)
  exact ⟨(Functor.Final.isColimitWhiskerEquiv (Over.forget i₀).op _).1
    ((IsColimit.precomposeHomEquiv α c₂).1 (hcol.ofIsoColimit e.symm))⟩

end Colimit

end Stacks.EtaleCohomology.AffineLimitCohomology

end
