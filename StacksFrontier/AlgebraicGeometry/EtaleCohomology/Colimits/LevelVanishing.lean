module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelMayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelColimitPresentation
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# Vanishing of the cohomology of the limit from vanishing on the levels

Let `(X_i)` be an inverse system of schemes with affine transition morphisms and limit `X`, let
`d` be a cocone on the system with vertex `S`, `p : X ⟶ S` compatible with the legs, and `𝓜` an
abelian sheaf on `S_étale`. If some level `X_{i₀}` is quasi-compact and quasi-separated and
`H^n(X_j, (X_j ⟶ S)⁻¹ 𝓜) = 0` for every level `j`, then `H^n(X, p⁻¹ 𝓜) = 0`
(`Stacks.EtaleCohomology.AffineLimitCohomology.subsingleton_sheafH_limit_of_levels`).

This is the `Ext` colimit for the constant sheaf at a quasi-compact quasi-separated level
(`Stacks.EtaleCohomology.AffineLimitCohomology.mvColimit_levelConstant`),
read at the colimit presentation of `p⁻¹ 𝓜` by the transported levels
(`Stacks.EtaleCohomology.TransitionBaseChange.isColimitPresentation_levelLeg`): the groups of the
diagram are identified with `H^n(X_j, (X_j ⟶ S)⁻¹ 𝓜)` and the vertex with `H^n(X, p⁻¹ 𝓜)`, through
the restriction equivalences to the levels and to the raised site of the limit, the comparison of
inverse images (`Stacks.Homology.squareIso`), and the inverse image of the constant sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.EtaleCohomology.AffineLimitCohomology

universe v u w w₁ w₂ w₃

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Sites.InverseSystem
  InverseSystemOfFiniteSites Stacks.WeakSites.ExtColimit Stacks.WeakSites.ColimitSiteCohomology
  Stacks.Sites.FreeRepresentable Stacks.EtaleCohomology.TransitionBaseChange Stacks.Homology

section Generic

/-- The vertex of a colimit cocone of zero objects is zero. -/
theorem isZero_pt_of_isColimit {J : Type w₁} [Category.{w₂} J] {𝒞 : Type*} [Category* 𝒞]
    [HasZeroMorphisms 𝒞] {F : J ⥤ 𝒞} {c : Cocone F} (hc : IsColimit c)
    (h : ∀ j, IsZero (F.obj j)) : IsZero c.pt :=
  (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j => (h j).eq_of_src _ _)

/-- **The inverse image of the constant sheaf `ℤ` along a morphism of schemes is the constant
sheaf**, on the small étale sites. -/
theorem nonempty_smallEtalePullbackAb_constant_iso {X Y : Scheme.{w}} (f : X ⟶ Y) :
    Nonempty ((smallEtalePullbackAb f).obj ((constantSheaf (smallEtaleTopology Y)
        AddCommGrpCat.{w + 1}).obj (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{w + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) := by
  have hT := isTerminal_etaleMkId Y
  have hT' : IsTerminal ((smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 Y))) :=
    hT.isTerminalObj (smallEtaleBaseChange f)
  have h₁ := (isCorepresentingSection_constantSheaf.{w + 1, w, w + 1} (smallEtaleTopology Y)
    hT).pullback (smallEtaleBaseChange f) (smallEtaleAdjunctionAb f)
  exact h₁.nonempty_iso
    (isCorepresentingSection_constantSheaf.{w + 1, w, w + 1} (smallEtaleTopology X) hT')

end Generic

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

attribute [local instance] isContinuous_levelEtale isContinuous_levelToLimit
  isContinuous_levelMathlib enoughInjectives_level hasExt_level hasExt_limitSite
  enoughInjectives_limitSite
  Stacks.EtaleCohomology.LimitSiteBridge.toLimitSmall_isContinuous
  preservesFiniteLimits_colimitPullback_sys
  isEquivalence_levelMathlibRestrict isContinuous_limitSmallMathlib

/-! ### The restriction to the site of the limit, at the spelling of the canonical system -/

/-- The reading of the site of the limit in Mathlib's small étale site is continuous, at the
spelling `limitSitePrecoverage`. -/
theorem isContinuous_limitSmallMathlib_site :
    (limitSmallMathlib (c := c) (hX := hX)).IsContinuous
      (limitSitePrecoverage D c B hX).toGrothendieck (smallEtaleTopology c.pt) :=
  isContinuous_limitSmallMathlib (c := c) (hX := hX)

attribute [local instance] isContinuous_limitSmallMathlib_site

/-- Restriction from Mathlib's small étale site of the limit to the site of the limit, at the
spelling `limitSitePrecoverage`. -/
abbrev limitRestrict :
    Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1} ⥤
      Sheaf (limitSitePrecoverage D c B hX).toGrothendieck AddCommGrpCat.{max u v + 1} :=
  (limitSmallMathlib (c := c) (hX := hX)).sheafPushforwardContinuous AddCommGrpCat.{max u v + 1}
    (limitSitePrecoverage D c B hX).toGrothendieck (smallEtaleTopology c.pt)

/-- Restriction to the site of the limit is an equivalence. -/
theorem isEquivalence_limitRestrict : (limitRestrict D c B hX).IsEquivalence :=
  isEquivalence_limitMathlibRestrict D c B hX

section Comparison

variable (i₀ : (sys D c B hD hX hc).I)

/-- **The groups of the diagram**: the inverse image of the restricted constant sheaf along an
arrow `A : Over i₀` is the restricted constant sheaf of the level. -/
theorem nonempty_pb_levelConstant_iso (A : Over i₀) :
    Nonempty ((pb.{v, v, max u v + 1} (sys D c B hD hX hc) A.hom).obj
        (levelConstant D c B hD hX hc i₀) ≅
      (levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) A.left).obj
        ((constantSheaf (smallEtaleTopology (levelScheme D c B hD hX hc A.left))
          AddCommGrpCat.{max u v + 1}).obj (AddCommGrpCat.of (ULift ℤ)))) := by
  let E := affineEtaleSiteColimit D c B hD hX hc
  let Ei := levelMathlibRestrict E A.left
  let Ej := levelMathlibRestrict E i₀
  let adj₁ := Ej.asEquivalence.symm.toAdjunction
  let adj₂ := Ei.asEquivalence.symm.toAdjunction
  let adjQ := abelianSheafAdjunction.{v, v, max v (max u v + 1), max u v + 1}
    (sys D c B hD hX hc) A.hom
  let adjP := smallEtaleAdjunctionAb (stageMor E A.hom)
  let θ := squareIso adjP adjQ adj₁ adj₂ (levelMathlibSquare E A.hom)
  obtain ⟨e⟩ := nonempty_smallEtalePullbackAb_constant_iso (stageMor E A.hom)
  let ℤi := (constantSheaf (smallEtaleTopology (levelScheme D c B hD hX hc i₀))
    AddCommGrpCat.{max u v + 1}).obj (AddCommGrpCat.of (ULift ℤ))
  exact ⟨(Ei.asEquivalence.counitIso.app _).symm ≪≫ Ei.mapIso (θ.app (Ej.obj ℤi)) ≪≫
    Ei.mapIso ((smallEtalePullbackAb (stageMor E A.hom)).mapIso
      (Ej.asEquivalence.unitIso.app ℤi).symm) ≪≫ Ei.mapIso e⟩

/-- **The vertex**: the inverse image of the restricted constant sheaf to the raised site of the
limit is the restriction of the constant sheaf of the limit. -/
theorem nonempty_top_levelConstant_iso :
    Nonempty ((colimitPullback.{v, v, max u v + 1} (sys D c B hD hX hc)
        (toLimitSmall D c B hD hX hc) (limitSitePrecoverage D c B hX) i₀).obj
        (levelConstant D c B hD hX hc i₀) ≅
      (limitRestrict D c B hX).obj
        ((constantSheaf (smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1}).obj
          (AddCommGrpCat.of (ULift ℤ)))) := by
  have := isEquivalence_limitMathlibRestrict D c B hX
  let E := affineEtaleSiteColimit D c B hD hX hc
  let Ej := levelMathlibRestrict E i₀
  let Ei := limitMathlibRestrict (c := c) (hX := hX)
  let adj₁ := Ej.asEquivalence.symm.toAdjunction
  let adj₂ := Ei.asEquivalence.symm.toAdjunction
  let adjQ := colimitAdj.{v, v, max u v + 1} E.system (levelToLimit E)
    (limitPrecoverageRaised (c := c) (hX := hX)) i₀
  let adjP := smallEtaleAdjunctionAb (coneProj E i₀)
  let θ := squareIso adjP adjQ adj₁ adj₂ (limitMathlibSquare E i₀)
  obtain ⟨e⟩ := nonempty_smallEtalePullbackAb_constant_iso (coneProj E i₀)
  let ℤi := (constantSheaf (smallEtaleTopology (levelScheme D c B hD hX hc i₀))
    AddCommGrpCat.{max u v + 1}).obj (AddCommGrpCat.of (ULift ℤ))
  exact ⟨(Ei.asEquivalence.counitIso.app _).symm ≪≫ Ei.mapIso (θ.app (Ej.obj ℤi)) ≪≫
    Ei.mapIso ((smallEtalePullbackAb (coneProj E i₀)).mapIso
      (Ej.asEquivalence.unitIso.app ℤi).symm) ≪≫ Ei.mapIso e⟩

end Comparison

section Vanishing

variable (d : Cocone D) (p : c.pt ⟶ d.pt)
  (hp : ∀ i : (sys D c B hD hX hc).I,
    p = coneProj (affineEtaleSiteColimit D c B hD hX hc) i ≫
      stageProj (affineEtaleSiteColimit D c B hD hX hc) d i)
  (𝓜 : Sheaf (smallEtaleTopology d.pt) AddCommGrpCat.{max u v + 1})

include hp in
/-- The colimit presentation of the inverse image to the limit by the transported levels, at the
spelling of the canonical system. -/
theorem isColimitPresentation_levelLeg_site :
    IsColimitPresentation.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (limitSitePrecoverage D c B hX) (levelSystem (affineEtaleSiteColimit D c B hD hX hc) d 𝓜)
      ((limitRestrict D c B hX).obj ((smallEtalePullbackAb p).obj 𝓜))
      (fun j => (levelLeg (affineEtaleSiteColimit D c B hD hX hc) d p hp 𝓜 j).hom) :=
  isColimitPresentation_levelLeg.{v, u} (hequivL := isEquivalence_limitMathlibRestrict D c B hX)
    (affineEtaleSiteColimit D c B hD hX hc) d p hp 𝓜

/-- The vanishing of `H^n(X_j, (X_j ⟶ S)⁻¹ 𝓜)` at a level `j`. -/
abbrev LevelHVanishes (n : ℕ) (j : (sys D c B hD hX hc).I) : Prop :=
  Subsingleton (Sheaf.H.{max u v + 1, max u v + 1}
    ((smallEtalePullbackAb (stageProj (affineEtaleSiteColimit D c B hD hX hc) d j)).obj 𝓜) n)

include hp in
/-- **Vanishing of the cohomology of the limit from vanishing on the levels.** If some level is
quasi-compact and quasi-separated and `H^n(X_j, (X_j ⟶ S)⁻¹ 𝓜) = 0` for every level `j`, then
`H^n(X, p⁻¹ 𝓜) = 0`. -/
theorem subsingleton_sheafH_limit_of_levels (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)] (n : ℕ)
    (h : ∀ j : (sys D c B hD hX hc).I, LevelHVanishes D c B hD hX hc d 𝓜 n j) :
    Subsingleton (Sheaf.H.{max u v + 1, max u v + 1} ((smallEtalePullbackAb p).obj 𝓜) n) := by
  let E := affineEtaleSiteColimit D c B hD hX hc
  obtain ⟨hcol⟩ := nonempty_isColimit_extCocone_of_presentation.{v, v, max u v + 1}
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc) (mem_limitSitePrecoverage_iff D c B hD hX hc)
    (pullbackFirstVariable.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX)
      (levelConstant D c B hD hX hc i₀)) n (levelSystem E d 𝓜) _
    (isColimitPresentation_levelLeg_site D c B hD hX hc d p hp 𝓜)
    (mvColimit_levelConstant D c B hD hX hc i₀ n (levelSystem E d 𝓜))
  have hz := isZero_pt_of_isColimit hcol (fun A => by
    obtain ⟨e⟩ := nonempty_pb_levelConstant_iso D c B hD hX hc i₀ A.unop
    exact AddCommGrpCat.isZero_iff_subsingleton.2 (subsingleton_ext_of_iso e (Iso.refl _)
      ((subsingleton_ext_iff_of_isEquivalence (levelMathlibRestrict E A.unop.left)
        (isEquivalence_levelMathlibRestrict D c B hD hX hc A.unop.left)
        ((constantSheaf (smallEtaleTopology (levelScheme D c B hD hX hc A.unop.left))
          AddCommGrpCat.{max u v + 1}).obj (AddCommGrpCat.of (ULift ℤ)))
        ((smallEtalePullbackAb (stageProj E d A.unop.left)).obj 𝓜) n).1 (h A.unop.left))))
  obtain ⟨e⟩ := nonempty_top_levelConstant_iso D c B hD hX hc i₀
  exact subsingleton_ext_of_isZero_extCocone_pt_of_equivalence _ _ _ _ hz
    (limitRestrict D c B hX) (isEquivalence_limitRestrict D c B hX) e.symm (Iso.refl _)

end Vanishing

end Stacks.EtaleCohomology.AffineLimitCohomology

end
