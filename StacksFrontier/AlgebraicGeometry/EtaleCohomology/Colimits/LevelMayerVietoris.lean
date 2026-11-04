module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelCanonicalInstances
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitSiteBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.QcqsOpenInduction
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitPullbackFirstVariable
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ColimitPresentationOfIsoLegs

/-!
# The `Ext` colimit for the constant sheaf at a quasi-compact quasi-separated level

At the canonical site system of Stacks 0EYL fix a level `i₀` whose scheme `X_{i₀}` is
quasi-compact and quasi-separated. For an open `W ⊆ X_{i₀}` let `ℤ[W]` be the free abelian sheaf
on the object `W` of the small étale site, restricted to the level `i₀`
(`Stacks.EtaleCohomology.AffineLimitCohomology.levelFree`). This file proves Stacks 09YP in its
`Ext` form for the pullback first variables of all these sheaves
(`Stacks.EtaleCohomology.AffineLimitCohomology.mvColimit_of_isCompact`):

* for an affine open `W`, `ℤ[W]` corepresents the sections over an object of the level, so the
  representable case
  `Stacks.WeakSites.ExtColimit.nonempty_isColimit_stdCocone_of_isCorepresentingSection` applies;
* for two opens the Mayer–Vietoris sequence `0 ⟶ ℤ[U ⊓ V] ⟶ ℤ[U] ⊞ ℤ[V] ⟶ ℤ[U ⊔ V] ⟶ 0`
  (`Stacks.EtaleCohomology.MayerVietoris.shortExact`) is carried to a short exact sequence of
  pullback first variables, and the five lemma
  (`Stacks.WeakSites.ExtColimit.FirstVariable.ShortExact.nonempty_isColimit_right`) passes the
  property from `U`, `V`, `U ⊓ V` to `U ⊔ V`;
* the Mayer–Vietoris induction `AlgebraicGeometry.Scheme.Opens.mayerVietoris_induction` reaches
  every quasi-compact open, in particular `X_{i₀}` itself, whose free sheaf is the constant sheaf.

The result (`Stacks.EtaleCohomology.AffineLimitCohomology.mvColimit_levelConstant`):
`colim_{A : Over i₀} Ext^n((A.hom)⁻¹ E(ℤ), F_A) = Ext^n(u_{i₀}⁻¹ E(ℤ), colim F)` in every degree
and for every system `F`, where `E(ℤ)` is the constant sheaf of Mathlib's small étale site of
`X_{i₀}` restricted to the level.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.EtaleCohomology.AffineLimitCohomology

universe v u w

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Sites.InverseSystem
  InverseSystemOfFiniteSites Stacks.WeakSites.ExtColimit Stacks.WeakSites.ColimitSiteCohomology
  Stacks.Sites.FreeRepresentable Stacks.EtaleCohomology.TransitionBaseChange

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

attribute [local instance] isContinuous_levelEtale isContinuous_levelToLimit
  isContinuous_levelMathlib enoughInjectives_level hasExt_level hasExt_limitSite
  enoughInjectives_limitSite

attribute [local instance]
  Stacks.EtaleCohomology.LimitSiteBridge.toLimitSmall_isContinuous

/-- The inverse images to the raised site of the limit are left exact. -/
theorem preservesFiniteLimits_colimitPullback_sys (j : (sys D c B hD hX hc).I) :
    PreservesFiniteLimits (colimitPullback.{v, v, max u v + 1} (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (limitSitePrecoverage D c B hX) j) :=
  Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_ab_largeSections
    (isMorphismOfSites_levelToLimit D c B hD hX hc j)

attribute [local instance] preservesFiniteLimits_colimitPullback_sys

section Level

variable (i₀ : (sys D c B hD hX hc).I)

/-- The scheme `X_{i₀}` of the level `i₀`. -/
local notation "Yl" => levelScheme D c B hD hX hc i₀

/-- Restriction from the one-universe model of the small étale site of `X_{i₀}`
(`Stacks.EtaleCohomology.MayerVietoris.Site`) to the level `i₀`. -/
abbrev mvToLevel :
    Sheaf (MayerVietoris.topology (levelScheme D c B hD hX hc i₀)) AddCommGrpCat.{max u v + 1} ⥤
      Sheaf ((sys D c B hD hX hc).J i₀) AddCommGrpCat.{max u v + 1} :=
  (AsSmall.up : (levelScheme D c B hD hX hc i₀).Etale ⥤
      MayerVietoris.Site _).sheafPushforwardContinuous
      AddCommGrpCat.{max u v + 1} (smallEtaleTopology (levelScheme D c B hD hX hc i₀))
      (MayerVietoris.topology (levelScheme D c B hD hX hc i₀)) ⋙
    levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) i₀

/-- Restriction along the raise of the small étale site is an equivalence. -/
theorem isEquivalence_asSmallUp_restrict :
    ((AsSmall.up : (levelScheme D c B hD hX hc i₀).Etale ⥤
        MayerVietoris.Site _).sheafPushforwardContinuous
      AddCommGrpCat.{max u v + 1} (smallEtaleTopology (levelScheme D c B hD hX hc i₀))
      (MayerVietoris.topology (levelScheme D c B hD hX hc i₀))).IsEquivalence :=
  inferInstance

attribute [local instance] isEquivalence_asSmallUp_restrict isEquivalence_levelMathlibRestrict

/-- Restriction from the small étale site of `X_{i₀}` to the level `i₀` is an equivalence. -/
theorem isEquivalence_mvToLevel : (mvToLevel D c B hD hX hc i₀).IsEquivalence := inferInstance

attribute [local instance] isEquivalence_mvToLevel

/-- Restriction to the level `i₀` preserves finite limits. -/
theorem preservesFiniteLimits_mvToLevel : PreservesFiniteLimits (mvToLevel D c B hD hX hc i₀) := by
  have : PreservesLimitsOfSize.{0, 0} (mvToLevel D c B hD hX hc i₀) :=
    Adjunction.isEquivalencePreservesLimits _
  exact ⟨fun _ _ _ => inferInstance⟩

/-- Restriction to the level `i₀` preserves finite colimits. -/
theorem preservesFiniteColimits_mvToLevel :
    PreservesFiniteColimits (mvToLevel D c B hD hX hc i₀) := by
  have : PreservesColimitsOfSize.{0, 0} (mvToLevel D c B hD hX hc i₀) :=
    Adjunction.isEquivalence_preservesColimits _
  exact ⟨fun _ _ _ => inferInstance⟩

/-- Restriction to the level `i₀` preserves zero morphisms. -/
theorem preservesZeroMorphisms_mvToLevel : (mvToLevel D c B hD hX hc i₀).PreservesZeroMorphisms :=
  have : (mvToLevel D c B hD hX hc i₀).IsLeftAdjoint :=
    ⟨_, ⟨(mvToLevel D c B hD hX hc i₀).asEquivalence.toAdjunction⟩⟩
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

attribute [local instance] preservesFiniteLimits_mvToLevel preservesFiniteColimits_mvToLevel
  preservesZeroMorphisms_mvToLevel

/-- Restriction to the level `i₀` is additive. -/
theorem additive_mvToLevel : (mvToLevel D c B hD hX hc i₀).Additive := by
  have : PreservesLimitsOfSize.{0, 0} (mvToLevel D c B hD hX hc i₀) :=
    Adjunction.isEquivalencePreservesLimits _
  exact Functor.additive_of_preserves_binary_products _

attribute [local instance] additive_mvToLevel

/-- **The free abelian sheaf on an open of `X_{i₀}`, at the level `i₀`.** -/
abbrev levelFree (W : (levelScheme D c B hD hX hc i₀).Opens) :
    Sheaf ((sys D c B hD hX hc).J i₀) AddCommGrpCat.{max u v + 1} :=
  (mvToLevel D c B hD hX hc i₀).obj
    (freeRep (MayerVietoris.topology _) ((MayerVietoris.opensToSite _).obj W))

/-- The `Ext` colimit property of the pullback first variable of a sheaf on the level `i₀`, in
every degree and for every system. -/
def MVColimit (P : Sheaf ((sys D c B hD hX hc).J i₀) AddCommGrpCat.{max u v + 1}) : Prop :=
  ∀ (n : ℕ) (F : AbelianSheafSystem.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)),
    Nonempty (IsColimit (stdCocone.{v, v, max u v + 1} (toLimitSmall_transition D c B hD hX hc)
      (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
      (toLimitSmall_hom_eventually_eq D c B hD hX hc) (mem_limitSitePrecoverage_iff D c B hD hX hc)
      (pullbackFirstVariable.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) P) n F))

/-- The object of the small affine étale site of `X_{i₀}` given by an affine open. -/
def affineOpenObj (W : (levelScheme D c B hD hX hc i₀).Opens) (hW : IsAffineOpen W) :
    AlgebraicGeometry.SmallAffineEtale B (levelScheme D c B hD hX hc i₀)
      (hD (levelIndex D c B hD hX hc i₀)) :=
  haveI : IsAffine W := hW
  ⟨⟨CategoryTheory.Over.mk (ObjectProperty.homMk W.ι :
      B.obj W ((Scheme.size_le_of_locallyOfFiniteType W.ι).trans_lt
        (hD (levelIndex D c B hD hX hc i₀))) ⟶ B.obj _ (hD (levelIndex D c B hD hX hc i₀))),
    (inferInstance : Etale W.ι)⟩, hW⟩

/-- The object of the level `i₀` given by an affine open of `X_{i₀}`. -/
def levelObj (W : (levelScheme D c B hD hX hc i₀).Opens) (hW : IsAffineOpen W) :
    (sys D c B hD hX hc).C i₀ :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.obj
    (affineOpenObj D c B hD hX hc i₀ W hW)

/-- The object of the level given by an affine open is that open, in Mathlib's small étale site. -/
def levelObjIso (W : (levelScheme D c B hD hX hc i₀).Opens) (hW : IsAffineOpen W) :
    (levelMathlib (affineEtaleSiteColimit D c B hD hX hc) i₀).obj
        (levelObj D c B hD hX hc i₀ W hW) ≅ (opensToEtale _).obj W :=
  (AlgebraicGeometry.SmallAffineEtale.inclusion B _ _ ⋙
      AlgebraicGeometry.SmallEtale.toEtaleSite B _ _).mapIso
    (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).counitIso.app
      (affineOpenObj D c B hD hX hc i₀ W hW)) ≪≫ Iso.refl _

/-- Pushing the free sheaf on an open down to the small étale site, it corepresents the sections
over any étale object whose image in the raised site is isomorphic to that open. -/
private theorem exists_isCorepresentingSection_freeRep_pushforward (Y : Scheme.{w})
    (W : Y.Opens) (X : Y.Etale) (e : (MayerVietoris.opensToSite Y).obj W ≅ AsSmall.up.obj X) :
    ∃ s, IsCorepresentingSection ((AsSmall.up.sheafPushforwardContinuous
      AddCommGrpCat.{w + 1} (smallEtaleTopology Y) (MayerVietoris.topology Y)).obj
        (freeRep (MayerVietoris.topology Y) ((MayerVietoris.opensToSite Y).obj W))) X s :=
  ⟨_, ((isCorepresentingSection_freeRep (MayerVietoris.topology Y)
    ((MayerVietoris.opensToSite Y).obj W)).ofIso e).pushforward_of_isEquivalence
      (JA := smallEtaleTopology Y) (JB := MayerVietoris.topology Y) AsSmall.up⟩

/-- **For an affine open `W`, the level sheaf `ℤ[W]` corepresents the sections over the object
of the level given by `W`.** -/
theorem isCorepresentingSection_levelFree (W : (levelScheme D c B hD hX hc i₀).Opens)
    (hW : IsAffineOpen W) :
    ∃ s, IsCorepresentingSection (levelFree D c B hD hX hc i₀ W)
      (levelObj D c B hD hX hc i₀ W hW) s := by
  obtain ⟨s, hs⟩ := exists_isCorepresentingSection_freeRep_pushforward
    (levelScheme D c B hD hX hc i₀) W _
    ((AsSmall.up : (levelScheme D c B hD hX hc i₀).Etale ⥤ MayerVietoris.Site _).mapIso
      (levelObjIso D c B hD hX hc i₀ W hW).symm)
  exact ⟨_, hs.pushforward_of_isEquivalence (JA := (sys D c B hD hX hc).J i₀)
    (JB := smallEtaleTopology _) (levelMathlib (affineEtaleSiteColimit D c B hD hX hc) i₀)⟩

/-- **The affine case**: the `Ext` colimit property holds for `ℤ[W]`, `W` an affine open. -/
theorem mvColimit_of_isAffineOpen (W : (levelScheme D c B hD hX hc i₀).Opens)
    (hW : IsAffineOpen W) : MVColimit D c B hD hX hc i₀ (levelFree D c B hD hX hc i₀ W) := by
  obtain ⟨s, hs⟩ := isCorepresentingSection_levelFree D c B hD hX hc i₀ W hW
  intro n F
  exact nonempty_isColimit_stdCocone_of_isCorepresentingSection.{v, v, max u v + 1}
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc) (mem_limitSitePrecoverage_iff D c B hD hX hc)
    hs n F

end Level

/-- The index category of the canonical site system is cofiltered. -/
theorem isCofiltered_sys_I : IsCofiltered (sys D c B hD hX hc).I :=
  IsCofiltered.of_equivalence (affineEtaleSiteColimit D c B hD hX hc).indexEquiv.symm

attribute [local instance] isCofiltered_sys_I

/-- The opposite of the category of indices over `i₀` is filtered. -/
theorem isFiltered_over_op (i₀ : (sys D c B hD hX hc).I) : IsFiltered (Over i₀)ᵒᵖ := inferInstance

attribute [local instance] isFiltered_over_op

/-- Colimits of abelian groups indexed by the opposite of the category of indices over `i₀` are
exact. -/
theorem hasExactColimitsOfShape_over_op (i₀ : (sys D c B hD hX hc).I) :
    HasExactColimitsOfShape (Over i₀)ᵒᵖ AddCommGrpCat.{max u v + 1} :=
  Stacks.Cohomology.ColimitLongExact.hasExactColimitsOfShape_of_isFiltered.{max u v + 1, v, v}
    (Over i₀)ᵒᵖ

attribute [local instance] hasExactColimitsOfShape_over_op

section Level

variable (i₀ : (sys D c B hD hX hc).I)

attribute [local instance] isEquivalence_asSmallUp_restrict isEquivalence_levelMathlibRestrict
  isEquivalence_mvToLevel preservesFiniteLimits_mvToLevel preservesFiniteColimits_mvToLevel
  preservesZeroMorphisms_mvToLevel additive_mvToLevel

/-- **The Mayer–Vietoris step**: the `Ext` colimit property passes from `ℤ[U]`, `ℤ[V]` and
`ℤ[U ⊓ V]` to `ℤ[U ⊔ V]`. -/
theorem mvColimit_sup (U V : (levelScheme D c B hD hX hc i₀).Opens)
    (hU : MVColimit D c B hD hX hc i₀ (levelFree D c B hD hX hc i₀ U))
    (hV : MVColimit D c B hD hX hc i₀ (levelFree D c B hD hX hc i₀ V))
    (hUV : MVColimit D c B hD hX hc i₀ (levelFree D c B hD hX hc i₀ (U ⊓ V))) :
    MVColimit D c B hD hX hc i₀ (levelFree D c B hD hX hc i₀ (U ⊔ V)) := by
  intro n F
  let Ψ := mvToLevel D c B hD hX hc i₀
  let S := (MayerVietoris.square (levelScheme D c B hD hX hc i₀) U V).shortComplex
  let P₁ := freeRep (MayerVietoris.topology _)
    ((MayerVietoris.opensToSite (levelScheme D c B hD hX hc i₀)).obj U)
  let P₂ := freeRep (MayerVietoris.topology _)
    ((MayerVietoris.opensToSite (levelScheme D c B hD hX hc i₀)).obj V)
  have hS' : (S.map Ψ).ShortExact := (MayerVietoris.shortExact U V).map_of_exact Ψ
  let SE := pullbackFirstVariableShortExact.{v, v, max u v + 1}
    (uC := toLimitSmall D c B hD hX hc) (hu := toLimitSmall_transition D c B hD hX hc)
    (K := limitSitePrecoverage D c B hX) (S.map Ψ) hS'
  let SP := pullbackFirstVariableSplit.{v, v, max u v + 1}
    (uC := toLimitSmall D c B hD hX hc) (hu := toLimitSmall_transition D c B hD hX hc)
    (K := limitSitePrecoverage D c B hX) (Ψ.map (biprod.inl (X := P₁) (Y := P₂)))
    (Ψ.map (biprod.inr (X := P₁) (Y := P₂)))
    (Ψ.map (biprod.fst (X := P₁) (Y := P₂))) (Ψ.map (biprod.snd (X := P₁) (Y := P₂)))
    (map_comp_eq_id' Ψ _ _ biprod.inl_fst)
    (map_comp_eq_id' Ψ _ _ biprod.inr_snd) (map_comp_eq_zero' Ψ _ _ biprod.inl_snd)
    (map_comp_eq_zero' Ψ _ _ biprod.inr_fst) (map_total_eq' Ψ _ _ _ _ biprod.total)
  exact FirstVariable.ShortExact.nonempty_isColimit_right (S := SE) (F := F) (ι := _) (hι := _)
    (fun m => FirstVariable.Split.nonempty_isColimit (P := SP) (F := F) (ι := _) (n := m)
      (hι := _) (hU m F) (hV m F))
    (fun m => hUV m F) n

/-- **Stacks 09YP in its `Ext` form for `ℤ[W]`, `W` a quasi-compact open of a quasi-separated
`X_{i₀}`**, by Mayer–Vietoris induction from the affine case. -/
theorem mvColimit_of_isCompact [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)]
    (W : (levelScheme D c B hD hX hc i₀).Opens)
    (hW : IsCompact (W : Set (levelScheme D c B hD hX hc i₀))) :
    MVColimit D c B hD hX hc i₀ (levelFree D c B hD hX hc i₀ W) :=
  AlgebraicGeometry.Scheme.Opens.mayerVietoris_induction
    (fun W => MVColimit D c B hD hX hc i₀ (levelFree D c B hD hX hc i₀ W))
    (fun W hW => mvColimit_of_isAffineOpen D c B hD hX hc i₀ W hW)
    (fun U V hU hV hUV => mvColimit_sup D c B hD hX hc i₀ U V hU hV hUV) hW

/-- The constant sheaf `ℤ` of Mathlib's small étale site of `X_{i₀}`, restricted to the level. -/
abbrev levelConstant : Sheaf ((sys D c B hD hX hc).J i₀) AddCommGrpCat.{max u v + 1} :=
  (levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) i₀).obj
    ((constantSheaf (smallEtaleTopology (levelScheme D c B hD hX hc i₀))
      AddCommGrpCat.{max u v + 1}).obj (AddCommGrpCat.of (ULift ℤ)))

/-- The identity of a scheme is the final object of its small étale site. -/
def isTerminal_etaleMkId (Y : Scheme.{w}) : IsTerminal (Scheme.Etale.mk (𝟙 Y)) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{w}) :=
    ⟨fun _ => inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

/-- **The free sheaf on the whole scheme is the constant sheaf**, at the level. -/
theorem nonempty_levelFree_top_iso :
    Nonempty (levelFree D c B hD hX hc i₀ ⊤ ≅ levelConstant D c B hD hX hc i₀) := by
  obtain ⟨s, h₃⟩ := exists_isCorepresentingSection_freeRep_pushforward
    (levelScheme D c B hD hX hc i₀) ⊤ (Scheme.Etale.mk (𝟙 (levelScheme D c B hD hX hc i₀)))
    (MayerVietoris.topIsoSelf (levelScheme D c B hD hX hc i₀))
  have h₄ := isCorepresentingSection_constantSheaf.{max u v + 1, max u v, max u v + 1}
    (smallEtaleTopology (levelScheme D c B hD hX hc i₀))
    (isTerminal_etaleMkId (levelScheme D c B hD hX hc i₀))
  obtain ⟨e⟩ := h₃.nonempty_iso h₄
  exact ⟨(levelMathlibRestrict (affineEtaleSiteColimit D c B hD hX hc) i₀).mapIso e⟩

/-- **Stacks 09YP in its `Ext` form for the constant sheaf at a quasi-compact quasi-separated
level**: `colim_{A : Over i₀} Ext^n((A.hom)⁻¹ E(ℤ), F_A) = Ext^n(u_{i₀}⁻¹ E(ℤ), colim F)` for
every `n` and every system `F`. -/
theorem mvColimit_levelConstant [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)] :
    MVColimit D c B hD hX hc i₀ (levelConstant D c B hD hX hc i₀) := by
  have h := mvColimit_of_isCompact D c B hD hX hc i₀ ⊤ (by simpa using isCompact_univ)
  obtain ⟨e⟩ := nonempty_levelFree_top_iso D c B hD hX hc i₀
  intro n F
  exact nonempty_isColimit_of_iso F _ n _ e (h n F)

end Level

end Stacks.EtaleCohomology.AffineLimitCohomology

end
