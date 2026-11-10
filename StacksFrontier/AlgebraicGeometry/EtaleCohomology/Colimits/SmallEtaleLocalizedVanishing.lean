module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLocalizedLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleSectionsPullbackBaseChange

/-!
# Cohomology of a colimit of injective sheaves over a localisation of the limit

Let `X = lim X_i` be a limit of schemes with affine transition morphisms over a nonempty directed
set, `i₀` an index and `b : B ⟶ X_{i₀}` an étale morphism from a quasi-compact and
quasi-separated scheme. Let `(F_i)` be a system of abelian sheaves on the `X_i` in the sense of
[Stacks, Tag 0EZL], with every `F_i` injective, and let `𝒢 = colim f_i^{-1}F_i` on `X`. Then the
restriction of `𝒢` to `B ×_{X_{i₀}} X` has vanishing cohomology in positive degrees.

This is [Stacks, Tag 09YQ] applied to the localised inverse system `B ×_{X_{i₀}} X_i`, `i ≥ i₀`,
whose limit is `B ×_{X_{i₀}} X`
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isLimitLocalizedCone`) and whose levels are
quasi-compact and quasi-separated, carrying the restricted system
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemBaseChange` presented by the restriction of
`𝒢`: every class on the limit comes from a level, and the cohomology of a level vanishes because
the restriction of an injective sheaf along an étale morphism is injective.

It is the input of [Stacks, Tag 0EYM] that makes the higher direct images of a colimit of
injective systems vanish: the source's "for any `U` affine and étale over `X` by Theorem 09YQ we
have `H^p(U ×_S X, 𝒢) = colim H^p(U_i ×_{S_i} X_i, 𝒢_i) = 0`".

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.injective_etaleAbelianInverseImage_obj` — the
  inverse image of an injective sheaf along an étale morphism is injective.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.localizedPresentedSystem` — the localised
  presented system.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_localizedPresentedSystem`
  — [Stacks, Tag 09YQ] over the localisation, in every degree.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.subsingleton_H_localized` — **the vanishing.**
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.qcqsSections_isColimit` — **the degree-zero
  statement on sections**: for `W` quasi-compact quasi-separated and étale over `X_{i₀}`,
  `𝓕(W ×_{X_{i₀}} X) = colim_{i ≥ i₀} F_i(W ×_{X_{i₀}} X_i)`, read off the localised degree-zero
  statement through `Stacks.EtaleCohomology.etaleSectionsPullback_comp_squareLeg`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v u V U

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

/-- **The inverse image of an injective abelian sheaf along an étale morphism is injective**:
it is the restriction, whose left adjoint, extension by zero, preserves monomorphisms. -/
theorem injective_etaleAbelianInverseImage_obj {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (M : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (hM : Injective M) :
    Injective ((etaleAbelianInverseImage.{u, u + 1} j).obj M) :=
  Injective.of_iso ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} j).app M).symm
    ((extensionByZeroAdj.{u, u + 1} j).map_injective M hM)

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Scheme.{max u v})
  (i₀ : I) {B : Scheme.{max u v}} (b : B ⟶ D.obj (op i₀)) (c : Cone D)

omit [IsDirected I (· ≤ ·)] in
/-- The transition maps of the localised system are base changes of those of `D`. -/
theorem isPullback_localizedDiagram_map {j k : (GeIndex i₀)ᵒᵖ} (a : j ⟶ k) :
    IsPullback ((localizedDiagram D i₀ b).map a) (pullback.snd _ _) (pullback.snd _ _)
      (D.map ((geIndexOpFunctor i₀).map a)) := by
  refine IsPullback.of_right ?_ (localizedDiagram_map_snd D i₀ b a)
    (IsPullback.of_hasPullback b (D.map (geIndexToBase i₀ k)))
  have key : ∀ {Y Z : Scheme.{max u v}} {B' : Scheme.{max u v}} (b' : B' ⟶ Z) (g g' : Y ⟶ Z),
      g = g' → IsPullback (pullback.fst b' g) (pullback.snd b' g) b' g' := by
    intro Y Z B' b' g g' hgg
    subst hgg
    exact IsPullback.of_hasPullback b' g
  rw [localizedDiagram_map_fst]
  exact key b _ _ (by rw [← D.map_comp, geIndexToBase_comp])

/-- If the transition morphisms of `D` are affine, so are those of the localised system. -/
instance isAffineHom_localizedDiagram_map [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    {j k : (GeIndex i₀)ᵒᵖ} (a : j ⟶ k) : IsAffineHom ((localizedDiagram D i₀ b).map a) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_localizedDiagram_map D i₀ b a).flip inferInstance

/-- If the transition morphisms of `D` are affine and `B` is quasi-compact, every level
`B ×_{X_{i₀}} X_j` of the localised system is quasi-compact. -/
instance compactSpace_localizedDiagram_obj [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [CompactSpace B] (j : (GeIndex i₀)ᵒᵖ) : CompactSpace ((localizedDiagram D i₀ b).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst b (D.map (geIndexToBase i₀ j)))

/-- If the transition morphisms of `D` are affine and `B` is quasi-separated, every level
`B ×_{X_{i₀}} X_j` of the localised system is quasi-separated. -/
instance quasiSeparatedSpace_localizedDiagram_obj
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] [QuasiSeparatedSpace B]
    (j : (GeIndex i₀)ᵒᵖ) : QuasiSeparatedSpace ((localizedDiagram D i₀ b).obj j) := by
  have : QuasiSeparated (pullback.fst b (D.map (geIndexToBase i₀ j))) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback b (D.map (geIndexToBase i₀ j))).flip inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst b (D.map (geIndexToBase i₀ j)))

/-- If `b` is étale, the projection `B ×_{X_{i₀}} X_j ⟶ X_j` is étale. -/
instance etale_localizedProj_app [Etale b] (j : (GeIndex i₀)ᵒᵖ) :
    Etale ((localizedProj D i₀ b).app j) :=
  inferInstanceAs (Etale (pullback.snd b (D.map (geIndexToBase i₀ j))))

section Vanishing

variable [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- The localised system of sheaves on the levels `B ×_{X_{i₀}} X_i`. -/
abbrev localizedSystem (F : EtaleSheafSystem D AddCommGrpCat.{max u v + 1}) :
    EtaleSheafSystem (localizedDiagram D i₀ b) AddCommGrpCat.{max u v + 1} :=
  systemBaseChange (localizedProj D i₀ b) (F.restrictIndex i₀)

/-- The legs of the localised system. -/
abbrev localizedLeg (F : EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1}}
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage (conePi c i)).obj (F.obj i) ⟶ 𝒢)
    (j : (GeIndex i₀)ᵒᵖ) :
    (etaleAbelianInverseImage (conePi (localizedCone D i₀ b c) j)).obj
        ((localizedSystem D i₀ b F).obj j) ⟶
      (etaleAbelianInverseImage (localizedLimitMap D i₀ b c)).obj 𝒢 :=
  baseChangeLeg (c := c.whisker (geIndexOpFunctor i₀)) (localizedProj D i₀ b)
    (localizedLimitMap D i₀ b c) (localizedCone_proj D i₀ b c) (F.restrictIndex i₀)
    (fun j => ι ((geIndexOpFunctor i₀).obj j)) j

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The restriction of `𝒢` to `B ×_{X_{i₀}} X` is presented by the localised system, with the
legs `localizedLeg`. -/
theorem isColimitPresentation_localizedSystem {F : EtaleSheafSystem D AddCommGrpCat.{max u v + 1}}
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1}}
    {ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage (conePi c i)).obj (F.obj i) ⟶ 𝒢}
    (h : IsColimitPresentation F 𝒢 ι) :
    IsColimitPresentation (c := localizedCone D i₀ b c) (localizedSystem D i₀ b F)
      ((etaleAbelianInverseImage (localizedLimitMap D i₀ b c)).obj 𝒢)
      (localizedLeg D i₀ b c F ι) :=
  isColimitPresentation_systemBaseChange (c := c.whisker (geIndexOpFunctor i₀))
    (localizedProj D i₀ b) (localizedLimitMap D i₀ b c) (localizedCone_proj D i₀ b c)
    (F.restrictIndex i₀) (isColimitPresentation_restrictIndex i₀ h)

/-- **The localised presented system**: the restriction of a presented system to the levels
`B ×_{X_{i₀}} X_i`, `i ≥ i₀`, presented on `B ×_{X_{i₀}} X` by the restriction of its sheaf. -/
def localizedPresentedSystem (E : PresentedSystem (c := c) IsColimitPresentation) :
    PresentedSystem (c := localizedCone D i₀ b c) IsColimitPresentation :=
  presentedSystemOfIsColimitPresentation (localizedSystem D i₀ b E.sys)
    ((etaleAbelianInverseImage (localizedLimitMap D i₀ b c)).obj E.sheaf)
    (localizedLeg D i₀ b c E.sys E.ι) (isColimitPresentation_localizedSystem D i₀ b c E.pres)

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The sheaf of the localised presented system is the restriction of the sheaf of `E` to
`B ×_{X_{i₀}} X`. -/
theorem localizedPresentedSystem_sheaf (E : PresentedSystem (c := c) IsColimitPresentation) :
    (localizedPresentedSystem D i₀ b c E).sheaf =
      (etaleAbelianInverseImage (localizedLimitMap D i₀ b c)).obj E.sheaf := rfl

/-- **[Stacks, Tag 09YQ] over a localisation.** Let `X` be the limit of the `X_i`, with affine
transition morphisms over a nonempty directed set, and let `b : B ⟶ X_{i₀}` be étale with `B`
quasi-compact and quasi-separated. The cohomology of the restriction of the sheaf presenting a
system to `B ×_{X_{i₀}} X` is the colimit of the cohomology of the restrictions of the levels to
the `B ×_{X_{i₀}} X_i`, in every degree. -/
theorem isCohomologyColimit_localizedPresentedSystem [Nonempty I] (hc : IsLimit c) [Etale b]
    [CompactSpace B] [QuasiSeparatedSpace B] (E : PresentedSystem (c := c) IsColimitPresentation)
    (q : ℕ) : IsCohomologyColimit (localizedPresentedSystem D i₀ b c E) q := by
  have : Small.{max u v} ↥(Set.range (localizedDiagram D i₀ b).obj ∪
      {(localizedCone D i₀ b c).pt} : Set Scheme.{max u v}) := by
    have : Small.{max u v} ↥(Set.range (localizedDiagram D i₀ b).obj) := small_range _
    infer_instance
  obtain ⟨B', hB'⟩ := BigEtaleSite.exists_contains_of_small
    (Set.range (localizedDiagram D i₀ b).obj ∪ {(localizedCone D i₀ b c).pt} :
      Set Scheme.{max u v})
  exact isCohomologyColimit_of_isLimit.{v, u} (localizedDiagram D i₀ b)
    (localizedCone D i₀ b c) B' (fun j => hB' _ (Or.inl ⟨j, rfl⟩)) (hB' _ (Or.inr rfl))
    (isLimitLocalizedCone D i₀ b c hc) q (localizedPresentedSystem D i₀ b c E)

/-- **[Stacks, Tag 09YQ] over a localisation, for a system of injective sheaves.** Let `X` be the
limit of the `X_i`, with affine transition morphisms over a nonempty directed set, let
`b : B ⟶ X_{i₀}` be étale with `B` quasi-compact and quasi-separated, and let `E` be a presented
system all of whose sheaves are injective. Then the restriction of the sheaf `𝒢` presenting `E`
to `B ×_{X_{i₀}} X` has vanishing cohomology in every positive degree. -/
theorem subsingleton_H_localized [Nonempty I] (hc : IsLimit c) [Etale b] [CompactSpace B]
    [QuasiSeparatedSpace B] (E : PresentedSystem (c := c) IsColimitPresentation)
    (hinj : ∀ i : Iᵒᵖ, Injective (E.sys.obj i)) (q : ℕ) :
    Subsingleton (Sheaf.H ((etaleAbelianInverseImage (localizedLimitMap D i₀ b c)).obj E.sheaf)
      (q + 1)) := by
  let E' := localizedPresentedSystem D i₀ b c E
  have h09 := isCohomologyColimit_localizedPresentedSystem D i₀ b c hc E (q + 1)
  refine ⟨fun y₁ y₂ => ?_⟩
  have hzero : ∀ y : Sheaf.H E'.sheaf (q + 1), y = 0 := by
    intro y
    obtain ⟨j, x, hx⟩ := h09.exists_leg_eq y
    have : Injective (E'.sys.obj j) :=
      injective_etaleAbelianInverseImage_obj _ _ (hinj _)
    rw [← hx, Abelian.Ext.eq_zero_of_injective x, map_zero]
  exact (hzero y₁).trans (hzero y₂).symm

end Vanishing

/-! ### Sections over the base change of a quasi-compact quasi-separated étale object -/

section QcqsSections

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Scheme.{max u v})
  (c : Cone D) (E : PresentedSystem (c := c) IsColimitPresentation) (i₀ : I)
  (W : (D.obj (op i₀)).Etale)

/-- The comparison `W_X ⟶ (W_i)_X` of iterated base changes. -/
abbrev qcqsLegComparison (j : (GeIndex i₀)ᵒᵖ) :
    (smallEtaleBaseChange (c.π.app (op i₀))).obj W ⟶
      (smallEtaleBaseChange (c.π.app ((geIndexOpFunctor i₀).obj j))).obj
        ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W) :=
  (smallEtaleBaseChangeComp' (c.π.app ((geIndexOpFunctor i₀).obj j)) (D.map (geIndexToBase i₀ j))
    (c.π.app (op i₀)) (c.w (geIndexToBase i₀ j)).symm).hom.app W

/-- **The leg on sections**, `F_i(W_i) ⟶ 𝓕(W_X)`: the transpose of the presentation map
`ι_i : f_i^{-1}F_i ⟶ 𝓕` over `W_i`, followed by restriction along the comparison of iterated base
changes. -/
def qcqsSectionsLeg (j : (GeIndex i₀)ᵒᵖ) :
    (E.sys.obj ((geIndexOpFunctor i₀).obj j)).obj.obj
        (op ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W)) ⟶
      E.sheaf.obj.obj (op ((smallEtaleBaseChange (c.π.app (op i₀))).obj W)) :=
  etaleTransposeSection.{max u v + 1, max u v} (c.π.app ((geIndexOpFunctor i₀).obj j))
      (E.ι ((geIndexOpFunctor i₀).obj j))
      ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W) ≫
    E.sheaf.obj.map (qcqsLegComparison D c i₀ W j).op

/-- The comparison `W_k ⟶ (W_j)_k` of iterated base changes along a transition. -/
abbrev qcqsTransitionComparison {j k : (GeIndex i₀)ᵒᵖ} (b : k ⟶ j) :
    (smallEtaleBaseChange (D.map (geIndexToBase i₀ k))).obj W ⟶
      (smallEtaleBaseChange (D.map ((geIndexOpFunctor i₀).map b))).obj
        ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W) :=
  (smallEtaleBaseChangeComp' (D.map ((geIndexOpFunctor i₀).map b)) (D.map (geIndexToBase i₀ j))
    (D.map (geIndexToBase i₀ k))
    (by rw [← D.map_comp, geIndexToBase_comp])).hom.app W

/-- **The transition on sections**, `F_j(W_j) ⟶ F_k(W_k)`: the transpose of the transition map of
the system over `W_j`, followed by restriction along the comparison of iterated base changes. -/
def qcqsSectionsTransition {j k : (GeIndex i₀)ᵒᵖ} (b : k ⟶ j) :
    (E.sys.obj ((geIndexOpFunctor i₀).obj j)).obj.obj
        (op ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W)) ⟶
      (E.sys.obj ((geIndexOpFunctor i₀).obj k)).obj.obj
        (op ((smallEtaleBaseChange (D.map (geIndexToBase i₀ k))).obj W)) :=
  etaleTransposeSection.{max u v + 1, max u v} (D.map ((geIndexOpFunctor i₀).map b))
      (systemTransitionMap E.sys ((geIndexOpFunctor i₀).map b))
      ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W) ≫
    (E.sys.obj ((geIndexOpFunctor i₀).obj k)).obj.map (qcqsTransitionComparison D i₀ W b).op

section Localized

variable [Etale W.hom] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- The comparison of iterated base changes is the morphism with components `a` and the second
projection, as soon as `a` lies over the first projection and over `f`. -/
private theorem smallEtaleBaseChangeComp'_hom_left_eq_lift {W X Y : Scheme.{u}} (f : W ⟶ X)
    (g : X ⟶ Y) (fg : W ⟶ Y) (hfg : fg = f ≫ g) (U : Y.Etale)
    (a : pullback U.hom fg ⟶ pullback U.hom g) (ha₁ : a ≫ pullback.fst _ _ = pullback.fst _ _)
    (ha₂ : a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f) :
    ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U).left =
      pullback.lift a (pullback.snd _ _) ha₂ := by
  have h₁ := smallEtaleBaseChangeComp'_fst_fst f g fg hfg U
  have h₂ := smallEtaleBaseChange_fst_snd f g ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U)
  have h₃ := smallEtaleBaseChange_w f ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U)
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · exact (Category.assoc _ _ _).trans (h₁.trans (ha₁.symm.trans (congrArg (· ≫ _)
      (pullback.lift_fst _ _ _).symm)))
  · exact (Category.assoc _ _ _).trans (h₂.trans (ha₂.symm.trans (congrArg (· ≫ _)
      (pullback.lift_fst _ _ _).symm)))
  · exact h₃.trans (pullback.lift_snd _ _ _).symm

omit [IsDirected I (· ≤ ·)] [Etale W.hom]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The comparison of iterated base changes is the morphism with components the projections of
the localised cone and the limit map. -/
theorem qcqsLegComparison_left (j : (GeIndex i₀)ᵒᵖ) :
    (qcqsLegComparison D c i₀ W j).left =
      pullback.lift (conePi (localizedCone D i₀ W.hom c) j) (localizedLimitMap D i₀ W.hom c)
        (localizedCone_proj D i₀ W.hom c j) := by
  exact smallEtaleBaseChangeComp'_hom_left_eq_lift _ _ _ _ W _ (localizedCone_π_fst D i₀ W.hom c j)
    (localizedCone_π_snd D i₀ W.hom c j)

omit [IsDirected I (· ≤ ·)] [Etale W.hom]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The comparison of iterated base changes along a transition is the morphism with components
the transition of the localised system and the projection. -/
theorem qcqsTransitionComparison_left {j k : (GeIndex i₀)ᵒᵖ} (b : k ⟶ j) :
    (qcqsTransitionComparison D i₀ W b).left =
      pullback.lift ((localizedDiagram D i₀ W.hom).map b) ((localizedProj D i₀ W.hom).app k)
        ((localizedProj D i₀ W.hom).naturality b) := by
  exact smallEtaleBaseChangeComp'_hom_left_eq_lift _ _ _ _ W _
    (localizedDiagram_map_fst D i₀ W.hom b) (localizedDiagram_map_snd D i₀ W.hom b)

/-- The identification of the sections of `F_j` over `W_j` with global sections of its
restriction. -/
abbrev qcqsLevelSections (j : (GeIndex i₀)ᵒᵖ) :
    (E.sys.obj ((geIndexOpFunctor i₀).obj j)).obj.obj
        (op ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W)) ⟶
      ((localizedPresentedSystem D i₀ W.hom c E).sys.obj j).obj.obj
        (op (Etale.mk (𝟙 ((localizedDiagram D i₀ W.hom).obj j)))) :=
  etaleSectionsPullback ((localizedProj D i₀ W.hom).app j)
    (Etale.mk ((localizedProj D i₀ W.hom).app j)) (𝟙 _) (Category.id_comp _)
    (E.sys.obj ((geIndexOpFunctor i₀).obj j))

/-- The identification of the sections of `𝓕` over `W_X` with global sections of its
restriction. -/
abbrev qcqsLimitSections :
    E.sheaf.obj.obj (op ((smallEtaleBaseChange (c.π.app (op i₀))).obj W)) ⟶
      (localizedPresentedSystem D i₀ W.hom c E).sheaf.obj.obj
        (op (Etale.mk (𝟙 (localizedCone D i₀ W.hom c).pt))) :=
  etaleSectionsPullback (localizedLimitMap D i₀ W.hom c)
    (Etale.mk (localizedLimitMap D i₀ W.hom c)) (𝟙 _) (Category.id_comp _) E.sheaf

/-- Restricting along a morphism `g` of étale objects, after pulling back along the identity of the
source, is pulling back along any `r` equal to the left component of `g`. -/
private theorem map_comp_etaleSectionsPullback_of_left_eq {Z : Scheme.{u}} {W₁ W₂ : Z.Etale}
    (g : W₂ ⟶ W₁) (p : W₂.left ⟶ Z) (r : W₂.left ⟶ W₁.left) (hp : 𝟙 W₂.left ≫ W₂.hom = p)
    (hg : g.left = r) (hr : r ≫ W₁.hom = p)
    (M : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    M.obj.map g.op ≫ etaleSectionsPullback p W₂ (𝟙 W₂.left) hp M =
      etaleSectionsPullback p W₁ r hr M :=
  (map_comp_etaleSectionsPullback p g (𝟙 W₂.left) hp M).trans
    (etaleSectionsPullback_congr _ _ ((Category.id_comp _).trans hg) _ hr M)

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- **The leg of the localised presented system on global sections is the leg on sections**,
through the identifications of global sections of inverse images along étale morphisms with
sections over those morphisms. -/
theorem legSection_qcqsLevelSections (j : (GeIndex i₀)ᵒᵖ)
    (t : (E.sys.obj ((geIndexOpFunctor i₀).obj j)).obj.obj
      (op ((smallEtaleBaseChange (D.map (geIndexToBase i₀ j))).obj W))) :
    (localizedPresentedSystem D i₀ W.hom c E).legSection j (qcqsLevelSections D c E i₀ W j t) =
      qcqsLimitSections D c E i₀ W (qcqsSectionsLeg D c E i₀ W j t) := by
  have G := etaleSectionsPullback_comp_squareLeg (conePi (localizedCone D i₀ W.hom c) j)
    ((localizedProj D i₀ W.hom).app j) (localizedLimitMap D i₀ W.hom c)
    (conePi (c.whisker (geIndexOpFunctor i₀)) j) (localizedCone_proj D i₀ W.hom c j)
    (E.sys.obj ((geIndexOpFunctor i₀).obj j)) E.sheaf (E.ι ((geIndexOpFunctor i₀).obj j))
  have R := map_comp_etaleSectionsPullback_of_left_eq (qcqsLegComparison D c i₀ W j)
    (localizedLimitMap D i₀ W.hom c) _ (Category.id_comp _) (qcqsLegComparison_left D c i₀ W j)
    (pullback.lift_snd _ _ (localizedCone_proj D i₀ W.hom c j)) E.sheaf
  have hM : qcqsLevelSections D c E i₀ W j ≫
        (localizedPresentedSystem D i₀ W.hom c E).legSection j =
      qcqsSectionsLeg D c E i₀ W j ≫ qcqsLimitSections D c E i₀ W := by
    refine G.trans ?_
    exact (congrArg (_ ≫ ·) R.symm).trans (Category.assoc _ _ _).symm
  convert ConcreteCategory.congr_hom hM t using 1

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- **The transition of the localised presented system on global sections is the transition on
sections.** -/
theorem etaleSectionsTransition_qcqsLevelSections {j k : (GeIndex i₀)ᵒᵖ} (b : k ⟶ j) :
    qcqsLevelSections D c E i₀ W j ≫
        etaleSectionsTransition (localizedPresentedSystem D i₀ W.hom c E).sys b =
      qcqsSectionsTransition D c E i₀ W b ≫ qcqsLevelSections D c E i₀ W k := by
  have G := etaleSectionsPullback_comp_squareLeg ((localizedDiagram D i₀ W.hom).map b)
    ((localizedProj D i₀ W.hom).app j) ((localizedProj D i₀ W.hom).app k)
    (D.map ((geIndexOpFunctor i₀).map b)) ((localizedProj D i₀ W.hom).naturality b)
    (E.sys.obj ((geIndexOpFunctor i₀).obj j)) (E.sys.obj ((geIndexOpFunctor i₀).obj k))
    (systemTransitionMap E.sys ((geIndexOpFunctor i₀).map b))
  have R := map_comp_etaleSectionsPullback_of_left_eq (qcqsTransitionComparison D i₀ W b)
    ((localizedProj D i₀ W.hom).app k) _ (Category.id_comp _)
    (qcqsTransitionComparison_left D i₀ W b)
    (pullback.lift_snd _ _ ((localizedProj D i₀ W.hom).naturality b))
    (E.sys.obj ((geIndexOpFunctor i₀).obj k))
  have hT : systemTransitionMap (localizedPresentedSystem D i₀ W.hom c E).sys b =
      baseChangeTransition (localizedProj D i₀ W.hom) (E.sys.restrictIndex i₀) b :=
    systemTransitionMap_systemBaseChange _ _ b
  unfold etaleSectionsTransition
  rw [hT]
  refine G.trans ?_
  exact (congrArg (_ ≫ ·) R.symm).trans (Category.assoc _ _ _).symm

/-- **Transporting a colimit description of abelian groups along bijections.** If the groups `A'_j`
with legs to `M'` and transitions have the two properties of a filtered colimit — every element of
`M'` comes from some `A'_j`, and an element killed by its leg is killed by a transition — and the
`A_j`, `M` are identified with them by bijections compatible with the legs and the transitions,
then the `A_j` with their legs to `M` have the same two properties. -/
theorem colimit_transfer {J : Type*} [Category* J] {A A' : J → AddCommGrpCat.{w}}
    {M M' : AddCommGrpCat.{w}} (leg : ∀ j, A j ⟶ M) (leg' : ∀ j, A' j ⟶ M')
    (trans : ∀ {j k : J}, (k ⟶ j) → (A j ⟶ A k)) (trans' : ∀ {j k : J}, (k ⟶ j) → (A' j ⟶ A' k))
    (Θ : ∀ j, A j ⟶ A' j) (Θ' : M ⟶ M') (hΘ : ∀ j, Function.Bijective (Θ j))
    (hΘ' : Function.Bijective Θ') (hleg : ∀ j t, leg' j (Θ j t) = Θ' (leg j t))
    (htrans : ∀ {j k : J} (b : k ⟶ j) t, trans' b (Θ j t) = Θ k (trans b t))
    (hS : ∀ y, ∃ j s, leg' j s = y)
    (hI : ∀ j s, leg' j s = 0 → ∃ (k : J) (b : k ⟶ j), trans' b s = 0) :
    (∀ x, ∃ j t, leg j t = x) ∧ (∀ j t, leg j t = 0 → ∃ (k : J) (b : k ⟶ j), trans b t = 0) := by
  refine ⟨fun x => ?_, fun j t ht => ?_⟩
  · obtain ⟨j, s, hs⟩ := hS (Θ' x)
    obtain ⟨t, rfl⟩ := (hΘ j).2 s
    exact ⟨j, t, hΘ'.1 ((hleg j t).symm.trans hs)⟩
  · have h0 : leg' j (Θ j t) = 0 := by rw [hleg, ht, map_zero]
    obtain ⟨k, b, hb⟩ := hI j _ h0
    refine ⟨k, b, (hΘ k).1 ?_⟩
    rw [← htrans, hb, map_zero]

/-- `colimit_transfer` at the degree-zero statement of [Stacks, Tag 09YQ] for a presented system,
read on global sections. -/
theorem isCohomologyColimit_zero_transfer {I' : Type V} [Preorder I'] {D' : I'ᵒᵖ ⥤ Scheme.{U}}
    {c' : Cone D'} {P : (F : EtaleSheafSystem D' AddCommGrpCat.{U + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c'.pt) AddCommGrpCat.{U + 1}) →
      (∀ i : I'ᵒᵖ, (etaleAbelianInverseImage (conePi c' i)).obj (F.obj i) ⟶ 𝒢) → Prop}
    (E'' : PresentedSystem (c := c') P) (h : IsCohomologyColimit E'' 0)
    {A : I'ᵒᵖ → AddCommGrpCat.{U + 1}} {M : AddCommGrpCat.{U + 1}}
    (leg : ∀ j, A j ⟶ M) (trans : ∀ {j k : I'ᵒᵖ}, (k ⟶ j) → (A j ⟶ A k))
    (Θ : ∀ j, A j ⟶ (E''.sys.obj j).obj.obj (op (Etale.mk (𝟙 (D'.obj j)))))
    (Θ' : M ⟶ E''.sheaf.obj.obj (op (Etale.mk (𝟙 c'.pt))))
    (hΘ : ∀ j, Function.Bijective (Θ j)) (hΘ' : Function.Bijective Θ')
    (hleg : ∀ j t, E''.legSection j (Θ j t) = Θ' (leg j t))
    (htrans : ∀ {j k : I'ᵒᵖ} (b : k ⟶ j),
      Θ j ≫ etaleSectionsTransition E''.sys b = trans b ≫ Θ k) :
    (∀ x, ∃ j t, leg j t = x) ∧ (∀ j t, leg j t = 0 → ∃ (k : I'ᵒᵖ) (b : k ⟶ j), trans b t = 0) :=
  colimit_transfer leg E''.legSection trans (etaleSectionsTransition E''.sys) Θ Θ' hΘ hΘ' hleg
    (fun b t => by
      have := ConcreteCategory.congr_hom (htrans b) t
      simpa only [ConcreteCategory.comp_apply] using this)
    ((isCohomologyColimit_zero_iff E'').mp h).1 ((isCohomologyColimit_zero_iff E'').mp h).2

variable [Nonempty I] (hc : IsLimit c) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
include hc

/-- The two properties of a filtered colimit, for the sections over the base changes of `W`. -/
theorem qcqsSections_isColimit :
    (∀ x, ∃ j t, qcqsSectionsLeg D c E i₀ W j t = x) ∧
      (∀ j t, qcqsSectionsLeg D c E i₀ W j t = 0 →
        ∃ (k : (GeIndex i₀)ᵒᵖ) (b : k ⟶ j), qcqsSectionsTransition D c E i₀ W b t = 0) := by
  have : CompactSpace ↥((𝟭 Scheme.{max u v}).obj W.left) := inferInstanceAs (CompactSpace W.left)
  have : QuasiSeparatedSpace ↥((𝟭 Scheme.{max u v}).obj W.left) :=
    inferInstanceAs (QuasiSeparatedSpace W.left)
  have h09 := (isCohomologyColimit_zero_iff _).mp
    (isCohomologyColimit_localizedPresentedSystem D i₀ W.hom c hc E 0)
  refine isCohomologyColimit_zero_transfer (localizedPresentedSystem D i₀ W.hom c E)
    (isCohomologyColimit_localizedPresentedSystem D i₀ W.hom c hc E 0)
    (qcqsSectionsLeg D c E i₀ W) (qcqsSectionsTransition D c E i₀ W)
    (qcqsLevelSections D c E i₀ W) (qcqsLimitSections D c E i₀ W) ?_ ?_ ?_ ?_
  · exact fun j => bijective_etaleSectionsPullback_self ((localizedProj D i₀ W.hom).app j)
      (E.sys.obj ((geIndexOpFunctor i₀).obj j))
  · exact bijective_etaleSectionsPullback_self (localizedLimitMap D i₀ W.hom c) E.sheaf
  · intro j t
    convert legSection_qcqsLevelSections D c E i₀ W j t using 2
  · intro j k b
    convert etaleSectionsTransition_qcqsLevelSections D c E i₀ W b using 2

end Localized

end QcqsSections

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
