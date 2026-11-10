module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment.SectionContainment

/-!
# The arrow containment of Stacks 03FM: the pair named by the point `u'`

In the fibre situation of Stacks 04RL at a point `u`, this file identifies the pair named at a
restriction of the point `u' = (u, Z_u)` with the base change `Z_u ×_{Spec κ(u)} Spec k`
(`AlgebraicGeometry.Space.objectsPair_restrict_fibrePoint_isBaseChange`), shows that membership
in `Z_u` is the condition that the target of the arrow be `u`
(`AlgebraicGeometry.Space.exists_lift_fibrePair_iff`), and combines the two into the form the
containment consumes (`AlgebraicGeometry.Space.ArrowToPoint`,
`AlgebraicGeometry.Space.cutsOut_fibrePoint`).
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

/-- Pullbacks of presheaves on `BigFppfOver C S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_FibrePair
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_FibrePair
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The pair named by the point `u'` -/

section Fibre

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  (hP : C.Contains (pullback G.source G.target).left)
  (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))
  (W : (G.source.left.fiber u).Opens)
  (hW : ∀ x : G.source.left.fiber u,
    x ∈ W ↔ G.target.left (G.source.left.fiberι u x) = u)
  (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u))

include hW in
/-- The inclusion of the object space of the finite part into the finite part presheaf carries
the point `u'` to the section which the pair `(u, Z_u)` names: `u'` is by construction the
image of that section under the inverse of the comparison isomorphism of the object space with
the finite part with section. -/
theorem objectsInclusion_app_fibrePoint :
    F.objectsInclusion.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) =
      fibrePresheafSection G C hS hU hR u hK hP W hWfin := by
  have h2 : F.objectsEquiv.hom.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) =
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection G C hS hU hR u hK hP F W hW hWfin⟩ :=
    congrArg (fun k => k.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection G C hS hU hR u hK hP F W hW hWfin⟩)
      F.objectsEquiv.inv_hom_id
  exact congrArg (fun z => (finitePartWithSection C S hS
      (G.realization C hS hU hR hP).source F.unit F.unit_source).toSubfunctor.ι.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z) h2

include hW in
/-- The classifying morphism of the pair `(u, Z_u)` is the point `u'`, read as a morphism out
of the presheaf represented by `Spec κ(u)`, followed by the inclusion of the object space of
the finite part. -/
theorem fibrePoint_comp_objectsInclusion :
    yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) ≫ F.objectsInclusion =
      (finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
        (AlgebraicGeometry.schemeSpace
          (schemeSiteObject C hS (X := residueOver G u) hK))).1.symm
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact objectsInclusion_app_fibrePoint G C hS hU hR u hK hP F W hW hWfin

include hW in
/-- **The restriction of the point `u'` along a morphism `Spec k ⟶ Spec κ(u)`.**  The pair
which the object space of the finite part names at the restricted point is the base change of
the pair `(u, Z_u)` along that morphism: on points, `Z_u ×_{Spec κ(u)} Spec k`.

This is the second missing ingredient of the third step of the proof of Stacks 03FM. -/
theorem objectsPair_restrict_fibrePoint_isBaseChange
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK) :
    (F.objectsPair V (yoneda.map h ≫
          yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).toBase.hom =
        yoneda.map h ≫
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom ∧
      ∃ j : (F.objectsPair V (yoneda.map h ≫
            yonedaEquiv.symm
              (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).subspace.toFunctor ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
        IsPullback ((F.objectsPair V (yoneda.map h ≫
              yonedaEquiv.symm
                (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).subspace.ι ≫
            pullback.fst (F.objectsPair V (yoneda.map h ≫
                yonedaEquiv.symm
                  (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).toBase.hom
              (G.realization C hS hU hR hP).source.hom) j (yoneda.map h)
          ((fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι ≫
            pullback.fst
              (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom
              (G.realization C hS hU hR hP).source.hom) ∧
        j ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι ≫
            pullback.snd
              (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom
              (G.realization C hS hU hR hP).source.hom =
          (F.objectsPair V (yoneda.map h ≫
            yonedaEquiv.symm
              (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).subspace.ι ≫
            pullback.snd (F.objectsPair V (yoneda.map h ≫
                yonedaEquiv.symm
                  (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).toBase.hom
              (G.realization C hS hU hR hP).source.hom := by
  have hp : (finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
        (AlgebraicGeometry.schemeSpace
          (schemeSiteObject C hS (X := residueOver G u) hK))).1
        (yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) ≫
          F.objectsInclusion) =
      fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin :=
    (congrArg (fun v => (finiteOpenSubspaceEquiv C S hS
          (G.realization C hS hU hR hP).source
          (AlgebraicGeometry.schemeSpace
            (schemeSiteObject C hS (X := residueOver G u) hK))).1 v)
        (fibrePoint_comp_objectsInclusion G C hS hU hR u hK hP F W hW hWfin)).trans
      (Equiv.apply_symm_apply _ _)
  have spec := (finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
      (AlgebraicGeometry.schemeSpace
        (schemeSiteObject C hS (X := residueOver G u) hK))).2
      (yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) ≫
        F.objectsInclusion)
      V (yoneda.map h)
  rwa [hp] at spec

/-- The open subspace of the pair `(u, Z_u)` is the image of the open `Z_u` of the fibre. -/
theorem fibreFiniteOpenSubspace_subspace :
    (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace =
      Subfunctor.range (fibreOpenPresheafMap G C hS hU hR u hK W) := rfl

/-- The base of the pair `(u, Z_u)` is the canonical morphism `Spec κ(u) ⟶ U`. -/
theorem fibreFiniteOpenSubspace_toBase_hom :
    (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
      yoneda.map (residueSiteMap G C hS hU u hK) := rfl

/-- The source of the realization is the Yoneda image of the source read in the site. -/
theorem realization_source_hom :
    (G.realization C hS hU hR hP).source.hom =
      yoneda.map (sourceSiteMap G C hS hU hR) := rfl

/-- The target of the realization is the Yoneda image of the target read in the site. -/
theorem realization_target_hom :
    (G.realization C hS hU hR hP).target.hom =
      yoneda.map (targetSiteMap G C hS hU hR) := rfl

/-- The underlying morphism of schemes of the target read in the site is the target. -/
theorem toScheme_map_targetSiteMap :
    (BigFppfOver.toScheme C S hS).map (targetSiteMap G C hS hU hR) = G.target.left := rfl

/-- The underlying morphism of schemes of the canonical point read in the site is the
canonical morphism from the spectrum of the residue field. -/
theorem toScheme_map_residueSiteMap :
    (BigFppfOver.toScheme C S hS).map (residueSiteMap G C hS hU u hK) =
      G.objects.left.fromSpecResidueField u := rfl

include hW in
/-- **Membership in `Z_u`, stated on sections.**  A section of the ambient fibre product
`Spec κ(u) ×_{u, U, s} R` over a scheme of the site factors through the open subspace of the
pair `(u, Z_u)` exactly when the target of its arrow carries every point of the test scheme
to `u`.

This is the whole content of the choice of `Z_u` made by the étale localization of
Situation 04RL: `Z_u` is the open and closed piece of the fibre `F_u` whose support is the set
of arrows from `u` to `u`, so membership in it is the condition that the target of the arrow
be `u`, a condition on the target of the arrow alone. -/
theorem exists_lift_fibrePair_iff (V' : BigFppfOver C S hS)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR)
    (hc : yoneda.map base ≫
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
        yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom) :
    (∃ n : yoneda.obj V' ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
        n ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
      ∀ p : (BigFppfOver.toScheme C S hS).obj V',
        G.target.left ((BigFppfOver.toScheme C S hS).map arr p) = u := by
  have hmono := mono_fibreOpenPresheafMap G C hS hU hR u hK W
  have hc' : yoneda.map base ≫ yoneda.map (residueSiteMap G C hS hU u hK) =
      yoneda.map arr ≫ yoneda.map (sourceSiteMap G C hS hU hR) := hc
  have hc₀ : base ≫ residueSiteMap G C hS hU u hK = arr ≫ sourceSiteMap G C hS hU hR :=
    yoneda.map_injective ((yoneda.map_comp _ _).trans
      (hc'.trans (yoneda.map_comp _ _).symm))
  have hk₀ : yoneda.map (pullback.lift base arr hc₀) ≫
      (fibreYonedaIso G C hS hU hR u hK).hom =
      pullback.lift (yoneda.map base) (yoneda.map arr) hc := by
    refine pullback.hom_ext ?_ ?_
    · refine Eq.trans ?_ (pullback.lift_fst (yoneda.map base) (yoneda.map arr) hc).symm
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← yoneda.map_comp,
        pullback.lift_fst]
    · refine Eq.trans ?_ (pullback.lift_snd (yoneda.map base) (yoneda.map arr) hc).symm
      rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← yoneda.map_comp,
        pullback.lift_snd]
  have hiso : ∀ l : yoneda.obj V' ⟶ yoneda.obj (fibreOpenSite G C hS hU hR u hK W),
      (l ≫ fibreOpenPresheafMap G C hS hU hR u hK W =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
        l ≫ yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W) =
          yoneda.map (pullback.lift base arr hc₀) := by
    intro l
    rw [← hk₀]
    constructor
    · intro h
      exact (Iso.cancel_iso_hom_right _ _ (fibreYonedaIso G C hS hU hR u hK)).1
        ((Category.assoc l (yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W))
          (fibreYonedaIso G C hS hU hR u hK).hom).trans h)
    · intro h
      exact (Category.assoc l (yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W))
          (fibreYonedaIso G C hS hU hR u hK).hom).symm.trans
        (congrArg (fun z => z ≫ (fibreYonedaIso G C hS hU hR u hK).hom) h)
  have step1 : (∃ n : yoneda.obj V' ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
        n ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
      ∃ l : yoneda.obj V' ⟶ yoneda.obj (fibreOpenSite G C hS hU hR u hK W),
        l ≫ fibreOpenPresheafMap G C hS hU hR u hK W =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc :=
    exists_lift_range_iff (fibreOpenPresheafMap G C hS hU hR u hK W) _
  have step2 : (∃ l : yoneda.obj V' ⟶ yoneda.obj (fibreOpenSite G C hS hU hR u hK W),
        l ≫ fibreOpenPresheafMap G C hS hU hR u hK W =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
      ∃ l₀ : V' ⟶ fibreOpenSite G C hS hU hR u hK W,
        l₀ ≫ fibreOpenSiteMap G C hS hU hR u hK W = pullback.lift base arr hc₀ := by
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨yoneda.preimage l, yoneda.map_injective ?_⟩
      rw [yoneda.map_comp, yoneda.map_preimage]
      exact (hiso l).1 hl
    · rintro ⟨l₀, hl₀⟩
      refine ⟨yoneda.map l₀, (hiso (yoneda.map l₀)).2 ?_⟩
      rw [← yoneda.map_comp, hl₀]
  have hmem : ∀ y : (BigFppfOver.toScheme C S hS).obj (fibreSiteObject G C hS hU hR u hK),
      y ∈ Set.range (fibreOpenImmersion G C hS hU hR u hK W).base ↔
        (etaleLocalFibreIso G C hS hU hR u hK).hom y ∈ W := by
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      have h1 : (etaleLocalFibreIso G C hS hU hR u hK).hom
          ((fibreOpenImmersion G C hS hU hR u hK W) x) = W.ι x := by
        change ((W.ι ≫ (etaleLocalFibreIso G C hS hU hR u hK).inv) ≫
          (etaleLocalFibreIso G C hS hU hR u hK).hom) x = W.ι x
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [h1]
      have hx : W.ι x ∈ Set.range W.ι.base := ⟨x, rfl⟩
      rwa [Scheme.Opens.range_ι] at hx
    · intro hy
      refine ⟨⟨(etaleLocalFibreIso G C hS hU hR u hK).hom y, hy⟩, ?_⟩
      change (etaleLocalFibreIso G C hS hU hR u hK).inv
        ((etaleLocalFibreIso G C hS hU hR u hK).hom y) = y
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
  have htgt : ∀ p : (BigFppfOver.toScheme C S hS).obj V',
      G.source.left.fiberι u ((etaleLocalFibreIso G C hS hU hR u hK).hom
        ((BigFppfOver.toScheme C S hS).map (pullback.lift base arr hc₀) p)) =
        (BigFppfOver.toScheme C S hS).map arr p := by
    intro p
    have h := congrArg (fun k => k ((BigFppfOver.toScheme C S hS).map
        (pullback.lift base arr hc₀) p)) (fibreIso_hom_comp_fiberι G C hS hU hR u hK)
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    have h2 : (BigFppfOver.toScheme C S hS).map (pullback.lift base arr hc₀) ≫
        (BigFppfOver.toScheme C S hS).map
          (pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) =
        (BigFppfOver.toScheme C S hS).map arr := by
      rw [← Functor.map_comp, pullback.lift_snd]
    exact (Scheme.Hom.comp_apply _ _ p).symm.trans (congrArg (fun k => k p) h2)
  refine step1.trans (step2.trans
    (((exists_siteOpen_lift_iff (fibreSiteObject G C hS hU hR u hK)
        (fibreOpenImmersion G C hS hU hR u hK W)
        (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W) V'
        (pullback.lift base arr hc₀)).trans
      ((exists_scheme_lift_iff_range_subset _
        (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W) _).trans ?_))))
  rw [Set.range_subset_iff]
  exact forall_congr' fun p => (hmem _).trans ((hW _).trans (by rw [htgt p]))

include hW in
/-- The point `u'`, read as a morphism out of the presheaf represented by `Spec κ(u)`,
followed by the étale projection `g : U' ⟶ U`, is the canonical morphism
`u : Spec κ(u) ⟶ U`. -/
theorem fibrePoint_comp_objectProjection :
    yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) ≫
        F.objectProjection.hom =
      yoneda.map (residueSiteMap G C hS hU u hK) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (objectProjection_fibrePoint G C hS hU hR u hK hP F W hW hWfin).trans
    (yonedaEquiv_yoneda_map _).symm

include hW in
/-- **Membership in `Z_univ` over the restriction of the point `u'`, reduced to the target
condition.**  This is the composite of the two missing ingredients of the third step of the
proof of Stacks 03FM: a section of the ambient fibre product whose `U'`-component is the
restriction of `u'` lies in `Z_univ` exactly when the target of its arrow carries every point
of the test scheme to `u`. -/
theorem exists_lift_universalOpen_fibrePoint_iff
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (hbase : yoneda.map base = φ ≫ yoneda.map h)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR)
    (hc' : (φ ≫ (yoneda.map h ≫
          yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))) ≫
        F.universalOpen.toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom) :
    (∃ n : yoneda.obj V' ⟶ F.universalOpen.subspace.toFunctor,
        n ≫ F.universalOpen.subspace.ι =
          pullback.lift (φ ≫ (yoneda.map h ≫
            yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin)))
            (yoneda.map arr) hc') ↔
      ∀ p : (BigFppfOver.toScheme C S hS).obj V',
        G.target.left ((BigFppfOver.toScheme C S hS).map arr p) = u := by
  have hbc := objectsPair_restrict_fibrePoint_isBaseChange G C hS hU hR u hK hP F W hW hWfin V h
  have hc : φ ≫ (F.objectsPair V (yoneda.map h ≫
        yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom :=
    (congrArg (fun z => φ ≫ z) (F.objectsPair_toBase_hom V _)).trans
      ((Category.assoc φ _ F.universalOpen.toBase.hom).symm.trans hc')
  have hc'' : (φ ≫ yoneda.map h) ≫
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom :=
    (Category.assoc φ (yoneda.map h) _).trans
      ((congrArg (fun z => φ ≫ z) hbc.1.symm).trans hc)
  have hcB : yoneda.map base ≫
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom :=
    (congrArg (fun z => z ≫
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom) hbase).trans hc''
  have hlift : pullback.lift (φ ≫ yoneda.map h) (yoneda.map arr) hc'' =
      pullback.lift (yoneda.map base) (yoneda.map arr) hcB :=
    pullback_lift_congr _ _ _ _ hc'' hcB hbase.symm rfl
  obtain ⟨jb, hjb, hjbsnd⟩ := hbc.2
  exact (F.exists_lift_universalOpen_iff V _ φ (yoneda.map arr) hc hc').symm.trans
    ((exists_lift_of_pairSquares (G.realization C hS hU hR hP).source
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin)
        (F.objectsPair V _) (yoneda.map h) jb hjb hjbsnd φ (yoneda.map arr) hc hc'').trans
      ((iff_of_eq (congrArg (fun z => ∃ n : yoneda.obj V' ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
          n ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι = z)
        hlift)).trans
        (exists_lift_fibrePair_iff G C hS hU hR u hK hP W hW hWfin V' base arr hcB)))

include hW in
/-- The base component of a section of the ambient fibre product over the restriction of the
point `u'`, read in the site. -/
theorem base_eq_of_fibrePoint
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (hbase : yoneda.map base = φ ≫ yoneda.map h) :
    (φ ≫ (yoneda.map h ≫
        yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))) ≫
      F.universalOpen.toBase.hom =
      yoneda.map (base ≫ residueSiteMap G C hS hU u hK) :=
  (Category.assoc φ _ F.universalOpen.toBase.hom).trans
    ((congrArg (fun z => φ ≫ z) (Category.assoc (yoneda.map h) _
        F.universalOpen.toBase.hom)).trans
      ((congrArg (fun z => φ ≫ yoneda.map h ≫ z)
          ((congrArg (fun z =>
              yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) ≫ z)
            F.universalOpen_toBase_hom).trans
            (fibrePoint_comp_objectProjection G C hS hU hR u hK hP F W hW hWfin))).trans
        ((Category.assoc φ (yoneda.map h)
            (yoneda.map (residueSiteMap G C hS hU u hK))).symm.trans
          ((congrArg (fun z => z ≫ yoneda.map (residueSiteMap G C hS hU u hK))
              hbase.symm).trans
            (yoneda.map_comp base (residueSiteMap G C hS hU u hK)).symm))))

/-- The arrow component of a section, followed by the target of the realization, read in the
site. -/
theorem arr_comp_target (V' : BigFppfOver C S hS)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR) :
    yoneda.map arr ≫ (G.realization C hS hU hR hP).target.hom =
      yoneda.map (arr ≫ targetSiteMap G C hS hU hR) :=
  (yoneda.map_comp arr (targetSiteMap G C hS hU hR)).symm

/-- Two morphisms of the site with equal composites agree after applying the underlying
morphisms of schemes to any point of the test scheme. -/
private theorem toScheme_map_apply_eq {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {V' A B Z : BigFppfOver C S hS} (a : V' ⟶ A) (b : V' ⟶ B) (f : A ⟶ Z) (g : B ⟶ Z)
    (h : a ≫ f = b ≫ g) (p : (BigFppfOver.toScheme C S hS).obj V') :
    (BigFppfOver.toScheme C S hS).map f ((BigFppfOver.toScheme C S hS).map a p) =
      (BigFppfOver.toScheme C S hS).map g ((BigFppfOver.toScheme C S hS).map b p) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    h]

/-- The predicate on arrows which the open `Z_u` cuts out: the arrow carries every point of
the test scheme to a point of the arrow scheme whose target is `u`.  It is stated through the
morphism of the site whose Yoneda image the given morphism of presheaves is. -/
def ArrowToPoint (V' : BigFppfOver C S hS)
    (ψ : yoneda.obj V' ⟶ (G.realization C hS hU hR hP).arrows.obj) : Prop :=
  ∃ arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR, yoneda.map arr = ψ ∧
    ∀ p : (BigFppfOver.toScheme C S hS).obj V',
      G.target.left ((BigFppfOver.toScheme C S hS).map arr p) = u

/-- **The predicate cut out by `Z_u` depends on an arrow only through its target.** -/
theorem targetInvariant_arrowToPoint (V' : BigFppfOver C S hS)
    (ψ₁ ψ₂ : yoneda.obj V' ⟶ (G.realization C hS hU hR hP).arrows.obj)
    (hψ : ψ₁ ≫ (G.realization C hS hU hR hP).target.hom =
      ψ₂ ≫ (G.realization C hS hU hR hP).target.hom) :
    ArrowToPoint G C hS hU hR u hP V' ψ₁ ↔ ArrowToPoint G C hS hU hR u hP V' ψ₂ := by
  have key : ∀ α β : yoneda.obj V' ⟶ (G.realization C hS hU hR hP).arrows.obj,
      α ≫ (G.realization C hS hU hR hP).target.hom =
        β ≫ (G.realization C hS hU hR hP).target.hom →
      ArrowToPoint G C hS hU hR u hP V' α → ArrowToPoint G C hS hU hR u hP V' β := by
    rintro α β hαβ ⟨arr₁, harr₁, hcond⟩
    obtain ⟨arr₂, harr₂⟩ := yoneda.map_surjective β
    refine ⟨arr₂, harr₂, fun p => ?_⟩
    have e : ∀ (a : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR) (γ : _ ⟶ _),
        yoneda.map a = γ → yoneda.map (a ≫ targetSiteMap G C hS hU hR) =
          γ ≫ (G.realization C hS hU hR hP).target.hom := fun a γ h =>
      (arr_comp_target G C hS hU hR hP V' a).symm.trans
        (congrArg (fun z => z ≫ (G.realization C hS hU hR hP).target.hom) h)
    have hsite : arr₁ ≫ targetSiteMap G C hS hU hR = arr₂ ≫ targetSiteMap G C hS hU hR :=
      yoneda.map_injective ((e _ _ harr₁).trans (hαβ.trans (e _ _ harr₂).symm))
    exact (toScheme_map_apply_eq _ _ _ _ hsite p).symm.trans (hcond p)
  exact ⟨key ψ₁ ψ₂ hψ, key ψ₂ ψ₁ hψ.symm⟩

include hW in
/-- **An arrow whose target is the restriction of the point `u'` satisfies the predicate cut
out by `Z_u`**: its target factors through `Spec κ(u)`, whose image in `U` is the single
point `u`. -/
theorem arrowToPoint_of_target
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (ψ : yoneda.obj V' ⟶ (G.realization C hS hU hR hP).arrows.obj)
    (ht : ψ ≫ (G.realization C hS hU hR hP).target.hom =
      (φ ≫ (yoneda.map h ≫
        yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))) ≫
        F.universalOpen.toBase.hom) :
    ArrowToPoint G C hS hU hR u hP V' ψ := by
  obtain ⟨arr, rfl⟩ := yoneda.map_surjective ψ
  obtain ⟨base, hbase⟩ := yoneda.map_surjective (φ ≫ yoneda.map h)
  refine ⟨arr, rfl, fun p => ?_⟩
  have hsite : arr ≫ targetSiteMap G C hS hU hR = base ≫ residueSiteMap G C hS hU u hK :=
    yoneda.map_injective
      ((arr_comp_target G C hS hU hR hP V' arr).symm.trans
        (ht.trans (base_eq_of_fibrePoint G C hS hU hR u hK hP F W hW hWfin V h V' φ base
          hbase)))
  have hp := toScheme_map_apply_eq _ _ _ _ hsite p
  have hr : (G.objects.left.fromSpecResidueField u)
      ((BigFppfOver.toScheme C S hS).map base p) ∈
      Set.range (G.objects.left.fromSpecResidueField u).base := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at hr
  exact hp.trans hr

include hW in
/-- **The predicate cut out by `Z_u` cuts out the open subspace which the restriction of the
point `u'` names.**  This is the conjunction of the two missing ingredients of the third step
of the proof of Stacks 03FM, read as the characterization the containment needs. -/
theorem cutsOut_fibrePoint
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK) :
    F.CutsOut (ArrowToPoint G C hS hU hR u hP) (yoneda.map h ≫
      yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin)) := by
  intro V' μ ψ φ hμ hc
  obtain ⟨arr, rfl⟩ := yoneda.map_surjective ψ
  obtain ⟨base, hbase⟩ := yoneda.map_surjective (φ ≫ yoneda.map h)
  subst hμ
  refine (exists_lift_universalOpen_fibrePoint_iff G C hS hU hR u hK hP F W hW hWfin V h V'
    φ base hbase arr hc).trans ?_
  constructor
  · intro hcond
    exact ⟨arr, rfl, hcond⟩
  · rintro ⟨arr', harr', hcond⟩
    obtain rfl := yoneda.map_injective harr'
    exact hcond

end Fibre

end AlgebraicGeometry.Space

end
