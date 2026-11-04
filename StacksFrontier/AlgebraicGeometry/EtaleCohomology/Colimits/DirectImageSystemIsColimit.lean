module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemColimit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelTransitionCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Stacks 0EYN (2): a sheaf on the limit is the colimit of `f_i^{-1}f_{i,*}𝓕`

Let `X = lim X_i` be a directed limit of schemes with affine transition morphisms `f_{i'i}` and
projections `f_i : X ⟶ X_i`, and let `𝓕` be a sheaf on the small étale site of `X`. Part (2) of
[Stacks, Tag 0EYN] asserts `𝓕 = colim_i f_i^{-1}f_{i,*}𝓕`, the colimit being over the system of
part (1), `Stacks.EtaleCohomology.directImageSystem`. This file proves it on Mathlib's small étale
site, for sheaves of sets and for sheaves of abelian groups: the cocone of counits
`Stacks.EtaleCohomology.pullbackDirectImageCocone` over the diagram
`Stacks.EtaleCohomology.pullbackDirectImageDiagram` is a colimit cocone.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitType_limitToSmallEtale`,
  `…_limitToEtaleSite`, `…_levelBaseChange` — the restriction form of the statement, for sheaves of
  sets, on the size-bounded small étale site of [Stacks, Tag 021B], on Mathlib's small étale site,
  and with the levels of [Stacks, Tag 0EYL] read by base change along the projections.
* `Stacks.EtaleCohomology.AffineLimitCohomology.existsUnique_of_directImage_compatible_type` —
  the descent statement for direct images of sheaves of sets: every compatible family of maps
  `f_{i,*}𝓕 ⟶ f_{i,*}𝒢` is the family of direct images of a unique `𝓕 ⟶ 𝒢`.
* `Stacks.EtaleCohomology.isColimitPullbackDirectImageCocone` — **[Stacks, Tag 0EYN] (2)** for
  sheaves of sets.
* `Stacks.EtaleCohomology.isColimitPullbackDirectImageCoconeAb` — the same for abelian sheaves.

## Implementation notes

The proof is the source's: via [Stacks, Tag 04HR] and [Stacks, Tag 0EYL] the statement is a special
case of [Stacks, Tag 0EXJ]. That special case is
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.restrictionIsColimit'_of_inputs`
at the system of sites of [Stacks, Tag 0EYL] (`Stacks.EtaleCohomology.AffineLimitCohomology.sys`),
whose four site inputs are the bundle
`Stacks.EtaleCohomology.AffineLimitCohomology.colimitSiteInputs_toLimitSmall`, and which is at an
arbitrary coefficient category. The three crossings that carry it to Mathlib's small étale sites —
the size cutoff of [Stacks, Tag 021B] at the limit, the identification of the levels with base
changes along the projections, and the size cutoff at the levels — are the ones the abelian
development carries out in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLimitColimitMainstreamSite.lean`,
`SmallEtaleLimitLevelBaseChangeColimit.lean`, `SmallEtaleLimitLevelCrossingAbelian.lean` and
`SmallEtaleLimitLevelTransitionCoherence.lean`; here they are done at sheaves of sets, the only
coefficient-specific inputs being the full faithfulness of restriction along the crossings, which
for sets is `Stacks.EtaleCohomology.AffineLimitCohomology.full_limitRestriction`,
`faithful_limitRestriction` and
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv`.

The big étale site `B` that bounds the sizes in [Stacks, Tag 021B] is an auxiliary choice of the
proof and does not occur in the statements of the main results: it is
`AlgebraicGeometry.BigEtaleSite.ofSet` of the set of schemes of the system and its limit.

The schemes live in `Scheme.{max u v}` for an index in `Type v`, as everywhere in the development
of [Stacks, Tag 0EYL]; the sheaves take values in `Type (max u v + 1)`, resp.
`AddCommGrpCat.{max u v + 1}`, the coefficients at which Mathlib's small étale site of a scheme in
`Scheme.{max u v}` has inverse images.

## References

* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EXJ](https://stacks.math.columbia.edu/tag/0EXJ)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)

Tags covered: 0EYN (part (2)).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology

/-- The sections of a transported map of direct images: restriction along the base-change
comparison, the map at the base change, and restriction back. -/
theorem coneDirectImageTransport_hom_app {I : Type v} [Preorder I]
    {D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{u}} {A : Type*} [Category* A] {c : Cone D}
    {i j : Iᵒᵖ} (a : i ⟶ j)
    {F G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) A}
    (σ : (smallEtalePushforward (c.π.app i) A).obj F ⟶
      (smallEtalePushforward (c.π.app i) A).obj G) (U : (D.obj j).Etale) :
    (coneDirectImageTransport D A c a σ).hom.app (op U) =
      F.obj.map ((smallEtaleBaseChangeComp' (c.π.app i) (D.map a) (c.π.app j)
          (c.w a).symm).inv.app U).op ≫
        σ.hom.app (op ((smallEtaleBaseChange (D.map a)).obj U)) ≫
          G.obj.map ((smallEtaleBaseChangeComp' (c.π.app i) (D.map a) (c.π.app j)
            (c.w a).symm).hom.app U).op := by
  simp only [coneDirectImageTransport, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app]
  have h₁ : ((coneDirectImageComp D A c a).inv.app F).hom.app (op U) =
      F.obj.map ((smallEtaleBaseChangeComp' (c.π.app i) (D.map a) (c.π.app j)
        (c.w a).symm).inv.app U).op := Category.comp_id _
  have h₂ : ((coneDirectImageComp D A c a).hom.app G).hom.app (op U) =
      G.obj.map ((smallEtaleBaseChangeComp' (c.π.app i) (D.map a) (c.π.app j)
        (c.w a).symm).hom.app U).op := Category.id_comp _
  rw [h₁, h₂]
  rfl

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]

/-! ### The restriction form, for sheaves of sets -/

/-- **The colimit half of [Stacks, Tag 0EYN] in restriction form, on the size-bounded small étale
site of the limit, for sheaves of sets**, with the transition data given by isomorphisms.
This is
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.restrictionIsColimit'_of_inputs` at
the system of sites of [Stacks, Tag 0EYL] and at sheaves of sets, the fully faithful restriction
along the crossing being `Stacks.EtaleCohomology.AffineLimitCohomology.full_limitRestriction` and
`faithful_limitRestriction`. -/
theorem restrictionIsColimitType_limitToSmallEtale
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1))) :
    InverseSystemOfFiniteSites.RestrictionIsColimit'
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX)
      (Type (max u v + 1)) (sys D c B hD hX hc)
      (fun i => toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX)
      (InverseSystemOfFiniteSites.compTransitionIso (limitToSmallEtale D c B hX)
        (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc)) F :=
  InverseSystemOfFiniteSites.restrictionIsColimit'_of_inputs
    (limitSitePrecoverage D c B hX) (AlgebraicGeometry.SmallEtale.topology B c.pt hX)
    (limitToSmallEtale D c B hX) (Type (max u v + 1)) (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
    (colimitSiteInputs_toLimitSmall D c B hD hX hc) F

/-- **The colimit half of [Stacks, Tag 0EYN] in restriction form, on Mathlib's small étale site of
the limit, for sheaves of sets.** This is
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitType_limitToSmallEtale` carried
across the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`, whose inverse is restriction
along `AlgebraicGeometry.SmallEtale.toEtaleSite`. -/
theorem restrictionIsColimitType_limitToEtaleSite
    (F : Sheaf (c.pt).smallEtaleTopology (Type (max u v + 1))) :
    InverseSystemOfFiniteSites.RestrictionIsColimit'
      (c.pt).smallEtaleTopology
      (Type (max u v + 1)) (sys D c B hD hX hc)
      (fun i => toLimitSmall D c B hD hX hc i ⋙
        (limitToSmallEtale D c B hX ⋙ AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX))
      (InverseSystemOfFiniteSites.compTransitionIso
        (limitToSmallEtale D c B hX ⋙ AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX)
        (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc)) F := by
  intro H g hg
  obtain ⟨h₀, hh₀, hu₀⟩ :=
    restrictionIsColimitType_limitToSmallEtale D c B hD hX hc
      ((AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX
        (Type (max u v + 1))).obj F)
      ((AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX
        (Type (max u v + 1))).obj H) g
      (by
        intro i j a V
        refine Eq.trans (hg a V) ?_
        simp only [InverseSystemOfFiniteSites.map_op_compTransitionIso_hom_app,
          InverseSystemOfFiniteSites.map_op_compTransitionIso_inv_app]
        rw [InverseSystemOfFiniteSites.map_eqToHom_sheafPushforwardContinuous
              (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX)
              (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (c.pt).smallEtaleTopology
              (Type (max u v + 1)) F
              (congrArg (limitToSmallEtale D c B hX).obj
                (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) V).symm),
          InverseSystemOfFiniteSites.map_eqToHom_sheafPushforwardContinuous
              (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX)
              (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (c.pt).smallEtaleTopology
              (Type (max u v + 1)) H
              (congrArg (limitToSmallEtale D c B hX).obj
                (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) V))]
        rfl)
  obtain ⟨h, rfl⟩ := (AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX
    (Type (max u v + 1))).map_surjective h₀
  exact ⟨h, fun i V => hh₀ i V, fun y hy =>
    (AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX
      (Type (max u v + 1))).map_injective
      (hu₀ ((AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX
        (Type (max u v + 1))).map y) fun i V => hy i V)⟩

/-- **The colimit half of [Stacks, Tag 0EYN] in restriction form, on Mathlib's small étale site of
the limit, with the levels read by base change along the projections, for sheaves of sets.** This
is `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitType_limitToEtaleSite` carried
across `Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso`. -/
theorem restrictionIsColimitType_levelBaseChange
    (F : Sheaf (c.pt).smallEtaleTopology (Type (max u v + 1))) :
    InverseSystemOfFiniteSites.RestrictionIsColimit'
      (c.pt).smallEtaleTopology (Type (max u v + 1)) (sys D c B hD hX hc)
      (levelBaseChangeCrossing D c B hD hX hc)
      (levelBaseChangeCrossing_transition D c B hD hX hc) F :=
  InverseSystemOfFiniteSites.RestrictionIsColimit'.ofIso
    (c.pt).smallEtaleTopology (Type (max u v + 1))
    (InverseSystemOfFiniteSites.compTransitionIso
      (limitToSmallEtale D c B hX ⋙ AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX)
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc))
    (levelCrossingIso D c B hD hX hc)
    (restrictionIsColimitType_limitToEtaleSite D c B hD hX hc F)

/-! ### The crossing at the levels, for sheaves of sets -/

/-- **Restriction of sheaves of sets from Mathlib's small étale site of `X_i` to a level of
[Stacks, Tag 0EYL] is an equivalence**: the level crossing of
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv` followed by the size
cutoff of [Stacks, Tag 021B], a dense subsite of Mathlib's small étale site. -/
theorem isEquivalence_levelEtaleRestrictionType (i : (sys D c B hD hX hc).I) :
    letI := isContinuous_levelToEtaleSite D c B hD hX hc i
    ((levelToSmallEtale D c B hD hX hc i ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _)).sheafPushforwardContinuous
        (Type (max u v + 1)) ((sys D c B hD hX hc).J i)
        (AlgebraicGeometry.Scheme.smallEtaleTopology
          (D.obj (levelIndex D c B hD hX hc i)))).IsEquivalence := by
  let := isContinuous_levelToEtaleSite D c B hD hX hc i
  let := QcSeparatedColimit.isContinuous_levelToSmallEtale D c B hD hX hc i
  let := AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite B
    (D.obj (levelIndex D c B hD hX hc i)) (hD _)
  let : ((levelToSmallEtale D c B hD hX hc i).sheafPushforwardContinuous
      (Type (max u v + 1)) ((sys D c B hD hX hc).J i)
      (AlgebraicGeometry.SmallEtale.topology B
        (D.obj (levelIndex D c B hD hX hc i)) (hD _))).IsEquivalence :=
    affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv D c B hD hX hc i
  exact Functor.isEquivalence_of_iso (Functor.sheafPushforwardContinuousComp
    (levelToSmallEtale D c B hD hX hc i)
    (AlgebraicGeometry.SmallEtale.toEtaleSite B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _)) (Type (max u v + 1))
    ((sys D c B hD hX hc).J i)
    (AlgebraicGeometry.SmallEtale.topology B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    (AlgebraicGeometry.Scheme.smallEtaleTopology
      (D.obj (levelIndex D c B hD hX hc i))))

/-- **A map of sheaves of sets on Mathlib's small étale site of `X_i` is determined by its values
on the objects coming from a level of [Stacks, Tag 0EYL]**: the faithfulness half of
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionType`. -/
theorem hom_ext_of_levelRestrictionType (i : (sys D c B hD hX hc).I)
    {F G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology
      (D.obj (levelIndex D c B hD hX hc i))) (Type (max u v + 1))} (φ ψ : F ⟶ G)
    (h : ∀ V : (sys D c B hD hX hc).C i,
      φ.hom.app (op ((levelToSmallEtale D c B hD hX hc i ⋙
          AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc i)) (hD _)).obj V)) =
        ψ.hom.app (op ((levelToSmallEtale D c B hD hX hc i ⋙
          AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc i)) (hD _)).obj V))) :
    φ = ψ := by
  let := isContinuous_levelToEtaleSite D c B hD hX hc i
  let := isEquivalence_levelEtaleRestrictionType D c B hD hX hc i
  refine ((levelToSmallEtale D c B hD hX hc i ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _)).sheafPushforwardContinuous
    (Type (max u v + 1)) ((sys D c B hD hX hc).J i)
    (AlgebraicGeometry.Scheme.smallEtaleTopology
      (D.obj (levelIndex D c B hD hX hc i)))).map_injective ?_
  exact Sheaf.hom_ext (NatTrans.ext (funext fun V => h V.unop))

/-! ### The descent of direct images, for sheaves of sets -/

/-- **The family of maps on the levels is compatible with the transition datum**, for any
coefficient category: the compatibility of `σ` over `Iᵒᵖ`, stated with
`Stacks.EtaleCohomology.coneDirectImageTransport`, read on the levels of [Stacks, Tag 0EYL]
through `Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition`. The
argument is that of `Stacks.EtaleCohomology.AffineLimitCohomology.levelFamily_compat`. -/
theorem levelFamily_compat_of_transport {A : Type*} [Category* A]
    (F G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) A)
    (σ : ∀ i : Iᵒᵖ, (Stacks.EtaleCohomology.smallEtalePushforward (c.π.app i) A).obj F ⟶
      (Stacks.EtaleCohomology.smallEtalePushforward (c.π.app i) A).obj G)
    (hσ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      σ j = Stacks.EtaleCohomology.coneDirectImageTransport D A c a (σ i))
    {p q : (sys D c B hD hX hc).I} (b : q ⟶ p) (V : (sys D c B hD hX hc).C p) :
    (Functor.whiskerLeft (levelEtaleSite D c B hD hX hc p).op
        (σ (levelIndex D c B hD hX hc p)).hom).app (op V) =
      F.obj.map ((levelBaseChangeCrossing_transition D c B hD hX hc b).hom.app V).op ≫
        (Functor.whiskerLeft (levelEtaleSite D c B hD hX hc q).op
            (σ (levelIndex D c B hD hX hc q)).hom).app
          (op (((sys D c B hD hX hc).u b).obj V)) ≫
          G.obj.map ((levelBaseChangeCrossing_transition D c B hD hX hc b).inv.app V).op := by
  have hm := (congrArg (fun z => F.obj.map (Quiver.Hom.op z))
    (levelBaseChangeCrossing_transition_hom_app D c B hD hX hc b V)).trans
      (F.obj.map_comp _ _)
  have hk := (G.obj.map_comp
      ((Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc q))).map
        ((levelTransitionIso D c B hD hX hc b).hom.app V)).op
      ((levelBaseChangeCrossing_transition D c B hD hX hc b).inv.app V).op).symm.trans
    (congrArg (fun z => G.obj.map (Quiver.Hom.op z))
      (levelBaseChangeCrossing_transition_inv_app_comp D c B hD hX hc b V))
  exact comp_comp_eq_of_naturality
    ((congrArg (fun z => z.hom.app (op ((levelEtaleSite D c B hD hX hc p).obj V)))
        (hσ ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b))).trans
      (Stacks.EtaleCohomology.coneDirectImageTransport_hom_app _ _ _))
    hm
    ((σ (levelIndex D c B hD hX hc q)).hom.naturality
      ((levelTransitionIso D c B hD hX hc b).hom.app V).op)
    hk

include B hD hX hc in
/-- **The descent of direct images of sheaves of sets along a limit of schemes.** Every family of
maps `σ_i : f_{i,*}𝓕 ⟶ f_{i,*}𝒢` of sheaves of sets on Mathlib's small étale sites, compatible with
the identifications `f_{i,*} ≅ f_{i'i,*}f_{i',*}`, is the family of direct images of a unique
`χ : 𝓕 ⟶ 𝒢`. The argument is that of
`Stacks.EtaleCohomology.AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange`. -/
theorem existsUnique_of_directImage_compatible_type
    (F G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) (Type (max u v + 1)))
    (σ : ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj F ⟶
        (Stacks.EtaleCohomology.smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj G)
    (hσ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      σ j = Stacks.EtaleCohomology.coneDirectImageTransport D (Type (max u v + 1)) c a (σ i)) :
    ∃! χ : F ⟶ G, ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePushforward (c.π.app i) (Type (max u v + 1))).map χ =
        σ i := by
  obtain ⟨χ, hχ, huniq⟩ := restrictionIsColimitType_levelBaseChange D c B hD hX hc F G
    (fun n => Functor.whiskerLeft (levelEtaleSite D c B hD hX hc n).op
      (σ (levelIndex D c B hD hX hc n)).hom)
    (levelFamily_compat_of_transport D c B hD hX hc F G σ hσ)
  have hlev : ∀ n : (sys D c B hD hX hc).I,
      (Stacks.EtaleCohomology.smallEtalePushforward
          (c.π.app (levelIndex D c B hD hX hc n)) (Type (max u v + 1))).map χ =
        σ (levelIndex D c B hD hX hc n) :=
    fun n => hom_ext_of_levelRestrictionType D c B hD hX hc n _ _ fun V => (hχ n V).symm
  have hgen : ∀ {k l : Iᵒᵖ} (a : k ⟶ l),
      (Stacks.EtaleCohomology.smallEtalePushforward (c.π.app k) (Type (max u v + 1))).map χ =
          σ k →
        (Stacks.EtaleCohomology.smallEtalePushforward (c.π.app l) (Type (max u v + 1))).map χ =
          σ l := by
    intro k l a hk
    rw [hσ a, ← hk, Stacks.EtaleCohomology.coneDirectImageTransport_map]
  refine ⟨χ, fun i => ?_, fun ψ hψ => ?_⟩
  · exact hgen ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom
      (hlev ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i))
  · refine huniq ψ fun n V => ?_
    rw [← hψ (levelIndex D c B hD hX hc n)]
    rfl

end Stacks.EtaleCohomology.AffineLimitCohomology

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v})
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]
  (c : Cone D) (hc : IsLimit c)

/-- The schemes of an inverse system together with the vertex of a cone over it. -/
abbrev coneSchemes : Set AlgebraicGeometry.Scheme.{max u v} := Set.range D.obj ∪ {c.pt}

/-- The schemes of an inverse system indexed by a type in `Type v`, together with the vertex of a
cone over it, form a small set. -/
instance small_coneSchemes : Small.{max u v} (coneSchemes D c) :=
  haveI := small_single.{max u v} c.pt
  small_union.{max u v} (Set.range D.obj) {c.pt}

/-- **[Stacks, Tag 0EYN] (2), for sheaves of sets.** Let `X = lim X_i` be a directed limit of
schemes with affine transition morphisms `f_{i'i}` and projection morphisms `f_i : X ⟶ X_i`, and
let `𝓕` be a sheaf of sets on the small étale site of `X`. Then `𝓕 = colim_i f_i^{-1}f_{i,*}𝓕`:
the cocone of counits `f_i^{-1}f_{i,*}𝓕 ⟶ 𝓕` over the diagram
`Stacks.EtaleCohomology.pullbackDirectImageDiagram`, whose transition maps are built from the maps
`φ_{i'i} : f_{i'i}^{-1}f_{i,*}𝓕 ⟶ f_{i',*}𝓕` of the system of sheaves of part (1),
`Stacks.EtaleCohomology.directImageSystem`, is a colimit cocone. Equivalently, the canonical map
`colim_i f_i^{-1}f_{i,*}𝓕 ⟶ 𝓕` is an isomorphism. -/
@[stacks 0EYN "part (2): `𝓕 = colim_i f_i^{-1}f_{i,*}𝓕` for the system of part (1), on Mathlib's \
small étale site, for sheaves of sets"]
def isColimitPullbackDirectImageCocone
    (F : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) (Type (max u v + 1))) :
    IsColimit (pullbackDirectImageCocone D (Type (max u v + 1)) c F) :=
  isColimitPullbackDirectImageCocone_of_descent D (Type (max u v + 1)) c F fun G σ hσ =>
    AffineLimitCohomology.existsUnique_of_directImage_compatible_type D c
      (AlgebraicGeometry.BigEtaleSite.ofSet (coneSchemes D c))
      (fun i => AlgebraicGeometry.BigEtaleSite.contains_ofSet _ (Or.inl ⟨i, rfl⟩))
      (AlgebraicGeometry.BigEtaleSite.contains_ofSet _ (Or.inr rfl)) hc F G σ hσ

/-- **[Stacks, Tag 0EYN] (2), for sheaves of abelian groups.** The cocone of counits
`f_i^{-1}f_{i,*}𝓕 ⟶ 𝓕` over `Stacks.EtaleCohomology.pullbackDirectImageDiagram` is a colimit
cocone for every abelian sheaf `𝓕` on the small étale site of the limit. The descent statement
for the direct images is
`Stacks.EtaleCohomology.AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange`. -/
def isColimitPullbackDirectImageCoconeAb
    (F : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1}) :
    IsColimit (pullbackDirectImageCocone D AddCommGrpCat.{max u v + 1} c F) :=
  isColimitPullbackDirectImageCocone_of_descent D AddCommGrpCat.{max u v + 1} c F fun G σ hσ =>
    AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange D c
      (AlgebraicGeometry.BigEtaleSite.ofSet (coneSchemes D c))
      (fun i => AlgebraicGeometry.BigEtaleSite.contains_ofSet _ (Or.inl ⟨i, rfl⟩))
      (AlgebraicGeometry.BigEtaleSite.contains_ofSet _ (Or.inr rfl)) hc F G σ fun a => hσ a

end Stacks.EtaleCohomology

end
