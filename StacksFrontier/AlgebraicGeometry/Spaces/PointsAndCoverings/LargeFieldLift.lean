module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Lifting a point of an algebraic space over a large algebraically closed field

Let `a : F ⟶ G` be a morphism of algebraic spaces over `S` and let `k` be an algebraically
closed field in the big fppf site of `S`, larger than every residue field of some surjective
étale scheme atlas of `F`. Then a point of `F` whose image in `G` is represented by a
`k`-valued point of `G` is itself represented by a `k`-valued point of `F` lying over that
one.

## Main results

* `AlgebraicGeometry.Space.exists_lift_of_large_field` is the lifting property.

## Implementation notes

The cardinal bound is formed from an arbitrary surjective étale scheme atlas of the source.
The point over the target is represented by a section on the field spectrum, so the
conclusion is an actual section on that same spectrum, not merely a representative over an
extension field.

The proof lifts the given atlas to one compatible with the atlas of `G` which the target's
algebraic-space structure supplies, and transports the point of `F` to a point of that
lifted atlas, which is possible because a relatively surjective morphism is surjective on
points. A representative of that point over the residue field at a scheme point is then
compared with the given `k`-valued point of `G` inside the fibre product of the two atlases,
and the resulting `k`-point of the fibre product is lifted to the atlas of `F` through the
cardinality bound: the residue field of the atlas at the relevant point is finite over the
corresponding residue field of the given atlas, hence still smaller than `k`, so it embeds
into `k`.

## References

* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-- Along an étale morphism, residue fields of the source stay below a cardinal exceeding `ℵ₀`
and every residue field of the target. -/
private theorem cardinalMk_residueField_lt_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (x : X) {K : Type u}
    (hK : Cardinal.aleph0 ⊔ ⨆ y : Y, Cardinal.mk (Y.residueField y) < Cardinal.mk K) :
    Cardinal.mk (X.residueField x) < Cardinal.mk K := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    finite_residueField_of_etale_fibers f (fun _ => inferInstance) x
  exact (Algebra.IsAlgebraic.cardinalMk_le_max _ _).trans_lt <| max_lt
    (((le_ciSup Cardinal.bddAbove_of_small (f x)).trans (le_max_right _ _)).trans_lt hK)
    ((le_max_left _ _).trans_lt hK)

private theorem toScheme_map_comp_inclusion_map_hom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom :=
  (B.inclusion.map_comp f.left Y.hom).symm.trans (congrArg B.inclusion.map (Over.w f))

/-- A morphism of the underlying schemes of two objects of the big fppf site of `S` compatible
with their structure morphisms comes from a morphism of the site. -/
private theorem exists_hom_of_toScheme_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hg : g ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom) :
    ∃ f : X ⟶ Y, (BigFppfOver.toScheme B S hS).map f = g :=
  let g' : B.inclusion.obj X.left ⟶ B.inclusion.obj Y.left := g
  ⟨Over.homMk (B.inclusion.preimage g') (B.inclusion.map_injective (by
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]; exact hg)), B.inclusion.map_preimage g'⟩

/-- Along a morphism of representable presheaves on the big fppf site of `S` that is étale,
residue fields of the source stay below a cardinal exceeding `ℵ₀` and every residue field of
the target. -/
private theorem cardinalMk_residueField_lt_of_presheaf_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U U' : BigFppfOver B S hS} (p : yoneda.obj U' ⟶ yoneda.obj U)
    (hp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) p)
    (u : (BigFppfOver.toScheme B S hS).obj U') {K : Type u}
    (hK : Cardinal.aleph0 ⊔ ⨆ t : (BigFppfOver.toScheme B S hS).obj U,
      Cardinal.mk (((BigFppfOver.toScheme B S hS).obj U).residueField t) < Cardinal.mk K) :
    Cardinal.mk (((BigFppfOver.toScheme B S hS).obj U').residueField u) < Cardinal.mk K := by
  let : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : QEtale.IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange (BigFppfOver.toScheme B S hS)
      (@Etale.{u} : MorphismProperty Scheme.{u})
  rw [← yoneda.map_preimage p] at hp
  have : Etale ((BigFppfOver.toScheme B S hS).map (yoneda.preimage p)) :=
    (MorphismProperty.relative_map_iff (F := yoneda) (P := QEtale)).mp hp
  exact cardinalMk_residueField_lt_of_etale
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage p)) u hK

/-- If the image under `yoneda.map α ≫ q` of the canonical point of `U` at `u` and a `k`-valued
point `y` of `G` define the same point of `G`, then `α u` lies in the image of the pullback of
`q` along `y`. -/
private theorem exists_pullback_point_of_class_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V : BigFppfOver B S hS}
    {q : yoneda.obj V ⟶ G} (hq : yoneda.relativelyRepresentable q) (α : U ⟶ V)
    (u : (BigFppfOver.toScheme B S hS).obj U) {k : Type u} [Field k]
    {hk : B.Contains (Spec (.of k))} {b : Spec (.of k) ⟶ S}
    {y : G.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))}
    (hclass : (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α ≫ q)
        (canonicalSiteFieldPoint B S hS U u)).class B S hS G =
      (⟨k, hk, b, y⟩ : FieldValuedPoint B S hS G).class B S hS G) :
    ∃ z, (BigFppfOver.toScheme B S hS).map (hq.fst' (yonedaEquiv.symm y)) z =
      (BigFppfOver.toScheme B S hS).map α u := by
  let Tsch := BigFppfOver.toScheme B S hS
  let T : BigFppfOver B S hS := Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)
  let η : yoneda.obj T ⟶ G := yonedaEquiv.symm y
  let pu := canonicalSiteFieldPoint B S hS U u
  obtain ⟨r, ⟨mU, hmU⟩, ⟨mT, hmT⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS G _ _).mp hclass
  let mU' : r.siteObject ⟶ pu.siteObject := mU
  let rhoV : r.siteObject ⟶ V := mU' ≫ pu.value ≫ α
  let rhoT : r.siteObject ⟶ T := mT
  have hsection : q.app (Opposite.op r.siteObject) rhoV =
      η.app (Opposite.op r.siteObject) rhoT := by
    calc q.app (Opposite.op r.siteObject) rhoV
        = G.map mU.op (q.app (Opposite.op pu.siteObject) (pu.value ≫ α)) :=
          congrArg (fun f => f (pu.value ≫ α)) (q.naturality mU.op)
      _ = G.map mT.op y := hmU.trans hmT.symm
      _ = η.app (Opposite.op r.siteObject) rhoT := rfl
  have hNat : yoneda.map rhoV ≫ q = yoneda.map rhoT ≫ η := by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_apply, NatTrans.comp_app, types_comp_apply, yoneda_map_app]
      using hsection
  let : Unique ↥(Tsch.obj pu.siteObject) := PrimeSpectrum.instUnique
  let cpR : ↥(Tsch.obj r.siteObject) := IsLocalRing.closedPoint r.carrier
  let cpPu : ↥(Tsch.obj pu.siteObject) := IsLocalRing.closedPoint pu.carrier
  refine ⟨Tsch.map (hq.lift' rhoV rhoT hNat) cpR, ?_⟩
  have h := congrArg (fun g : r.siteObject ⟶ V => Tsch.map g cpR) (hq.lift'_fst rhoV rhoT hNat)
  simp only [rhoV, Functor.map_comp, Scheme.Hom.comp_apply] at h
  refine h.trans ?_
  rw [Subsingleton.elim (Tsch.map mU' cpR) cpPu]
  exact congrArg (Tsch.map α) (canonicalSiteFieldPoint_point B S hS U u)

/-- A point of the pullback of an étale chart `q` of `G` along a `k`-valued point `y`, with `k`
separably closed, is the image of a `k`-valued section of the chart lying over `y`. -/
private theorem exists_section_of_pullback_point (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    {q : yoneda.obj V ⟶ G} (hq : yoneda.relativelyRepresentable q)
    (hq_etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    {k : Type u} [Field k] [IsSepClosed k] {hk : B.Contains (Spec (.of k))}
    {b : Spec (.of k) ⟶ S} (y : G.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))))
    (z : (BigFppfOver.toScheme B S hS).obj (hq.pullback (yonedaEquiv.symm y))) :
    ∃ g : Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) ⟶ V,
      q.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))) g = y ∧
      (BigFppfOver.toScheme B S hS).map g (by exact IsLocalRing.closedPoint k) =
        (BigFppfOver.toScheme B S hS).map (hq.fst' (yonedaEquiv.symm y)) z := by
  let T : BigFppfOver B S hS := Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)
  let : Unique ↥((BigFppfOver.toScheme B S hS).obj T) := PrimeSpectrum.instUnique
  let : Unique ↥(Spec (.of k)) := PrimeSpectrum.instUnique
  let η : yoneda.obj T ⟶ G := yonedaEquiv.symm y
  let sT : hq.pullback η ⟶ T := hq.snd η
  let : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : QEtale.IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange (BigFppfOver.toScheme B S hS)
      (@Etale.{u} : MorphismProperty Scheme.{u})
  have : Etale ((BigFppfOver.toScheme B S hS).map sT) :=
    (MorphismProperty.relative_map_iff (F := yoneda) (P := QEtale)).mp
      ((MorphismProperty.relative_isStableUnderBaseChange QEtale).of_isPullback
        (hq.isPullback η) hq_etale)
  obtain ⟨barR, hbarR, hbarRpt⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    ((BigFppfOver.toScheme B S hS).map sT) (𝟙 (Spec (.of k))) z (Subsingleton.elim _ _)
  obtain ⟨barRSite, hbarRSite⟩ :=
    exists_hom_of_toScheme_map B S hS (X := T) (Y := hq.pullback η) barR (by
      rw [← toScheme_map_comp_inclusion_map_hom B S hS sT, ← Category.assoc, hbarR]
      exact Category.id_comp _)
  have hsT : barRSite ≫ sT = 𝟙 T := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, hbarRSite]; exact hbarR)
  have h : q.app (Opposite.op T) (barRSite ≫ hq.fst' η) =
      η.app (Opposite.op T) (barRSite ≫ sT) := by
    have h := congrArg (fun n => n.app (Opposite.op T) barRSite) (hq.isPullback η).w
    rw [← hq.map_fst'] at h
    exact h
  refine ⟨barRSite ≫ hq.fst' η,
    h.trans ((congrArg (fun t => η.app (Opposite.op T) t) hsT).trans
      (yonedaEquiv.apply_symm_apply y)), ?_⟩
  rw [Functor.map_comp, hbarRSite]
  exact congrArg ((BigFppfOver.toScheme B S hS).map (hq.fst' η))
    ((congrArg barR (Subsingleton.elim _ _)).trans hbarRpt)

/-- **Stacks 0488, part (4).** A point in the source over the image of a geometric target
point lifts over the same sufficiently large algebraically closed field: the map
`X(k) → |X| ×_{|Y|} Y(k)` is surjective. -/
theorem exists_lift_of_large_field
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G)
    (a : F ⟶ G)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F)
    (hp_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (_hp_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (k : Type u) [Field k] [IsAlgClosed k]
    (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (hlarge : Cardinal.aleph0 ⊔
      ⨆ u : (BigFppfOver.toScheme B S hS).obj U,
        Cardinal.mk (((BigFppfOver.toScheme B S hS).obj U).residueField u) <
          Cardinal.mk k)
    (x : points B S hS F)
    (y : G.obj (Opposite.op
      (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))))
    (hxy : pointsMap B S hS F a x =
      (⟨k, hk, b, y⟩ : FieldValuedPoint B S hS G).class B S hS G) :
    ∃ z : F.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))),
      (a.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))) z = y) ∧
      ((⟨k, hk, b, z⟩ : FieldValuedPoint B S hS F).class B S hS F = x) := by
  obtain ⟨V, q, hq_surjective, hq_etale⟩ := hG.exists_atlas
  obtain ⟨U', p', α, hp'a, hp'_surjective, hp'_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS (isAlgebraicSpace_yoneda B S hS U) hG
      (p ≫ a) V q hq_surjective hq_etale
  obtain ⟨xu₀, hxu₀⟩ := surjective_pointsMap_of_presheaf_surjective B S hS p hp_surjective x
  obtain ⟨xu, hxu⟩ := surjective_pointsMap_of_presheaf_surjective B S hS p' hp'_surjective xu₀
  obtain ⟨pu₀, hpu₀⟩ := Quot.exists_rep xu
  let u' := (schemeFieldPoint B S hS pu₀).point
  have hpu : (canonicalSiteFieldPoint B S hS U' u').class B S hS (yoneda.obj U') = xu :=
    (canonicalSiteFieldPoint_class_eq B S hS U' pu₀ u' rfl).trans hpu₀
  let hqR : yoneda.relativelyRepresentable q :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := G)).mp
      hG.diagonal_representable q
  have hclass : (FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map α ≫ q)
      (canonicalSiteFieldPoint B S hS U' u')).class B S hS G =
      (⟨k, hk, b, y⟩ : FieldValuedPoint B S hS G).class B S hS G := by
    rw [← pointsMap_class, hpu, ← hp'a, pointsMap_comp_apply B S hS p' (p ≫ a), hxu,
      pointsMap_comp_apply B S hS p a, hxu₀, hxy]
  -- The atlas point and the given geometric point have a common refinement
  -- over the target; the residue-field bound then makes that refinement a
  -- point over `k` itself.
  obtain ⟨z, hz⟩ := exists_pullback_point_of_class_eq B S hS hqR α u' hclass
  obtain ⟨g, hgy, hgpt⟩ := exists_section_of_pullback_point B S hS hqR hq_etale y z
  obtain ⟨l, hlpt, hl⟩ := exists_spec_lift_of_large_field ((BigFppfOver.toScheme B S hS).map α)
    u' k ((BigFppfOver.toScheme B S hS).map g) (hgpt.trans hz).symm
    (cardinalMk_residueField_lt_of_presheaf_etale B S hS p' hp'_etale u' hlarge)
  obtain ⟨lSite, hlSite⟩ := exists_hom_of_toScheme_map B S hS
    (X := Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) (Y := U') l (by
      rw [← toScheme_map_comp_inclusion_map_hom B S hS α, ← Category.assoc, hl,
        toScheme_map_comp_inclusion_map_hom])
  have hlα : lSite ≫ α = g := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, hlSite, hl])
  have hpk : (⟨k, hk, b, lSite⟩ : FieldValuedPoint B S hS (yoneda.obj U')).class B S hS
      (yoneda.obj U') = xu :=
    (canonicalSiteFieldPoint_class_eq B S hS U' _ u' (by
      show (BigFppfOver.toScheme B S hS).map lSite (IsLocalRing.closedPoint k) = u'
      rw [hlSite, hlpt])).symm.trans hpu
  refine ⟨p.app _ (p'.app _ lSite), ?_, ?_⟩
  · have h : a.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))
        (p.app _ (p'.app _ lSite)) =
          q.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))) (lSite ≫ α) := by
      simpa [NatTrans.comp_app, types_comp_apply, yoneda_map_app] using
        congrArg (fun n => n.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))) lSite) hp'a
    rw [h, hlα, hgy]
  · show (FieldValuedPoint.map B S hS (yoneda.obj U) p
      (FieldValuedPoint.map B S hS (yoneda.obj U') p' ⟨k, hk, b, lSite⟩)).class B S hS F = x
    rw [← pointsMap_class, ← pointsMap_class, hpk, hxu, hxu₀]

end AlgebraicGeometry.Space

end
