module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Charts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence

/-!
# Coverings of affine étale formal charts, tested on affine points

Let `X` be an fppf sheaf over `S` with a reduction `X_red`, and let `{u_k : U_k ⟶ U}` be a family
of morphisms of affine étale formal charts over `X` whose reductions `W_k ⟶ W` are jointly
surjective. This file shows that the family is then a covering on affine points: for every
affine object `T` of the site and every point `a ∈ U(T)`, the arrows `T' ⟶ T` along which `a`
lifts to some `U_k` form a covering sieve of the big affine fppf site. The base change of `u_k`
to `T` is an affine scheme `T_k` étale over `T` (Stacks 0AKN, Stacks 03FV), and the `T_k` cover
`T` because the reductions `W_k` cover `W` and a chart and its reduction have the same points.

## Main results

* `AlgebraicGeometry.FormalSpace.Reduction.exists_pointsMapULift_eq_of_isPullback`: a family of
  morphisms of charts whose reductions are jointly surjective is jointly surjective on points.
* `AlgebraicGeometry.FormalSpace.mem_topology_of_jointly_surjective_points`: a family of
  morphisms of charts which is jointly surjective on points is a covering on affine points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : FppfSheaf B S hS}

/-- The comparison of the underlying presheaf of a sheafified representable with the
universe-lifted Yoneda presheaf. -/
noncomputable abbrev sheafifiedYonedaObjULiftIso (T : BigFppfOver B S hS) :
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T).obj ≅
      (uliftYoneda.{u + 1}).obj T :=
  (sheafifiedYonedaCompForgetIso B S hS).app T

/-- The comparison `sheafifiedYonedaObjULiftIso` is natural in the representing object. -/
theorem sheafifiedYonedaObjULiftIso_hom_naturality {T T' : BigFppfOver B S hS} (f : T' ⟶ T) :
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f).hom ≫
        (sheafifiedYonedaObjULiftIso T).hom =
      (sheafifiedYonedaObjULiftIso T').hom ≫ (uliftYoneda.{u + 1}).map f :=
  (sheafifiedYonedaCompForgetIso B S hS).hom.naturality f

/-- The points of a sheafified representable are the points of the representing scheme. -/
noncomputable def pointsEquivSchemeSheafified (T : BigFppfOver B S hS) :
    Space.pointsULift.{u + 1} B S hS ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      T).obj ≃ (BigFppfOver.toScheme B S hS).obj T where
  toFun p := Space.pointsEquivSchemeULift.{u + 1} B S hS T
    (Space.pointsMapULift.{u + 1} B S hS _ (sheafifiedYonedaObjULiftIso T).hom p)
  invFun x := Space.pointsMapULift.{u + 1} B S hS _ (sheafifiedYonedaObjULiftIso T).inv
    ((Space.pointsEquivSchemeULift.{u + 1} B S hS T).symm x)
  left_inv p := by
    simp only [Equiv.symm_apply_apply]
    rw [← Function.comp_apply (f := Space.pointsMapULift.{u + 1} B S hS _ _),
      ← Space.pointsMapULift_comp, Iso.hom_inv_id, Space.pointsMapULift_id, id]
  right_inv x := by
    simp only
    rw [← Function.comp_apply (f := Space.pointsMapULift.{u + 1} B S hS _ _),
      ← Space.pointsMapULift_comp, Iso.inv_hom_id, Space.pointsMapULift_id, id,
      Equiv.apply_symm_apply]

/-- The map on points of a composite of morphisms of presheaves, applied to a point. -/
private theorem pointsMapULift_comp_apply_aux
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (α : F ⟶ G) (β : G ⟶ H)
    (v : Space.pointsULift.{u + 1} B S hS F) :
    Space.pointsMapULift B S hS F (α ≫ β) v =
      Space.pointsMapULift B S hS G β (Space.pointsMapULift B S hS F α v) := by
  simp only [Space.pointsMapULift_comp, Function.comp_apply]

/-- The identification `pointsEquivSchemeSheafified` of the points of a sheafified
representable with the points of the representing scheme is natural in the representing
object. -/
theorem pointsEquivSchemeSheafified_naturality {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (p : Space.pointsULift.{u + 1} B S hS ((Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj T').obj) :
    pointsEquivSchemeSheafified T (Space.pointsMapULift.{u + 1} B S hS _
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f).hom p) =
      (BigFppfOver.toScheme B S hS).map f (pointsEquivSchemeSheafified T' p) := by
  dsimp only [pointsEquivSchemeSheafified, Equiv.coe_fn_mk]
  rw [← pointsMapULift_comp_apply_aux, sheafifiedYonedaObjULiftIso_hom_naturality,
    pointsMapULift_comp_apply_aux, Space.pointsEquivSchemeULift_naturality]

namespace Reduction

variable (R : Reduction B S hS X)

/-- **A family of morphisms of charts whose reductions are jointly surjective is jointly
surjective on points.** Let `u_k : U_k ⟶ U` be morphisms of affine étale formal charts over
`X`, with reduction squares `W_k ⟶ U_k` and `W ⟶ U` and morphisms of reductions `f_k : W_k ⟶ W`
lying over the `u_k`. If the `f_k` are jointly surjective on underlying schemes, then every
point of `U` comes from a point of some `U_k`: it comes from a point of `W`, which comes from a
point of some `W_k`, which maps to `U_k`. -/
theorem exists_pointsMapULift_eq_of_isPullback {ι : Type*} {Y : R.AffineEtale}
    {Yk : ι → R.AffineEtale} (f : ∀ k, Yk k ⟶ Y)
    (hf : ∀ y : (BigFppfOver.toScheme B S hS).obj (R.affineChartObj Y), ∃ k r,
      (BigFppfOver.toScheme B S hS).map ((Space.AffineEtale.toOver B S hS R.space.obj).map (f k))
        r = y)
    {U : AffineEtaleFormalCharts B S hS X} {Uk : ι → AffineEtaleFormalCharts B S hS X}
    (v : ∀ k, Uk k ⟶ U)
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj Y) ⟶
      U.obj.left}
    {ak : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      (R.affineChartObj (Yk k)) ⟶ (Uk k).obj.left}
    (ha : IsPullback a (R.affineChartMap Y) U.obj.hom R.inclusion)
    (hcomm : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((Space.AffineEtale.toOver B S hS R.space.obj).map (f k)) ≫ a = ak k ≫ (v k).hom.left)
    (x : Space.pointsULift.{u + 1} B S hS U.obj.left.obj) :
    ∃ k, ∃ z : Space.pointsULift.{u + 1} B S hS (Uk k).obj.left.obj,
      Space.pointsMapULift.{u + 1} B S hS _ (v k).hom.left.hom z = x := by
  obtain ⟨q, rfl⟩ := R.surjective_pointsMapULift_of_isPullback ha x
  obtain ⟨k, r, hr⟩ := hf (pointsEquivSchemeSheafified _ q)
  refine ⟨k, Space.pointsMapULift.{u + 1} B S hS _ (ak k).hom
    ((pointsEquivSchemeSheafified _).symm r), ?_⟩
  have hq : Space.pointsMapULift.{u + 1} B S hS _ ((Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map ((Space.AffineEtale.toOver B S hS
        R.space.obj).map (f k))).hom ((pointsEquivSchemeSheafified _).symm r) = q := by
    apply (pointsEquivSchemeSheafified _).injective
    rw [pointsEquivSchemeSheafified_naturality, Equiv.apply_symm_apply, hr]
  rw [← hq]
  rw [← pointsMapULift_comp_apply_aux, ← pointsMapULift_comp_apply_aux]
  exact (congrArg (fun m => Space.pointsMapULift.{u + 1} B S hS _ m.hom
    ((pointsEquivSchemeSheafified _).symm r)) (hcomm k)).symm

end Reduction

/-- **A family of morphisms of charts which is jointly surjective on points is a covering on
affine points.** Let `v_k : U_k ⟶ U` be morphisms of affine étale formal charts over `X` such that
every point of `U` comes from a point of some `U_k`. Then for every affine object `T` of the site
and every `a ∈ U(T)`, the arrows `T' ⟶ T` of the big affine site along which `a` lifts to some
`U_k` form a covering sieve of the big affine fppf site.

The base change of `v_k` along `a` is represented by an affine object `T_k` of the site, étale
over `T` (Stacks 0AKN); the `T_k ⟶ T` are jointly surjective by the hypothesis on points, so they
generate a covering sieve, and `a` lifts along each of them through the cartesian square. -/
theorem mem_topology_of_jointly_surjective_points {ι : Type (u + 1)}
    {U : AffineEtaleFormalCharts B S hS X} {Uk : ι → AffineEtaleFormalCharts B S hS X}
    (v : ∀ k, Uk k ⟶ U)
    (hpoints : ∀ x : Space.pointsULift.{u + 1} B S hS U.obj.left.obj,
      ∃ k, ∃ z : Space.pointsULift.{u + 1} B S hS (Uk k).obj.left.obj,
        Space.pointsMapULift.{u + 1} B S hS _ (v k).hom.left.hom z = x)
    (T : BigAffineFppf B S hS)
    (a : U.obj.left.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))) :
    (⟨fun T' t => ∃ k, ∃ b : (Uk k).obj.left.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T')),
        (v k).hom.left.hom.app _ b =
          U.obj.left.obj.map ((BigAffineFppf.inclusion B S hS).map t).op a,
      fun {T' T''} t ⟨k, b, hb⟩ s => ⟨k, (Uk k).obj.left.obj.map
        ((BigAffineFppf.inclusion B S hS).map s).op b, by
          rw [NatTrans.naturality_apply, hb, Functor.map_comp, op_comp, Functor.map_comp_apply]⟩⟩ :
        Sieve T) ∈ BigAffineFppf.topology B S hS T := by
  let J := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda J
  let incl := BigAffineFppf.inclusion B S hS
  let i : sY.obj (incl.obj T) ⟶ U.obj.left := (Sheaf.sectionEquiv J).symm a
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj (incl.obj T)) := T.property
  let chart : ∀ k, AffineEtaleFormalCharts B S hS U.obj.left := fun k =>
    ⟨Over.mk (v k).hom.left, (Uk k).property.1,
      AffineEtaleFormalCharts.isRepresentableEtale_hom_left (v k)⟩
  let d : ∀ k, AffineEtaleBaseChange B S hS U.obj.left (incl.obj T) i (chart k) := fun k =>
    affineEtaleBaseChangeData B S hS U.property.1 (incl.obj T) hT i (chart k)
  let Tk : ι → BigAffineFppf B S hS := fun k => ⟨(d k).obj, (d k).isAffine⟩
  let tk : ∀ k, Tk k ⟶ T := fun k => ObjectProperty.homMk (d k).proj
  have hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj (incl.obj T),
      ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (d k).proj) := by
    intro x
    let p := (pointsEquivSchemeSheafified (incl.obj T)).symm x
    obtain ⟨k, z, hz⟩ := hpoints (Space.pointsMapULift.{u + 1} B S hS _ i.hom p)
    have sq : IsPullback (d k).fst.hom (sY.map (d k).proj).hom (v k).hom.left.hom i.hom :=
      (d k).isPullback.map (sheafToPresheaf J (Type (u + 1)))
    obtain ⟨w, -, hw⟩ := Space.exists_point_of_isPullbackULift B S hS sq z p hz
    refine ⟨k, pointsEquivSchemeSheafified _ w, ?_⟩
    rw [← pointsEquivSchemeSheafified_naturality, hw, Equiv.apply_symm_apply]
  refine (BigAffineFppf.topology B S hS).superset_covering (S := Sieve.ofArrows Tk tk) ?_ ?_
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro T' t ⟨k⟩
    refine ⟨k, Sheaf.sectionEquiv J (d k).fst, ?_⟩
    calc (v k).hom.left.hom.app _ (Sheaf.sectionEquiv J (d k).fst)
        = Sheaf.sectionEquiv J ((d k).fst ≫ (v k).hom.left) :=
          (Sheaf.sectionEquiv_comp J _ _).symm
      _ = Sheaf.sectionEquiv J (sY.map (d k).proj ≫ i) :=
          congrArg (Sheaf.sectionEquiv J) (d k).isPullback.w
      _ = U.obj.left.obj.map (d k).proj.op (Sheaf.sectionEquiv J i) :=
          Sheaf.sectionEquiv_map_comp J _ _
      _ = _ := by
          rw [Equiv.apply_symm_apply]
          rfl
  · rw [← Functor.functorPushforward_mem_iff (G := incl) (J := BigAffineFppf.topology B S hS)
      (K := J)]
    refine J.superset_covering ?_ (BigFppfOver.ofArrows_mem_topology_of_etale B S hS
      (fun k => (d k).obj) (fun k => (d k).proj) (fun k => (d k).etale) hcov)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Z f ⟨k⟩
    exact ⟨Tk k, tk k, 𝟙 _, Sieve.ofArrows_mk _ _ k, (Category.id_comp _).symm⟩

end AlgebraicGeometry.FormalSpace

end
