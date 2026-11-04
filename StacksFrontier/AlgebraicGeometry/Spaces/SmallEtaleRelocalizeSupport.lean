module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# Supports of sheaves on an algebraic space and on its lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site, let `F` be an algebraic space over `W` and
`Λ_h F` its lower-shriek extension, an algebraic space over `S`.  A geometric point of `F` is a
geometric point of `Λ_h F`, and its small étale neighbourhoods are those of the relocalized
point: the equivalence of small étale sites
`AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence` matches the two categories of
neighbourhoods.  So the stalk of a sheaf on `Λ_h F` at the relocalized point is the stalk of its
restriction to `F`, and the support (Stacks 04KA) of a sheaf on `Λ_h F` corresponds to the
support of its restriction under the bijection of points of Stacks 03I5.

## Main definitions

* `AlgebraicGeometry.Space.GeometricPoint.relocalizeSE`: a geometric point of `F` read on `Λ_h F`.
* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.relocalizeSE`: the equivalence of the categories
  of small étale neighbourhoods.
* `AlgebraicGeometry.Space.stalkSetRelocalizeEquivSE`: the stalks agree.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_relocalizeSE` and
  `AlgebraicGeometry.Space.supportOfSheaf_relocalize_eq_imageSE`: the supports correspond.

## Implementation notes

The functor of `AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence` sends a chart
`a : h_U ⟶ F` to `AlgebraicGeometry.relocalizeChart`, whose value on a morphism `g` into `U`
viewed over `S` is the pair of the factorization `g ≫ U.hom` and the section `a(g)`
(`AlgebraicGeometry.Space.relocalizeChart_app_fst`).  That one computation gives both the lift
of a geometric point to a relocalized neighbourhood and, through
`AlgebraicGeometry.Space.relocalizeChartDescent_spec`, the lift to the neighbourhood of `F`
attached to a neighbourhood of the relocalized point.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}

/-- The value of the extension of a chart `b : h_U ⟶ F` on a morphism `g` into `U` viewed over
`S`: the factorization `g ≫ U.hom` together with the section `b(g)`. -/
theorem relocalizeChart_app_fst {U : BigFppfOver B W hW} (b : yoneda.obj U ⟶ F)
    {Y : BigFppfOver B S hS} (g : Y ⟶ (Over.map h).obj U) :
    ((relocalizeChart B W S hW hS h b).app (op Y) g).1 =
      ⟨g.left ≫ U.hom, b.app (op (Over.mk (g.left ≫ U.hom))) (Over.homMk g.left rfl)⟩ :=
  rfl

/-- The factorization carried by the value of an extended chart. -/
theorem relocalizeChart_app_fst_fst {U : BigFppfOver B W hW} (b : yoneda.obj U ⟶ F)
    {Y : BigFppfOver B S hS} (g : Y ⟶ (Over.map h).obj U) :
    ((relocalizeChart B W S hW hS h b).app (op Y) g).1.1 = g.left ≫ U.hom :=
  rfl

/-- The value of the extension of a chart on the image of a morphism of the site of `W` is the
section the chart names there, with the structure morphism as factorization. -/
theorem relocalizeChart_app_overMap {U Y : BigFppfOver B W hW} (b : yoneda.obj U ⟶ F)
    (k : Y ⟶ U) :
    (relocalizeChart B W S hW hS h b).app (op ((Over.map h).obj Y)) ((Over.map h).map k) =
      OverShriek.relocalizeMk h F (W := op ((Over.map h).obj Y)) Y.hom (b.app (op Y) k) rfl := by
  apply Subtype.ext
  rw [relocalizeChart_app_fst]
  change (⟨k.left ≫ U.hom, b.app (op (Over.mk (k.left ≫ U.hom))) (Over.homMk k.left rfl)⟩ :
      Σ χ : Y.left ⟶ B.obj hW, F.obj (op (Over.mk χ))) = ⟨Y.hom, b.app (op Y) k⟩
  have e : ∀ Z : BigFppfOver B W hW, ∀ f : Z ⟶ U, b.app (op Z) f =
      F.map (Over.homMk f.left (Over.w f) : Over.mk Z.hom ⟶ Over.mk U.hom).op (yonedaEquiv b) := by
    intro Z f
    rw [yonedaEquiv_naturality']
    rfl
  rw [e (Over.mk (k.left ≫ U.hom)) (Over.homMk k.left rfl), e Y k]
  exact OverShriek.sigmaMk_eq F (yonedaEquiv b) _ _ rfl

/-- A geometric point of `F`, read as a geometric point of `Λ_h F`. -/
def GeometricPoint.relocalizeSE (p : GeometricPoint B W hW F) :
    GeometricPoint B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) :=
  ⟨FieldValuedPoint.relocalize B W S hW hS h F p.val, p.property⟩

/-- The relocalized geometric point lies over the relocalized point. -/
theorem GeometricPoint.image_relocalizeSE (p : GeometricPoint B W hW F) :
    (p.relocalizeSE B W S hW hS h).image = pointsRelocalize B W S hW hS h F p.image :=
  rfl

/-- The lift carried by a small étale neighbourhood of `p` is a lift of the relocalized point to
the relocalized chart. -/
theorem SmallEtaleNeighborhood.relocalize_point_compSE {p : GeometricPoint B W hW F}
    (N : SmallEtaleNeighborhood p) :
    ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj N.chart).obj.hom.app
        (op (p.relocalizeSE B W S hW hS h).val.siteObject) ((Over.map h).map N.point) =
      (p.relocalizeSE B W S hW hS h).val.value := by
  refine (relocalizeChart_app_overMap B W S hW hS h N.chart.obj.hom N.point).trans ?_
  rw [N.point_comp]
  rfl

/-- **Small étale neighbourhoods of a geometric point of `F` are small étale neighbourhoods of
the relocalized point**: the chart is relocalized and the lift is unchanged. -/
def SmallEtaleNeighborhood.relocalizeSE (p : GeometricPoint B W hW F) :
    SmallEtaleNeighborhood p ⥤ SmallEtaleNeighborhood (p.relocalizeSE B W S hW hS h) where
  obj N :=
    { chart := (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj N.chart
      point := (Over.map h).map N.point
      point_comp := N.relocalize_point_compSE B W S hW hS h }
  map φ :=
    { hom := (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.map φ.hom
      point_comp := Over.OverMorphism.ext (congrArg (fun k => k.left) φ.point_comp) }
  map_id N := SmallEtaleNeighborhood.Hom.ext
    ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.map_id N.chart)
  map_comp φ ψ := SmallEtaleNeighborhood.Hom.ext
    ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.map_comp φ.hom ψ.hom)

/-- Relocalizing small étale neighbourhoods is faithful: a morphism of neighbourhoods is determined
by its morphism of charts, and relocalization is faithful on charts. -/
instance (p : GeometricPoint B W hW F) :
    (SmallEtaleNeighborhood.relocalizeSE B W S hW hS h p).Faithful where
  map_injective {_ _} _ _ e := SmallEtaleNeighborhood.Hom.ext
    ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.map_injective
      (congrArg SmallEtaleNeighborhood.Hom.hom e))

/-- Relocalizing small étale neighbourhoods is full: a morphism between relocalized
neighbourhoods comes from the preimage of its morphism of charts, which respects the lifts. -/
instance (p : GeometricPoint B W hW F) :
    (SmallEtaleNeighborhood.relocalizeSE B W S hW hS h p).Full where
  map_surjective {N N'} ψ := by
    let φ₀ := (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.preimage ψ.hom
    have hφ₀ : (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.map φ₀ = ψ.hom :=
      (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.map_preimage ψ.hom
    refine ⟨⟨φ₀, Over.OverMorphism.ext ?_⟩, SmallEtaleNeighborhood.Hom.ext hφ₀⟩
    have h1 := congrArg (fun k => k.left) ψ.point_comp
    have h2 := congrArg (fun k => k.hom.left.left) hφ₀
    exact (congrArg (fun k => N.point.left ≫ k) h2).trans h1

variable {h} in
/-- The factorization through `W` that a chart of `Λ_h F` descends along, composed with the
underlying morphism of a lift of the relocalized point, is the structure morphism of the
point. -/
theorem SmallEtaleNeighborhood.point_left_comp_relocalizeChartBase
    {p : GeometricPoint B W hW F}
    (M : SmallEtaleNeighborhood (p.relocalizeSE B W S hW hS h)) :
    M.point.left ≫ relocalizeChartBase B W S hW hS h M.chart.obj = p.val.siteObject.hom := by
  have hspec := congrArg (fun a => (a.app (op (p.relocalizeSE B W S hW hS h).val.siteObject)
    M.point).1.1) (relocalizeChartDescent_spec B W S hW hS h M.chart.obj)
  have hv := congrArg (fun z => z.1.1) M.point_comp
  simp only at hspec hv
  rw [hv] at hspec
  refine (Eq.trans ?_ hspec.symm)
  change M.point.left ≫ relocalizeChartBase B W S hW hS h M.chart.obj =
    (M.point.left ≫ 𝟙 _) ≫ relocalizeChartBase B W S hW hS h M.chart.obj
  rw [Category.comp_id]

/-- The value of a chart of `Λ_h F` on a morphism from an object of the site of `W` whose
underlying morphism factors the descended structure morphism: it is the section named by the
descended chart of `F`. -/
theorem relocalizeChart_app_eq_relocalizeMk_descent
    (V : CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj F))
    {Y : BigFppfOver B W hW} (k : (Over.map h).obj Y ⟶ V.left)
    (hk : k.left ≫ relocalizeChartBase B W S hW hS h V = Y.hom) :
    V.hom.app (op ((Over.map h).obj Y)) k =
      OverShriek.relocalizeMk h F (W := op ((Over.map h).obj Y)) Y.hom
        ((relocalizeChartDescent B W S hW hS h V).app (op Y) (Over.homMk k.left hk)) rfl := by
  have hspec := congrArg (fun a => a.app (op ((Over.map h).obj Y)) k)
    (relocalizeChartDescent_spec B W S hW hS h V)
  refine hspec.trans ?_
  change (relocalizeChart B W S hW hS h (relocalizeChartDescent B W S hW hS h V)).app _
      (k ≫ relocalizeBaseHom B W S hW hS h (relocalizeChartBase_comp B W S hW hS h V)) = _
  have hk' : k ≫ relocalizeBaseHom B W S hW hS h (relocalizeChartBase_comp B W S hW hS h V) =
      (Over.map h).map (Over.homMk k.left hk : Y ⟶ Over.mk (relocalizeChartBase B W S hW hS h V)) :=
    Over.OverMorphism.ext (by simp [relocalizeBaseHom])
  rw [hk']
  exact relocalizeChart_app_overMap B W S hW hS h _ _

variable {h} in
/-- A small étale neighbourhood of the relocalized point, read back as a small étale
neighbourhood of the original geometric point. -/
def SmallEtaleNeighborhood.derelocalizeSE {p : GeometricPoint B W hW F}
    (M : SmallEtaleNeighborhood (p.relocalizeSE B W S hW hS h)) : SmallEtaleNeighborhood p where
  chart := (SmallEtale.relocalizeEquivalence B W S hW hS h F).inverse.obj M.chart
  point := Over.homMk M.point.left (M.point_left_comp_relocalizeChartBase B W S hW hS)
  point_comp := by
    have e := (relocalizeChart_app_eq_relocalizeMk_descent B W S hW hS h M.chart.obj
      (Y := p.val.siteObject) M.point
      (M.point_left_comp_relocalizeChartBase B W S hW hS)).symm.trans M.point_comp
    have e2 : (⟨p.val.siteObject.hom,
        (relocalizeChartDescent B W S hW hS h M.chart.obj).app (op p.val.siteObject)
          (Over.homMk M.point.left (M.point_left_comp_relocalizeChartBase B W S hW hS))⟩ :
        Σ χ : p.val.siteObject.left ⟶ B.obj hW, F.obj (op (Over.mk χ))) =
        ⟨p.val.siteObject.hom, p.val.value⟩ := congrArg (fun z => z.1) e
    change (relocalizeChartDescent B W S hW hS h M.chart.obj).app (op p.val.siteObject)
      (Over.homMk M.point.left (M.point_left_comp_relocalizeChartBase B W S hW hS)) = p.val.value
    exact eq_of_heq (Sigma.mk.inj_iff.mp e2).2

/-- Relocalizing small étale neighbourhoods is essentially surjective: every small étale
neighbourhood of the relocalized point is isomorphic to the relocalization of its
derelocalization. -/
instance (p : GeometricPoint B W hW F) :
    (SmallEtaleNeighborhood.relocalizeSE B W S hW hS h p).EssSurj where
  mem_essImage M := ⟨M.derelocalizeSE B W S hW hS, ⟨
    { hom :=
        { hom := (SmallEtale.relocalizeEquivalence B W S hW hS h F).counit.app M.chart
          point_comp := Over.OverMorphism.ext (by
            change M.point.left ≫
              ((SmallEtale.relocalizeEquivalence B W S hW hS h F).counit.app
                M.chart).hom.left.left = M.point.left
            rw [show ((SmallEtale.relocalizeEquivalence B W S hW hS h F).counit.app
                M.chart).hom.left.left = 𝟙 _ from
              relocalizeChartsDescentIso_hom_left_left B W S hW hS h M.chart.obj]
            exact Category.comp_id _) }
      inv :=
        { hom := (SmallEtale.relocalizeEquivalence B W S hW hS h F).counitInv.app M.chart
          point_comp := Over.OverMorphism.ext (by
            change M.point.left ≫
              ((SmallEtale.relocalizeEquivalence B W S hW hS h F).counitInv.app
                M.chart).hom.left.left = M.point.left
            rw [show ((SmallEtale.relocalizeEquivalence B W S hW hS h F).counitInv.app
                M.chart).hom.left.left = 𝟙 _ from
              relocalizeChartsDescentIso_inv_left_left B W S hW hS h M.chart.obj]
            exact Category.comp_id _) }
      hom_inv_id := SmallEtaleNeighborhood.Hom.ext
        ((SmallEtale.relocalizeEquivalence B W S hW hS h F).counitIso.hom_inv_id_app M.chart)
      inv_hom_id := SmallEtaleNeighborhood.Hom.ext
        ((SmallEtale.relocalizeEquivalence B W S hW hS h F).counitIso.inv_hom_id_app
          M.chart) }⟩⟩

/-- The relocalization of small étale neighbourhoods is an equivalence of categories. -/
instance (p : GeometricPoint B W hW F) :
    (SmallEtaleNeighborhood.relocalizeSE B W S hW hS h p).IsEquivalence where

/-- **The stalk of a presheaf on `Λ_h F` at the relocalized point is the stalk of its
restriction to `F`.** -/
def stalkSetRelocalizeEquivSE (p : GeometricPoint B W hW F)
    (P : (SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))ᵒᵖ ⥤ Type v) :
    stalkSet p ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.op ⋙ P) ≃
      stalkSet (p.relocalizeSE B W S hW hS h) P :=
  Equiv.ofBijective
    (Functor.colimitTypePrecomp (SmallEtaleNeighborhood.relocalizeSE B W S hW hS h p).op
      (SmallEtaleNeighborhood.sections (x := p.relocalizeSE B W S hW hS h) P))
    (Functor.bijective_colimitTypePrecomp _ _)

variable (hF' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))

include hF' in
/-- **The support of an abelian sheaf on `Λ_h F`, read on `F`.** A point of `F` lies in the
support of the restriction of `M` to the small étale site of `F` exactly when the corresponding
point of `Λ_h F` lies in the support of `M`. -/
theorem supportOfSheaf_relocalizeSE
    (M : Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      AddCommGrpCat.{v}) :
    supportOfSheaf B W hW F
        (((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B W hW F) (SmallEtale.topology B S hS _)).obj
          M) =
      pointsRelocalize B W S hW hS h F ⁻¹' supportOfSheaf B S hS _ M := by
  ext x
  constructor
  · rintro ⟨p, hp, hn⟩
    refine ⟨p.relocalizeSE B W S hW hS h, (GeometricPoint.image_relocalizeSE B W S hW hS h p).trans
      (congrArg _ hp), fun hs => hn ?_⟩
    exact (stalkSetRelocalizeEquivSE B W S hW hS h p
      (M.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})).subsingleton_congr.2 hs
  · rintro ⟨q, hq, hn⟩
    obtain ⟨p, hp⟩ := exists_geometricRepresentative B W hW F x
    have hp' : (p.relocalizeSE B W S hW hS h).LiesOver (pointsRelocalize B W S hW hS h F x) :=
      (GeometricPoint.image_relocalizeSE B W S hW hS h p).trans (congrArg _ hp)
    obtain ⟨φ⟩ := stalkSetFunctor_iso_of_liesOver.{u, v} hF' q (p.relocalizeSE B W S hW hS h) hq hp'
    refine ⟨p, hp, fun hs => hn ?_⟩
    have h1 := (stalkSetRelocalizeEquivSE B W S hW hS h p
      (M.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})).subsingleton_congr.1 hs
    exact ((φ.app (M.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})).toEquiv).subsingleton_congr.2
      h1

include hF' in
/-- **The support of an abelian sheaf on `Λ_h F` is the image of the support of its restriction
to `F`.** -/
theorem supportOfSheaf_relocalize_eq_imageSE
    (M : Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      AddCommGrpCat.{v}) :
    supportOfSheaf B S hS _ M = pointsRelocalize B W S hW hS h F ''
      supportOfSheaf B W hW F
        (((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B W hW F) (SmallEtale.topology B S hS _)).obj
          M) := by
  rw [supportOfSheaf_relocalizeSE B W S hW hS h hF' M,
    Set.image_preimage_eq _ (pointsRelocalize_surjective B W S hW hS h F)]

end AlgebraicGeometry.Space

end
