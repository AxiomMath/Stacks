module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# Supports of sheaves across the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site and `X` an algebraic space over `T`, with
lower-shriek extension `Λ X` over `S`. A geometric point of `X` is a geometric point of `Λ X`, and
its small étale neighbourhoods are those of the relocalized point, the equivalence of small étale
sites matching the two categories of neighbourhoods. So the stalk of a sheaf on `Λ X` at the
relocalized point is the stalk of its restriction to `X`, and the support (Stacks 04KA) of a sheaf
on `Λ X` corresponds to the support of its restriction under the bijection of points of Stacks
03I5.

## Main definitions

* `AlgebraicGeometry.Space.GeometricPoint.relocalize`: a geometric point of `X` read on `Λ X`.
* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.relocalize`: the equivalence of categories of
  small étale neighbourhoods.
* `AlgebraicGeometry.Space.stalkSetRelocalizeEquiv`: the stalks agree.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_relocalize` and
  `AlgebraicGeometry.Space.supportOfSheaf_relocalize_eq_image`: the supports correspond.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}

/-- A geometric point of `X`, read as a geometric point of `Λ X`. -/
def GeometricPoint.relocalize (p : GeometricPoint B T hT X) :
    GeometricPoint B S hS ((OverShriek.relocalizePresheafFunctor g).obj X) :=
  ⟨FieldValuedPoint.relocalize B T S hT hS g X p.val, p.property⟩

/-- The relocalized geometric point lies over the relocalized point. -/
theorem GeometricPoint.image_relocalize (p : GeometricPoint B T hT X) :
    (p.relocalize B hT hS g).image = pointsRelocalize B T S hT hS g X p.image :=
  rfl

/-- The chart of `X` attached to a geometric point. -/
abbrev GeometricPoint.chart (p : GeometricPoint B T hT X) : CostructuredArrow yoneda X :=
  CostructuredArrow.mk (yonedaEquiv.symm p.val.value)

/-- A small étale neighbourhood of a geometric point is a morphism from the chart of the point. -/
def SmallEtaleNeighborhood.chartHom {p : GeometricPoint B T hT X} (N : SmallEtaleNeighborhood p) :
    p.chart B hT ⟶ N.chart.obj :=
  CostructuredArrow.homMk N.point (yonedaEquiv.injective (by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact N.point_comp.trans (Equiv.apply_symm_apply yonedaEquiv _).symm))

variable (hX : IsAlgebraicSpace B T hT X)

/-- The lift carried by a small étale neighbourhood of `p` is a lift of the relocalized point to
the relocalized chart. -/
theorem SmallEtaleNeighborhood.relocalize_point_comp {p : GeometricPoint B T hT X}
    (N : SmallEtaleNeighborhood p) :
    ((SmallEtale.relocalize B hT hS g X hX).functor.obj N.chart).obj.hom.app
        (op (p.relocalize B hT hS g).val.siteObject) ((Over.map g).map N.point) =
      (p.relocalize B hT hS g).val.value := by
  have h' := congrArg yonedaEquiv (OverShriek.relocalizeChart_w g X (N.chartHom B hT))
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at h'
  refine h'.trans ((Equiv.apply_symm_apply yonedaEquiv _).trans ?_)
  exact congrArg (fun s => OverShriek.relocalizeMk g X (W := op ((Over.map g).obj p.val.siteObject))
    (⟨p.val.toBase⟩ : B.obj p.val.contained ⟶ B.obj hT) s rfl) (Equiv.apply_symm_apply _ _)

/-- **Small étale neighbourhoods of a geometric point of `X` are small étale neighbourhoods of
the relocalized point**: the chart is relocalized and the lift is unchanged. -/
def SmallEtaleNeighborhood.relocalize (p : GeometricPoint B T hT X) :
    SmallEtaleNeighborhood p ⥤ SmallEtaleNeighborhood (p.relocalize B hT hS g) where
  obj N :=
    { chart := (SmallEtale.relocalize B hT hS g X hX).functor.obj N.chart
      point := (Over.map g).map N.point
      point_comp := N.relocalize_point_comp B hT hS g hX }
  map φ :=
    { hom := (SmallEtale.relocalize B hT hS g X hX).functor.map φ.hom
      point_comp := Over.OverMorphism.ext (congrArg (fun k => k.left) φ.point_comp) }
  map_id N := SmallEtaleNeighborhood.Hom.ext
    ((SmallEtale.relocalize B hT hS g X hX).functor.map_id N.chart)
  map_comp φ ψ := SmallEtaleNeighborhood.Hom.ext
    ((SmallEtale.relocalize B hT hS g X hX).functor.map_comp φ.hom ψ.hom)

/-- The relocalization of small étale neighbourhoods is faithful. -/
instance (p : GeometricPoint B T hT X) :
    (SmallEtaleNeighborhood.relocalize B hT hS g hX p).Faithful where
  map_injective {_ _} _ _ h := SmallEtaleNeighborhood.Hom.ext
    ((SmallEtale.relocalize B hT hS g X hX).functor.map_injective
      (congrArg SmallEtaleNeighborhood.Hom.hom h))

/-- The relocalization of small étale neighbourhoods is full. -/
instance (p : GeometricPoint B T hT X) :
    (SmallEtaleNeighborhood.relocalize B hT hS g hX p).Full where
  map_surjective {N N'} ψ := by
    let φ₀ := (SmallEtale.relocalize B hT hS g X hX).functor.preimage ψ.hom
    have hφ₀ : (SmallEtale.relocalize B hT hS g X hX).functor.map φ₀ = ψ.hom :=
      (SmallEtale.relocalize B hT hS g X hX).functor.map_preimage ψ.hom
    refine ⟨⟨φ₀, Over.OverMorphism.ext ?_⟩, SmallEtaleNeighborhood.Hom.ext hφ₀⟩
    have h1 := congrArg (fun k => k.left) ψ.point_comp
    have h2 := congrArg (fun k => k.hom.left.left) hφ₀
    exact (congrArg (fun k => N.point.left ≫ k) h2).trans h1

/-- A section of `X` over a chart, restricted along a lift of a geometric point through the
factorization carried by the relocalized point, is the section of the point. -/
theorem GeometricPoint.map_homMk_eq_value_of_eq_relocalize (p : GeometricPoint B T hT X)
    (z : ((OverShriek.relocalizePresheafFunctor g).obj X).obj
      (op ((Over.map g).obj p.val.siteObject)))
    (hz : z = (p.relocalize B hT hS g).val.value) {V : BigFppfOver B T hT}
    (c : X.obj (op V)) (l : p.val.siteObject.left ⟶ V.left)
    (h₁ : l ≫ V.hom = z.1.1) (h₂ : l ≫ V.hom = p.val.siteObject.hom)
    (hc : X.map (Over.homMk l h₁ : Over.mk z.1.1 ⟶ V).op c = z.1.2) :
    X.map (Over.homMk l h₂ : p.val.siteObject ⟶ V).op c = p.val.value := by
  subst hz
  exact hc

/-- A small étale neighbourhood of the relocalized point, read back as a small étale
neighbourhood of the original geometric point. -/
def SmallEtaleNeighborhood.derelocalize {p : GeometricPoint B T hT X}
    (M : SmallEtaleNeighborhood (p.relocalize B hT hS g)) : SmallEtaleNeighborhood p where
  chart := (SmallEtale.relocalize B hT hS g X hX).inverse.obj M.chart
  point := Over.homMk M.point.left ((OverShriek.chartFactor_comp g X (M.chartHom B hS)).trans
    (congrArg (fun z : ((OverShriek.relocalizePresheafFunctor g).obj X).obj
        (op ((Over.map g).obj p.val.siteObject)) => z.1.1)
      (Equiv.apply_symm_apply yonedaEquiv _)))
  point_comp := GeometricPoint.map_homMk_eq_value_of_eq_relocalize B hT hS g p _
    (Equiv.apply_symm_apply yonedaEquiv _) _ _
    (OverShriek.chartFactor_comp g X (M.chartHom B hS)) _
    (OverShriek.chartSection_map g X (M.chartHom B hS))

/-- The relocalization of small étale neighbourhoods is essentially surjective. -/
instance (p : GeometricPoint B T hT X) :
    (SmallEtaleNeighborhood.relocalize B hT hS g hX p).EssSurj where
  mem_essImage M := ⟨M.derelocalize B hT hS g hX, ⟨
    { hom :=
        { hom := (SmallEtale.relocalize B hT hS g X hX).counit.app M.chart
          point_comp := Over.OverMorphism.ext (Category.comp_id M.point.left) }
      inv :=
        { hom := (SmallEtale.relocalize B hT hS g X hX).counitInv.app M.chart
          point_comp := Over.OverMorphism.ext (Category.comp_id M.point.left) }
      hom_inv_id := SmallEtaleNeighborhood.Hom.ext
        ((SmallEtale.relocalize B hT hS g X hX).counitIso.hom_inv_id_app M.chart)
      inv_hom_id := SmallEtaleNeighborhood.Hom.ext
        ((SmallEtale.relocalize B hT hS g X hX).counitIso.inv_hom_id_app M.chart) }⟩⟩

/-- The relocalization of small étale neighbourhoods is an equivalence of categories. -/
instance (p : GeometricPoint B T hT X) :
    (SmallEtaleNeighborhood.relocalize B hT hS g hX p).IsEquivalence where

/-- **The stalk of a presheaf on `Λ X` at the relocalized point is the stalk of its restriction
to `X`.** -/
def stalkSetRelocalizeEquiv (p : GeometricPoint B T hT X)
    (P : (SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))ᵒᵖ ⥤ Type v) :
    stalkSet p ((SmallEtale.relocalize B hT hS g X hX).functor.op ⋙ P) ≃
      stalkSet (p.relocalize B hT hS g) P :=
  Equiv.ofBijective
    (Functor.colimitTypePrecomp (SmallEtaleNeighborhood.relocalize B hT hS g hX p).op
      (SmallEtaleNeighborhood.sections (x := p.relocalize B hT hS g) P))
    (Functor.bijective_colimitTypePrecomp _ _)

/-- **The support of an abelian sheaf on `Λ X`, read on `X`.** A point of `X` lies in the
support of the restriction of `M` to the small étale site of `X` exactly when the corresponding
point of `Λ X` lies in the support of `M`. -/
theorem supportOfSheaf_relocalize
    (M : Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))
      AddCommGrpCat.{v}) :
    supportOfSheaf B T hT X
        (((SmallEtale.relocalize B hT hS g X hX).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _)).obj M) =
      pointsRelocalize B T S hT hS g X ⁻¹' supportOfSheaf B S hS _ M := by
  have e (p : GeometricPoint B T hT X) := (stalkSetRelocalizeEquiv B hT hS g hX p
    (M.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})).subsingleton_congr
  ext x
  constructor
  · rintro ⟨p, hp, hn⟩
    exact ⟨p.relocalize B hT hS g, congrArg (pointsRelocalize B T S hT hS g X) hp,
      fun hs => hn ((e p).2 hs)⟩
  · rintro ⟨q, hq, hn⟩
    obtain ⟨p, hp⟩ := exists_geometricRepresentative B T hT X x
    obtain ⟨φ⟩ := stalkSetFunctor_iso_of_liesOver.{u, v}
      (isAlgebraicSpace_relocalize' B hT hS g X hX) q (p.relocalize B hT hS g) hq
      (congrArg (pointsRelocalize B T S hT hS g X) hp)
    exact ⟨p, hp, fun hs => hn ((φ.app _).toEquiv.subsingleton_congr.2 ((e p).1 hs))⟩

/-- **The support of an abelian sheaf on `Λ X` is the image of the support of its restriction
to `X`.** -/
theorem supportOfSheaf_relocalize_eq_image
    (M : Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))
      AddCommGrpCat.{v}) :
    supportOfSheaf B S hS _ M = pointsRelocalize B T S hT hS g X ''
      supportOfSheaf B T hT X
        (((SmallEtale.relocalize B hT hS g X hX).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B T hT X)
          (SmallEtale.topology B S hS _)).obj M) := by
  rw [supportOfSheaf_relocalize B hT hS g hX M,
    Set.image_preimage_eq _ (pointsRelocalize_surjective B T S hT hS g X)]

end AlgebraicGeometry.Space

end
