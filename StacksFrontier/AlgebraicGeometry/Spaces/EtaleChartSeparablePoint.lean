module

public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationLocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.Deformation.Artin.SliceTangentSpace

/-!
# A point of an étale chart over a point with exact residue field

Let `Q` be an algebraic space over `S` with a morphism `s : Q ⟶ V` to a scheme `V`, and let
`r : Spec l ⟶ Q` be a point lying over a point `ν : Spec l ⟶ V` whose residue field is exactly
`l` (the map `κ(ν) ⟶ l` is surjective). For an étale surjective scheme chart `a : W ⟶ Q` there are
a finite separable extension `L/l` and a point `w : Spec L ⟶ W` over `r` such that `L` is
separable over the residue field of `W` at `w`. The same holds at the diagonal point `e(ν)` of a
presented self-intersection `R = V ×_𝒳 V` of a 1-morphism from a scheme to an algebraic stack,
with `s` the source morphism.

## Main results

* `Algebra.isSeparable_of_comp_eq_comp_of_bijective`: separability over an intermediate field.
* `AlgebraicGeometry.isSeparable_residueField_of_comp_eq`: the residue field of a point over a
  point with exact residue field.
* `AlgebraicGeometry.Space.exists_point_isSeparable_of_etale`: the point of a given étale chart.
* `AlgebraicGeometry.Space.exists_etaleChart_point_isSeparable`: the same for some étale chart of
  an algebraic space.
* `AlgebraicGeometry.Stack.selfIntersectionDiagonalMap_comp_sourceMap`: the diagonal of a
  presented self-intersection is a section of its source morphism.
* `AlgebraicGeometry.Stack.exists_etaleChart_point_isSeparable_selfIntersection`: the statement
  at the diagonal point of a presented self-intersection.

## References

* [Stacks Project, Tag 0DSB](https://stacks.math.columbia.edu/tag/0DSB)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- **Separability descends to an intermediate field through a bijection.** Let `F ⟶ K ⟶ L`
be field homomorphisms whose composite is `F ≃ l ⟶ L` for a bijection `θ : F ⟶ l` and a
homomorphism `β : l ⟶ L` making `L` separable over `l`. Then `L` is separable over `K`. -/
theorem Algebra.isSeparable_of_comp_eq_comp_of_bijective {F K L l : Type*} [Field F] [Field K]
    [Field L] [Field l] [Algebra l L] [Algebra.IsSeparable l L] (θ : F →+* l)
    (hθ : Function.Bijective θ) (ι : F →+* K) (φ : K →+* L)
    (h : φ.comp ι = (algebraMap l L).comp θ) :
    letI := φ.toAlgebra; Algebra.IsSeparable K L := by
  let : Algebra F L := (φ.comp ι).toAlgebra
  have hF : Algebra.IsSeparable F L :=
    Algebra.IsSeparable.of_equiv_equiv (RingEquiv.ofBijective θ hθ).symm (RingEquiv.refl L) (by
      ext x
      show φ (ι ((RingEquiv.ofBijective θ hθ).symm x)) = algebraMap l L x
      rw [← RingHom.comp_apply, h, RingHom.comp_apply]
      exact congrArg (algebraMap l L) ((RingEquiv.ofBijective θ hθ).apply_symm_apply x))
  let : Algebra F K := ι.toAlgebra
  let : Algebra K L := φ.toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.isSeparable_tower_top_of_isSeparable F K L

namespace AlgebraicGeometry

/-- **The residue field of a point over a separable extension of an exact residue field.** Let
`e : Spec l ⟶ X` be a point whose residue field map `κ(x) ⟶ l` is surjective (so `κ(x) = l`),
and let `w : Spec L ⟶ Y` be a point of a scheme over `X` lying over `e` along `Spec L ⟶ Spec l`
for a separable extension `L/l`. Then `L` is separable over the residue field of `Y` at the image
of `w`. -/
theorem isSeparable_residueField_of_comp_eq {L l : Type u} [Field L] [Field l] [Algebra l L]
    [Algebra.IsSeparable l L] {X Y : Scheme.{u}} (q : Y ⟶ X) (w : Spec (.of L) ⟶ Y)
    (e : Spec (.of l) ⟶ X) (h : w ≫ q = Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫ e)
    (he : Function.Surjective (Scheme.SpecToEquivOfField l X e).2) :
    letI := (Scheme.SpecToEquivOfField L Y w).2.hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (Scheme.SpecToEquivOfField L Y w).1) L := by
  set yw := Scheme.SpecToEquivOfField L Y w
  set xe := Scheme.SpecToEquivOfField l X e
  have h1 : (Scheme.SpecToEquivOfField L X).symm ⟨q yw.1, q.residueFieldMap yw.1 ≫ yw.2⟩ =
      w ≫ q := by
    rw [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc]
    exact congrArg (· ≫ q) ((Scheme.SpecToEquivOfField L Y).left_inv w)
  have h2 : (Scheme.SpecToEquivOfField L X).symm
      ⟨xe.1, xe.2 ≫ CommRingCat.ofHom (algebraMap l L)⟩ =
      Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫ e := by
    rw [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]
    exact congrArg _ ((Scheme.SpecToEquivOfField l X).left_inv e)
  obtain ⟨hpt, hmap⟩ := Scheme.SpecToEquivOfField_eq_iff.1
    ((Scheme.SpecToEquivOfField L X).symm.injective (h1.trans (h.trans h2.symm)))
  refine Algebra.isSeparable_of_comp_eq_comp_of_bijective
    ((X.residueFieldCongr hpt).hom ≫ xe.2).hom ?_ (q.residueFieldMap yw.1).hom yw.2.hom
    (congrArg CommRingCat.Hom.hom hmap)
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨a, ha⟩ := he x
  refine ⟨(X.residueFieldCongr hpt).inv a, ?_⟩
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  simp only [Iso.inv_hom_id_apply]
  exact ha

namespace Space

open Deformation.Artin.SliceTangent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A point of an étale chart over a point with exact residue field.** Let `a : W ⟶ Q` be an
étale surjective scheme chart of a presheaf `Q` on the big fppf site of `S`, let `s : Q ⟶ V` be a
morphism to a scheme, and let `r` be a point of `Q` over the object `u₀` of `(Sch/V)` lying over
`Spec l ⟶ Spec Λ ⟶ S`, with `r ≫ s = u₀`, such that the residue field map `κ(ν) ⟶ l` of the
point `ν : Spec l ⟶ V` of `u₀` is surjective. Then there are a finite separable extension `L/l`
and an object `w₀` of `(Sch/W)` lying over `Spec L ⟶ Spec Λ ⟶ S`, with an arrow
`π : w₀ ⟶ u₀` over `Spec L ⟶ Spec l` such that `w₀ ≫ a = π ≫ r` (so `w₀` is a point of
`W ×_Q Spec l`), and `L` is separable over the residue field of `W` at the image of `w₀`. -/
theorem exists_point_isSeparable_of_etale
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS} (a : yoneda.obj W ⟶ Q)
    (haSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (haEt : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    {V : BigFppfOver B S hS} (s : Q ⟶ yoneda.obj V)
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] {iΛ : Spec (.of Λ) ⟶ S}
    (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (r : yoneda.obj u₀.left ⟶ Q) (hr : r ≫ s = yoneda.map u₀.hom)
    (hres : Function.Surjective (Scheme.SpecToEquivOfField l _ (pointMap hu₀)).2) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra l L) (_ : Algebra Λ L) (_ : IsScalarTower Λ l L),
      Module.Finite l L ∧ Algebra.IsSeparable l L ∧
      ∃ (w₀ : Over W)
        (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
        (π : w₀.left ⟶ u₀.left),
        eqToHom (congrArg Over.left hw₀).symm ≫ B.inclusion.map π.left ≫
            eqToHom (congrArg Over.left hu₀) = Spec.map (CommRingCat.ofHom (algebraMap l L)) ∧
        yoneda.map w₀.hom ≫ a = yoneda.map π ≫ r ∧
        letI := (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).2.hom.toAlgebra
        Algebra.IsSeparable ((B.inclusion.obj W.left).residueField
          (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).1) L := by
  classical
  have hrep := haEt.rep
  let Pb : BigFppfOver B S hS := hrep.pullback r
  let snd : Pb ⟶ u₀.left := hrep.snd r
  let fst : Pb ⟶ W := hrep.fst' r
  have hw : yoneda.map fst ≫ a = yoneda.map snd ≫ r := by
    rw [hrep.map_fst']
    exact hrep.w r
  have het : Etale (B.inclusion.map snd.left) := haEt.property_snd r
  have hsu : Surjective (B.inclusion.map snd.left) := haSurj.property_snd r
  let X : Scheme.{u} := B.inclusion.obj Pb.left
  have hY : B.inclusion.obj u₀.left.left = Spec (.of l) := congrArg Over.left hu₀
  let sl : X ⟶ Spec (.of l) := B.inclusion.map snd.left ≫ eqToHom hY
  have : Smooth sl := inferInstance
  have : Surjective sl := inferInstance
  obtain ⟨t₀, -⟩ := sl.surjective (IsLocalRing.closedPoint l)
  have : Nonempty X := ⟨t₀⟩
  obtain ⟨p, -, hfin, hsep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth sl).nonempty
  let L := X.residueField p
  let algl : Algebra l L :=
    ((Scheme.ΓSpecIso (.of l)).inv ≫ sl.appTop ≫ X.Γevaluation p).hom.toAlgebra
  let algΛ : Algebra Λ L := ((algebraMap l L).comp (algebraMap Λ l)).toAlgebra
  have : IsScalarTower Λ l L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.IsSeparable l L := hsep
  have hL : B.Contains (Spec (.of L)) := B.residueField_spec_contains Pb.left.2 p
  let jp : B.obj hL ⟶ Pb.left := B.inclusion.preimage (X.fromSpecResidueField p)
  have hjp : B.inclusion.map jp = X.fromSpecResidueField p := B.inclusion.map_preimage _
  let PL : BigFppfOver B S hS := Over.mk (jp ≫ Pb.hom)
  let ι : PL ⟶ Pb := Over.homMk jp rfl
  let π : PL ⟶ u₀.left := ι ≫ snd
  let w₀ : Over W := Over.mk (ι ≫ fst)
  have hUhom : B.inclusion.map u₀.left.hom =
      eqToHom hY ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ :=
    ((congrArg (· ≫ _) (Over.eqToHom_left hu₀).symm).trans (Over.w (eqToHom hu₀))).symm
  have hπl : B.inclusion.map π.left ≫ eqToHom hY =
      Spec.map (CommRingCat.ofHom (algebraMap l L)) := by
    show B.inclusion.map (jp ≫ snd.left) ≫ eqToHom hY = _
    rw [Functor.map_comp, hjp, Category.assoc]
    exact (SpecMap_algebraMap_residueField sl p).symm
  have hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ) := by
    have hΛL : CommRingCat.ofHom (algebraMap Λ L) =
        CommRingCat.ofHom (algebraMap Λ l) ≫ CommRingCat.ofHom (algebraMap l L) := rfl
    show Over.mk (B.inclusion.map PL.hom) = _
    rw [← Over.w π, Functor.map_comp, hUhom, ← Category.assoc, hπl, hΛL, Spec.map_comp,
      Category.assoc]
  have hπ : eqToHom (congrArg Over.left hw₀).symm ≫ B.inclusion.map π.left ≫
      eqToHom (congrArg Over.left hu₀) = Spec.map (CommRingCat.ofHom (algebraMap l L)) :=
    (Category.id_comp _).trans hπl
  have hyon : yoneda.map w₀.hom ≫ a = yoneda.map π ≫ r := by
    show yoneda.map (ι ≫ fst) ≫ a = yoneda.map (ι ≫ snd) ≫ r
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hw]
  refine ⟨L, inferInstance, algl, algΛ, inferInstance, hfin, hsep, w₀, hw₀, π, hπ, hyon, ?_⟩
  let qs : W ⟶ V := yoneda.preimage (a ≫ s)
  have hq : w₀.hom ≫ qs = π ≫ u₀.hom := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, ← Category.assoc, hyon,
      Category.assoc, hr]
  have hcomp : pointMap hw₀ ≫ B.inclusion.map qs.left =
      Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫ pointMap hu₀ := by
    have h1 : B.inclusion.map w₀.hom.left ≫ B.inclusion.map qs.left =
        B.inclusion.map π.left ≫ B.inclusion.map u₀.hom.left := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun f => B.inclusion.map f.left) hq
    rw [← hπ]
    simp only [pointMap, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [h1]
  exact isSeparable_residueField_of_comp_eq (B.inclusion.map qs.left) (pointMap hw₀)
    (pointMap hu₀) hcomp hres

/-- **An étale chart point over a point with exact residue field.** For an algebraic space `Q` with
a morphism `s : Q ⟶ V` to a scheme and a point `r` of `Q` over a point `ν` of `V` with residue
field exactly `l`, some étale surjective scheme chart `a : W ⟶ Q` has a point `w₀` over `r` with
residue field `L` finite separable over `l` and separable over the residue field of `W` at `w₀`. -/
theorem exists_etaleChart_point_isSeparable
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    {V : BigFppfOver B S hS} (s : Q ⟶ yoneda.obj V)
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] {iΛ : Spec (.of Λ) ⟶ S}
    (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (r : yoneda.obj u₀.left ⟶ Q) (hr : r ≫ s = yoneda.map u₀.hom)
    (hres : Function.Surjective (Scheme.SpecToEquivOfField l _ (pointMap hu₀)).2) :
    ∃ (W : BigFppfOver B S hS) (a : yoneda.obj W ⟶ Q),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra l L) (_ : Algebra Λ L) (_ : IsScalarTower Λ l L),
        Module.Finite l L ∧ Algebra.IsSeparable l L ∧
        ∃ (w₀ : Over W)
          (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
          (π : w₀.left ⟶ u₀.left),
          eqToHom (congrArg Over.left hw₀).symm ≫ B.inclusion.map π.left ≫
              eqToHom (congrArg Over.left hu₀) = Spec.map (CommRingCat.ofHom (algebraMap l L)) ∧
          yoneda.map w₀.hom ≫ a = yoneda.map π ≫ r ∧
          letI := (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).2.hom.toAlgebra
          Algebra.IsSeparable ((B.inclusion.obj W.left).residueField
            (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).1) L := by
  obtain ⟨W, a, hsurj, het⟩ := hQ.exists_atlas
  exact ⟨W, a, hsurj, het, exists_point_isSeparable_of_etale a hsurj het s u₀ hu₀ r hr hres⟩

end Space

namespace Stack

universe w

/-- **The diagonal of a self-intersection is a section of its source morphism.** For a presented
self-intersection `R = U ×_𝒳 U` of a 1-morphism `f : U ⟶ 𝒳`, the diagonal `e : U ⟶ R` induced by
a mediating morphism `δ` from the tautological square, followed by the source morphism
`s : R ⟶ U`, is the identity. -/
theorem selfIntersectionDiagonalMap_comp_sourceMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (sq : Bicategory.TwoCommSq f f)
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eU : StacksRepresentableCFG.EquivalenceOver
      (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (eR : StacksRepresentableCFG.EquivalenceOver
      sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq) :
    selfIntersectionDiagonalMap B S hS U f sq R eU eR δ ≫
      selfIntersectionSourceMap B S hS U f sq R eU eR = 𝟙 _ := by
  rw [← representingMap_comp B S hS _ _ _ eU eR eU δ.hom.hom sq.snd.hom]
  exact (representingMap_congr_twoIso B S hS _ _ eU eU
    (algebraicStacksTwoIsoHom B S hS δ.isoSnd.symm)).trans (representingMap_id B S hS _ _ eU)

open Deformation.Artin.SliceTangent in
/-- **An étale chart point over the diagonal point of a self-intersection.** Let `R = V ×_𝒳 V` be a
presented self-intersection of a 1-morphism `g : V ⟶ 𝒳` from a scheme, an algebraic space `Q` with
diagonal `e : V ⟶ Q`, and let `u₀` be an object of `(Sch/V)` over `Spec l ⟶ Spec Λ ⟶ S` at whose
point `ν` the residue field of `V` is exactly `l`. Then some étale surjective scheme chart
`a : W ⟶ Q` has an object `w₀` of `(Sch/W)` over `Spec L ⟶ Spec Λ ⟶ S`, for a finite separable
extension `L/l`, lying over `e(ν)`: an arrow `π : w₀ ⟶ u₀` over `Spec L ⟶ Spec l` with
`w₀ ≫ a = π ≫ ν ≫ e`; and `L` is separable over the residue field of `W` at `w₀`. -/
theorem exists_etaleChart_point_isSeparable_selfIntersection (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (T : Bicategory.TwoCommSq g g) (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hQ : IsAlgebraicSpace B S hS Q)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (schemeStack.{u, w} B S hS V).val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] {iΛ : Spec (.of Λ) ⟶ S}
    (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hres : Function.Surjective (Scheme.SpecToEquivOfField l _ (pointMap hu₀)).2) :
    ∃ (W : BigFppfOver B S hS) (a : yoneda.obj W ⟶ Q),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra l L) (_ : Algebra Λ L) (_ : IsScalarTower Λ l L),
        Module.Finite l L ∧ Algebra.IsSeparable l L ∧
        ∃ (w₀ : Over W)
          (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
          (π : w₀.left ⟶ u₀.left),
          eqToHom (congrArg Over.left hw₀).symm ≫ B.inclusion.map π.left ≫
              eqToHom (congrArg Over.left hu₀) = Spec.map (CommRingCat.ofHom (algebraMap l L)) ∧
          yoneda.map w₀.hom ≫ a = yoneda.map π ≫ yoneda.map u₀.hom ≫
            selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ ∧
          letI := (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).2.hom.toAlgebra
          Algebra.IsSeparable ((B.inclusion.obj W.left).residueField
            (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).1) L :=
  Space.exists_etaleChart_point_isSeparable hQ (selfIntersectionSourceMap B S hS V g T Q eV eQ)
    u₀ hu₀ (yoneda.map u₀.hom ≫ selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ)
    (by rw [Category.assoc, selfIntersectionDiagonalMap_comp_sourceMap, Category.comp_id]) hres

end Stack

end AlgebraicGeometry
