module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint

/-!
# The geometric stalk does not depend on the geometric point above a point

Two geometric points of an algebraic space `F` over `S` lying over the same point of
`AlgebraicGeometry.Space.points` have isomorphic stalk functors on the small étale site.  By
the definition of the point set the two are dominated by a third geometric point, and
restricting small étale neighbourhoods along a domination is an initial functor, so each of
the two stalk colimits is identified with the one taken at the dominating point.

## Main definitions

* `AlgebraicGeometry.Space.neighborhoodAlong` restricts a small étale neighbourhood of a
  geometric point to one of a geometric point dominating it.
* `AlgebraicGeometry.Space.stalkFunctorIsoAlong` and
  `AlgebraicGeometry.Space.stalkSetFunctorIsoAlong` are the induced isomorphisms of stalk
  functors, with `AlgebraicGeometry.Space.stalkSetEquivAlong` the underlying bijection of
  set-valued stalks.

## Main results

* `AlgebraicGeometry.Space.GeometricPoint.exists_common_extension`: two geometric points
  lying over the same point of the space are dominated by a single geometric point.
* `AlgebraicGeometry.Space.exists_neighborhood_map_of_dominates`: a small étale
  neighbourhood of a dominating geometric point already contains a lift of the dominated
  one, compatibly with the domination, and
  `AlgebraicGeometry.Space.chartLift_unique_of_comp_eq` says that lift is unique.
* `AlgebraicGeometry.Space.neighborhoodAlong_initial`: restriction of neighbourhoods along a
  domination is initial.
* `AlgebraicGeometry.Space.stalkFunctor_iso_of_liesOver` is Stacks 04K4: the stalk functors
  at two geometric points lying over the same point are isomorphic;
  `AlgebraicGeometry.Space.stalkSetFunctor_iso_of_liesOver` is the same statement for
  set-valued stalks with no smallness restriction on the universe of the values.

## Implementation notes

A domination of field-valued points is the existence of a morphism of field spectra
restricting one section to the other, so the morphism itself is carried as explicit data
throughout: every construction here takes a morphism `f` of the underlying objects of the
big fppf site together with the identity `F.map f.op x.val.value = y.val.value` witnessing
it, and only the final statements quantify existentially.  Accordingly those statements
assert that an isomorphism of stalk functors exists rather than naming one: the dominating
geometric point is produced by a choice of common extension and of an algebraic closure, so
there is no distinguished isomorphism.

The key geometric input is that a small étale neighbourhood of the dominating point `y`
contains a lift of the dominated point `x`.  The chart is representable and étale over `F`,
so its base change along `x` is a scheme étale over the spectrum of the algebraically closed
field of `x`, and the lift carried by the neighbourhood is a point of that base change with
values in the field of `y`; `AlgebraicGeometry.etale_field_map_factors` turns it into a
section over the field of `x`.  Uniqueness of that lift is
`AlgebraicGeometry.ext_of_apply_closedPoint_eq`: two sections of a morphism locally of finite
type to the spectrum of an algebraically closed field which agree at the closed point are
equal.

Cofilteredness of the neighbourhood categories is not reproved; it is
`AlgebraicGeometry.Space.isCofiltered_smallEtaleNeighborhood`, which is where the
algebraic-space hypothesis enters.  Everything else depends only on the geometric points and
their étale charts.

## References

* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Domination of field-valued points is transitive: restricting along two morphisms of field
spectra is restricting along their composite. -/
theorem FieldValuedPoint.dominates_trans {a b c : FieldValuedPoint B S hS F}
    (hab : FieldValuedPoint.Dominates B S hS F a b)
    (hbc : FieldValuedPoint.Dominates B S hS F b c) :
    FieldValuedPoint.Dominates B S hS F a c := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hbc
  refine ⟨f ≫ g, ?_⟩
  show F.map (f ≫ g).op c.value = a.value
  rw [CategoryTheory.op_comp, Functor.map_comp]
  show F.map f.op (F.map g.op c.value) = a.value
  rw [hg, hf]

/-- Two geometric points lying over the same point of the space are dominated by a single
geometric point: a common field-valued extension exists by the definition of the point set,
and an algebraic closure of its field is again small enough to lie in the site. -/
theorem GeometricPoint.exists_common_extension {x : points B S hS F}
    (p q : GeometricPoint B S hS F) (hp : p.LiesOver x) (hq : q.LiesOver x) :
    ∃ r : GeometricPoint B S hS F,
      FieldValuedPoint.Dominates B S hS F r.val p.val ∧
        FieldValuedPoint.Dominates B S hS F r.val q.val := by
  classical
  obtain ⟨a, hap, haq⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS F p.val q.val).mp (hp.trans hq.symm)
  let L := AlgebraicClosure a.carrier
  let : Field L := inferInstance
  let : IsAlgClosed L := AlgebraicClosure.isAlgClosed a.carrier
  have hLCard : Cardinal.mk L ≤ max (Cardinal.mk a.carrier) ℵ₀ := by
    dsimp [L]
    exact Algebra.IsAlgebraic.cardinalMk_le_max _ _
  have hLSize : (Spec (CommRingCat.of L)).size < B.cutoff :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      a.contained (by simpa [max_comm] using hLCard)
  let φ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of a.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap a.carrier L))
  let φBelow : B.inclusion.obj (B.obj hLSize) ⟶ B.inclusion.obj (B.obj a.contained) := φ
  let e₀ : B.obj hLSize ⟶ B.obj a.contained := B.inclusion.preimage φBelow
  let zToBase : Spec (CommRingCat.of L) ⟶ S := B.inclusion.map (e₀ ≫ a.siteObject.hom)
  let siteL : BigFppfOver B S hS := Over.mk (⟨zToBase⟩ : B.obj hLSize ⟶ B.obj hS)
  let f : siteL ⟶ a.siteObject := Over.homMk e₀ rfl
  let r : FieldValuedPoint B S hS F :=
    { carrier := L
      field := inferInstance
      contained := hLSize
      toBase := zToBase
      value := F.map f.op a.value }
  have har : FieldValuedPoint.Dominates B S hS F r a := ⟨f, rfl⟩
  exact ⟨⟨r, inferInstance⟩, FieldValuedPoint.dominates_trans har hap,
    FieldValuedPoint.dominates_trans har haq⟩

/-- Restriction of small étale neighbourhoods along a domination of geometric points: the
chart is unchanged and the lift of the dominating point is composed with the morphism of
field spectra witnessing the domination. -/
noncomputable def neighborhoodAlong {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    SmallEtaleNeighborhood x ⥤ SmallEtaleNeighborhood y where
  obj U :=
    { chart := U.chart
      point := f ≫ U.point
      point_comp := by
        have hn' := congrArg (fun k => k U.point) (U.chart.obj.hom.naturality f.op)
        have hh : U.chart.obj.hom.app (Opposite.op y.val.siteObject) (f ≫ U.point) =
            F.map f.op (U.chart.obj.hom.app (Opposite.op x.val.siteObject) U.point) := by
          simpa only [types_comp_apply, yoneda_obj_map, Quiver.Hom.unop_op,
            ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, Function.comp_apply] using hn'
        rw [U.point_comp, hf] at hh
        exact hh }
  map {U V} g :=
    { hom := g.hom
      point_comp := by
        simpa [Category.assoc] using congrArg (fun k => f ≫ k) g.point_comp }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The chart of the restriction of a neighbourhood along `neighborhoodAlong` is the original
chart. -/
@[simp]
theorem neighborhoodAlong_obj_chart {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) (U : SmallEtaleNeighborhood x) :
    ((neighborhoodAlong f hf).obj U).chart = U.chart := rfl

/-- The lift of the restriction of a neighbourhood along `neighborhoodAlong` is the original
lift precomposed with `f`. -/
@[simp]
theorem neighborhoodAlong_obj_point {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) (U : SmallEtaleNeighborhood x) :
    ((neighborhoodAlong f hf).obj U).point = f ≫ U.point := rfl

/-- The underlying morphism of charts of the image of `g` under `neighborhoodAlong` is that
of `g`. -/
@[simp]
theorem neighborhoodAlong_map_hom {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) {U V : SmallEtaleNeighborhood x} (g : U ⟶ V) :
    ((neighborhoodAlong f hf).map g).hom = g.hom := rfl

/-- A small étale neighbourhood of a geometric point `y` is already a neighbourhood of any
geometric point `x` that `y` dominates: the chart is étale over `F`, so its base change along
`x` is étale over the spectrum of the algebraically closed field of `x`, and the lift carried
by the neighbourhood factors through a section of that base change. -/
theorem exists_neighborhood_map_of_dominates {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) (U : SmallEtaleNeighborhood y) :
    ∃ z : x.val.siteObject ⟶ U.chart.obj.left,
      U.chart.obj.hom.app (Opposite.op x.val.siteObject) z = x.val.value ∧ f ≫ z = U.point := by
  classical
  let G := BigFppfOver.toScheme B S hS
  let η := U.chart.obj.hom
  let α : yoneda.obj x.val.siteObject ⟶ F := yonedaEquiv.symm x.val.value
  let hRep : yoneda.relativelyRepresentable η := U.chart.property.1
  have hcompat : yoneda.map U.point ≫ η = yoneda.map f ≫ α := by
    apply yonedaEquiv.injective
    show η.app (Opposite.op y.val.siteObject) U.point =
      α.app (Opposite.op y.val.siteObject) f
    rw [U.point_comp]
    show y.val.value = F.map f.op x.val.value
    exact hf.symm
  let k := hRep.lift (yoneda.map U.point) f hcompat
  let b' := yoneda.preimage (hRep.fst α)
  have hkfirst : k ≫ b' = U.point := by
    apply yoneda.map_injective
    simp [k, b']
  have hEtale : Etale (G.map (hRep.snd α)) :=
    U.chart.property.2 α (hRep.fst α) (hRep.snd α) (hRep.isPullback α)
  let : IsAlgClosed x.val.carrier := x.property
  obtain ⟨l, hl, hq⟩ := etale_field_map_factors x.val.carrier
    (G.map (hRep.snd α)) hEtale y.val.carrier (G.map k)
  have hbase : k ≫ hRep.snd α = f := hRep.lift_snd (yoneda.map U.point) f hcompat
  have hq' : G.map k = G.map f ≫ l := hq.trans (by rw [← Functor.map_comp, hbase])
  have hpoint : G.map f ≫ l ≫ G.map b' = G.map U.point := by
    rw [← Category.assoc, ← hq', ← Functor.map_comp, hkfirst]
  have hsndBase : B.inclusion.map (hRep.pullback α).hom =
      B.inclusion.map (hRep.snd α).left ≫ B.inclusion.map x.val.siteObject.hom := by
    rw [← B.inclusion.map_comp, (hRep.snd α).w]
  have hlBase : l ≫ B.inclusion.map (hRep.pullback α).hom =
      B.inclusion.map x.val.siteObject.hom := by
    calc
      l ≫ B.inclusion.map (hRep.pullback α).hom =
          l ≫ B.inclusion.map (hRep.snd α).left ≫
            B.inclusion.map x.val.siteObject.hom := by rw [hsndBase]
      _ = (l ≫ G.map (hRep.snd α)) ≫ B.inclusion.map x.val.siteObject.hom := by
            simp [G, Category.assoc]
      _ = B.inclusion.map x.val.siteObject.hom := by rw [hl]; simp
  let lBelow : B.inclusion.obj x.val.siteObject.left ⟶
      B.inclusion.obj (hRep.pullback α).left := l
  let lSite : x.val.siteObject ⟶ hRep.pullback α :=
    Over.homMk (B.inclusion.preimage lBelow) (by
      apply B.inclusion.map_injective
      calc
        B.inclusion.map (B.inclusion.preimage lBelow ≫ (hRep.pullback α).hom) =
            B.inclusion.map (B.inclusion.preimage lBelow) ≫
              B.inclusion.map (hRep.pullback α).hom := by rw [Functor.map_comp]
        _ = l ≫ B.inclusion.map (hRep.pullback α).hom := by rw [B.inclusion.map_preimage]
        _ = B.inclusion.map x.val.siteObject.hom := hlBase)
  have hlMap : G.map lSite = l := by
    show B.inclusion.map (B.inclusion.preimage lBelow) = l
    exact B.inclusion.map_preimage lBelow
  have hlSite : lSite ≫ hRep.snd α = 𝟙 _ := by
    apply Functor.map_injective G
    rw [Functor.map_comp, hlMap, G.map_id]
    exact hl
  refine ⟨lSite ≫ b', ?_, ?_⟩
  · have hsec : η.app (Opposite.op (hRep.pullback α)) b' =
        F.map (hRep.snd α).op x.val.value := by
      have heq := congrArg yonedaEquiv (hRep.w α)
      have hfstMap : yoneda.map b' = hRep.fst α := yoneda.map_preimage _
      have hfstEq : yonedaEquiv (hRep.fst α) = b' := by
        simpa only [yonedaEquiv_yoneda_map] using congrArg yonedaEquiv hfstMap.symm
      simp only [yonedaEquiv_comp, hfstEq, yonedaEquiv_yoneda_map] at heq
      simpa [α, yonedaEquiv_symm_app_apply] using heq
    have hnat := congrArg (fun k => k b') (η.naturality lSite.op)
    have hnat' : η.app (Opposite.op x.val.siteObject) (lSite ≫ b') =
        F.map lSite.op (η.app (Opposite.op (hRep.pullback α)) b') := by
      simpa only [types_comp_apply, yoneda_obj_map, Quiver.Hom.unop_op,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, Function.comp_apply] using hnat
    rw [hnat', hsec]
    show (F.map (hRep.snd α).op ≫ F.map lSite.op) x.val.value = x.val.value
    rw [← Functor.map_comp, ← op_comp, hlSite]
    simp
  · apply Functor.map_injective G
    show (G.map f ≫ G.map lSite) ≫ G.map b' = G.map U.point
    rw [hlMap]
    simpa [Category.assoc] using hpoint

/-- The lift given by `AlgebraicGeometry.Space.exists_neighborhood_map_of_dominates` is
unique: two lifts of a geometric point into a chart which agree after restriction along a
domination are equal, because sections of the base chart, which is étale over the spectrum of
an algebraically closed field, are determined by their value at the closed point. -/
theorem chartLift_unique_of_comp_eq {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject) (V : SmallEtaleNeighborhood y)
    (z z' : x.val.siteObject ⟶ V.chart.obj.left)
    (hz : V.chart.obj.hom.app (Opposite.op x.val.siteObject) z = x.val.value)
    (hz' : V.chart.obj.hom.app (Opposite.op x.val.siteObject) z' = x.val.value)
    (hext : f ≫ z = f ≫ z') : z = z' := by
  classical
  let G := BigFppfOver.toScheme B S hS
  let η := V.chart.obj.hom
  let α : yoneda.obj x.val.siteObject ⟶ F := yonedaEquiv.symm x.val.value
  let hRep := V.chart.property.1
  have hlift : ∀ w : x.val.siteObject ⟶ V.chart.obj.left,
      η.app (Opposite.op x.val.siteObject) w = x.val.value →
      ∃ l, l ≫ hRep.snd α = 𝟙 x.val.siteObject ∧ yoneda.map l ≫ hRep.fst α = yoneda.map w := by
    intro w hw
    have hcompat : yoneda.map w ≫ η = yoneda.map (𝟙 x.val.siteObject) ≫ α := by
      have h₀ : yoneda.map w ≫ η = α := by
        apply yonedaEquiv.injective
        simpa only [η, yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply,
          α] using hw
      rw [h₀]
      simp
    exact ⟨hRep.lift _ _ hcompat, hRep.lift_snd _ _ hcompat, hRep.lift_fst _ _ hcompat⟩
  obtain ⟨l, hl_snd, hl_fst⟩ := hlift z hz
  obtain ⟨l', hl'_snd, hl'_fst⟩ := hlift z' hz'
  have hLift : f ≫ l = f ≫ l' := by
    apply hRep.hom_ext
    · calc
        yoneda.map (f ≫ l) ≫ hRep.fst α = yoneda.map f ≫ yoneda.map z := by
          rw [Functor.map_comp, Category.assoc, hl_fst]
        _ = yoneda.map f ≫ yoneda.map z' := by
          simpa only [Functor.map_comp] using congrArg yoneda.map hext
        _ = yoneda.map (f ≫ l') ≫ hRep.fst α := by
          rw [Functor.map_comp, Category.assoc, hl'_fst]
    · calc
        (f ≫ l) ≫ hRep.snd α = f := by rw [Category.assoc, hl_snd]; simp
        _ = (f ≫ l') ≫ hRep.snd α := by rw [Category.assoc, hl'_snd]; simp
  let : Etale (G.map (hRep.snd α)) :=
    V.chart.property.2 α (hRep.fst α) (hRep.snd α) (hRep.isPullback α)
  let : LocallyOfFiniteType (G.map (hRep.snd α)) := inferInstance
  have hScheme : ∀ m, m ≫ hRep.snd α = 𝟙 x.val.siteObject →
      G.map m ≫ G.map (hRep.snd α) = 𝟙 (G.obj x.val.siteObject) := fun m hm => by
    rw [← Functor.map_comp, hm]
    simp
  have hclosed : (G.map f) (IsLocalRing.closedPoint y.val.carrier) =
      IsLocalRing.closedPoint x.val.carrier :=
    Subsingleton.elim (α := PrimeSpectrum x.val.carrier) _ _
  have heval : (G.map l) (IsLocalRing.closedPoint x.val.carrier) =
      (G.map l') (IsLocalRing.closedPoint x.val.carrier) := by
    have h := congrArg (fun q => q (IsLocalRing.closedPoint y.val.carrier))
      (congrArg G.map hLift)
    change (G.map l) ((G.map f) (IsLocalRing.closedPoint y.val.carrier)) =
      (G.map l') ((G.map f) (IsLocalRing.closedPoint y.val.carrier)) at h
    rwa [hclosed] at h
  have hscheme : G.map l = G.map l' :=
    let : IsAlgClosed x.val.carrier := x.property
    AlgebraicGeometry.ext_of_apply_closedPoint_eq
      (G.map (hRep.snd α)) (hScheme l hl_snd) (hScheme l' hl'_snd) heval
  have hsite : l = l' := Functor.map_injective G hscheme
  apply yoneda.map_injective
  calc
    yoneda.map z = yoneda.map l ≫ hRep.fst α := hl_fst.symm
    _ = yoneda.map l' ≫ hRep.fst α := by rw [hsite]
    _ = yoneda.map z' := hl'_fst

/-- Restriction of small étale neighbourhoods along a domination of geometric points is an
initial functor: every neighbourhood of the dominating point is in its image up to a
morphism, and the resulting morphism is unique after a further refinement. -/
theorem neighborhoodAlong_initial (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    Functor.Initial (neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) f hf) := by
  classical
  let T := neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) f hf
  let : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS F hF x
  let : IsCofiltered (SmallEtaleNeighborhood y) :=
    isCofiltered_smallEtaleNeighborhood B S hS F hF y
  apply Functor.initial_of_exists_of_isCofiltered T
  · intro V
    obtain ⟨z, hz, hfz⟩ := exists_neighborhood_map_of_dominates f hf V
    let U : SmallEtaleNeighborhood x := ⟨V.chart, z, hz⟩
    let g : U.chart ⟶ V.chart := ⟨CostructuredArrow.homMk (𝟙 V.chart.obj.left) rfl⟩
    exact ⟨U, ⟨{ hom := g, point_comp := hfz }⟩⟩
  · intro V U s s'
    obtain ⟨W, a, ha⟩ := IsCofilteredOrEmpty.cone_maps s s'
    obtain ⟨z, hz, hfz⟩ := exists_neighborhood_map_of_dominates f hf W
    let W' : SmallEtaleNeighborhood x := ⟨W.chart, z, hz⟩
    let t : W' ⟶ U :=
      { hom := a.hom
        point_comp := by
          show z ≫ (SmallEtale.toOver B S hS F).map a.hom = U.point
          let m : W.chart.obj.left ⟶ U.chart.obj.left := a.hom.hom.left
          have hcomm : yoneda.map m ≫ U.chart.obj.hom = W.chart.obj.hom := by
            show yoneda.map a.hom.hom.left ≫ (T.obj U).chart.obj.hom = W.chart.obj.hom
            simpa only [T, neighborhoodAlong] using CostructuredArrow.Hom.w a.hom.hom
          have hval : U.chart.obj.hom.app (Opposite.op x.val.siteObject) (z ≫ m) =
              x.val.value := by
            have hmap : yoneda.map (z ≫ m) ≫ U.chart.obj.hom =
                yoneda.map z ≫ W.chart.obj.hom := by
              calc
                yoneda.map (z ≫ m) ≫ U.chart.obj.hom =
                    (yoneda.map z ≫ yoneda.map m) ≫ U.chart.obj.hom := by
                      rw [Functor.map_comp]
                _ = yoneda.map z ≫ (yoneda.map m ≫ U.chart.obj.hom) :=
                      (Category.assoc (yoneda.map z) (yoneda.map m) U.chart.obj.hom).symm
                _ = yoneda.map z ≫ W.chart.obj.hom := by rw [hcomm]
            have hv := congrArg yonedaEquiv hmap
            change U.chart.obj.hom.app (Opposite.op x.val.siteObject) (z ≫ m) =
              W.chart.obj.hom.app (Opposite.op x.val.siteObject) z at hv
            rw [hz] at hv
            exact hv
          have hextEq : f ≫ (z ≫ (SmallEtale.toOver B S hS F).map a.hom) = f ≫ U.point := by
            rw [← Category.assoc, hfz]
            show W.point ≫ (SmallEtale.toOver B S hS F).map a.hom = (T.obj U).point
            exact a.point_comp
          exact chartLift_unique_of_comp_eq f (T.obj U)
            (z ≫ (SmallEtale.toOver B S hS F).map a.hom) U.point hval U.point_comp hextEq }
    let i : T.obj W' ⟶ W :=
      { hom := ⟨CostructuredArrow.homMk (𝟙 W.chart.obj.left) rfl⟩
        point_comp := hfz }
    have ht : T.map t = i ≫ a := by
      apply SmallEtaleNeighborhood.Hom.ext
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      rfl
    exact ⟨W', t, by rw [ht, Category.assoc, ha, Category.assoc]⟩

/-- The isomorphism of category-valued stalk functors along a domination of geometric points:
restriction of neighbourhoods is initial, so the two stalk colimits agree. -/
noncomputable def stalkFunctorIsoAlong (hF : IsAlgebraicSpace B S hS F) (C : Type w)
    [Category.{v} C] {x y : GeometricPoint B S hS F}
    [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ C]
    [HasColimitsOfShape (SmallEtaleNeighborhood y)ᵒᵖ C]
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    stalkFunctor C x ≅ stalkFunctor C y := by
  classical
  let T := neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) f hf
  have : Functor.Initial T := neighborhoodAlong_initial hF f hf
  have : Functor.Final T.op := Functor.final_op_of_initial T
  refine NatIso.ofComponents (fun P => ?_) ?_
  · change colimit (T.op ⋙ SmallEtaleNeighborhood.sections (x := y) P) ≅
      colimit (SmallEtaleNeighborhood.sections (x := y) P)
    exact Functor.Final.colimitIso T.op (SmallEtaleNeighborhood.sections (x := y) P)
  · intro P Q α
    let β : SmallEtaleNeighborhood.sections (x := y) P ⟶
        SmallEtaleNeighborhood.sections (x := y) Q :=
      { app U := α.app (Opposite.op U.unop.chart)
        naturality _ _ g := α.naturality g.unop.hom.op }
    let Rx : (SmallEtaleNeighborhood x)ᵒᵖ ⥤ (SmallEtale B S hS F)ᵒᵖ :=
      { obj U := Opposite.op U.unop.chart
        map g := g.unop.hom.op
        map_id := by simp
        map_comp := by simp }
    have hP : T.op ⋙ SmallEtaleNeighborhood.sections (x := y) P =
        SmallEtaleNeighborhood.sections (x := x) P := rfl
    have hQ : T.op ⋙ SmallEtaleNeighborhood.sections (x := y) Q =
        SmallEtaleNeighborhood.sections (x := x) Q := rfl
    have hβ : T.op.whiskerLeft β = Rx.whiskerLeft α := by
      ext U
      rfl
    have hnat := (Functor.Final.colimIso T.op).hom.naturality β
    change colim.map (T.op.whiskerLeft β) ≫
        (Functor.Final.colimIso T.op).hom.app (SmallEtaleNeighborhood.sections (x := y) Q) =
      (Functor.Final.colimIso T.op).hom.app
          (SmallEtaleNeighborhood.sections (x := y) P) ≫ colim.map β at hnat
    rw [hβ] at hnat
    cases hP
    cases hQ
    cases hβ
    exact hnat

/-- The bijection of set-valued stalks along a domination of geometric points. -/
noncomputable def stalkSetEquivAlong (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w) : stalkSet x P ≃ stalkSet y P := by
  classical
  let T := neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) f hf
  have : Functor.Initial T := neighborhoodAlong_initial hF f hf
  have : Functor.Final T.op := Functor.final_op_of_initial T
  change (SmallEtaleNeighborhood.sections (x := x) P).ColimitType ≃
    (SmallEtaleNeighborhood.sections (x := y) P).ColimitType
  exact Equiv.ofBijective
    (Functor.colimitTypePrecomp T.op (SmallEtaleNeighborhood.sections (x := y) P))
    (Functor.bijective_colimitTypePrecomp T.op (SmallEtaleNeighborhood.sections (x := y) P))

/-- The isomorphism of set-valued stalk functors along a domination of geometric points. -/
noncomputable def stalkSetFunctorIsoAlong (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    stalkSetFunctor.{u, w} x ≅ stalkSetFunctor.{u, w} y := by
  classical
  refine NatIso.ofComponents (fun P => Equiv.toIso (stalkSetEquivAlong hF f hf P)) ?_
  intro P Q α
  ext z
  obtain ⟨U, a, rfl⟩ :=
    (SmallEtaleNeighborhood.sections (x := x) P).ιColimitType_jointly_surjective z
  rfl

/-- **Stacks 04K4.** The stalk functors on the small étale site at two geometric points
lying over the same point of the algebraic space are isomorphic, naturally in the presheaf.
The isomorphism is not canonical: the two points are compared through a common dominating
geometric point. -/
@[stacks 04K4]
theorem stalkFunctor_iso_of_liesOver (hF : IsAlgebraicSpace B S hS F) (C : Type w)
    [Category.{v} C] {x : points B S hS F} (p q : GeometricPoint B S hS F)
    [HasColimitsOfShape (SmallEtaleNeighborhood p)ᵒᵖ C]
    [HasColimitsOfShape (SmallEtaleNeighborhood q)ᵒᵖ C]
    (hp : p.LiesOver x) (hq : q.LiesOver x) :
    Nonempty (stalkFunctor C p ≅ stalkFunctor C q) := by
  classical
  obtain ⟨r, ⟨fp, hfp⟩, ⟨fq, hfq⟩⟩ := GeometricPoint.exists_common_extension p q hp hq
  let Tp := neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) fp hfp
  have : Functor.Initial Tp := neighborhoodAlong_initial hF fp hfp
  have : Functor.Final Tp.op := Functor.final_op_of_initial Tp
  let : HasColimitsOfShape (SmallEtaleNeighborhood r)ᵒᵖ C :=
    Functor.Final.hasColimitsOfShape_of_final Tp.op
  exact ⟨stalkFunctorIsoAlong hF C fp hfp ≪≫ (stalkFunctorIsoAlong hF C fq hfq).symm⟩

/-- **Stacks 04K4.** The set-valued stalk functors at two geometric points lying over the
same point of the algebraic space are isomorphic, naturally in the presheaf, with no
smallness restriction on the universe of the values. -/
theorem stalkSetFunctor_iso_of_liesOver (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (p q : GeometricPoint B S hS F)
    (hp : p.LiesOver x) (hq : q.LiesOver x) :
    Nonempty (stalkSetFunctor.{u, w} p ≅ stalkSetFunctor.{u, w} q) := by
  classical
  obtain ⟨r, ⟨fp, hfp⟩, ⟨fq, hfq⟩⟩ := GeometricPoint.exists_common_extension p q hp hq
  exact ⟨stalkSetFunctorIsoAlong hF fp hfp ≪≫ (stalkSetFunctorIsoAlong hF fq hfq).symm⟩

end AlgebraicGeometry.Space

end
