module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityZariskiGlue

/-!
# A chart criterion for effectivity of a descent datum relative to a family

Let `𝒰 = {X i ⟶ S}` be a family of morphisms of schemes with fixed target and let `D` be a
descent datum relative to it. Effectivity of `D` is membership in the essential image of the
canonical-descent-datum functor, which to verify asks for a morphism of descent data, hence for
its compatibility square in the category of products in `Over S`. This file turns effectivity
into concrete geometry, as `AlgebraicGeometry.DescentData.Scheme.EffectiveCriterion` does for a
single morphism: a scheme over `S`, a projection of each component of the datum onto it
exhibiting that component as a base change, and the statement that the gluing isomorphisms
preserve those projections.

## Main definitions

* `AlgebraicGeometry.DescentData.srcGluingMap` and
  `AlgebraicGeometry.DescentData.tgtGluingMap` are the maps induced on the source and the target
  of the gluing isomorphisms by a family of morphisms of the components.
* `AlgebraicGeometry.DescentData.Chart` is the concrete datum described above.
* `AlgebraicGeometry.DescentData.Chart.objIso` is the identification of a component of the datum
  with the chosen fibre product that a chart carries.

## Main results

* `AlgebraicGeometry.isBasis_setOf_exists_le`: the opens contained in some member of an open
  covering form a basis of the topology.
* `AlgebraicGeometry.DescentData.comm_iff_gluingPullback`: **the compatibility condition on a
  morphism of descent data for a family, read on the literal fibre products.** Together with
  `AlgebraicGeometry.DescentData.gluingPullback_naturality` this is the family analogue of
  `AlgebraicGeometry.DescentData.hom_comm_iff_gluingPullback`, which is stated only for a single
  morphism.
* `AlgebraicGeometry.DescentData.Chart.isFamilyEffective` and
  `AlgebraicGeometry.DescentData.nonempty_chart_of_isFamilyEffective`: **a descent datum
  relative to a family is effective exactly when it carries a chart.**

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- **The opens contained in some member of an open covering form a basis of the topology.** -/
lemma isBasis_setOf_exists_le {α : Type*} [TopologicalSpace α] {J : Type*} (U : J → Opens α)
    (hU : ⨆ j, U j = ⊤) : Opens.IsBasis {V : Opens α | ∃ j, V ≤ U j} := by
  rw [Opens.isBasis_iff_nbhd]
  intro O x hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hU ▸ Opens.mem_top x : x ∈ ⨆ j, U j)
  exact ⟨O ⊓ U j, ⟨j, inf_le_right⟩, ⟨hx, hj⟩, inf_le_left⟩

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  {D E : DescentData f}

/-- The map induced on the sources of the gluing isomorphisms by a family of morphisms of the
components. -/
def srcGluingMap (u : ∀ i, D.obj i ⟶ E.obj i) (i j : ι) :
    pullback ((D.obj i).hom ≫ f i) (f j) ⟶ pullback ((E.obj i).hom ≫ f i) (f j) :=
  pullback.map _ _ _ _ (u i).left (𝟙 (X j)) (𝟙 S) (by simp) (by simp)

/-- The map induced on the targets of the gluing isomorphisms by a family of morphisms of the
components. -/
def tgtGluingMap (u : ∀ i, D.obj i ⟶ E.obj i) (i j : ι) :
    pullback (f i) ((D.obj j).hom ≫ f j) ⟶ pullback (f i) ((E.obj j).hom ≫ f j) :=
  pullback.map _ _ _ _ (𝟙 (X i)) (u j).left (𝟙 S) (by simp) (by simp)

/-- The first projection after `srcGluingMap u i j` is the first projection followed by
`(u i).left`. -/
@[reassoc (attr := simp)]
lemma srcGluingMap_fst (u : ∀ i, D.obj i ⟶ E.obj i) (i j : ι) :
    srcGluingMap u i j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (u i).left :=
  pullback.lift_fst _ _ _

/-- `srcGluingMap u i j` commutes with the second projections. -/
@[reassoc (attr := simp)]
lemma srcGluingMap_snd (u : ∀ i, D.obj i ⟶ E.obj i) (i j : ι) :
    srcGluingMap u i j ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `tgtGluingMap u i j` commutes with the first projections. -/
@[reassoc (attr := simp)]
lemma tgtGluingMap_fst (u : ∀ i, D.obj i ⟶ E.obj i) (i j : ι) :
    tgtGluingMap u i j ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The second projection after `tgtGluingMap u i j` is the second projection followed by
`(u j).left`. -/
@[reassoc (attr := simp)]
lemma tgtGluingMap_snd (u : ∀ i, D.obj i ⟶ E.obj i) (i j : ι) :
    tgtGluingMap u i j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (u j).left :=
  pullback.lift_snd _ _ _

/-- A map of products in `Over S`, transported to the literal fibre products. -/
private lemma prodMapLeft_eq {A B A' B' : Over S} (p : A ⟶ A') (q : B ⟶ B') :
    (Over.prodLeftIsoPullback A B).inv ≫ (prod.map p q).left ≫
        (Over.prodLeftIsoPullback A' B').hom =
      pullback.map A.hom B.hom A'.hom B'.hom p.left q.left (𝟙 S) (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.lift_fst]
    rw [← Over.comp_left, prod.map_fst, Over.comp_left]
    simp
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.lift_snd]
    rw [← Over.comp_left, prod.map_snd, Over.comp_left]
    simp

/-- The gluing isomorphism on literal fibre products, as a conjugate of the gluing morphism. -/
private lemma gluingPullbackIso_hom_eq (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).hom =
      (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).inv ≫
        (D.gluing i j).hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))).hom := by
  simp only [DescentData.gluingPullbackIso, DescentData.gluingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map]

/-- **The compatibility condition on a morphism of descent data for a family, in fibre-product
form.** The two forms are conjugate by `CategoryTheory.Over.prodLeftIsoPullback`. -/
lemma comm_iff_gluingPullback (u : ∀ i, D.obj i ⟶ E.obj i) (i j : ι) :
    (srcGluingMap u i j ≫ (E.gluingPullbackIso i j).hom =
        (D.gluingPullbackIso i j).hom ≫ tgtGluingMap u i j) ↔
      prod.map ((Over.map (f i)).map (u i)) (𝟙 (Over.mk (f j))) ≫ (E.gluing i j).hom.left =
        (D.gluing i j).hom.left ≫
          prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (u j)) := by
  have hs : srcGluingMap u i j = _ :=
    (prodMapLeft_eq ((Over.map (f i)).map (u i)) (𝟙 (Over.mk (f j)))).symm
  have ht : tgtGluingMap u i j = _ :=
    (prodMapLeft_eq (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (u j))).symm
  rw [hs, ht, gluingPullbackIso_hom_eq, gluingPullbackIso_hom_eq]
  simp [Over.OverMorphism.ext_iff]

/-- The compatibility square of a morphism of descent data for a family, read on the literal
fibre products. -/
lemma gluingPullback_naturality (φ : D ⟶ E) (i j : ι) :
    srcGluingMap φ.hom i j ≫ (E.gluingPullbackIso i j).hom =
      (D.gluingPullbackIso i j).hom ≫ tgtGluingMap φ.hom i j :=
  (comm_iff_gluingPullback φ.hom i j).mpr (φ.comm i j)

section Chart

attribute [local implicit_reducible] CanonicalDatum.datum CanonicalDatum.functor

/-- **A chart of a descent datum relative to a family**: a scheme over the base together with
projections exhibiting every component of the datum as its base change, compatibly with the
gluing isomorphisms. A chart is the same thing as a witness of effectivity, written on the
literal fibre products. -/
structure Chart (D : DescentData f) where
  /-- The scheme over the base. -/
  base : Over S
  /-- The projection of the `i`-th component of the datum onto it. -/
  proj (i : ι) : (D.obj i).left ⟶ base.left
  /-- The `i`-th component of the datum is the base change of `base` along the `i`-th member of
  the family. -/
  isPullback (i : ι) : IsPullback (proj i) (D.obj i).hom base.hom (f i)
  /-- The gluing isomorphisms of the datum preserve the projection. -/
  compat (i j : ι) :
    (D.gluingPullbackIso i j).hom ≫
        pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ proj j =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ proj i

namespace Chart

variable (C : D.Chart)

/-- The identification of the `i`-th component of the datum with the chosen fibre product. -/
def objIso (i : ι) : D.obj i ≅ (Over.pullback (f i)).obj C.base :=
  Over.isoMk (C.isPullback i).isoPullback (by
    simpa only [Over.pullback_obj_hom] using (C.isPullback i).isoPullback_hom_snd)

/-- The identification `C.objIso i` followed by the first projection is the projection
`C.proj i`. -/
@[reassoc]
lemma objIso_hom_left_fst (i : ι) :
    (C.objIso i).hom.left ≫ pullback.fst C.base.hom (f i) = C.proj i :=
  (C.isPullback i).isoPullback_hom_fst

include C in
/-- **A chart makes the datum effective.** -/
theorem isFamilyEffective : D.IsFamilyEffective :=
  ⟨C.base, ⟨(D.isoCanonicalDatum C.base C.objIso fun i j ↦ by
    simpa only [C.objIso_hom_left_fst] using C.compat i j).symm⟩⟩

end Chart

/-- **An effective datum carries a chart.** -/
theorem nonempty_chart_of_isFamilyEffective (D : DescentData f) (h : D.IsFamilyEffective) :
    Nonempty D.Chart := by
  obtain ⟨W, ⟨e⟩⟩ := h
  set K := canonicalFamilyDescentFunctor f with hK
  have hwν (i : ι) :
      ((e.inv.hom i).left ≫ (eqToHom (K.obj W i)).left) ≫ pullback.snd W.hom (f i) =
        (D.obj i).hom := by
    simpa only [Over.comp_left, Category.assoc, Over.pullback_obj_hom] using
      Over.w (e.inv.hom i ≫ eqToHom (K.obj W i))
  have hiso (i : ι) : IsIso ((e.inv.hom i).left ≫ (eqToHom (K.obj W i)).left) := by
    have h₁ : IsIso (e.inv.hom i) := by
      simpa only [evaluation_map] using (evaluation (f := f) i).map_isIso e.inv
    have h₂ : IsIso (e.inv.hom i).left := (Over.forget (X i)).map_isIso (e.inv.hom i)
    have h₃ : IsIso (eqToHom (K.obj W i)).left :=
      (Over.forget (X i)).map_isIso (eqToHom (K.obj W i))
    infer_instance
  refine ⟨{ base := W
            proj := fun i ↦ (e.inv.hom i).left ≫ (eqToHom (K.obj W i)).left ≫
              pullback.fst W.hom (f i)
            isPullback := fun i ↦ ?_
            compat := fun i j ↦ ?_ }⟩
  · refine IsPullback.of_iso_pullback ⟨?_⟩
      (asIso ((e.inv.hom i).left ≫ (eqToHom (K.obj W i)).left)) ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
        ← Category.assoc, hwν i]
    · simp
    · simpa using hwν i
  · have hkey := congrArg (fun q ↦ q ≫
      pullback.snd (f i) (((K.functor.obj W).obj j).hom ≫ f j) ≫
        (eqToHom (K.obj W j)).left ≫ pullback.fst W.hom (f j))
      (gluingPullback_naturality e.inv i j)
    simp only [Category.assoc, K.gluing W i j,
      reassoc_of% (srcGluingMap_fst e.inv.hom i j),
      reassoc_of% (tgtGluingMap_snd e.inv.hom i j)] at hkey
    simpa only [Category.assoc] using hkey.symm

end Chart

end DescentData

end AlgebraicGeometry

end

end
