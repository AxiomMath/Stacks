module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityBaseLocal

/-!
# Transporting a chart of a descent datum relative to a family

Let `𝒰 = {X i ⟶ S}` be a family of morphisms of schemes with fixed target and let `D` be a
descent datum relative to it. A chart of `D`, in the sense of
`AlgebraicGeometry.DescentData.Chart`, is a scheme over `S` exhibiting every component of `D` as
its base change, compatibly with the gluing isomorphisms. This file records how charts move.

A chart on a prescribed scheme over the base is the same thing as an isomorphism of the datum
with the canonical descent datum of that scheme. Consequently a chart transports along an
isomorphism of descent data without changing the scheme it is built on, and it pushes forward
along a morphism of families `F`, the chart of the datum pulled back along `F` being built on the
base change of the original scheme along the morphism of base schemes. Taking `F` to be the
restriction of the family to an open of the base, the latter restricts a chart to that open.

Charts are moreover rigid as soon as the canonical-descent-datum functor is fully faithful,
which along a covering family for the fpqc topology it always is: two charts of one datum are
then connected by exactly one morphism over the base compatible with their projections.

## Main definitions

* `AlgebraicGeometry.DescentData.Chart.isoCanonicalDatum`: the identification of a datum
  carrying a chart with the canonical descent datum of the chart's scheme over the base.
* `AlgebraicGeometry.DescentData.Chart.ofIsoCanonicalDatum`: the converse, the chart on a
  prescribed scheme over the base carried by such an identification.
* `AlgebraicGeometry.DescentData.Chart.ofIso`: the transport of a chart along an isomorphism of
  descent data.
* `AlgebraicGeometry.DescentData.Chart.pulledBack`: the chart of the pulled-back datum, on the
  base change of the scheme over the base.

## Main results

* `AlgebraicGeometry.DescentData.Chart.map_eq_iff_proj_comp_eq`: a morphism over the base is
  compatible with the projections of two charts exactly when its canonical descent datum is the
  comparison of the two identifications with canonical data.
* `AlgebraicGeometry.DescentData.Chart.existsUnique_hom_comp_proj_eq`: **two charts of one datum
  are uniquely isomorphic over the base** when the canonical-descent-datum functor is fully
  faithful, and `AlgebraicGeometry.DescentData.Chart.eq_of_proj_comp_eq` is the uniqueness half,
  which needs only faithfulness.
* `AlgebraicGeometry.DescentData.Chart.existsUnique_hom_comp_proj_eq_of_fpqc`: the same along a
  covering family for the fpqc topology, where full faithfulness is automatic.

## References

* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

section ChartTransport

attribute [local implicit_reducible] CanonicalDatum.datum CanonicalDatum.functor

namespace Chart

/-- **A datum carrying a chart is the canonical descent datum of the chart's scheme over the
base.** -/
def isoCanonicalDatum {D : DescentData f} (C : D.Chart) :
    D ≅ (canonicalFamilyDescentFunctor f).functor.obj C.base :=
  D.isoCanonicalDatum C.base C.objIso fun i j ↦ by
    simpa only [C.objIso_hom_left_fst] using C.compat i j

/-- The `i`-th component of `C.isoCanonicalDatum` is the identification `C.objIso i`. -/
lemma isoCanonicalDatum_hom_hom {D : DescentData f} (C : D.Chart) (i : ι) :
    C.isoCanonicalDatum.hom.hom i = (C.objIso i).hom := rfl

/-- The `i`-th component of the inverse of `C.isoCanonicalDatum` is the inverse of
`C.objIso i`. -/
lemma isoCanonicalDatum_inv_hom {D : DescentData f} (C : D.Chart) (i : ι) :
    C.isoCanonicalDatum.inv.hom i = (C.objIso i).inv := rfl

/-- **The chart on a prescribed scheme over the base carried by an isomorphism of the datum with
the canonical descent datum of that scheme.** This is the converse of
`AlgebraicGeometry.DescentData.Chart.isoCanonicalDatum`. -/
def ofIsoCanonicalDatum {D : DescentData f} (W : Over S)
    (e : D ≅ (canonicalFamilyDescentFunctor f).functor.obj W) : D.Chart := by
  set K := canonicalFamilyDescentFunctor f with hK
  have hwν (i : ι) :
      ((e.hom.hom i).left ≫ (eqToHom (K.obj W i)).left) ≫ pullback.snd W.hom (f i) =
        (D.obj i).hom := by
    simpa only [Over.comp_left, Category.assoc, Over.pullback_obj_hom] using
      Over.w (e.hom.hom i ≫ eqToHom (K.obj W i))
  have hiso (i : ι) : IsIso ((e.hom.hom i).left ≫ (eqToHom (K.obj W i)).left) := by
    have h₁ : IsIso (e.hom.hom i) := by
      simpa only [evaluation_map] using (evaluation (f := f) i).map_isIso e.hom
    have h₂ : IsIso (e.hom.hom i).left := (Over.forget (X i)).map_isIso (e.hom.hom i)
    have h₃ : IsIso (eqToHom (K.obj W i)).left :=
      (Over.forget (X i)).map_isIso (eqToHom (K.obj W i))
    infer_instance
  refine { base := W
           proj := fun i ↦ (e.hom.hom i).left ≫ (eqToHom (K.obj W i)).left ≫
             pullback.fst W.hom (f i)
           isPullback := fun i ↦ ?_
           compat := fun i j ↦ ?_ }
  · refine IsPullback.of_iso_pullback ⟨?_⟩
      (asIso ((e.hom.hom i).left ≫ (eqToHom (K.obj W i)).left)) ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
        ← Category.assoc, hwν i]
    · simp
    · simpa using hwν i
  · have hkey := congrArg (fun q ↦ q ≫
      pullback.snd (f i) (((K.functor.obj W).obj j).hom ≫ f j) ≫
        (eqToHom (K.obj W j)).left ≫ pullback.fst W.hom (f j))
      (gluingPullback_naturality e.hom i j)
    simp only [Category.assoc, K.gluing W i j,
      reassoc_of% (srcGluingMap_fst e.hom.hom i j),
      reassoc_of% (tgtGluingMap_snd e.hom.hom i j)] at hkey
    simpa only [Category.assoc] using hkey.symm

/-- The chart `ofIsoCanonicalDatum W e` is built on the prescribed scheme `W` over the base. -/
@[simp]
lemma ofIsoCanonicalDatum_base {D : DescentData f} (W : Over S)
    (e : D ≅ (canonicalFamilyDescentFunctor f).functor.obj W) :
    (ofIsoCanonicalDatum W e).base = W := rfl

/-- **A chart of a datum is a chart of every isomorphic datum**, on the same scheme over the
base. -/
def ofIso {D E : DescentData f} (e : D ≅ E) (C : D.Chart) : E.Chart :=
  ofIsoCanonicalDatum C.base (e.symm ≪≫ C.isoCanonicalDatum)

/-- The transported chart `ofIso e C` is built on the same scheme over the base as `C`. -/
@[simp]
lemma ofIso_base {D E : DescentData f} (e : D ≅ E) (C : D.Chart) :
    (ofIso e C).base = C.base := rfl

/-! ### Charts along a morphism of families -/

/-- **The chart of a pulled-back datum.** The pullback of a datum along a morphism of families
`F` is charted by the base change, along the morphism of base schemes, of a chart of the
original datum. -/
def pulledBack (F : MorphismOfSchemeFamilies.{u}) {E : DescentData F.targetFamily.f}
    (C : E.Chart) :
    ((MorphismOfSchemeFamilies.pullbackFunctor F).functor.obj E).Chart :=
  ofIsoCanonicalDatum ((Over.pullback F.baseHom).obj C.base)
    ((MorphismOfSchemeFamilies.pullbackFunctor F).functor.mapIso C.isoCanonicalDatum ≪≫
      pullbackFunctorCanonicalObjIsoOver F C.base)

/-- The chart `pulledBack F C` is built on the base change of `C.base` along the morphism of base
schemes of `F`. -/
@[simp]
lemma pulledBack_base (F : MorphismOfSchemeFamilies.{u}) {E : DescentData F.targetFamily.f}
    (C : E.Chart) : (pulledBack F C).base = (Over.pullback F.baseHom).obj C.base := rfl

/-! ### Two charts of one datum -/

variable {D : DescentData f}

/-- A morphism over the base is compatible with the identifications of the components that two
charts carry exactly when it is compatible with their projections. -/
lemma objIso_comp_pullback_map_iff (C C' : D.Chart) (e : C.base ⟶ C'.base) (i : ι) :
    (C.objIso i).hom ≫ (Over.pullback (f i)).map e = (C'.objIso i).hom ↔
      C.proj i ≫ e.left = C'.proj i := by
  have key : ((C.objIso i).hom ≫ (Over.pullback (f i)).map e).left ≫
      pullback.fst C'.base.hom (f i) = C.proj i ≫ e.left := by
    simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst,
      reassoc_of% (C.objIso_hom_left_fst i)]
  constructor
  · intro h
    rw [← key, h, C'.objIso_hom_left_fst]
  · intro h
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · rw [key, h, C'.objIso_hom_left_fst]
    · simpa using (Over.w ((C.objIso i).hom ≫ (Over.pullback (f i)).map e)).trans
        (Over.w (C'.objIso i).hom).symm

/-- **A morphism over the base compatible with the projections of two charts has the comparison
of their identifications with canonical data as its canonical descent datum**, and
conversely. -/
lemma map_eq_iff_proj_comp_eq (C C' : D.Chart) (e : C.base ⟶ C'.base) :
    (canonicalFamilyDescentFunctor f).functor.map e =
        (C.isoCanonicalDatum.symm ≪≫ C'.isoCanonicalDatum).hom ↔
      ∀ i, C.proj i ≫ e.left = C'.proj i := by
  have hcomp : ∀ i : ι, ((C.isoCanonicalDatum.symm ≪≫ C'.isoCanonicalDatum).hom).hom i =
      (C.objIso i).inv ≫ (C'.objIso i).hom := fun _ ↦ rfl
  have hmap : ∀ i : ι, ((canonicalFamilyDescentFunctor f).functor.map e).hom i =
      (Over.pullback (f i)).map e := fun _ ↦ rfl
  constructor
  · intro h i
    rw [← C.objIso_comp_pullback_map_iff C' e i, ← hmap i, h, hcomp i]
    simp
  · intro h
    refine DescentData.hom_ext fun i ↦ ?_
    rw [hmap i, hcomp i, ← (C.objIso_comp_pullback_map_iff C' e i).mpr (h i)]
    simp

/-- **Two charts of one datum are uniquely isomorphic over the base.** If the
canonical-descent-datum functor of the family is fully faithful, there is exactly one morphism
over the base between the two schemes the charts are built on which is compatible with their
projections. -/
theorem existsUnique_hom_comp_proj_eq
    (hff : (canonicalFamilyDescentFunctor f).functor.FullyFaithful) (C C' : D.Chart) :
    ∃! e : C.base ⟶ C'.base, ∀ i, C.proj i ≫ e.left = C'.proj i := by
  have hfaith := hff.faithful
  exact ⟨hff.preimage (C.isoCanonicalDatum.symm ≪≫ C'.isoCanonicalDatum).hom,
    (C.map_eq_iff_proj_comp_eq C' _).mp (hff.map_preimage _), fun e he ↦
      (canonicalFamilyDescentFunctor f).functor.map_injective
        (((C.map_eq_iff_proj_comp_eq C' e).mpr he).trans (hff.map_preimage _).symm)⟩

/-- **A morphism over the base compatible with the projections of two charts is unique** as soon
as the canonical-descent-datum functor of the family is faithful. -/
theorem eq_of_proj_comp_eq (hfaith : (canonicalFamilyDescentFunctor f).functor.Faithful)
    (C C' : D.Chart) {e e' : C.base ⟶ C'.base}
    (he : ∀ i, C.proj i ≫ e.left = C'.proj i)
    (he' : ∀ i, C.proj i ≫ e'.left = C'.proj i) : e = e' :=
  have := hfaith
  (canonicalFamilyDescentFunctor f).functor.map_injective
    (((C.map_eq_iff_proj_comp_eq C' e).mpr he).trans
      ((C.map_eq_iff_proj_comp_eq C' e').mpr he').symm)

/-- **Two charts of one datum relative to a covering family for the fpqc topology are uniquely
isomorphic over the base.** -/
theorem existsUnique_hom_comp_proj_eq_of_fpqc {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) {D : DescentData 𝒰.f}
    (C C' : D.Chart) : ∃! e : C.base ⟶ C'.base, ∀ i, C.proj i ≫ e.left = C'.proj i :=
  (canonicalFamilyDescentFunctor_fullyFaithful_of_fpqc h𝒰).elim fun hff ↦
    existsUnique_hom_comp_proj_eq hff C C'

end Chart

end ChartTransport

end DescentData

end AlgebraicGeometry

end

end
