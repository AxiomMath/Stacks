module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.Deformation.ToposThickening.ObstructionIX.DoubledOriginDatum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A flat group scheme of finite type that is not quasi-separated

Over countably infinite-dimensional affine space `A = Spec k[X₀, X₁, …]` there is a group scheme,
flat and of finite type over `A`, whose structure morphism is not quasi-separated. The witness is
the scheme obtained by doubling the origin of `A`, which carries a group structure over `A` because
its two charts are copies of `A` itself: a point of the doubled scheme over a point of `A` is a
point of `A` together with a choice of chart, so the fibres are the group of order two.

## Main results

* `AlgebraicGeometry.exists_flat_finiteType_groupScheme_not_quasiSeparated`: over any field there
  is a group scheme over infinite-dimensional affine space which is flat, locally of finite type
  and quasi-compact over it, and not quasi-separated over it.

## Implementation notes

A group scheme over `S` is a group object in `Over S`, where the cartesian monoidal structure is
the one given by pullbacks (`CategoryTheory.Over.cartesianMonoidalCategory`). Finite type is
expressed by local finite type together with quasi-compactness of the structure morphism, which is
how `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` splits it.

The structure morphism to the base is `doubledOriginToBase`, built by gluing the identity on each
of the two charts; it is packaged with its restriction equations, in the manner of
`AlgebraicGeometry.structureMorphism`, because every later proof needs both. That the composite to
`Spec k` is `AlgebraicGeometry.structureMorphism` is what transports
`AlgebraicGeometry.structureMorphism_not_quasiSeparated` to it: quasi-separatedness of a morphism
is inherited by the first factor of a composite.

The multiplication is defined by gluing over the open cover of `X ×_A X` by the four products of
charts. On the product of chart `a` with chart `b` it is the projection to the first factor
followed by the chart labelled `doubledOriginLabelMul a b`, that is, by the chart `0` when `a = b`
and the chart `1` otherwise — the multiplication table of the group of order two. The group axioms
are checked on sections: `doubledOriginSection_hom_ext` reduces an equation between two morphisms
into the doubled scheme to the case where the test morphism factors through a single chart, after
which both sides are sections and `doubledOriginMul_sections` evaluates the multiplication on them.

Flatness and local finite type are checked on the chart cover, where the structure morphism
restricts to the identity. Quasi-compactness is checked directly: the inverse image of an affine
open is the union of its two chart images.

Four definitions in this file are opaque at `implicit` transparency, which is the level at which
instance search and the rewriting machinery work, and are therefore marked `implicit_reducible`
locally. `AlgebraicGeometry.Scheme.Cover.copy` and
`AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight` hide the index type of the chart cover and
of the product cover, so without them an index of the product cover is not recognized as a pair of
chart indices and nothing about the product cover can be rewritten;
`CategoryTheory.Precoverage.ZeroHypercover.pullback₁` and
`CategoryTheory.PreZeroHypercover.pullback₁` do the same for the pullback of the chart cover used
in `doubledOriginSection_hom_ext`. With those attributes in force the cone point of the product
cover in `doubledOriginMul_sections` is produced at a spelling for which
`CategoryTheory.Limits.pullback.lift_fst` is no longer a `simp` step, so that proof names the four
projection equations it needs explicitly rather than calling `simp`.

## References

* [Stacks Project, Tag 08IX](https://stacks.math.columbia.edu/tag/08IX)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Under the identifications of a `DoubledOriginData`, the two overlap inclusions of a pair of
charts agree up to the transition map. -/
private theorem doubledOrigin_chart_compatibility {k : Type u} [Field k]
    (D : DoubledOriginData k) (a b : Fin 2) :
    D.glueData.f (D.indexEquiv a) (D.indexEquiv b) ≫ (D.chartIso a).hom =
      D.glueData.t (D.indexEquiv a) (D.indexEquiv b) ≫
        D.glueData.f (D.indexEquiv b) (D.indexEquiv a) ≫ (D.chartIso b).hom := by
  apply (cancel_epi (D.overlapIso a b).hom).mp
  calc
    (D.overlapIso a b).hom ≫ D.glueData.f (D.indexEquiv a) (D.indexEquiv b) ≫
        (D.chartIso a).hom = doubledOriginOverlapι k a b := by
          simpa only [Category.assoc] using D.overlap_f a b
    _ = doubledOriginOverlapSwap k a b ≫ doubledOriginOverlapι k b a := by
          classical
          fin_cases a <;> fin_cases b <;> rfl
    _ = (D.overlapIso a b).hom ≫ D.glueData.t (D.indexEquiv a) (D.indexEquiv b) ≫
        D.glueData.f (D.indexEquiv b) (D.indexEquiv a) ≫ (D.chartIso b).hom := by
          calc
            _ = ((D.overlapIso a b).hom ≫ D.glueData.t (D.indexEquiv a)
                  (D.indexEquiv b) ≫ (D.overlapIso b a).inv) ≫
                  ((D.overlapIso b a).hom ≫ D.glueData.f (D.indexEquiv b)
                    (D.indexEquiv a) ≫ (D.chartIso b).hom) := by
                    rw [D.transition a b, D.overlap_f b a]
            _ = _ := by simp [Category.assoc]

/-- The structure morphism of a doubled-origin scheme to the affine space it doubles, together with
the statement that it restricts to the identity on each chart. -/
@[sga "3 VIB 5.6.4" "partial"]
private noncomputable def doubledOriginToBase {k : Type u} [Field k]
    (D : DoubledOriginData k) :
    { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) } := by
  classical
  let chartMap : ∀ i : D.glueData.J, D.glueData.U i ⟶ infiniteAffineSpace k := fun i =>
    eqToHom (congrArg D.glueData.U (D.indexEquiv.apply_symm_apply i).symm) ≫
      (D.chartIso (D.indexEquiv.symm i)).hom
  have chartIso_transport : ∀ {a b : Fin 2} (h : a = b),
      eqToHom (congrArg (fun x => D.glueData.U (D.indexEquiv x)) h) ≫
        (D.chartIso b).hom = (D.chartIso a).hom := by
    intro a b h
    cases h
    simp
  have chartMap_index : ∀ a : Fin 2,
      chartMap (D.indexEquiv a) = (D.chartIso a).hom := by
    intro a
    dsimp [chartMap]
    have h := (D.indexEquiv.symm_apply_apply a).symm
    have hcast : (D.indexEquiv.apply_symm_apply (D.indexEquiv a)).symm =
        congrArg D.indexEquiv h := Subsingleton.elim _ _
    rw [hcast]
    simpa [Category.assoc] using chartIso_transport h
  have compatible : ∀ i j,
      D.glueData.f i j ≫ chartMap i =
        D.glueData.t i j ≫ D.glueData.f j i ≫ chartMap j := by
    intro i j
    obtain ⟨a, rfl⟩ := D.indexEquiv.surjective i
    obtain ⟨b, rfl⟩ := D.indexEquiv.surjective j
    rw [chartMap_index a, chartMap_index b]
    exact doubledOrigin_chart_compatibility D a b
  let maps : ∀ i : (MultispanShape.prod D.glueData.J).R,
      D.glueData.toGlueData.diagram.right i ⟶ infiniteAffineSpace k := fun i => by
    simpa only [CategoryTheory.GlueData.diagram_right] using chartMap i
  let gluedMap := Multicoequalizer.desc D.glueData.toGlueData.diagram _ maps (by
    intro p
    rcases p with ⟨i, j⟩
    change D.glueData.f i j ≫ maps i =
      (D.glueData.t i j ≫ D.glueData.f j i) ≫ maps j
    simpa [maps, CategoryTheory.GlueData.diagram] using compatible i j)
  refine ⟨gluedMap, ?_⟩
  intro i
  dsimp only [DoubledOriginData.chart]
  dsimp [AlgebraicGeometry.Scheme.GlueData.ι, CategoryTheory.GlueData.ι]
  let idx : (MultispanShape.prod D.glueData.J).R := D.indexEquiv i
  calc
    (D.chartIso i).inv ≫ Multicoequalizer.π D.glueData.toGlueData.diagram idx ≫
        gluedMap = (D.chartIso i).inv ≫ maps idx := by
          simpa only [Category.assoc, D.glueData.toGlueData.diagram_right] using
            congrArg (fun g => (D.chartIso i).inv ≫ g)
              (Multicoequalizer.π_desc D.glueData.toGlueData.diagram _ maps _ idx)
    _ = 𝟙 (infiniteAffineSpace k) := by
      rw [show maps idx = chartMap (D.indexEquiv i) by simp [maps, idx], chartMap_index]
      simp

/-- The structure morphism of a doubled-origin scheme to the affine space it doubles is not
quasi-separated, because its composite with the structure morphism to `Spec k` is not. -/
@[sga "3 VIB 5.6.4" "special case"]
private theorem doubledOriginToBase_not_quasiSeparated {k : Type u} [Field k]
    (D : DoubledOriginData k) : ¬ QuasiSeparated (doubledOriginToBase D).1 := by
  classical
  let c : infiniteAffineSpace k ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial ℕ k))
  have hcomp : (doubledOriginToBase D).1 ≫ c = (structureMorphism D).1 := by
    apply D.glueData.openCover.hom_ext
    intro i
    let a := D.indexEquiv.symm i
    have hai : D.indexEquiv a = i := D.indexEquiv.apply_symm_apply i
    have hchart : D.chart a = (D.chartIso a).inv ≫ D.glueData.ι (D.indexEquiv a) := rfl
    change D.glueData.ι i ≫ (doubledOriginToBase D).1 ≫ c =
      D.glueData.ι i ≫ (structureMorphism D).1
    rw [← hai]
    apply (cancel_epi (D.chartIso a).inv).mp
    calc
      (D.chartIso a).inv ≫ D.glueData.ι (D.indexEquiv a) ≫
          (doubledOriginToBase D).1 ≫ c =
          (D.chart a ≫ (doubledOriginToBase D).1) ≫ c := by
            rw [hchart]
            simp [Category.assoc]
      _ = c := by rw [(doubledOriginToBase D).2 a, Category.id_comp]
      _ = D.chart a ≫ (structureMorphism D).1 := ((structureMorphism D).2 a).symm
      _ = (D.chartIso a).inv ≫ D.glueData.ι (D.indexEquiv a) ≫
          (structureMorphism D).1 := by
            rw [hchart]
            simp [Category.assoc]
  intro hqs
  apply structureMorphism_not_quasiSeparated D
  rw [← hcomp]
  infer_instance

/-- The cover of a doubled-origin scheme by its two charts, indexed by `Fin 2`. -/
private noncomputable abbrev doubledOriginChartCover {k : Type u} [Field k]
    (D : DoubledOriginData k) : Scheme.OpenCover.{0} D.scheme :=
  Scheme.Cover.copy D.glueData.openCover (Fin 2)
    (fun _ => infiniteAffineSpace k) (D.chart) D.indexEquiv
    (fun i => (D.chartIso i).symm) (fun _ => rfl)

/-- The members of the chart cover are the charts. -/
private theorem doubledOriginChartCover_f {k : Type u} [Field k]
    (D : DoubledOriginData k) (i : Fin 2) :
    (doubledOriginChartCover D).f i = D.chart i := rfl

attribute [local simp] doubledOriginChartCover_f

/-- The multiplication table of the group of order two, written on chart labels: the product of two
labels is the label `0` when they agree and the label `1` when they differ. -/
private def doubledOriginLabelMul (a b : Fin 2) : Fin 2 := if a = b then 0 else 1

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Cover.copy
  AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
  CategoryTheory.Precoverage.ZeroHypercover.pullback₁
  CategoryTheory.PreZeroHypercover.pullback₁

/-- The cover of the product of a doubled-origin scheme with itself over the affine space by the
four products of charts. -/
private noncomputable abbrev doubledOriginProductCover {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) }) :=
  Scheme.Pullback.openCoverOfLeftRight (doubledOriginChartCover D)
    (doubledOriginChartCover D) F.1 F.1

/-- The multiplication, read on the product of two charts: project to the first factor and include
through the chart named by the product of the two labels. -/
private noncomputable def doubledOriginProductChartMap {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) })
    (p : (doubledOriginProductCover D F).I₀) :
    (doubledOriginProductCover D F).X p ⟶ D.scheme := by
  let U := doubledOriginChartCover D
  exact pullback.fst (U.f p.1 ≫ F.1) (U.f p.2 ≫ F.1) ≫
    D.chart (doubledOriginLabelMul p.1 p.2)

/-- On the product of two charts over the affine space the two projections agree, because both
charts are sections of the structure morphism. -/
private theorem doubledOriginProduct_fst_eq_snd {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) }) (a b : Fin 2) :
    pullback.fst (D.chart a ≫ F.1) (D.chart b ≫ F.1) =
      pullback.snd (D.chart a ≫ F.1) (D.chart b ≫ F.1) := by
  simpa only [F.2, Category.comp_id] using
    pullback.condition (f := D.chart a ≫ F.1) (g := D.chart b ≫ F.1)

/-- The label multiplication respects an identification of two pairs of sections: if a test
morphism meets the sections `a, b` where another meets `c, d`, the two meet the same product
section. -/
private theorem doubledOriginLabelMul_compatible {T S G : Scheme.{u}}
    (s : Fin 2 → (S ⟶ G)) (f : G ⟶ S) (hs : ∀ i, s i ≫ f = 𝟙 S)
    (x y : T ⟶ S) (a b c d : Fin 2)
    (h₁ : x ≫ s a = y ≫ s c) (h₂ : x ≫ s b = y ≫ s d) :
    x ≫ s (doubledOriginLabelMul a b) = y ≫ s (doubledOriginLabelMul c d) := by
  have hxy : x = y := by
    simpa only [Category.assoc, hs, Category.comp_id] using congrArg (· ≫ f) h₁
  subst y
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [doubledOriginLabelMul]

/-- The chartwise multiplications agree on the overlaps of the product cover, so they glue. -/
private theorem doubledOriginProductChartMap_compatible {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) })
    (p q : (doubledOriginProductCover D F).I₀) :
    pullback.fst ((doubledOriginProductCover D F).f p)
        ((doubledOriginProductCover D F).f q) ≫
        doubledOriginProductChartMap D F p =
      pullback.snd ((doubledOriginProductCover D F).f p)
        ((doubledOriginProductCover D F).f q) ≫
        doubledOriginProductChartMap D F q := by
  have h := pullback.condition (f := (doubledOriginProductCover D F).f p)
    (g := (doubledOriginProductCover D F).f q)
  have h₁ := congrArg (· ≫ pullback.fst F.1 F.1) h
  have h₂ := congrArg (· ≫ pullback.snd F.1 F.1) h
  simp only [Category.assoc, doubledOriginProductCover,
    Scheme.Pullback.openCoverOfLeftRight_f, pullback.map, pullback.lift_fst,
    pullback.lift_snd] at h₁ h₂
  change _ ≫ pullback.fst (D.chart p.1 ≫ F.1) (D.chart p.2 ≫ F.1) ≫ D.chart p.1 =
    _ ≫ pullback.fst (D.chart q.1 ≫ F.1) (D.chart q.2 ≫ F.1) ≫ D.chart q.1 at h₁
  change _ ≫ pullback.snd (D.chart p.1 ≫ F.1) (D.chart p.2 ≫ F.1) ≫ D.chart p.2 =
    _ ≫ pullback.snd (D.chart q.1 ≫ F.1) (D.chart q.2 ≫ F.1) ≫ D.chart q.2 at h₂
  rw [← doubledOriginProduct_fst_eq_snd D F p.1 p.2,
    ← doubledOriginProduct_fst_eq_snd D F q.1 q.2] at h₂
  dsimp only [doubledOriginProductChartMap]
  apply doubledOriginLabelMul_compatible D.chart F.1 F.2
    (pullback.fst ((doubledOriginProductCover D F).f p)
      ((doubledOriginProductCover D F).f q) ≫
      pullback.fst (D.chart p.1 ≫ F.1) (D.chart p.2 ≫ F.1))
    (pullback.snd ((doubledOriginProductCover D F).f p)
      ((doubledOriginProductCover D F).f q) ≫
      pullback.fst (D.chart q.1 ≫ F.1) (D.chart q.2 ≫ F.1)) p.1 p.2 q.1 q.2
  · simpa only [Category.assoc] using h₁
  · simpa only [Category.assoc] using h₂

/-- The multiplication of the doubled-origin group scheme, as a morphism of schemes. -/
@[sga "3 VIB 5.6.4" "partial"]
private noncomputable def doubledOriginMultiplicationMap {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) }) :
    pullback F.1 F.1 ⟶ D.scheme :=
  (doubledOriginProductCover D F).glueMorphisms
    (doubledOriginProductChartMap D F) (doubledOriginProductChartMap_compatible D F)

/-- The multiplication restricts on each product of charts to the chartwise formula. -/
private theorem doubledOriginMultiplicationMap_chart {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) })
    (p : (doubledOriginProductCover D F).I₀) :
    (doubledOriginProductCover D F).f p ≫ doubledOriginMultiplicationMap D F =
      doubledOriginProductChartMap D F p := by
  apply Scheme.Cover.ι_glueMorphisms

/-- The multiplication is a morphism over the affine space. -/
private theorem doubledOriginMultiplicationMap_base {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) }) :
    doubledOriginMultiplicationMap D F ≫ F.1 = pullback.fst F.1 F.1 ≫ F.1 := by
  apply (doubledOriginProductCover D F).hom_ext
  intro p
  rw [← Category.assoc, doubledOriginMultiplicationMap_chart]
  simp only [doubledOriginProductCover, Scheme.Pullback.openCoverOfLeftRight_f,
    pullback.map, pullback.lift_fst_assoc]
  change (pullback.fst (D.chart p.1 ≫ F.1) (D.chart p.2 ≫ F.1) ≫
    D.chart (doubledOriginLabelMul p.1 p.2)) ≫ F.1 = _
  simp only [Category.assoc, doubledOriginChartCover_f, F.2, Category.comp_id]
  exact (Category.comp_id _).symm

section GroupStructure

open MonoidalCategory CartesianMonoidalCategory

variable {k : Type u} [Field k] (D : DoubledOriginData k)
  (F : { f : D.scheme ⟶ infiniteAffineSpace k //
    ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) })

/-- The section of the doubled-origin scheme over a scheme over the affine space given by a chart
label. -/
@[sga "3 VIB 5.6.4" "partial"]
private noncomputable def doubledOriginSection (T : Over (infiniteAffineSpace k)) (i : Fin 2) :
    T ⟶ Over.mk F.1 :=
  Over.homMk (T.hom ≫ D.chart i) (by
    change (T.hom ≫ D.chart i) ≫ F.1 = T.hom
    simp only [Category.assoc, F.2, Category.comp_id])

/-- The chart sections are natural in the test object. -/
private theorem doubledOriginSection_comp {T W : Over (infiniteAffineSpace k)}
    (t : W ⟶ T) (i : Fin 2) :
    t ≫ doubledOriginSection D F T i = doubledOriginSection D F W i := by
  apply Over.OverMorphism.ext
  change t.left ≫ (T.hom ≫ D.chart i) = W.hom ≫ D.chart i
  rw [← Category.assoc, t.w]

/-- Two morphisms out of a test object agree as soon as they agree after every base change on which
a given morphism to the doubled-origin scheme becomes a chart section. This is the chart cover of
the doubled-origin scheme, pulled back along that morphism. -/
private theorem doubledOriginSection_hom_ext {T Y : Over (infiniteAffineSpace k)}
    (a : T ⟶ Over.mk F.1) {b c : T ⟶ Y}
    (h : ∀ (W : Over (infiniteAffineSpace k)) (t : W ⟶ T) (i : Fin 2),
      t ≫ a = doubledOriginSection D F W i → t ≫ b = t ≫ c) : b = c := by
  apply Over.OverMorphism.ext
  let U := doubledOriginChartCover D
  apply Scheme.Cover.hom_ext (U.pullback₁ a.left)
  intro i
  let p := (U.pullback₁ a.left).f i
  let W := Over.mk (p ≫ T.hom)
  let t : W ⟶ T := Over.homMk p
  have hi : t ≫ a = doubledOriginSection D F W i := by
    apply Over.OverMorphism.ext
    change p ≫ a.left = (p ≫ T.hom) ≫ D.chart i
    have hp : p ≫ a.left = pullback.snd a.left (D.chart i) ≫ D.chart i :=
      pullback.condition
    have hb : p ≫ T.hom = pullback.snd a.left (D.chart i) := by
      rw [← a.w, ← Category.assoc, hp, Category.assoc]
      change _ ≫ (D.chart i ≫ F.1) = _
      rw [F.2, Category.comp_id]
    rwa [hb]
  exact congrArg (fun f => f.left) (h W t i hi)

/-- The multiplication of the doubled-origin group scheme, as a morphism over the affine space. -/
private noncomputable def doubledOriginMulHom :
    Over.mk F.1 ⊗ Over.mk F.1 ⟶ Over.mk F.1 :=
  Over.homMk (doubledOriginMultiplicationMap D F) (doubledOriginMultiplicationMap_base D F)

/-- The product of two points of the doubled-origin group scheme over a test object. -/
@[sga "3 VIB 5.6.4" "partial"]
private noncomputable abbrev doubledOriginMul {T : Over (infiniteAffineSpace k)}
    (a b : T ⟶ Over.mk F.1) : T ⟶ Over.mk F.1 :=
  lift a b ≫ doubledOriginMulHom D F

/-- The product of two points is natural in the test object. -/
private theorem doubledOriginMul_comp {T W : Over (infiniteAffineSpace k)}
    (t : W ⟶ T) (a b : T ⟶ Over.mk F.1) :
    t ≫ doubledOriginMul D F a b = doubledOriginMul D F (t ≫ a) (t ≫ b) := by
  simp only [doubledOriginMul, comp_lift_assoc]

/-- On chart sections the product is the chart section of the product label. -/
private theorem doubledOriginMul_sections (T : Over (infiniteAffineSpace k)) (i j : Fin 2) :
    doubledOriginMul D F (doubledOriginSection D F T i) (doubledOriginSection D F T j) =
      doubledOriginSection D F T (doubledOriginLabelMul i j) := by
  apply Over.OverMorphism.ext
  let q : T.left ⟶ (doubledOriginProductCover D F).X (i, j) :=
    pullback.lift T.hom T.hom (by
      change T.hom ≫ (D.chart i ≫ F.1) = T.hom ≫ (D.chart j ≫ F.1)
      rw [F.2, F.2])
  have hq_fst : q ≫ pullback.fst (D.chart i ≫ F.1) (D.chart j ≫ F.1) = T.hom :=
    pullback.lift_fst _ _ _
  have hq_snd : q ≫ pullback.snd (D.chart i ≫ F.1) (D.chart j ≫ F.1) = T.hom :=
    pullback.lift_snd _ _ _
  have hcover_fst : (doubledOriginProductCover D F).f (i, j) ≫ pullback.fst F.1 F.1 =
      pullback.fst (D.chart i ≫ F.1) (D.chart j ≫ F.1) ≫ D.chart i := by
    simp only [doubledOriginProductCover, Scheme.Pullback.openCoverOfLeftRight_f,
      pullback.map, doubledOriginChartCover_f]
    exact pullback.lift_fst _ _ _
  have hcover_snd : (doubledOriginProductCover D F).f (i, j) ≫ pullback.snd F.1 F.1 =
      pullback.snd (D.chart i ≫ F.1) (D.chart j ≫ F.1) ≫ D.chart j := by
    simp only [doubledOriginProductCover, Scheme.Pullback.openCoverOfLeftRight_f,
      pullback.map, doubledOriginChartCover_f]
    exact pullback.lift_snd _ _ _
  have hlift_fst : (lift (doubledOriginSection D F T i)
      (doubledOriginSection D F T j)).left ≫ pullback.fst F.1 F.1 = T.hom ≫ D.chart i := by
    rw [Over.lift_left]
    exact pullback.lift_fst _ _ _
  have hlift_snd : (lift (doubledOriginSection D F T i)
      (doubledOriginSection D F T j)).left ≫ pullback.snd F.1 F.1 = T.hom ≫ D.chart j := by
    rw [Over.lift_left]
    exact pullback.lift_snd _ _ _
  have hq : q ≫ (doubledOriginProductCover D F).f (i, j) =
      (lift (doubledOriginSection D F T i) (doubledOriginSection D F T j)).left :=
    pullback.hom_ext
      (by rw [Category.assoc, hcover_fst, ← Category.assoc, hq_fst, hlift_fst])
      (by rw [Category.assoc, hcover_snd, ← Category.assoc, hq_snd, hlift_snd])
  change (lift (doubledOriginSection D F T i) (doubledOriginSection D F T j)).left ≫
    doubledOriginMultiplicationMap D F = T.hom ≫ D.chart (doubledOriginLabelMul i j)
  rw [← hq, Category.assoc, doubledOriginMultiplicationMap_chart]
  change q ≫ pullback.fst (D.chart i ≫ F.1) (D.chart j ≫ F.1) ≫
    D.chart (doubledOriginLabelMul i j) = _
  rw [← Category.assoc, hq_fst]

/-- The chart section `0` is a left unit. -/
private theorem doubledOriginMul_one_left {T : Over (infiniteAffineSpace k)}
    (a : T ⟶ Over.mk F.1) :
    doubledOriginMul D F (doubledOriginSection D F T 0) a = a := by
  apply doubledOriginSection_hom_ext D F a
  intro W t i hi
  rw [doubledOriginMul_comp, doubledOriginSection_comp, hi, doubledOriginMul_sections]
  fin_cases i <;> rfl

/-- The chart section `0` is a right unit. -/
private theorem doubledOriginMul_one_right {T : Over (infiniteAffineSpace k)}
    (a : T ⟶ Over.mk F.1) :
    doubledOriginMul D F a (doubledOriginSection D F T 0) = a := by
  apply doubledOriginSection_hom_ext D F a
  intro W t i hi
  rw [doubledOriginMul_comp, doubledOriginSection_comp, hi, doubledOriginMul_sections]
  fin_cases i <;> rfl

/-- Every point is its own inverse. -/
private theorem doubledOriginMul_self {T : Over (infiniteAffineSpace k)}
    (a : T ⟶ Over.mk F.1) :
    doubledOriginMul D F a a = doubledOriginSection D F T 0 := by
  apply doubledOriginSection_hom_ext D F a
  intro W t i hi
  rw [doubledOriginMul_comp, doubledOriginSection_comp, hi, doubledOriginMul_sections]
  simp only [doubledOriginLabelMul, ↓reduceIte]

/-- The product of the identity with itself is the unit section. -/
private theorem doubledOriginMul_id_id :
    doubledOriginMul D F (𝟙 (Over.mk F.1)) (𝟙 _) =
      toUnit (Over.mk F.1) ≫ doubledOriginSection D F _ 0 := by
  rw [doubledOriginMul_self, doubledOriginSection_comp]

/-- The multiplication is associative. -/
private theorem doubledOriginMul_assoc {T : Over (infiniteAffineSpace k)}
    (a b c : T ⟶ Over.mk F.1) :
    doubledOriginMul D F (doubledOriginMul D F a b) c =
      doubledOriginMul D F a (doubledOriginMul D F b c) := by
  apply doubledOriginSection_hom_ext D F a
  intro W t i hi
  simp only [doubledOriginMul_comp, hi]
  apply doubledOriginSection_hom_ext D F (t ≫ b)
  intro V r j hj
  simp only [doubledOriginMul_comp, doubledOriginSection_comp, hj]
  apply doubledOriginSection_hom_ext D F (r ≫ t ≫ c)
  intro Z s l hl
  simp only [doubledOriginMul_comp, doubledOriginSection_comp, hl,
    doubledOriginMul_sections]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> rfl

/-- The group structure on the doubled-origin scheme over the affine space it doubles: the fibres
are the group of order two, with the chart label as the group element. -/
@[instance_reducible, sga "3 VIB 5.6.4" "special case"]
private noncomputable def doubledOriginGrpObj : GrpObj (Over.mk F.1) where
  one := doubledOriginSection D F _ 0
  mul := doubledOriginMulHom D F
  one_mul := by
    let X := Over.mk F.1
    have h : doubledOriginSection D F (𝟙_ _) 0 ▷ X =
        lift (doubledOriginSection D F (𝟙_ _ ⊗ X) 0) (snd (𝟙_ _) X) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [doubledOriginSection_comp]
    rw [h]
    exact (doubledOriginMul_one_left D F _).trans (leftUnitor_hom X).symm
  mul_one := by
    let X := Over.mk F.1
    have h : X ◁ doubledOriginSection D F (𝟙_ _) 0 =
        lift (fst X (𝟙_ _)) (doubledOriginSection D F (X ⊗ 𝟙_ _) 0) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [doubledOriginSection_comp]
    rw [h]
    exact (doubledOriginMul_one_right D F _).trans (rightUnitor_hom X).symm
  mul_assoc := by
    let X := Over.mk F.1
    have hleft : doubledOriginMulHom D F ▷ X =
        lift (doubledOriginMul D F (fst (X ⊗ X) X ≫ fst X X)
          (fst (X ⊗ X) X ≫ snd X X)) (snd (X ⊗ X) X) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp [X, doubledOriginMul]
    have hright : (α_ X X X).hom ≫ (X ◁ doubledOriginMulHom D F) =
        lift (fst (X ⊗ X) X ≫ fst X X)
          (doubledOriginMul D F (fst (X ⊗ X) X ≫ snd X X) (snd (X ⊗ X) X)) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
        change _ = lift _ _ ≫ doubledOriginMulHom D F
        rw [← Category.assoc]
        apply congrArg (fun g : (X ⊗ X) ⊗ X ⟶ X ⊗ X => g ≫ doubledOriginMulHom D F)
        apply CartesianMonoidalCategory.hom_ext <;> simp [X]
    rw [hleft, ← Category.assoc, hright]
    exact doubledOriginMul_assoc D F
      (fst (X ⊗ X) X ≫ fst X X) (fst (X ⊗ X) X ≫ snd X X) (snd (X ⊗ X) X)
  inv := 𝟙 _
  left_inv := doubledOriginMul_id_id D F
  right_inv := doubledOriginMul_id_id D F

end GroupStructure

/-- A property of morphisms defined by a ring-hom property holds for the structure morphism to the
affine space as soon as the ring-hom property holds for the identity: on the chart cover the
structure morphism is the identity. -/
private theorem doubledOriginToBase_of_id {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) })
    (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    (hQ : ∀ (R : Type u) [CommRing R], Q (RingHom.id R)) : P F.1 := by
  have : ∀ i, IsAffine ((doubledOriginChartCover D).X i) :=
    fun _ => inferInstanceAs (IsAffine (infiniteAffineSpace k))
  apply (HasRingHomProperty.iff_of_source_openCover (P := P) (doubledOriginChartCover D)).2
  intro i
  have hi : (doubledOriginChartCover D).f i ≫ F.1 = 𝟙 (infiniteAffineSpace k) := F.2 i
  rw [hi, Scheme.Hom.id_appTop]
  exact hQ _

/-- The structure morphism to the affine space is flat: on the chart cover it is the identity. -/
private theorem doubledOriginToBase_flat {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) }) : Flat F.1 :=
  doubledOriginToBase_of_id D F @Flat fun _ => RingHom.Flat.id _

/-- The structure morphism to the affine space is locally of finite type: on the chart cover it is
the identity. -/
private theorem doubledOriginToBase_locallyOfFiniteType {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) }) :
    LocallyOfFiniteType F.1 :=
  doubledOriginToBase_of_id D F @LocallyOfFiniteType fun _ =>
    RingHom.finiteType_holdsForLocalizationAway.containsIdentities _

/-- The structure morphism to the affine space is quasi-compact: the inverse image of an affine
open is the union of its two chart images. -/
private theorem doubledOriginToBase_quasiCompact {k : Type u} [Field k]
    (D : DoubledOriginData k)
    (F : { f : D.scheme ⟶ infiniteAffineSpace k //
      ∀ i : Fin 2, D.chart i ≫ f = 𝟙 (infiniteAffineSpace k) }) :
    QuasiCompact F.1 := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  have hval (i : Fin 2) (y : infiniteAffineSpace k) : F.1 (D.chart i y) = y :=
    congrArg (fun f : infiniteAffineSpace k ⟶ infiniteAffineSpace k => f y) (F.2 i)
  have hpre : F.1 ⁻¹' (U : Set (infiniteAffineSpace k)) =
      ⋃ i : Fin 2, D.chart i '' (U : Set (infiniteAffineSpace k)) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨i, y, hxy⟩ := (doubledOriginChartCover D).exists_eq x
      change D.chart i y = x at hxy
      refine Set.mem_iUnion.mpr ⟨i, y, ?_, hxy⟩
      simpa only [← hxy, Set.mem_preimage, hval] using hx
    · obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      simpa only [Set.mem_preimage, hval] using hy
  change IsCompact (F.1 ⁻¹' (U : Set (infiniteAffineSpace k)))
  rw [hpre]
  exact isCompact_iUnion (fun i => hU.isCompact.image (D.chart i).continuous)

/-- **Stacks Project, Tag 08IX.** A flat finite-type group scheme over
infinite-dimensional affine space need not be quasi-separated. -/
@[stacks 08IX]
public theorem exists_flat_finiteType_groupScheme_not_quasiSeparated
    (k : Type u) [Field k] :
    ∃ G : Grp (Over (Spec (.of (MvPolynomial ℕ k)))),
      Flat G.X.hom ∧ LocallyOfFiniteType G.X.hom ∧
        QuasiCompact G.X.hom ∧ ¬ QuasiSeparated G.X.hom := by
  let D := doubledOriginDatum k
  let F := doubledOriginToBase D
  let _inst := doubledOriginGrpObj D F
  exact ⟨⟨Over.mk F.1⟩, doubledOriginToBase_flat D F,
    doubledOriginToBase_locallyOfFiniteType D F, doubledOriginToBase_quasiCompact D F,
    doubledOriginToBase_not_quasiSeparated D⟩

end AlgebraicGeometry

end

end
