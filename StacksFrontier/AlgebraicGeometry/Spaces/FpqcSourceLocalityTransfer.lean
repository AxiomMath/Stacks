module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact

/-!
# Source locality for the fpqc topology transferred from schemes to algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target (Stacks 04QZ). Stacks 03MJ turns `P` into
the property `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of morphisms of algebraic
spaces over `S`. Stacks 06ER says that if `P` is local on the source for one of the five
topologies of Stacks 03YH then so is the associated property of morphisms of algebraic spaces.
This module proves the fpqc case.

## Main results

* `AlgebraicGeometry.Space.isFpqcCovering_yoneda_of_isCovering`: an fpqc covering of algebraic
  spaces by representables is an fpqc covering of the representing schemes.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso`: the chart condition of
  Stacks 03MJ respects isomorphisms of algebraic spaces.
* `AlgebraicGeometry.Space.isLocalAtSource_fpqc_of_schemes`: if `P` is local on the source for
  the fpqc topology of schemes, the associated property of morphisms of algebraic spaces is local
  on the source for the fpqc topology of algebraic spaces.

## References

* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site times out;
supply them directly. -/
local instance : HasLimitsOfSize.{u, u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
local instance : HasLimitsOfSize.{0, 0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
local instance (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  HasLimitsOfSize.has_limits_of_shape _
local instance : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### Points of a representable presheaf and points of the representing scheme -/

/-- A family of morphisms of the site whose Yoneda images are jointly surjective on points of
the associated presheaves is jointly surjective on the points of the representing schemes. -/
theorem scheme_family_jointly_surjective_of_points
    {I : Type v} (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (f : ∀ i, U i ⟶ V)
    (hpoints : (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (U i))
      (yoneda.map (f i)))) = Set.univ) :
    ∀ x : (BigFppfOver.toScheme B S hS).obj V,
      ∃ i y, ((BigFppfOver.toScheme B S hS).map (f i)) y = x := by
  intro x
  let pt := residueFieldValuedPoint B S hS V x
  have hpt : (reprSchemePoint pt).point = x := reprSchemePoint_residueFieldValuedPoint B S hS V x
  have hx := (Set.eq_univ_iff_forall.mp hpoints) (pt.class B S hS (yoneda.obj V))
  obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hx
  obtain ⟨r, rfl⟩ := Quot.exists_rep q
  let rclass := r.class B S hS (yoneda.obj (U i))
  let rV : FieldValuedPoint B S hS (yoneda.obj V) :=
    FieldValuedPoint.map B S hS (yoneda.obj (U i)) (yoneda.map (f i)) r
  have hmap : pointsMap B S hS (yoneda.obj (U i)) (yoneda.map (f i)) rclass =
      pt.class B S hS (yoneda.obj V) := by
    simpa [rclass] using hq
  have hrV : rV.class B S hS (yoneda.obj V) = pt.class B S hS (yoneda.obj V) := by
    simpa [rV, rclass] using hmap
  have hschemePt := reprSchemePoint_eq_of_commonExtension
    (FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj V) rV pt |>.mp hrV)
  refine ⟨i, (reprSchemePoint r).point, ?_⟩
  rw [← hpt, ← hschemePt]
  rfl

/-- The Yoneda image of a family of morphisms of the site which is an fpqc covering of
algebraic spaces is jointly surjective on points. -/
theorem points_jointly_surjective_of_isFpqcCovering
    {I : Type v} (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (f : ∀ i, U i ⟶ V)
    (hc : IsFpqcCovering B S hS (fun i => yoneda.map (f i))) :
    (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (U i)) (yoneda.map (f i)))) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun p ↦ ?_
  obtain ⟨p, rfl⟩ := Quot.exists_rep p
  let T : BigAffineFppf B S hS := ⟨p.siteObject, by
    show IsAffine (Spec (.of p.carrier))
    infer_instance⟩
  let Vmap : p.siteObject ⟶ V := p.value
  obtain ⟨W, _, hW, hfactor⟩ := hc.2 T (yoneda.map Vmap)
  let F := BigAffineFppf.toScheme B S hS
  have hflatMem : Presieve.ofArrows
      (fun j => F.obj (W.X j)) (fun j => F.map (W.f j)) ∈
        Scheme.precoverage (@Flat.{u}) (F.obj T) := by
    change Presieve.map F W.presieve₀ ∈ Scheme.fpqcPrecoverage (F.obj T) at hW
    change (Presieve.map F W.presieve₀ ∈ Scheme.qcPrecoverage (F.obj T)) ∧
      Presieve.map F W.presieve₀ ∈ Scheme.precoverage (@Flat.{u}) (F.obj T) at hW
    simpa [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀] using hW.2
  have hjoint := (Scheme.ofArrows_mem_precoverage_iff (P := (@Flat.{u} :
      MorphismProperty Scheme.{u}))).mp hflatMem |>.1
  obtain ⟨j, y, hy⟩ := hjoint (IsLocalRing.closedPoint p.carrier)
  obtain ⟨i, a, ha⟩ := hfactor j
  let Wsite := (BigAffineFppf.inclusion B S hS).obj (W.X j)
  let dsite := (BigAffineFppf.inclusion B S hS).map (W.f j)
  let asite := yoneda.preimage a
  have hasite : yoneda.map asite = a := by simp [asite]
  have hcomp : asite ≫ f i = dsite ≫ Vmap := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hasite]
    exact ha
  let rW := residueFieldValuedPoint B S hS Wsite y
  let rUi := FieldValuedPoint.map B S hS (yoneda.obj Wsite) (yoneda.map asite) rW
  let rT := FieldValuedPoint.map B S hS (yoneda.obj Wsite) (yoneda.map dsite) rW
  let rV := FieldValuedPoint.map B S hS (yoneda.obj (U i)) (yoneda.map (f i)) rUi
  have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj V) rV p := by
    refine ⟨rT.value, ?_⟩
    show rT.value ≫ Vmap = rV.value
    show (rW.value ≫ dsite) ≫ Vmap = rW.value ≫ asite ≫ f i
    rw [Category.assoc, ← hcomp]
  have hclass := FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj V)
      ⟨rV, FieldValuedPoint.dominates_refl B S hS (yoneda.obj V) rV, hdom⟩
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨rUi.class B S hS (yoneda.obj (U i)), ?_⟩⟩
  simpa [rV] using hclass

/-! ### Étale charts -/

/-- An étale chart of a presheaf on the big fppf site of `S` is an étale morphism of algebraic
spaces in the sense of Stacks 03FR. -/
theorem chart_map_isEtale
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsEtale B S hS a :=
  (isEtale_iff_presheaf_of_yoneda B S hS a).2 ha

/-! ### Fpqc coverings of representables -/

/-- An fpqc covering family of algebraic spaces over `S` all of whose members and whose target
are representable comes from an fpqc covering family of the representing schemes. -/
theorem isFpqcCovering_yoneda_of_isCovering
    {I : Type v} (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (f : ∀ i, U i ⟶ V)
    (hcover : Topology.IsCovering .fpqc B S hS
      (fun i => yoneda.obj (U i)) (fun i => yoneda.map (f i))) :
    Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj (U i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj V) := by
  rcases hcover with ⟨_, _, hc⟩
  let T := BigFppfOver.toScheme B S hS
  let Xi : I → Scheme.{u} := fun i => T.obj (U i)
  let gi : ∀ i, Xi i ⟶ T.obj V := fun i => T.map (f i)
  have hpoints := points_jointly_surjective_of_isFpqcCovering B S hS U V f hc
  have hsurj := scheme_family_jointly_surjective_of_points B S hS U V f hpoints
  have hflat : ∀ i, Flat (gi i) := fun i =>
    (hc.1 i) (U i) V (𝟙 (yoneda.obj (U i))) (𝟙 (yoneda.obj V)) (f i)
      (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS V) (by simp)
  let : Scheme.JointlySurjective (Scheme.precoverage (@Flat.{u})) := by
    refine ⟨fun R hR x ↦ ?_⟩
    rcases hR with ⟨hjs, _⟩
    rw [Scheme.jointlySurjectivePrecoverage,
      Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hjs
    exact hjs x
  let C : (T.obj V).Cover (Scheme.precoverage (@Flat.{u} : MorphismProperty Scheme.{u})) :=
    Scheme.Cover.mkOfCovers I Xi gi hsurj hflat
  have hqc : QuasiCompactCover C.toPreZeroHypercover := by
    refine ⟨fun {O} hO => ?_⟩
    let W : (T.obj V).affineOpens := ⟨O, hO⟩
    let hW : B.Contains W.1.toScheme := by
      show W.1.toScheme.size < B.cutoff
      exact (Scheme.size_coe_opens_le (T.obj V) W.1).trans_lt V.left.2
    let j : B.inclusion.obj (B.obj hW) ⟶ B.inclusion.obj V.left := by
      show W.1.toScheme ⟶ T.obj V
      exact W.1.ι
    let m : B.obj hW ⟶ V.left := B.inclusion.preimage j
    let Tsite : BigFppfOver B S hS := Over.mk (m ≫ V.hom)
    let Taff : BigAffineFppf B S hS := ⟨Tsite, by
      show IsAffine W.1.toScheme
      exact W.2⟩
    let qsite : Tsite ⟶ V := Over.homMk m (by simp [Tsite])
    have hq : T.map qsite = W.1.ι := by
      show B.inclusion.map (B.inclusion.preimage j) = j
      exact B.inclusion.map_preimage j
    obtain ⟨R, hfinite, hR, hfactor⟩ := hc.2 Taff (yoneda.map qsite)
    let A := BigAffineFppf.toScheme B S hS
    let Rsch : PreZeroHypercover (A.obj Taff) :=
      { I₀ := R.I₀
        X j := A.obj (R.X j)
        f j := A.map (R.f j) }
    have hR' : Presieve.ofArrows Rsch.X Rsch.f ∈ Scheme.fpqcPrecoverage (A.obj Taff) := by
      change Presieve.map A R.presieve₀ ∈ Scheme.fpqcPrecoverage (A.obj Taff) at hR
      simpa [Rsch, PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀] using hR
    have hparts :
        Presieve.ofArrows Rsch.X Rsch.f ∈ Scheme.qcPrecoverage (A.obj Taff) ∧
          Presieve.ofArrows Rsch.X Rsch.f ∈
            Scheme.precoverage (@Flat.{u} : MorphismProperty Scheme.{u}) (A.obj Taff) :=
      hR'
    have hRqc : QuasiCompactCover Rsch :=
      (Scheme.presieve₀_mem_qcPrecoverage_iff).mp hparts.1
    choose k a ha using hfactor
    let ai (j : R.I₀) : (BigAffineFppf.inclusion B S hS).obj (R.X j) ⟶ U (k j) :=
      yoneda.preimage (a j)
    let aj (j : R.I₀) := T.map (ai j)
    have hfactorScheme (j : R.I₀) : aj j ≫ gi (k j) = Rsch.f j ≫ T.map qsite := by
      have hsite : ai j ≫ f (k j) =
          (BigAffineFppf.inclusion B S hS).map (R.f j) ≫ qsite := by
        apply yoneda.map_injective
        simpa [ai] using ha j
      exact congrArg T.map hsite
    have hcompact : IsCompactOpenCovered (fun j => (Rsch.f j).base)
        (Set.univ : Set (A.obj Taff)) :=
      QuasiCompactCover.isCompactOpenCovered_of_isCompact Rsch
        (U := (⊤ : (A.obj Taff).Opens)) isCompact_univ
    let rj : ∀ j, Rsch.X j → T.obj V := fun j => (Rsch.f j ≫ T.map qsite).base
    have hcompactOpen : IsCompactOpenCovered rj (Set.range (T.map qsite).base) := by
      obtain ⟨s, hs, O, hcompactO, hcover⟩ := hcompact
      refine ⟨s, hs, O, hcompactO, ?_⟩
      simpa [rj, Scheme.Hom.comp_base, Set.image_iUnion, Set.image_image,
        Set.image_univ] using congrArg (Set.image (T.map qsite).base) hcover
    have hcompactCover : IsCompactOpenCovered (fun i => (gi i).base)
        (Set.range (T.map qsite).base) := by
      let ajt : ∀ j, Rsch.X j → Xi (k j) := fun j => (aj j).base
      apply IsCompactOpenCovered.of_comp (f := fun i => (gi i).base)
        (g := rj) (a := k) (t := ajt)
      · exact fun j => (aj j).continuous
      · intro j
        funext x
        simpa [rj, ajt, Function.comp_apply, Scheme.Hom.comp_base] using
          (congrArg (fun k => k.base x) (hfactorScheme j)).symm
      · exact fun i => (gi i).continuous
      · rw [hq]
        exact IsOpenImmersion.isOpen_range _
      · exact hcompactOpen
    have hrange : Set.range (T.map qsite).base = (W.1 : Set (T.obj V)) := by
      rw [hq]
      exact Scheme.Opens.range_ι W.1
    show IsCompactOpenCovered (fun i => (gi i).base) (↑O : Set (T.obj V))
    rwa [← hrange]
  let C' := C.ofQuasiCompactCover
  show Presieve.ofArrows Xi gi ∈ Scheme.fpqcPrecoverage (T.obj V)
  simpa [C, C', Xi, gi, T, Scheme.fpqcPrecoverage, Scheme.propQCPrecoverage,
    Scheme.Cover.ofQuasiCompactCover, Scheme.Cover.mkOfCovers] using C'.mem₀

/-- Composing an fpqc covering of algebraic spaces over `S` with a surjective étale scheme
atlas of each of its members gives an fpqc covering, indexed by the members paired with a
one-element type. -/
theorem etale_atlases_comp_isFpqcCovering
    {I : Type v} (Z : I → AlgebraicSpaces B S hS) (V : AlgebraicSpaces B S hS)
    (g : ∀ i, Z i ⟶ V)
    (hbase : Topology.IsCovering .fpqc B S hS (fun i => (Z i).1) (fun i => (g i).hom))
    (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ (Z i).1)
    (hsurj : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hetale : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i)) :
    Topology.IsCovering .fpqc B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (U p.1))
      (fun p => a p.1 ≫ (g p.1).hom) := by
  have hatlas : ∀ i, IsFpqcCovering B S hS (fun _ : PUnit.{v + 1} => a i) := fun i =>
    isFpqcCovering_of_isEtaleCovering B S hS _ _
      (isEtaleCovering_atlas B S hS (hbase.2.1 i) (hsurj i) (hetale i))
  refine ⟨hbase.1, fun p => isAlgebraicSpace_yoneda B S hS (U p.1), ?_⟩
  exact isFpqcCovering_comp (B := B) (S := S) (hS := hS) (I := I)
    (J := fun _ : I => PUnit.{v + 1}) (X := V.1) (Xi := fun i => (Z i).1)
    (Xij := fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (U p.1))
    hbase.1 hbase.2.1 (fun i _ => isAlgebraicSpace_yoneda B S hS (U i))
    (fun i => (g i).hom) (fun i _ => a i) hbase.2.2 hatlas

/-- Base change of an fpqc covering of algebraic spaces over `S` along a chart of its target:
the fibre products form an fpqc covering of the chart, and each of them sits in a pullback
square over the chart and the corresponding member of the original family. -/
theorem isFpqcCovering_baseChange_of_chart
    {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .fpqc B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i),
        Topology.IsCovering .fpqc B S hS (fun i => (Ai i).1) (fun i => (qi i).hom) ∧
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) := by
  let Uobj := representedAlgebraicSpace B S hS U
  let au : Uobj ⟶ X := ObjectProperty.homMk a
  let Ai : I → AlgebraicSpaces B S hS :=
    fun i => AlgebraicSpaces.fiberProduct B S hS (gi i) au
  refine ⟨Ai, fun i => ObjectProperty.homMk (pullback.snd (gi i).hom au.hom),
    fun i => ObjectProperty.homMk (pullback.fst (gi i).hom au.hom), ?_, ?_⟩
  · exact ⟨Uobj.property, fun i => (Ai i).property,
      isFpqcCovering_pullback B S hS gi au hcover.2.2⟩
  · exact fun i => (AlgebraicSpaces.isPullback_fiberProduct B S hS (gi i) au).flip

/-- Étale atlases of the members of an fpqc covering of a representable space give an fpqc
covering of the representing scheme, whose members map to the chart through `d`. -/
private theorem exists_scheme_cover_of_atlases
    {I : Type v} (U : BigFppfOver B S hS) (Ai : I → AlgebraicSpaces B S hS)
    (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
    (hAi : Topology.IsCovering .fpqc B S hS (fun i => (Ai i).1) (fun i => (qi i).hom))
    (Wi : I → BigFppfOver B S hS) (wi : ∀ i, yoneda.obj (Wi i) ⟶ (Ai i).1)
    (hsurjWi : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (wi i))
    (hetaleWi : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (wi i)) :
    ∃ d : ∀ p : Σ _ : I, PUnit.{v + 1}, Wi p.1 ⟶ U,
      (∀ p, yoneda.map (d p) = wi p.1 ≫ (qi p.1).hom) ∧
      Presieve.ofArrows
        (fun p : Σ _ : I, PUnit.{v + 1} => (BigFppfOver.toScheme B S hS).obj (Wi p.1))
        (fun p => (BigFppfOver.toScheme B S hS).map (d p)) ∈
        Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U) := by
  let d : ∀ p : Σ _ : I, PUnit.{v + 1}, Wi p.1 ⟶ U :=
    fun p => yoneda.preimage (wi p.1 ≫ (qi p.1).hom)
  have hd (p : Σ _ : I, PUnit.{v + 1}) : yoneda.map (d p) = wi p.1 ≫ (qi p.1).hom := by
    simp [d]
  refine ⟨d, hd, isFpqcCovering_yoneda_of_isCovering B S hS _ U d ?_⟩
  simpa only [hd] using etale_atlases_comp_isFpqcCovering B S hS Ai
    (representedAlgebraicSpace B S hS U) qi hAi Wi wi hsurjWi hetaleWi

/-- If `qi` is the base change of a chart `a` along `gi`, then the composite of an étale chart
of the source of `qi` with the other projection is an étale chart of the source of `gi`. -/
private theorem presheaf_etale_comp_of_isPullback
    {X Z A : AlgebraicSpaces B S hS} (U W : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1)
    (g : Z ⟶ X) (q : A ⟶ representedAlgebraicSpace B S hS U) (r : A ⟶ Z)
    (hpb : IsPullback q r (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) g)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (w : yoneda.obj W ⟶ A.1)
    (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (w ≫ r.hom) :=
  (isEtale_iff_presheaf_of_yoneda B S hS _).1 <| isEtale_comp B S hS
    (chart_map_isEtale B S hS W w hw)
    (isEtale_of_isPullback B S hS q r _ g hpb (chart_map_isEtale B S hS U a ha))

/-! ### Invariance under isomorphism -/

/-- The chart condition `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, read as a property of
morphisms of the category of algebraic spaces over `S`, respects isomorphisms. -/
theorem holdsOnEveryEtaleChart_respectsIso (P : MorphismProperty Scheme.{u}) :
    MorphismProperty.RespectsIso
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom) := by
  let C := AlgebraicSpaces B S hS
  let Cobj : ObjectProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := IsAlgebraicSpace B S hS
  let Q : MorphismProperty C := fun {F G} f => HoldsOnEveryEtaleChart B S hS P f.hom
  let E0 := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let E := E0.presheaf
  let : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : E0.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let : E.RespectsIso := MorphismProperty.relative_respectsIso E0
  refine MorphismProperty.RespectsIso.mk Q ?_ ?_
  · intro F G H e f hf
    show HoldsOnEveryEtaleChart B S hS P (e.hom ≫ f).hom
    intro U V a b h ha hb hh
    have ha' : E (a ≫ Cobj.ι.map e.hom) :=
      MorphismProperty.RespectsIso.postcomp E (Cobj.ι.map e.hom) a ha
    apply hf U V (a ≫ Cobj.ι.map e.hom) b h ha' hb
    change yoneda.map h ≫ b = a ≫ (Cobj.ι.map e.hom ≫ f.hom) at hh
    simpa [Category.assoc] using hh
  · intro F G H e f hf
    show HoldsOnEveryEtaleChart B S hS P (f ≫ e.hom).hom
    intro U V a b h ha hb hh
    have hb' : E (b ≫ Cobj.ι.map e.inv) :=
      MorphismProperty.RespectsIso.postcomp E (Cobj.ι.map e.inv) b hb
    apply hf U V a (b ≫ Cobj.ι.map e.inv) h ha hb'
    change yoneda.map h ≫ b = a ≫ (f.hom ≫ Cobj.ι.map e.hom) at hh
    rw [← Category.assoc, hh]
    simp

/-! ### Source locality for the fpqc topology -/

/-- If a property `P` of morphisms of schemes is étale local on the source and target and local
on the source for the fpqc topology of schemes, then the associated property
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of morphisms of algebraic spaces over `S`
is local on the source for the fpqc topology of algebraic spaces. -/
theorem isLocalAtSource_fpqc_of_schemes
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsLocalAtSource Scheme.fpqcPrecoverage] :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have hlocal : P.IsLocalAtSource Scheme.fpqcPrecoverage := ‹_›
  let C := AlgebraicSpaces B S hS
  let Q : MorphismProperty C := fun {F G} f => HoldsOnEveryEtaleChart B S hS P f.hom
  let T := BigFppfOver.toScheme B S hS
  let : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS P
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover ?_
  intro X Y f E
  rcases E.mem₀ with ⟨I, Zi, gi, hpres, hcover⟩
  constructor
  · intro hf i
    have hgiQ : ∀ j : I, Q ((gi j) ≫ f) := by
      intro j
      obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.property.exists_atlas
      obtain ⟨T0, t, alpha, hα, htSurj, htEtale⟩ :=
        exists_surjective_etale_presentation_lift B S hS
          X.property Y.property f.hom V b hbSurj hbEtale
      have hPalpha : P (T.map alpha) := hf T0 V t b alpha htEtale hbEtale hα.symm
      let Tobj : AlgebraicSpaces B S hS :=
        ⟨yoneda.obj T0, isAlgebraicSpace_yoneda B S hS T0⟩
      let tX : Tobj ⟶ X := ObjectProperty.homMk t
      obtain ⟨Ai, qi, projZ, hAi, hpb⟩ :=
        isFpqcCovering_baseChange_of_chart B S hS Zi gi hcover T0 t
      choose Wi wi hsurjWi hetaleWi using fun k => (Ai k).property.exists_atlas
      obtain ⟨d, hd, hschemeCover⟩ :=
        exists_scheme_cover_of_atlases B S hS T0 Ai qi hAi Wi wi hsurjWi hetaleWi
      have hPbranch (p : Σ _ : I, PUnit.{v + 1}) : P (T.map (d p ≫ alpha)) := by
        show P (T.map (d p) ≫ T.map alpha)
        exact hlocal.comp hschemeCover (T.map (d p)) (by exact ⟨p⟩) hPalpha
      let c : yoneda.obj (Wi j) ⟶ (Zi j).1 := wi j ≫ (projZ j).hom
      have hcEtale' := presheaf_etale_comp_of_isPullback B S hS T0 (Wi j) t (gi j) (qi j)
        (projZ j) (hpb j) htEtale (wi j) (hetaleWi j)
      have htSurjPts : IsSurjective B S hS t :=
        (surjective_iff_surjective_pointsMap B S hS X.1 X.property T0 t).mp htSurj
      have hprojSurj : IsSurjective B S hS (projZ j).hom :=
        isSurjective_of_isPullback B S hS (hpb j) htSurjPts
      have hwiSurj : IsSurjective B S hS (wi j) :=
        (surjective_iff_surjective_pointsMap B S hS (Ai j).1 (Ai j).property
          (Wi j) (wi j)).mp (hsurjWi j)
      have hcSurjPts : IsSurjective B S hS c := isSurjective_comp B S hS hwiSurj hprojSurj
      have hcSurj := (surjective_iff_surjective_pointsMap B S hS
        (Zi j).1 (Zi j).property (Wi j) c).mpr hcSurjPts
      let p : Σ _ : I, PUnit.{v + 1} := ⟨j, PUnit.unit⟩
      let h : Wi j ⟶ V := yoneda.preimage (wi j ≫ (qi j).hom ≫ yoneda.map alpha)
      have hh : yoneda.map h = wi j ≫ (qi j).hom ≫ yoneda.map alpha := by simp [h]
      have hPh : P (T.map h) := by
        have heq : h = d p ≫ alpha := by
          apply yoneda.map_injective
          simp [p, hd, hh, Functor.map_comp]
        simpa [heq, Functor.map_comp] using hPbranch p
      have hcomm : yoneda.map h ≫ b = c ≫ (gi j).hom ≫ f.hom := by
        have hpbw : (qi j).hom ≫ tX.hom = (projZ j).hom ≫ (gi j).hom :=
          congrArg (fun k => k.hom) (hpb j).w
        have hα' : tX.hom ≫ f.hom = yoneda.map alpha ≫ b := by simpa [tX] using hα
        rw [hh]
        simp only [Category.assoc, ← hα', reassoc_of% hpbw, c]
      exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP (Zi j).property
        Y.property ((gi j ≫ f).hom)).2
          ⟨Wi j, V, c, b, h, hcEtale', hbEtale, hcSurj, hcomm, hPh⟩
    have hmem : E.presieve₀ (E.f i) := ⟨i⟩
    obtain ⟨j, hobj, hindex⟩ := Presieve.ofArrows_surj gi (E.f i) (by
      simpa only [hpres] using hmem)
    let e : E.toPreZeroHypercover.2 i ⟶ Zi j := eqToHom hobj.symm
    let : IsIso e := inferInstance
    show Q (E.f i ≫ f)
    rw [hindex]
    exact MorphismProperty.RespectsIso.precomp Q e (gi j ≫ f) (hgiQ j)
  · intro hall U V a b h ha hb hcomm
    let Uobj : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
    let au : Uobj ⟶ X := ObjectProperty.homMk a
    obtain ⟨Ai, qi, projZ, hAi, hpb⟩ :=
      isFpqcCovering_baseChange_of_chart B S hS Zi gi hcover U a
    choose Wi wi hsurjWi hetaleWi using fun i => (Ai i).property.exists_atlas
    obtain ⟨d, hd, hschemeCover⟩ :=
      exists_scheme_cover_of_atlases B S hS U Ai qi hAi Wi wi hsurjWi hetaleWi
    apply hlocal.of_forall_comp hschemeCover
    intro W' k hk
    cases hk with
    | mk p =>
      rcases p with ⟨i, ji⟩
      let wz : yoneda.obj (Wi i) ⟶ (Zi i).1 := wi i ≫ (projZ i).hom
      have hwzEtale' := presheaf_etale_comp_of_isPullback B S hS U (Wi i) a (gi i) (qi i)
        (projZ i) (hpb i) ha (wi i) (hetaleWi i)
      let hV : Wi i ⟶ V := yoneda.preimage (wi i ≫ (qi i).hom ≫ yoneda.map h)
      have hhV : yoneda.map hV = wi i ≫ (qi i).hom ≫ yoneda.map h := by simp [hV]
      have hbaseEq : (qi i).hom ≫ a = (projZ i).hom ≫ (gi i).hom :=
        congrArg (fun k => k.hom) (hpb i).w
      have hchartComm : yoneda.map hV ≫ b = wz ≫ (gi i).hom ≫ f.hom := by
        rw [hhV]
        simp only [Category.assoc, hcomm, reassoc_of% hbaseEq, wz]
      have hmem : E.presieve₀ (gi i) := by rw [hpres]; exact ⟨i⟩
      obtain ⟨j, hobj, hgi⟩ := Presieve.ofArrows_surj E.f (gi i) (by
        simpa only [hpres] using hmem)
      have hi := hall j
      change HoldsOnEveryEtaleChart B S hS P ((E.f j ≫ f).hom) at hi
      let e : Zi i ⟶ E.toPreZeroHypercover.2 j := eqToHom hobj.symm
      let : IsIso e := inferInstance
      have hi' : HoldsOnEveryEtaleChart B S hS P ((gi i).hom ≫ f.hom) := by
        show Q (gi i ≫ f)
        rw [hgi]
        exact MorphismProperty.RespectsIso.precomp Q e (E.f j ≫ f) hi
      have hPi := hi' (Wi i) V wz b hV hwzEtale' hb hchartComm
      let p : Σ _ : I, PUnit.{v + 1} := ⟨i, ji⟩
      have hdcomp : d p ≫ h = hV := by
        apply yoneda.map_injective
        simp [p, hd, hhV, Functor.map_comp]
      rw [← Functor.map_comp, hdcomp]
      exact hPi

end AlgebraicGeometry.Space

end
