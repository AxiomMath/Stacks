module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# Refining a covering of the small étale site to finitely many members near a compact set

Let `X` be an algebraic space, `V` a family of objects of its small étale site covering the final
object, and `T ⊆ |X|` a closed and compact set of points.  Then there is a finite subfamily
`(V k)_{k ∈ F}` and a family of objects covering the final object each member of which either maps
to some `V k` with `k ∈ F`, or has all its points outside `T`.

This is the step "`T` is quasi-compact, so finitely many members of the covering suffice near `T`"
of the proofs of Stacks 0DJQ and Stacks 0DKJ, in the form in which a local statement with a
uniform bound can be propagated: a property of the restrictions to the `V k` that passes along
arrows of the site holds on the members of the first kind, with the bounds of finitely many `V k`.

## Main results

* `AlgebraicGeometry.Space.exists_mem_range_chartSchemeToPoints_of_coversTop`: the members of a
  covering family are jointly surjective on `|X|`.
* `AlgebraicGeometry.Space.isOpen_range_chartSchemeToPoints`: the image of an étale chart is open.
* `AlgebraicGeometry.Space.exists_coversTop_finite_near`: the refinement.

## The proof

The images of the members of the family are open (Stacks 03BX (3)) and cover `|X|`, so finitely
many of them cover `T`.  The refining family has two kinds of members: for an object `A` and a
member `V k` of the finite subfamily, the fibre product `A ×_X V k`; and for an object `A`, the
open subscheme of `A` lying over `|X| \ T`.  It covers the final object by the pointwise
criterion for covering sieves of the small étale site: a point of an object `A` over a point
outside `T` lies in the second member at `A`, and a point over a point of `T` lies in the image of
the fibre product with a `V k` containing that point in its image, by Stacks 03H4.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The point of `X` determined by a point of an étale chart is the image of the corresponding
point of the represented presheaf. -/
theorem chartSchemeToPoints_eq (A : SmallEtale B S hS X.1)
    (p : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A))) :
    chartSchemeToPoints B S hS X.1 A
        (pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A) p) =
      pointsMap B S hS _ A.obj.hom p := by
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
  congr 1
  exact (pointsEquivScheme B S hS _).symm_apply_apply p

/-- **The image of an étale chart is open.** -/
theorem isOpen_range_chartSchemeToPoints (A : SmallEtale B S hS X.1) :
    IsOpen (Set.range (chartSchemeToPoints B S hS X.1 A)) := by
  have h : Set.range (chartSchemeToPoints B S hS X.1 A) =
      Set.range (pointsMap B S hS _ A.obj.hom) :=
    Set.Subset.antisymm (Set.range_subset_iff.2 fun x => ⟨_,
      (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 A x).symm⟩)
      (Set.range_subset_iff.2 fun p => ⟨_, chartSchemeToPoints_eq B S hS X A p⟩)
  rw [h]
  exact (isOpenMap_pointsMap_of_presheafEtale B S hS A.obj.hom A.property).isOpen_range

/-- Every point of `X` lies in the image of some étale chart. -/
theorem exists_mem_range_chartSchemeToPoints (y : points B S hS X.1) :
    ∃ (A : SmallEtale B S hS X.1) (x : chartScheme A), chartSchemeToPoints B S hS X.1 A x = y := by
  obtain ⟨W, b, -, hb, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X.1 X.2 y
  let A : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hb⟩
  exact ⟨A, pointsToScheme B S hS W w, (chartSchemeToPoints_eq B S hS X A w).trans hw⟩

/-- **The members of a family covering the final object are jointly surjective on `|X|`.** -/
theorem exists_mem_range_chartSchemeToPoints_of_coversTop {K : Type*}
    {V : K → SmallEtale B S hS X.1} (hV : (SmallEtale.topology B S hS X.1).CoversTop V)
    (y : points B S hS X.1) :
    ∃ (k : K) (z : chartScheme (V k)), chartSchemeToPoints B S hS X.1 (V k) z = y := by
  obtain ⟨A, x, rfl⟩ := exists_mem_range_chartSchemeToPoints B S hS X y
  obtain ⟨W, g, hg, z, rfl⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 _).1 (hV A) x
  obtain ⟨k, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  refine ⟨k, (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h) z, ?_⟩
  rw [chartSchemeToPoints_map, chartSchemeToPoints_map]

/-- The open subscheme of an étale chart lying over the complement of a closed set of points. -/
def chartComplOpens (A : SmallEtale B S hS X.1) (T : Set (points B S hS X.1))
    (hT : IsClosed T) : (chartScheme A).Opens :=
  ⟨chartSchemeToPoints B S hS X.1 A ⁻¹' Tᶜ,
    hT.isOpen_compl.preimage (continuous_chartSchemeToPoints B S hS A)⟩

/-- The points of the open subchart over the complement of `T` lie outside `T`. -/
theorem chartSchemeToPoints_openChart_chartComplOpens_notMem (A : SmallEtale B S hS X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (z : chartScheme (openChart B S hS X.1 A (chartComplOpens B S hS X A T hT))) :
    chartSchemeToPoints B S hS X.1 (openChart B S hS X.1 A (chartComplOpens B S hS X A T hT)) z ∉
      T := by
  rw [← chartSchemeToPoints_map B S hS X.1 (openChartInclusion B S hS X.1 A _),
    toScheme_map_toOver_map_openChartInclusion]
  have hz : (chartComplOpens B S hS X A T hT).ι z ∈
      ((chartComplOpens B S hS X A T hT : (chartScheme A).Opens) : Set (chartScheme A)) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨z, rfl⟩
  exact hz

/-- **A point of an étale chart `A` over a point of an étale chart `V` lies in the image of the
fibre product `A ×_X V`**, by Stacks 03H4. -/
theorem exists_prodFst_eq (A V : SmallEtale B S hS X.1) (x : chartScheme A) (z : chartScheme V)
    (h : chartSchemeToPoints B S hS X.1 A x = chartSchemeToPoints B S hS X.1 V z) :
    ∃ w : chartScheme (SmallEtale.prodObj B S hS X.1 A V),
      (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map (SmallEtale.prodFst B S hS X.1 A V)) w = x := by
  let a := (SmallEtale.toOver B S hS X.1).obj A
  let v := (SmallEtale.toOver B S hS X.1).obj V
  let pr := (SmallEtale.toOver B S hS X.1).obj (SmallEtale.prodObj B S hS X.1 A V)
  let Za : AlgebraicSpaces B S hS := ⟨yoneda.obj a, isAlgebraicSpace_yoneda B S hS a⟩
  let Zv : AlgebraicSpaces B S hS := ⟨yoneda.obj v, isAlgebraicSpace_yoneda B S hS v⟩
  let Zp : AlgebraicSpaces B S hS := ⟨yoneda.obj pr, isAlgebraicSpace_yoneda B S hS pr⟩
  let fst : Zp ⟶ Za := ObjectProperty.homMk (yoneda.map (A.property.rep.fst' V.obj.hom))
  let snd : Zp ⟶ Zv := ObjectProperty.homMk (yoneda.map (A.property.rep.snd V.obj.hom))
  let ga : Za ⟶ X := ObjectProperty.homMk A.obj.hom
  let gv : Zv ⟶ X := ObjectProperty.homMk V.obj.hom
  have sq0 := A.property.rep.isPullback' V.obj.hom
  have sq : IsPullback fst snd ga gv :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq0.w) sq0
  obtain ⟨pw, hpa, -⟩ := exists_point_of_isPullback B S hS sq
    ((pointsEquivScheme B S hS a).symm x) ((pointsEquivScheme B S hS v).symm z)
    ((chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 A x).symm.trans
      (h.trans (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 V z)))
  refine ⟨pointsToScheme B S hS pr pw, ?_⟩
  have e1 : (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (SmallEtale.prodFst B S hS X.1 A V)) =
      (BigFppfOver.toScheme B S hS).map (A.property.rep.fst' V.obj.hom) := rfl
  rw [e1]
  refine (pointsToScheme_pointsMap_yoneda B S hS _ pw).symm.trans ?_
  show pointsToScheme B S hS a (pointsMap B S hS Zp.1 fst.hom pw) = x
  rw [hpa]
  exact (pointsEquivScheme B S hS a).apply_symm_apply x

/-- Finitely many members of a covering family suffice to see every point of a compact set `T`:
a point of a chart `A` over `T` lies in the image of some `A ×_X V k` with `k` in a fixed finite
set. -/
private theorem exists_finset_prodFst {K : Type*} {V : K → SmallEtale B S hS X.1}
    (hV : (SmallEtale.topology B S hS X.1).CoversTop V) (T : Set (points B S hS X.1))
    (hTc : IsCompact T) :
    ∃ F : Finset K, ∀ (A : SmallEtale B S hS X.1) (x : chartScheme A),
      chartSchemeToPoints B S hS X.1 A x ∈ T → ∃ k ∈ F,
        ∃ w : chartScheme (SmallEtale.prodObj B S hS X.1 A (V k)),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
            (SmallEtale.prodFst B S hS X.1 A (V k))) w = x := by
  obtain ⟨F, hF⟩ := hTc.elim_finite_subcover
    (fun k => Set.range (chartSchemeToPoints B S hS X.1 (V k)))
    (fun k => isOpen_range_chartSchemeToPoints B S hS X (V k))
    (fun y _ => Set.mem_iUnion.2 (exists_mem_range_chartSchemeToPoints_of_coversTop B S hS X hV y))
  refine ⟨F, fun A x hx => ?_⟩
  obtain ⟨k, hkF, z, hz⟩ := Set.mem_iUnion₂.1 (hF hx)
  exact ⟨k, hkF, exists_prodFst_eq B S hS X A (V k) x z hz.symm⟩

/-- **Refining a covering family to finitely many members near a compact closed set.**  If `V`
covers the final object of the small étale site of `X` and `T ⊆ |X|` is compact and closed, there
are a finite set `F` of indices and a family covering the final object each member of which either
maps to `V k` for some `k ∈ F` or has all its points outside `T`. -/
theorem exists_coversTop_finite_near {K : Type w} {V : K → SmallEtale B S hS X.1}
    (hV : (SmallEtale.topology B S hS X.1).CoversTop V) (T : Set (points B S hS X.1))
    (hTc : IsCompact T) (hTcl : IsClosed T) :
    ∃ (F : Finset K) (I : Type (max w (u + 1))) (W : I → SmallEtale B S hS X.1),
      (SmallEtale.topology B S hS X.1).CoversTop W ∧
      ∀ i, (∃ k ∈ F, Nonempty (W i ⟶ V k)) ∨
        ∀ z : chartScheme (W i), chartSchemeToPoints B S hS X.1 (W i) z ∉ T := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_prodFst B S hS X hV T hTc
  let I : Type (max w (u + 1)) := (Σ _ : F, SmallEtale B S hS X.1) ⊕ SmallEtale B S hS X.1
  let W : I → SmallEtale B S hS X.1 := fun i => match i with
    | Sum.inl ⟨k, A⟩ => SmallEtale.prodObj B S hS X.1 A (V k.1)
    | Sum.inr A => openChart B S hS X.1 A (chartComplOpens B S hS X A T hTcl)
  refine ⟨F, I, W, fun A => ?_, fun i => ?_⟩
  · refine (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 _).2 fun x => ?_
    by_cases hx : chartSchemeToPoints B S hS X.1 A x ∈ T
    · obtain ⟨k, hkF, w, hw⟩ := hF A x hx
      exact ⟨_, SmallEtale.prodFst B S hS X.1 A (V k),
        (Sieve.mem_ofObjects_iff _ _).2 ⟨Sum.inl ⟨⟨k, hkF⟩, A⟩, ⟨𝟙 _⟩⟩, w, hw⟩
    · refine ⟨_, openChartInclusion B S hS X.1 A (chartComplOpens B S hS X A T hTcl),
        (Sieve.mem_ofObjects_iff _ _).2 ⟨Sum.inr A, ⟨𝟙 _⟩⟩, ?_⟩
      rw [toScheme_map_toOver_map_openChartInclusion]
      exact ⟨⟨x, hx⟩, rfl⟩
  · match i with
    | Sum.inl ⟨k, A⟩ => exact Or.inl ⟨k.1, k.2, ⟨SmallEtale.prodSnd B S hS X.1 A (V k.1)⟩⟩
    | Sum.inr A => exact Or.inr fun z =>
        chartSchemeToPoints_openChart_chartComplOpens_notMem B S hS X A T hTcl z

/-- A point of an étale chart lying outside a closed set lies in the open subchart over the
complement. -/
theorem exists_openChart_chartComplOpens (A : SmallEtale B S hS X.1) (T : Set (points B S hS X.1))
    (hT : IsClosed T) (x : chartScheme A) (hx : chartSchemeToPoints B S hS X.1 A x ∉ T) :
    ∃ y : chartScheme (openChart B S hS X.1 A (chartComplOpens B S hS X A T hT)),
      chartSchemeToPoints B S hS X.1 (openChart B S hS X.1 A (chartComplOpens B S hS X A T hT)) y =
        chartSchemeToPoints B S hS X.1 A x := by
  have hmem : x ∈ Set.range (chartComplOpens B S hS X A T hT).ι := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, hy⟩ := hmem
  have h := chartSchemeToPoints_map B S hS X.1
    (openChartInclusion B S hS X.1 A (chartComplOpens B S hS X A T hT)) y
  rw [toScheme_map_toOver_map_openChartInclusion] at h
  exact ⟨y, h.symm.trans (congrArg _ hy)⟩

/-- A point of `|X|` outside a closed set `T` is the image of a point of the open subchart, over
the complement of `T`, of a member of a covering family. -/
private theorem exists_openChart_point_of_notMem {K : Type*} {V : K → SmallEtale B S hS X.1}
    (hV : (SmallEtale.topology B S hS X.1).CoversTop V) (T : Set (points B S hS X.1))
    (hT : IsClosed T) (x : points B S hS X.1) (hx : x ∉ T) :
    ∃ (k : K) (y : chartScheme (openChart B S hS X.1 (V k) (chartComplOpens B S hS X (V k) T hT))),
      chartSchemeToPoints B S hS X.1
        (openChart B S hS X.1 (V k) (chartComplOpens B S hS X (V k) T hT)) y = x := by
  obtain ⟨k, z, rfl⟩ := exists_mem_range_chartSchemeToPoints_of_coversTop B S hS X hV x
  obtain ⟨y, hy⟩ := exists_openChart_chartComplOpens B S hS X (V k) T hT z hx
  exact ⟨k, y, hy⟩

/-- **Refining a covering family near a compact closed set, with every member over a member of
the family.**  If `V` covers the final object of the small étale site of `X` and `T ⊆ |X|` is
compact and closed, there are a finite set `F` of indices and a family `W` covering the final
object, each member of which maps to some `V (κ i)`, with either `κ i ∈ F` or all the points of
`W i` outside `T`; moreover every point outside `T` is a point of a member of the second kind. -/
theorem exists_coversTop_finite_near_over {K : Type w} {V : K → SmallEtale B S hS X.1}
    (hV : (SmallEtale.topology B S hS X.1).CoversTop V) (T : Set (points B S hS X.1))
    (hTc : IsCompact T) (hTcl : IsClosed T) :
    ∃ (F : Finset K) (I : Type (max w (u + 1))) (W : I → SmallEtale B S hS X.1) (κ : I → K),
      (SmallEtale.topology B S hS X.1).CoversTop W ∧ (∀ i, Nonempty (W i ⟶ V (κ i))) ∧
      (∀ i, κ i ∈ F ∨ ∀ z : chartScheme (W i), chartSchemeToPoints B S hS X.1 (W i) z ∉ T) ∧
      ∀ x : points B S hS X.1, x ∉ T → ∃ (i : I) (z : chartScheme (W i)),
        (∀ z' : chartScheme (W i), chartSchemeToPoints B S hS X.1 (W i) z' ∉ T) ∧
          chartSchemeToPoints B S hS X.1 (W i) z = x := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_prodFst B S hS X hV T hTc
  let Vc : K → SmallEtale B S hS X.1 := fun k =>
    openChart B S hS X.1 (V k) (chartComplOpens B S hS X (V k) T hTcl)
  let I : Type (max w (u + 1)) :=
    (Σ _ : F, SmallEtale B S hS X.1) ⊕ (Σ _ : K, SmallEtale B S hS X.1)
  let W : I → SmallEtale B S hS X.1 := fun i => match i with
    | Sum.inl ⟨k, A⟩ => SmallEtale.prodObj B S hS X.1 A (V k.1)
    | Sum.inr ⟨k, A⟩ => SmallEtale.prodObj B S hS X.1 A (Vc k)
  let κ : I → K := fun i => match i with
    | Sum.inl ⟨k, _⟩ => k.1
    | Sum.inr ⟨k, _⟩ => k
  have hout : ∀ (k : K) (A : SmallEtale B S hS X.1)
      (z : chartScheme (SmallEtale.prodObj B S hS X.1 A (Vc k))),
      chartSchemeToPoints B S hS X.1 (SmallEtale.prodObj B S hS X.1 A (Vc k)) z ∉ T := by
    intro k A z
    rw [← chartSchemeToPoints_map B S hS X.1 (SmallEtale.prodSnd B S hS X.1 A (Vc k))]
    exact chartSchemeToPoints_openChart_chartComplOpens_notMem B S hS X (V k) T hTcl _
  refine ⟨F, I, W, κ, fun A => ?_, fun i => ?_, fun i => ?_, fun x hx => ?_⟩
  · refine (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 _).2 fun x => ?_
    by_cases hx : chartSchemeToPoints B S hS X.1 A x ∈ T
    · obtain ⟨k, hkF, w, hw⟩ := hF A x hx
      exact ⟨_, SmallEtale.prodFst B S hS X.1 A (V k),
        (Sieve.mem_ofObjects_iff _ _).2 ⟨Sum.inl ⟨⟨k, hkF⟩, A⟩, ⟨𝟙 _⟩⟩, w, hw⟩
    · obtain ⟨k, y, hy⟩ := exists_openChart_point_of_notMem B S hS X hV T hTcl _ hx
      obtain ⟨w, hw⟩ := exists_prodFst_eq B S hS X A (Vc k) x y hy.symm
      exact ⟨_, SmallEtale.prodFst B S hS X.1 A (Vc k),
        (Sieve.mem_ofObjects_iff _ _).2 ⟨Sum.inr ⟨k, A⟩, ⟨𝟙 _⟩⟩, w, hw⟩
  · match i with
    | Sum.inl ⟨k, A⟩ => exact ⟨SmallEtale.prodSnd B S hS X.1 A (V k.1)⟩
    | Sum.inr ⟨k, A⟩ => exact ⟨SmallEtale.prodSnd B S hS X.1 A (Vc k) ≫
        openChartInclusion B S hS X.1 (V k) (chartComplOpens B S hS X (V k) T hTcl)⟩
  · match i with
    | Sum.inl ⟨k, _⟩ => exact Or.inl k.2
    | Sum.inr ⟨k, A⟩ => exact Or.inr (hout k A)
  · obtain ⟨k, y, hy⟩ := exists_openChart_point_of_notMem B S hS X hV T hTcl x hx
    obtain ⟨w, hw⟩ := exists_prodFst_eq B S hS X (Vc k) (Vc k) y y rfl
    refine ⟨Sum.inr ⟨k, Vc k⟩, w, hout k (Vc k), ?_⟩
    show chartSchemeToPoints B S hS X.1 (SmallEtale.prodObj B S hS X.1 (Vc k) (Vc k)) w = x
    rw [← chartSchemeToPoints_map B S hS X.1 (SmallEtale.prodFst B S hS X.1 (Vc k) (Vc k)), hw, hy]

end AlgebraicGeometry.Space

end
