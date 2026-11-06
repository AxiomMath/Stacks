module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Extending a relative-dimension bound from a dense open subspace

A flat morphism of algebraic spaces over `S` locally of finite type has relative dimension at most
`d` as soon as its restriction over a dense open subspace of the target does, provided the
morphism is locally of finite presentation or the open immersion is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.relativeDimensionLE_of_dense_open` is **Stacks 0878**.
* `AlgebraicGeometry.Space.exists_chartOpen_dense_of_isOpenSubspace` transports a dense open
  subspace of the target to a dense open subset of a chart of it.
* `AlgebraicGeometry.Space.isRetrocompact_chartOpen_of_isQuasiCompact` transports
  quasi-compactness of the open immersion to retrocompactness of that open subset.

## Implementation notes

The statement is pointwise, so it is tested on one pointed étale chart at the given point of the
source (Stacks 04RE), where it becomes the corresponding statement for schemes, Stacks 081L. What
has to be transported to the chart is the open subspace and its two hypotheses.

The open subspace corresponds to an open subset of the points of the target (Stacks 03BZ), and the
point topology of a represented presheaf is the topology of the representing scheme (Stacks 03BX);
so the preimage of that open subset under the target chart is cut out by an open subset `W` of the
representing scheme. Density transports because the chart is étale, hence open on points.

The relative-dimension bound transports point by point: a point of the fibre product of the chart
with `W` determines a point of the source lying over a point of the open subspace, which by Stacks
03H4 lifts to the restriction of the morphism over the open subspace, where the bound applies;
part (1) of Stacks 04NS carries the bound back, and Stacks 04NL reads it on the chart as a bound
on the local dimension of a fibre.

Quasi-compactness of the open immersion transports as retrocompactness of `W`: for a compact open
`K` of the chart, the intersection `W ∩ K` is the image of the points of the fibre product of the
open subspace with the restriction of the chart to `K`, which is a quasi-compact algebraic space
and so has compact point space (Stacks 03E4). Both inclusions of that description are Stacks 03H4.

## References

* [Stacks Project, Tag 0878](https://stacks.math.columbia.edu/tag/0878)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Composing a morphism of schemes with an injective one does not change the local dimension of
the fibre through a point: the two set-theoretic fibres through that point coincide. -/
private lemma topologicalKrullDimAt_fiber_comp_of_injective {X V W : Scheme.{u}}
    (g : X ⟶ V) (k : V ⟶ W) (hk : Function.Injective k) (x : X) :
    topologicalKrullDimAt ((g ≫ k).fiber ((g ≫ k) x)) ((g ≫ k).asFiber x) =
      topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) := by
  have hAB : (g ≫ k) ⁻¹' {(g ≫ k) x} = g ⁻¹' {g x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
    exact hk.eq_iff
  rw [topologicalKrullDimAt_eq_of_homeomorph ((g ≫ k).fiberHomeo _) _,
    topologicalKrullDimAt_eq_of_homeomorph (g.fiberHomeo _) _]
  have hpA : ((g ≫ k).fiberHomeo _) ((g ≫ k).asFiber x) =
      (⟨x, by simp⟩ : ((g ≫ k) ⁻¹' {(g ≫ k) x})) := by
    ext
    exact (g ≫ k).fiberι_asFiber x
  have hpB : (g.fiberHomeo _) (g.asFiber x) = (⟨x, by simp⟩ : (g ⁻¹' {g x})) := by
    ext
    exact g.fiberι_asFiber x
  rw [hpA, hpB, topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hAB)]
  rfl

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_relativeDimensionDenseOpen
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Transporting the open subspace to a chart -/

/-- The points of an open subspace form an open subset of the points of the ambient algebraic
space: this is the content of the order isomorphism of Stacks 03BZ. -/
theorem isOpen_range_pointsMap_ι_of_isOpenSubspace (hY : IsAlgebraicSpace B S hS Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) :
    IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
  openSubspacesOrderIso_apply B S hS Y hY ⟨V, hV⟩ ▸
    (openSubspacesOrderIso B S hS Y hY ⟨V, hV⟩).2

/-- The preimage of an open subspace of the target under a chart of it is cut out by an open
subset of the representing scheme: the preimage is open in the points of the chart, and on a
represented presheaf the point topology is the topology of the representing scheme. -/
theorem exists_chartOpen_of_isOpenSubspace (hY : IsAlgebraicSpace B S hS Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) (U : BigFppfOver B S hS)
    (b : yoneda.obj U ⟶ Y) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) b (p.class B S hS (yoneda.obj U)) ∈
            Set.range (pointsMap B S hS V.toFunctor V.ι) ↔
          schemePoint B S hS U p ∈ W := by
  obtain ⟨W, hW, hmem⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS U _).mp
    ((continuous_pointsMap B S hS b).isOpen_preimage _
      (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY V hV))
  exact ⟨⟨W, hW⟩, hmem⟩

/-- The open subset of a chart cutting out a dense open subspace of the target is dense: the chart
is étale, hence open on points, and the preimage of a dense set under an open map is dense. -/
theorem exists_chartOpen_dense_of_isOpenSubspace (hY : IsAlgebraicSpace B S hS Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)))
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ Y)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      (∀ p : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) b (p.class B S hS (yoneda.obj U)) ∈
            Set.range (pointsMap B S hS V.toFunctor V.ι) ↔
          schemePoint B S hS U p ∈ W) ∧
        Dense (W : Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  obtain ⟨W, hmem⟩ := exists_chartOpen_of_isOpenSubspace B S hS hY V hV U b
  refine ⟨W, hmem, ?_⟩
  have hA : Dense (pointsMap B S hS (yoneda.obj U) b ⁻¹'
      Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    hVdense.preimage (isOpenMap_pointsMap_of_etale B S hS hY U b hb)
  rw [dense_iff_inter_open]
  intro C hC hCne
  have hEopen : IsOpen (pointsToScheme B S hS U ⁻¹' C) :=
    (isOpen_yoneda_iff_isSchemeOpen B S hS U _).mpr
      ((isSchemeOpen_iff_exists_preimage B S hS U _).mpr ⟨C, hC, rfl⟩)
  have hEne : (pointsToScheme B S hS U ⁻¹' C).Nonempty := by
    obtain ⟨x, hx⟩ := hCne
    refine ⟨(schemePointRepresentative B S hS U x).class B S hS (yoneda.obj U), ?_⟩
    show schemePoint B S hS U (schemePointRepresentative B S hS U x) ∈ C
    rwa [schemePointRepresentative_point]
  obtain ⟨z, hzE, hzA⟩ := (dense_iff_inter_open.mp hA) _ hEopen hEne
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  exact ⟨schemePoint B S hS U p, hzE, (hmem p).mp hzA⟩

/-! ### Transporting quasi-compactness of the open immersion to a chart -/

/-- A point of a chart's source mapping into the open subset `W` of the target chart gives a
point of the open subspace with the same image in `Y`. -/
private theorem exists_pointsMap_eq_of_map_mem_chartOpen {Z : BigFppfOver B S hS}
    {b : yoneda.obj Z ⟶ Y} {V : Subfunctor Y} {W : ((BigFppfOver.toScheme B S hS).obj Z).Opens}
    (hW : ∀ p : FieldValuedPoint B S hS (yoneda.obj Z),
      pointsMap B S hS (yoneda.obj Z) b (p.class B S hS (yoneda.obj Z)) ∈
          Set.range (pointsMap B S hS V.toFunctor V.ι) ↔
        schemePoint B S hS Z p ∈ W)
    {U : BigFppfOver B S hS} (h : U ⟶ Z) (y : (BigFppfOver.toScheme B S hS).obj U)
    (hy : (BigFppfOver.toScheme B S hS).map h y ∈ W) :
    ∃ yV, pointsMap B S hS (yoneda.obj U) (yoneda.map h ≫ b)
        ((schemePointRepresentative B S hS U y).class B S hS (yoneda.obj U)) =
      pointsMap B S hS V.toFunctor V.ι yV := by
  obtain ⟨yV, hyV⟩ := (hW (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map h)
    (schemePointRepresentative B S hS U y))).mpr
    (by rw [schemePoint_map_yoneda, schemePointRepresentative_point]; exact hy)
  exact ⟨yV, by rw [pointsMap_comp_apply, pointsMap_class]; exact hyV.symm⟩

/-- The open subset of a chart cutting out an open subspace whose immersion is quasi-compact is
retrocompact.

For a compact open `K` of the chart, let `UO` be the object of the site given by `K`. The
intersection `W ∩ K` is the image, under the first projection on points followed by the comparison
bijection with scheme points and the inclusion of `K`, of the points of the fibre product of the
open subspace with `yoneda.obj UO`; both inclusions are Stacks 03H4. That fibre product is a
quasi-compact algebraic space, so its points form a compact space (Stacks 03E4), and a continuous
image of a compact space is compact. -/
@[ega "IV 8.6.1" "partial"]
theorem isRetrocompact_chartOpen_of_isQuasiCompact (hY : IsAlgebraicSpace B S hS Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hqc : IsQuasiCompact B S hS V.ι) (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ Y)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hW : ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) b (p.class B S hS (yoneda.obj U)) ∈
          Set.range (pointsMap B S hS V.toFunctor V.ι) ↔
        schemePoint B S hS U p ∈ W) :
    IsRetrocompact (W : Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  classical
  intro K hKcompact hKopen
  have hjmap : (BigFppfOver.toScheme B S hS).map
      (openSiteObjectHom B S hS U ⟨K, hKopen⟩) =
      Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj U) ⟨K, hKopen⟩ :=
    map_openSiteObjectHom B S hS U ⟨K, hKopen⟩
  have hrangeK : Set.range ((BigFppfOver.toScheme B S hS).map
      (openSiteObjectHom B S hS U ⟨K, hKopen⟩)) = K := by
    rw [hjmap]
    exact Scheme.Opens.range_ι _
  have hUOspace := isAlgebraicSpace_yoneda B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
  have hOcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (openSiteObject B S hS U ⟨K, hKopen⟩)) := isCompact_iff_compactSpace.mp hKcompact
  have hPspace : IsAlgebraicSpace B S hS
      (pullback (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) :=
    isAlgebraicSpace_pullback B S hS _ V.ι hUOspace hV.1 hY
  have hPcompact : CompactSpace (points B S hS
      (pullback (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hPspace).mp
      (hqc (yoneda.obj (openSiteObject B S hS U ⟨K, hKopen⟩)) hUOspace
        (isQuasiCompactSpace_yoneda_obj B S hS hOcompact) _)
  have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) :
      (⟨yoneda.obj (openSiteObject B S hS U ⟨K, hKopen⟩), hUOspace⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk V.ι :
      (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
  have hcont : Continuous (fun w : points B S hS
      (pullback (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) ↦
      (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS U ⟨K, hKopen⟩)
        (pointsToScheme B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
          (pointsMap B S hS _ (pullback.fst
            (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) w))) :=
    ((BigFppfOver.toScheme B S hS).map
        (openSiteObjectHom B S hS U ⟨K, hKopen⟩)).continuous.comp
      ((schemePointsHomeomorph B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)).continuous.comp
        (continuous_pointsMap B S hS (pullback.fst
          (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι)))
  have hkey : ∀ pw : FieldValuedPoint B S hS
      (pullback (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι),
      (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS U ⟨K, hKopen⟩)
          (schemePoint B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
            (FieldValuedPoint.map B S hS _ (pullback.fst
              (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) pw)) ∈
        (W : Set ((BigFppfOver.toScheme B S hS).obj U)) ∩ K := by
    intro pw
    refine ⟨?_, ?_⟩
    · rw [← schemePoint_map_yoneda]
      refine (hW _).mp ⟨(FieldValuedPoint.map B S hS _ (pullback.snd
        (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) pw).class
          B S hS V.toFunctor, ?_⟩
      rw [← pointsMap_class, ← pointsMap_class, ← pointsMap_comp_apply, ← pointsMap_class]
      exact (pointsMap_apply_comm B S hS
        (pullback.condition
          (f := yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) (g := V.ι))
        (pw.class B S hS _)).symm
    · exact hrangeK.subset ⟨_, rfl⟩
  have hrange : (W : Set ((BigFppfOver.toScheme B S hS).obj U)) ∩ K =
      Set.range (fun w : points B S hS
        (pullback (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) ↦
        (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS U ⟨K, hKopen⟩)
          (pointsToScheme B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
            (pointsMap B S hS _ (pullback.fst
              (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) w))) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨hxW, hxK⟩
      obtain ⟨y, hxO⟩ : x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
          (openSiteObjectHom B S hS U ⟨K, hKopen⟩)) := by
        rw [hrangeK]
        exact hxK
      obtain ⟨yV, hcompat⟩ := exists_pointsMap_eq_of_map_mem_chartOpen B S hS hW
        (openSiteObjectHom B S hS U ⟨K, hKopen⟩) y (hxO ▸ hxW)
      obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS hsq _ yV hcompat
      refine ⟨w, ?_⟩
      have hw' : pointsMap B S hS
          (pullback (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι)
          (pullback.fst (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) w =
          (schemePointRepresentative B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
            y).class B S hS _ := hw
      have hsp : pointsToScheme B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
          ((schemePointRepresentative B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
            y).class B S hS _) = y :=
        schemePointRepresentative_point B S hS _ y
      show (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS U ⟨K, hKopen⟩)
        (pointsToScheme B S hS (openSiteObject B S hS U ⟨K, hKopen⟩)
          (pointsMap B S hS _ (pullback.fst
            (yoneda.map (openSiteObjectHom B S hS U ⟨K, hKopen⟩) ≫ b) V.ι) w)) = x
      rw [hw', hsp]
      exact hxO
    · rintro x ⟨w, rfl⟩
      obtain ⟨pw, rfl⟩ := Quot.exists_rep w
      exact hkey pw
  rw [hrange]
  exact isCompact_range hcont

/-! ### Transporting the bound to a chart -/

/-- The relative-dimension bound over the dense open subspace, read on a pointed étale chart: at
every point of the fibre product of the chart morphism with `W` the local dimension of the fibre of
the chart morphism is a natural number at most `d`.

A point of that fibre product determines a point of the source lying over a point of the open
subspace, so Stacks 03H4 lifts it to the restriction of the morphism over the open subspace, where
the bound holds; part (1) of Stacks 04NS carries it back, and Stacks 04NL reads it on the chart. -/
private theorem exists_chart_fiberDimension_le (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) (hlft : IsLocallyOfFiniteType B S hS f) (d : ℕ)
    (hdim : HasRelativeDimensionLE d B S hS (pullback.snd f V.ι))
    {U Z : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (b : yoneda.obj Z ⟶ Y) (h : U ⟶ Z)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    {W : ((BigFppfOver.toScheme B S hS).obj Z).Opens}
    (hW : ∀ p : FieldValuedPoint B S hS (yoneda.obj Z),
      pointsMap B S hS (yoneda.obj Z) b (p.class B S hS (yoneda.obj Z)) ∈
          Set.range (pointsMap B S hS V.toFunctor V.ι) ↔
        schemePoint B S hS Z p ∈ W)
    (q : ↥(pullback ((BigFppfOver.toScheme B S hS).map h) W.ι)) :
    ∃ e : ℕ, e ≤ d ∧
      topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map h).fiber
            (((BigFppfOver.toScheme B S hS).map h)
              (pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q)))
          (((BigFppfOver.toScheme B S hS).map h).asFiber
            (pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q)) =
        (e : WithBot ℕ∞) := by
  classical
  have hq' : ((BigFppfOver.toScheme B S hS).map h)
      (pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q) =
      W.ι (pullback.snd ((BigFppfOver.toScheme B S hS).map h) W.ι q) := by
    simpa using congrArg
      (fun k : pullback ((BigFppfOver.toScheme B S hS).map h) W.ι ⟶
        (BigFppfOver.toScheme B S hS).obj Z ↦ k q)
      (pullback.condition (f := (BigFppfOver.toScheme B S hS).map h) (g := W.ι))
  obtain ⟨yV, hyV⟩ := exists_pointsMap_eq_of_map_mem_chartOpen B S hS hW h _
    (by rw [hq']; exact (pullback.snd ((BigFppfOver.toScheme B S hS).map h) W.ι q).2)
  have hcompat : pointsMap B S hS X f
      (pointsMap B S hS (yoneda.obj U) a
        ((schemePointRepresentative B S hS U
          (pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q)).class
            B S hS (yoneda.obj U))) =
      pointsMap B S hS V.toFunctor V.ι yV := by
    rw [← pointsMap_comp_apply, ← hcomm]
    exact hyV
  obtain ⟨xV, hxV, -⟩ := exists_point_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk V.ι :
        (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩))
    _ yV hcompat
  obtain ⟨e, he, hdimAtV⟩ := hdim xV
  have hdimAtX : HasRelativeDimensionAt (e : ℕ∞) B S hS f
      (pointsMap B S hS (yoneda.obj U) a
        ((schemePointRepresentative B S hS U
          (pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q)).class
            B S hS (yoneda.obj U))) := by
    rw [← hxV]
    exact (hasRelativeDimensionAt_iff_of_isPullback B S hS
      (IsPullback.of_hasPullback f V.ι) hX hV.1 hY hlft xV (e : ℕ∞)).2 hdimAtV
  refine ⟨e, he, ?_⟩
  let c : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a
        ((schemePointRepresentative B S hS U
          (pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q)).class
            B S hS (yoneda.obj U))) :=
    { U := U
      V := Z
      a := a
      b := b
      h := h
      a_etale := ha
      b_etale := hb
      comm := hcomm
      representative := schemePointRepresentative B S hS U
        (pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q)
      point := IsLocalRing.closedPoint _
      maps_to := rfl }
  have hsrc : c.sourcePoint B S hS =
      pullback.fst ((BigFppfOver.toScheme B S hS).map h) W.ι q :=
    schemePointRepresentative_point B S hS U _
  have hchart := (AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) (e : ℕ∞)).mp (hdimAtX c)
  rw [hsrc] at hchart
  exact hchart

/-! ### The theorem -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0878.** A flat morphism of algebraic spaces over `S` locally of finite type has
relative dimension at most `d` if its restriction over a dense open subspace of the target does,
provided the morphism is locally of finite presentation or the open immersion is quasi-compact. -/
@[stacks 0878]
theorem relativeDimensionLE_of_dense_open (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V)
    (hVdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)))
    (hflat : IsFlat B S hS f) (hlft : IsLocallyOfFiniteType B S hS f) (d : ℕ)
    (hdim : HasRelativeDimensionLE d B S hS (pullback.snd f V.ι))
    (hfin : IsLocallyOfFinitePresentation B S hS f ∨ IsQuasiCompact B S hS V.ι) :
    HasRelativeDimensionLE d B S hS f := by
  classical
  intro x
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hX hY f x
  obtain ⟨W, hW, hWdense⟩ :=
    exists_chartOpen_dense_of_isOpenSubspace B S hS hY V hV hVdense c.V c.b c.b_etale
  have hflatChart : Flat ((BigFppfOver.toScheme B S hS).map c.h) :=
    hflat c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  have hlftChart : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
    hlft c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  have hdimW : RelativeDimensionLE
      (pullback.snd ((BigFppfOver.toScheme B S hS).map c.h) W.ι) d := by
    intro q
    obtain ⟨e, he, heq⟩ := exists_chart_fiberDimension_le B S hS hX hY f V hV hlft d hdim
      c.a c.b c.h c.a_etale c.b_etale c.comm hW q
    rw [relativeDimensionLEAt_iff]
    have hrestrict : topologicalKrullDimAt
          ((pullback.snd ((BigFppfOver.toScheme B S hS).map c.h) W.ι).fiber
            ((pullback.snd ((BigFppfOver.toScheme B S hS).map c.h) W.ι) q))
          ((pullback.snd ((BigFppfOver.toScheme B S hS).map c.h) W.ι).asFiber q) =
        topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map c.h).fiber
            (((BigFppfOver.toScheme B S hS).map c.h)
              (pullback.fst ((BigFppfOver.toScheme B S hS).map c.h) W.ι q)))
          (((BigFppfOver.toScheme B S hS).map c.h).asFiber
            (pullback.fst ((BigFppfOver.toScheme B S hS).map c.h) W.ι q)) := by
      rw [← AlgebraicGeometry.topologicalKrullDimAt_fiber_comp_of_injective
          (pullback.snd ((BigFppfOver.toScheme B S hS).map c.h) W.ι) W.ι
          W.ι.isOpenEmbedding.injective q,
        ← pullback.condition (f := (BigFppfOver.toScheme B S hS).map c.h) (g := W.ι)]
      exact AlgebraicGeometry.fiberDimensionAt_comp_openImmersion
        (pullback.fst ((BigFppfOver.toScheme B S hS).map c.h) W.ι)
        ((BigFppfOver.toScheme B S hS).map c.h) q
    rw [hrestrict, heq]
    exact WithBot.coe_le_coe.mpr (by exact_mod_cast he)
  have hfinChart : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map c.h) ∨
      IsRetrocompact (W : Set ((BigFppfOver.toScheme B S hS).obj c.V)) := by
    rcases hfin with hfp | hqc
    · exact Or.inl (hfp c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm)
    · exact Or.inr (isRetrocompact_chartOpen_of_isQuasiCompact B S hS hY V hV hqc
        c.V c.b W hW)
  have hschemeLE := AlgebraicGeometry.relativeDimensionLE_of_dense_open
    ((BigFppfOver.toScheme B S hS).map c.h) W hWdense d hdimW hfinChart
  have hdimLE := (relativeDimensionLEAt_iff ((BigFppfOver.toScheme B S hS).map c.h) d
    (c.sourcePoint B S hS)).mp (hschemeLE (c.sourcePoint B S hS))
  have hne := topologicalKrullDimAt_ne_bot
    (((BigFppfOver.toScheme B S hS).map c.h).asFiber (c.sourcePoint B S hS))
  obtain ⟨e, hde, hed⟩ : ∃ e : ℕ,
      topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map c.h).fiber
            (((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)))
          (((BigFppfOver.toScheme B S hS).map c.h).asFiber (c.sourcePoint B S hS)) =
        (e : WithBot ℕ∞) ∧ e ≤ d := by
    cases hval : topologicalKrullDimAt
        (((BigFppfOver.toScheme B S hS).map c.h).fiber
          (((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)))
        (((BigFppfOver.toScheme B S hS).map c.h).asFiber (c.sourcePoint B S hS)) with
    | bot => exact absurd hval hne
    | coe r =>
      cases r with
      | top =>
        rw [hval] at hdimLE
        exact absurd (WithBot.coe_le_coe.mp hdimLE) (by simp)
      | coe m =>
        refine ⟨m, rfl, ?_⟩
        rw [hval] at hdimLE
        exact_mod_cast WithBot.coe_le_coe.mp hdimLE
  refine ⟨e, hed, ?_⟩
  refine (holdsOnEveryEtaleChartAtPoint_iff_some B S hS
    (@AlgebraicGeometry.HasFiberDimensionAt.{u} (e : ℕ∞))
    (AlgebraicGeometry.fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞))
    hX hY f x).mpr ⟨c, ?_⟩
  exact (AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) (e : ℕ∞)).mpr hde

end Space

end AlgebraicGeometry

end
