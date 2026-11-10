module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartDiagramsOfModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapFinitePresentationClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSectionsConverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank loci of a finite locally free module on an algebraic space

Let `M` be a finite locally free `𝒪_Y`-module on the small étale site of an algebraic space `Y`.
For `n : ℕ` its *rank locus* is the set of points of `|Y|` around which `M` is a coproduct of `n`
copies of the structure sheaf. The rank loci are open, pairwise disjoint and cover `|Y|`; and
for a morphism `f : X ⟶ Y` of algebraic spaces the pullback `f^*M` is finite locally free of
rank `n` (the rank clause of Stacks 0409) exactly when `|f|` maps into the rank locus of `n`.
This is the statement that the rank of a finite locally free module is a locally constant
function whose formation commutes with arbitrary base change.

## Main definitions

* `AlgebraicGeometry.Space.IsFreeOfRankOn`: the restriction of `M` to the slice at an étale
  chart `V` is a coproduct of `n` copies of the structure sheaf.
* `AlgebraicGeometry.Space.rankLocus`: the points of `|Y|` in the image of an étale chart on
  which `M` is free of rank `n`.

## Main results

* `AlgebraicGeometry.Space.isOpen_rankLocus`: the rank loci are open.
* `AlgebraicGeometry.Space.eq_of_mem_rankLocus_of_mem_rankLocus`: they are pairwise disjoint.
* `AlgebraicGeometry.Space.exists_mem_rankLocus`: those of a finite locally free module cover.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_iff`: for `M` finite locally
  free and `f : X ⟶ Y`, `f^*M` is finite locally free of rank `n` exactly when `|f|` maps into
  the rank locus of `n`.

## Implementation notes

The rank is read on sections. Over a chart `W` lying over a chart where the module is a
coproduct of `n` copies of the structure sheaf, its sections are free of rank `n` over
`𝒪(W)` (`AlgebraicGeometry.RingedSite.nonempty_basis_sections_of_isColimitCofanUnit`), and when
`W` is nonempty the ring `𝒪(W)` is nonzero, so `n` is determined. Across `f`, the sections of
`f^*M` over an affine chart of `X` are the base change of the sections of `M` over an affine chart
of `Y` below it
(`AlgebraicGeometry.Space.isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite`), a finite
locally free module being quasi-coherent; so ranks are compared on an affine chart diagram through
a point, supplied by `AlgebraicGeometry.Space.exists_hasAffineChartDiagramWith_onRange`. No local
form of the pullback of modules is used. For the converse direction the pullback, which is
quasi-coherent, is shown to be of rank `n` through the chartwise reading of the rank
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_freeRankPresieve`, the rank form of Descent,
Proposition 03DX (2)): around every point of a chart of `X` there is an affine chart over which the
sections of `f^*M` are a base change of a free module of rank `n`.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- **`M` is free of rank `n` on the étale chart `V`**: the restriction of `M` to the slice of the
small étale site at `V` is a coproduct of `n` copies of the structure sheaf of that slice. -/
def IsFreeOfRankOn (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (n : ℕ) : Prop :=
  ∃ ι : ∀ _ : Fin n, SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V) ⟶
        M.over V,
    Nonempty (IsColimit (Cofan.mk (M.over V) ι))

/-- **The rank locus of `n`**: the points of `|Y|` in the image of an étale chart on which `M` is
free of rank `n`. -/
def rankLocus (M : Modules.{u, u} B S hS Y.1 Y.2) (n : ℕ) : Set (points B S hS Y.1) :=
  ⋃ V ∈ {V : SmallEtale B S hS Y.1 | IsFreeOfRankOn M V n},
    Set.range (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V)) V.1.hom)

/-- A point `y` of `|Y|` lies in the rank locus of `n` exactly when it is the image of a point of
an étale chart `V` on which `M` is free of rank `n`. -/
theorem mem_rankLocus_iff (M : Modules.{u, u} B S hS Y.1 Y.2) (n : ℕ) (y : points B S hS Y.1) :
    y ∈ rankLocus M n ↔ ∃ (V : SmallEtale B S hS Y.1) (v : chartScheme V),
      IsFreeOfRankOn M V n ∧ chartSchemeToPoints B S hS Y.1 V v = y := by
  simp only [rankLocus, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨V, hV, hy⟩
    obtain ⟨v, hv⟩ := exists_chartSchemeToPoints_eq_of_mem_range B S hS V hy
    exact ⟨V, v, hV, hv⟩
  · rintro ⟨V, v, hV, rfl⟩
    exact ⟨V, hV, chartSchemeToPoints_mem_range B S hS V v⟩

/-- **The rank loci are open**: each is a union of images of étale charts, which are open by
Stacks 03IR. -/
theorem isOpen_rankLocus (M : Modules.{u, u} B S hS Y.1 Y.2) (n : ℕ) : IsOpen (rankLocus M n) :=
  isOpen_biUnion fun V _ =>
    isOpen_range_pointsMap_of_isEtale B S hS V.1.hom
      (isAlgebraicSpace_yoneda B S hS _) Y.2 (isEtale_hom_of_isEtaleChart B S hS V.2)

/-- Over a chart lying over one on which `M` is free of rank `n`, the sections of `M` are free of
rank `n` over the ring of sections of the structure sheaf. -/
theorem IsFreeOfRankOn.nonempty_basis {M : Modules.{u, u} B S hS Y.1 Y.2}
    {V : SmallEtale B S hS Y.1} {n : ℕ} (h : IsFreeOfRankOn M V n) {W : SmallEtale B S hS Y.1}
    (m : W ⟶ V) :
    Nonempty (Module.Basis (Fin n) (chartRing B S hS Y.1 Y.2 W) (M.val.obj (op W))) := by
  obtain ⟨ι, ⟨hι⟩⟩ := h
  exact RingedSite.nonempty_basis_sections_of_isColimitCofanUnit
    (smallEtaleRingedSite B S hS Y.1 Y.2) M n V ι hι m

/-- The ring of sections of the structure sheaf over a chart with a point is nonzero. -/
theorem nontrivial_chartRing_of_point {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (W : SmallEtale B S hS F) (w : chartScheme W) :
    Nontrivial (chartRing B S hS F hF W) :=
  ((chartScheme W).presheaf.germ ⊤ w trivial).hom.domain_nontrivial

/-- **The rank of a free module is determined on a chart with a point.** -/
theorem eq_of_basis_of_basis {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (W : SmallEtale B S hS F) (w : chartScheme W)
    {N : Type u} [AddCommGroup N] [Module (chartRing B S hS F hF W) N] {n m : ℕ}
    (b : Module.Basis (Fin n) (chartRing B S hS F hF W) N)
    (b' : Module.Basis (Fin m) (chartRing B S hS F hF W) N) : n = m := by
  have := nontrivial_chartRing_of_point hF W w
  simpa using (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis b')

/-- **The rank loci are pairwise disjoint.** Two charts on which `M` is free, with points over
one point of `|Y|`, have a common refinement through a point over both
(`AlgebraicGeometry.Space.exists_affine_common_chart_point`); over it the sections of `M` are free
of both ranks. -/
theorem eq_of_mem_rankLocus_of_mem_rankLocus {M : Modules.{u, u} B S hS Y.1 Y.2} {n m : ℕ}
    {y : points B S hS Y.1} (hn : y ∈ rankLocus M n) (hm : y ∈ rankLocus M m) : n = m := by
  obtain ⟨U, u, hU, rfl⟩ := (mem_rankLocus_iff M n y).mp hn
  obtain ⟨V, v, hV, hv⟩ := (mem_rankLocus_iff M m _).mp hm
  obtain ⟨W, a, b, w, -, -, -⟩ := exists_affine_common_chart_point B S hS U V u v hv.symm
  obtain ⟨β⟩ := hU.nonempty_basis a
  obtain ⟨β'⟩ := hV.nonempty_basis b
  exact eq_of_basis_of_basis Y.2 W w β β'

/-- A point of a chart lies, as a point of the space, under a point of one of the charts of a
covering family. -/
private theorem exists_chartSchemeToPoints_eq_of_ofArrows
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : SmallEtale B S hS F} {I : Type*}
    {V : I → SmallEtale B S hS F} {g : ∀ i, V i ⟶ U}
    (hcov : Sieve.ofArrows V g ∈ SmallEtale.topology B S hS F U) (u : chartScheme U) :
    ∃ (i : I) (v : chartScheme (V i)),
      chartSchemeToPoints B S hS F (V i) v = chartSchemeToPoints B S hS F U u := by
  obtain ⟨Z, g', hg', z', hz'⟩ := exists_mem_sieve_scheme_point B S hS F U hcov u
  obtain ⟨T, h, t, ⟨i⟩, rfl⟩ := hg'
  refine ⟨i, (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map h) z', ?_⟩
  rw [← hz']
  exact (chartSchemeToPoints_map B S hS _ h z').trans
    (chartSchemeToPoints_map B S hS _ (h ≫ g i) z').symm

/-- **The rank loci of a finite locally free module cover `|Y|`.** -/
theorem exists_mem_rankLocus {M : Modules.{u, u} B S hS Y.1 Y.2}
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) (y : points B S hS Y.1) :
    ∃ n : ℕ, y ∈ rankLocus M n := by
  obtain ⟨U, u, rfl⟩ := exists_chartSchemeToPoints_eq B S hS Y y
  obtain ⟨I, V, g, hcov, hfree⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit M).mp hM U
  obtain ⟨i, v, hv⟩ := exists_chartSchemeToPoints_eq_of_ofArrows hcov u
  obtain ⟨n, ι, hι⟩ := hfree i
  exact ⟨n, (mem_rankLocus_iff M n _).mpr ⟨V i, v, ⟨ι, hι⟩, hv⟩⟩

/-- A diagram of étale charts over `f` carries the point of `|X|` determined by a point of its
chart of `X` to the point of `|Y|` determined by the image of that point in its chart of `Y`. -/
theorem pointsMap_chartSchemeToPoints_of_chartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (x : chartScheme d.U) :
    pointsMap B S hS X.1 f.hom (chartSchemeToPoints B S hS X.1 d.U x) =
      chartSchemeToPoints B S hS Y.1 d.V ((BigFppfOver.toScheme B S hS).map d.g x) := by
  rw [pointsMap_chartSchemeToPoints, d.comm, pointsMap_comp, Function.comp_apply,
    pointsMap_yoneda_map_class_canonicalSiteFieldPoint, chartSchemeToPoints_eq_pointsMap]

/-- Around every point of an étale chart `U` of `X` there is an affine chart `W` over `U` on which
the sections of `f^*M` are free of a rank `m`, the one of `M` at the image point.

An affine chart diagram over `f` through the point, whose chart of `Y` lies over a chart where `M`
is free, is supplied by `AlgebraicGeometry.Space.exists_hasAffineChartDiagramWith_onRange`; over
it the sections of `f^*M` are the base change of those of `M`. -/
private theorem exists_affine_chart_basis_modulePullback (f : X ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (U : SmallEtale B S hS X.1) (z : chartScheme U) :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U) (z' : chartScheme W) (m : ℕ),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) ∧
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) z' = z ∧
      Nonempty (Module.Basis (Fin m) (chartRing B S hS X.1 X.2 W)
        (((modulePullback B S hS f).obj M).val.obj (op W))) ∧
      pointsMap B S hS X.1 f.hom (chartSchemeToPoints B S hS X.1 W z') ∈ rankLocus M m := by
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hM
  let P : SmallEtale B S hS Y.1 → Prop := fun V =>
    ∃ (A : SmallEtale B S hS Y.1) (_ : V ⟶ A) (m : ℕ), IsFreeOfRankOn M A m
  have hPhom : ∀ {V V' : SmallEtale B S hS Y.1}, (V' ⟶ V) → P V → P V' := by
    rintro V V' a ⟨A, c, m, hA⟩
    exact ⟨A, a ≫ c, m, hA⟩
  have hPcov : ∀ y : points B S hS Y.1, y ∈ Set.range (pointsMap B S hS X.1 f.hom) →
      ∃ V : SmallEtale B S hS Y.1, P V ∧
        y ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V)) V.1.hom) := by
    intro y _
    obtain ⟨m, hm⟩ := exists_mem_rankLocus hM y
    obtain ⟨V, v, hV, rfl⟩ := (mem_rankLocus_iff M m y).mp hm
    exact ⟨V, ⟨V, 𝟙 V, m, hV⟩, chartSchemeToPoints_mem_range B S hS V v⟩
  obtain ⟨W, a, ⟨hWaff, V, q, hq, hVaff, A, c, m, hA⟩, z', hz'⟩ :=
    exists_hasAffineChartDiagramWith_onRange B S hS P f hPhom hPcov U z
  let d : ChartDiagram B S hS X.1 Y.1 f.hom :=
    { U := W
      V := V
      g := q
      comm := hq.symm }
  obtain ⟨e⟩ := isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite B S hS f M
    inferInstance d hWaff hVaff
  let := chartDiagramAlgebra B S hS f d
  obtain ⟨βV⟩ := hA.nonempty_basis c
  refine ⟨W, a, z', m, hWaff, hz', ⟨(βV.baseChange (chartRing B S hS X.1 X.2 W)).map e⟩, ?_⟩
  rw [pointsMap_chartSchemeToPoints_of_chartDiagram f d z']
  exact (mem_rankLocus_iff M m _).mpr ⟨A, _, hA, chartSchemeToPoints_map B S hS Y.1 c _⟩

/-- **The rank of `f^*M` at a point is the rank of `M` at its image.** If `f^*M` is free of rank
`k` on an étale chart `Z` of `X`, then every point of `Z` maps into the rank locus of `k` of `M`. -/
theorem mem_rankLocus_of_isFreeOfRankOn_modulePullback (f : X ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    {Z : SmallEtale B S hS X.1} {k : ℕ}
    (hZ : IsFreeOfRankOn ((modulePullback B S hS f).obj M) Z k) (z : chartScheme Z) :
    pointsMap B S hS X.1 f.hom (chartSchemeToPoints B S hS X.1 Z z) ∈ rankLocus M k := by
  obtain ⟨W, a, z', m, -, hz', ⟨β⟩, hmem⟩ := exists_affine_chart_basis_modulePullback f hM Z z
  obtain ⟨βW⟩ := hZ.nonempty_basis a
  obtain rfl : k = m := eq_of_basis_of_basis X.2 W z' βW β
  rwa [← hz', chartSchemeToPoints_map]

/-- **The rank of a pullback of a finite locally free module, read on points.** For a finite
locally free `𝒪_Y`-module `M` and a morphism `f : X ⟶ Y` of algebraic spaces, `f^*M` is finite
locally free of rank `n` (the rank clause of Stacks 0409) exactly when `|f|` maps `|X|` into the
rank locus of `n` of `M`.

So the rank of a finite locally free module is a locally constant function on `|Y|`
(`AlgebraicGeometry.Space.isOpen_rankLocus`,
`AlgebraicGeometry.Space.eq_of_mem_rankLocus_of_mem_rankLocus`,
`AlgebraicGeometry.Space.exists_mem_rankLocus`) whose formation commutes with arbitrary base
change. -/
theorem isFiniteLocallyFreeOfRank_modulePullback_iff (f : X ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (n : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
        ((modulePullback B S hS f).obj M) n ↔
      Set.range (pointsMap B S hS X.1 f.hom) ⊆ rankLocus M n := by
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hM
  constructor
  · rintro h _ ⟨x, rfl⟩
    obtain ⟨U, u, rfl⟩ := exists_chartSchemeToPoints_eq B S hS X x
    obtain ⟨I, V, g, hcov, hfree⟩ := h U
    obtain ⟨i, v, hv⟩ := exists_chartSchemeToPoints_eq_of_ofArrows hcov u
    rw [← hv]
    exact mem_rankLocus_of_isFreeOfRankOn_modulePullback f hM (hfree i) v
  · intro h
    have hN : ((modulePullback B S hS f).obj M).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f M inferInstance
    refine isFiniteLocallyFreeOfRank_of_freeRankPresieve B S hS X.1 X.2 _
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hN) n fun U => ?_
    refine smallEtale_sieve_of_pointwise_covering B S hS X.1 U _ fun z => ?_
    obtain ⟨W, a, z', m, hWaff, hz', ⟨β⟩, hmem⟩ :=
      exists_affine_chart_basis_modulePullback f hM U z
    obtain rfl : m = n := eq_of_mem_rankLocus_of_mem_rankLocus hmem (h ⟨_, rfl⟩)
    exact ⟨W, a, ⟨W, 𝟙 W, a, ⟨hWaff, Module.isFiniteLocallyFreeOfRank_of_basis β⟩,
      Category.id_comp _⟩, z', hz'⟩

/-- **A module of rank `r` has every point in its rank locus of `r`.** -/
theorem mem_rankLocus_of_isFiniteLocallyFreeOfRank {M : Modules.{u, u} B S hS Y.1 Y.2} {r : ℕ}
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) M r)
    (y : points B S hS Y.1) : y ∈ rankLocus M r := by
  obtain ⟨U, u, rfl⟩ := exists_chartSchemeToPoints_eq B S hS Y y
  obtain ⟨I, V, g, hcov, hfree⟩ := h U
  obtain ⟨i, v, hv⟩ := exists_chartSchemeToPoints_eq_of_ofArrows hcov u
  exact (mem_rankLocus_iff M r _).mpr ⟨V i, v, hfree i, hv⟩

/-- **The rank of a finite locally free module on a nonempty algebraic space is unique.** -/
@[sga "6 I 6.10" "special case"]
theorem eq_of_isFiniteLocallyFreeOfRank_of_isFiniteLocallyFreeOfRank
    {M : Modules.{u, u} B S hS Y.1 Y.2} {r r' : ℕ}
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) M r)
    (h' : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) M r')
    (y : points B S hS Y.1) : r = r' :=
  eq_of_mem_rankLocus_of_mem_rankLocus (mem_rankLocus_of_isFiniteLocallyFreeOfRank h y)
    (mem_rankLocus_of_isFiniteLocallyFreeOfRank h' y)

end AlgebraicGeometry.Space

end
