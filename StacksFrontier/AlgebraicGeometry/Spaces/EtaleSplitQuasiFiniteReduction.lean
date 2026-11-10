module

public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.Decomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparatedFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFibrePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# The reduction steps of Stacks 082H: from algebraic spaces to the scheme-level splitting

`StacksFrontier/AlgebraicGeometry/Spaces/ClopenPartFinite.lean` proves the conclusion of
Stacks 082H — the open-and-closed decomposition with its finiteness clause — from the
existence, after an étale base change of the target, of an affine object `Z₁` of the site
étale over the base change and finite over an affine base, together with the two conditions
on the fibre. What Stacks 082H asserts and that file does not is the production of such a
`Z₁`, which is the first three paragraphs of the source proof. This file carries out those
paragraphs as far as the scheme level.

The source's three paragraphs are:

1. Replace `Y` by an étale neighbourhood `(U, u) ⟶ (Y, y)` and `f` by its base change; the set
   of points of `|U ×_Y X|` over `u` mapping to one of the `xᵢ` is finite by Decent Spaces
   0AC6 (if `f` is of finite type) or 0AC7 (if `Y` is decent). In particular `Y` may be
   assumed to be an affine scheme.
2. Choose an affine scheme `Z` and an étale `Z ⟶ X` whose image contains the chosen points;
   the preimage `{z₁, …, z_m}` of those points in `|Z|` is finite by Properties of Spaces
   03IJ.
3. Apply More on Morphisms 02LN to `Z ⟶ Y` at `(y, z₁, …, z_m)`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_neighbourhood_finite_fibrePoints` is the first
  paragraph: an affine object of the site étale over `Y` through `y`, for which the set of
  points of the base change lying over the distinguished point and mapping to one of the `xᵢ`
  is finite.
* `AlgebraicGeometry.Space.quasiFiniteAt_toScheme_map_of_chart` identifies quasi-finiteness of
  a morphism of algebraic spaces at a point in the image of an étale chart with scheme-level
  quasi-finiteness of the chart-to-base morphism at the corresponding point of the chart.
* `AlgebraicGeometry.Space.exists_affine_chart_isolated_fibre_points` is the second paragraph
  together with the hypotheses Tag 02LN needs: an affine étale chart of the base change whose
  image contains the prescribed points, the finite injectively-indexed family of points of
  its underlying scheme lying over them, and the isolation of each of those points in its
  fibre.
* `AlgebraicGeometry.Space.exists_etaleNeighbourhood_decomposition_of_isQuasiFiniteAt` is the
  second and third paragraphs: the elementary étale neighbourhood and the open-and-closed
  decomposition of `Z ×_{Y₀} U` that Tag 02LN produces, with all of its hypotheses supplied
  from the algebraic-space data.
* `AlgebraicGeometry.Space.contains_of_locallyOfFiniteType_of_quasiCompact` and
  `AlgebraicGeometry.Space.exists_siteObject_toScheme_map_eq` put a scheme of finite type over
  an object of the site, and a morphism to that object, inside the site.
* `AlgebraicGeometry.Space.exists_affine_siteObject_of_etaleNeighborhood` is the source's "we
  may assume that `U` is affine": every étale neighbourhood of a point of an affine object of
  the site contains an affine open neighbourhood of its distinguished point which is itself an
  object of the site, étale over that affine object.

## Implementation notes

The reduction of the first paragraph is not performed as a replacement of `f` by a base
change: an existential over the étale neighbourhood is produced instead, since the statement
being reduced to has its base as an existential as well. The set whose finiteness the
paragraph asserts is the union over `i` of the sets of Tag 0AC2 attached to `xᵢ` and the
distinguished point, so `AlgebraicGeometry.Space.PointsFibresDiagram` applies with the
cartesian square of the base change read in its reflected orientation
(`CategoryTheory.IsPullback.flip`), and the two cases of the source's hypothesis (4) are
exactly the library's forms of 0AC6 and 0AC7.

`AlgebraicGeometry.Space.quasiFiniteAt_toScheme_map_of_chart` is the bridge that makes the
isolation hypothesis of Tag 02LN available. It is not proved by transporting quasi-finiteness
along the chart but by evaluating both sides against relative dimension zero: quasi-finiteness
at a point of an algebraic space is relative dimension zero there
(`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero`), that is read off a
single chart square by `AlgebraicGeometry.Space.hasRelativeDimensionAt_pointsMap_iff`, and
relative dimension zero of a scheme morphism at a point is quasi-finiteness there by
`AlgebraicGeometry.quasiFiniteAt_iff_fiberDimensionAt_eq_zero`. The chart square used is the
one over the identity of the target, which is a chart because the target is representable. The
passage from quasi-finiteness to isolation in the fibre is
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`; the equivalence
`AlgebraicGeometry.quasiFiniteAt_tfae` proves the same thing but its `List.TFAE.out` cannot be
elaborated against the `IsOpen` spelling of the conclusion.

Separatedness of the chart-to-base morphism of schemes, which Tag 02LN needs, is not
transported from separatedness of the morphism of algebraic spaces: both the chart and the
base are affine, so instance search supplies it.

The points of the chart are indexed by `Fin` of the cardinality of the finite set they form,
through `Finset.equivFin` of its `Set.Finite.toFinset`; this is what makes the indexing
injective, which is a hypothesis of Tag 02LN and is not available from an arbitrary indexing
of the prescribed points of the space (the source does not claim the `xᵢ` are distinct, and
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_finite_points` does not claim its
preimages are).

The size obligation for putting an affine open of an étale neighbourhood into the site is
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`, Stacks 000R (5):
such an open is quasi-compact and of finite type over the affine base. Neither the strong
prelimit nor the cofinality field of `AlgebraicGeometry.BigFppfSite` is used for it. Building
the object of the site out of the resulting size bound follows the recipe of
`AlgebraicGeometry.BigFppfOver.exists_descent_of_exists_descent_scheme`: the underlying scheme
is the scheme itself, the structure morphism is obtained by composing with that of the target,
and the morphism of the site is the preimage of the morphism of schemes under the fully
faithful inclusion of the size-bounded subcategory.

Nothing here carries the tag 082H, and nothing here is the tag. What remains between the last
result of this file and the hypotheses of
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite` is the
re-absorption of the scheme-level decomposition into the site over the affine open produced by
`AlgebraicGeometry.Space.exists_affine_siteObject_of_etaleNeighborhood`: the restriction of the
decomposition to that open, the assembly of the finitely many pieces indexed by `some` into a
single object of the site finite over it, and the identification of the resulting morphism of
presheaves with a morphism into `h_{Y₀} ×_Y X` base changed to that open.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 03IJ](https://stacks.math.columbia.edu/tag/03IJ)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 0AC6](https://stacks.math.columbia.edu/tag/0AC6)
* [Stacks Project, Tag 0AC7](https://stacks.math.columbia.edu/tag/0AC7)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out at the default
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_etaleSplitQuasiFiniteReduction :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_etaleSplitQuasiFiniteReduction
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The first paragraph: reduction to an affine base -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out at the default
/-- **An affine étale neighbourhood of the target over which the relevant set of points of the
base change is finite.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, let `y` be a point of `|Y|` and let `x₁, …, x_n` be points of `|X|`
over `y` at which `f` is quasi-finite. If `f` is quasi-compact or `Y` is decent, then there is
an object `Y₀` of the big fppf site of `S` with affine underlying scheme, an étale morphism
`g : h_{Y₀} ⟶ Y` and a point `u` of `|h_{Y₀}|` over `y` such that only finitely many points of
`|h_{Y₀} ×_Y X|` lie over `u` and map to one of the `xᵢ`.

This is the first paragraph of the proof of Stacks 082H. The étale neighbourhood is
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, which produces an affine chart
through a prescribed point of an arbitrary algebraic space, and the finiteness is Decent Spaces
0AC6 in the quasi-compact case and 0AC7 in the decent case, applied once for each `xᵢ`: the set
in question is the union over `i` of the sets of Tag 0AC2 attached to `xᵢ` and `u`. The library's
two forms match the two cases of the source's hypothesis (4) exactly — 0AC6 asks for the
right vertical morphism to be of finite type and quasi-finite at the point, and 0AC7 for the
lower-right corner to be decent and the lower horizontal morphism to be étale, which the
chart is. -/
theorem exists_affine_etale_neighbourhood_finite_fibrePoints
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y) {n : ℕ} (x : Fin n → points B S hS X)
    (hx : ∀ i, pointsMap B S hS X f (x i) = y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqf : ∀ i, IsQuasiFiniteAt B S hS f (x i))
    (hqc : IsQuasiCompact B S hS f ∨ IsDecentSpace B S hS Y) :
    ∃ (Y₀ : BigFppfOver B S hS) (g : yoneda.obj Y₀ ⟶ Y)
      (u : points B S hS (yoneda.obj Y₀)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀) ∧
      IsEtale B S hS g ∧
      pointsMap B S hS (yoneda.obj Y₀) g u = y ∧
      {w : points B S hS (pullback g f) |
        pointsMap B S hS (pullback g f) (pullback.fst g f) w = u ∧
        ∃ i, pointsMap B S hS (pullback g f) (pullback.snd g f) w = x i}.Finite := by
  obtain ⟨Y₀, g, hY₀, hgE, u, hgu⟩ := exists_affine_etale_chart_at_point B S hS Y hY y
  refine ⟨Y₀, g, u, hY₀, isEtale_of_presheaf_etale B S hS hgE, hgu, ?_⟩
  let D : PointsFibresDiagram B S hS :=
    { W := pullback g f, Z := yoneda.obj Y₀, X := X, Y := Y
      W_isAlgebraicSpace :=
        isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS Y₀) hX hY
      Z_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS Y₀
      X_isAlgebraicSpace := hX, Y_isAlgebraicSpace := hY
      q := pullback.fst g f, p := pullback.snd g f, f := f, g := g
      isPullback := (IsPullback.of_hasPullback g f).flip }
  have hcompat : ∀ i, pointsMap B S hS D.X D.f (x i) = pointsMap B S hS D.Z D.g u :=
    fun i => (hx i).trans hgu.symm
  have hfin : ∀ i, (fibrePoints D (x i) u (hcompat i)).Finite := by
    intro i
    rcases hqc with hqcf | hdec
    · exact finite_fibrePoints_of_isFiniteType_of_isQuasiFiniteAt D (x i) u
        (hcompat i) ⟨hft, hqcf⟩ (hqf i)
    · exact finite_fibrePoints_of_mono_of_isQuasiFiniteAt D (x i) u (hcompat i)
        (hdec.hasMonomorphicFieldRepresentative B S hS D.Y _)
        (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS D.Z_isAlgebraicSpace
          (isLocallyQuasiFinite_of_isEtale' B S hS
            (isEtale_of_presheaf_etale B S hS hgE)) u)
  exact (Set.finite_iUnion hfin).subset fun w ⟨hw1, i, hw2⟩ => Set.mem_iUnion.2 ⟨i, hw2, hw1⟩

/-! ### Quasi-finiteness read off an étale chart -/

/-- **Quasi-finiteness at a point in the image of an étale chart is quasi-finiteness of the
chart-to-base morphism of schemes.** Let `k₁ : P ⟶ h_{Y₀}` be a morphism from an algebraic
space over `S` to a representable presheaf which is locally of finite type, let
`b : h_Z ⟶ P` be an étale chart and let `τ : Z ⟶ Y₀` be the morphism of the site whose Yoneda
image is `b ≫ k₁`. Then for a point `a` of the underlying scheme of `Z`, the morphism `k₁` is
quasi-finite at the image of `a` in `|P|` exactly when the scheme morphism underlying `τ` is
quasi-finite at `a`.

Both sides are relative dimension zero: on the left by
`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero`, and the passage
between the two readings of relative dimension is
`AlgebraicGeometry.Space.hasRelativeDimensionAt_pointsMap_iff` for the chart square over the
identity of `h_{Y₀}`, which is a chart square because the target is representable. -/
theorem quasiFiniteAt_toScheme_map_of_chart
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Y₀ Z : BigFppfOver B S hS}
    {k₁ : P ⟶ yoneda.obj Y₀} (hft : IsLocallyOfFiniteType B S hS k₁)
    (b : yoneda.obj Z ⟶ P)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    {τ : Z ⟶ Y₀} (hτ : yoneda.map τ = b ≫ k₁)
    (a : (BigFppfOver.toScheme B S hS).obj Z) :
    IsQuasiFiniteAt B S hS k₁
        (pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a)) ↔
      AlgebraicGeometry.quasiFiniteAt ((BigFppfOver.toScheme B S hS).map τ) a := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hbp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj Y₀)) :=
    MorphismProperty.id_mem _ _
  have _ : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map τ) :=
    locallyOfFiniteType_toScheme_map_of_chart B S hS hft b hb hτ
  have hcomm : yoneda.map τ ≫ 𝟙 (yoneda.obj Y₀) = b ≫ k₁ := (Category.comp_id _).trans hτ
  have hzero : ((0 : ℕ∞) : WithBot ℕ∞) = 0 := rfl
  rw [isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hP
      (isAlgebraicSpace_yoneda B S hS Y₀) k₁ hft,
    hasRelativeDimensionAt_pointsMap_iff B S hS 0 k₁ Z Y₀ b (𝟙 (yoneda.obj Y₀)) τ hb hbp
      hcomm a,
    AlgebraicGeometry.quasiFiniteAt_iff_fiberDimensionAt_eq_zero, hzero]

/-! ### The second paragraph: the affine chart and the isolated points of its fibre -/

/-- **An affine étale chart with the finite family of isolated points Tag 02LN needs.** Let
`k₁ : P ⟶ h_{Y₀}` be a separated morphism, locally of finite type, from an algebraic space over
`S` to a representable presheaf with affine underlying scheme, let `u` be a point of `|h_{Y₀}|`
and let `w₁, …, w_p` be points of `|P|` over `u` at which `k₁` is quasi-finite. Then there are
an object `Z` of the site with affine underlying scheme, an étale chart `b : h_Z ⟶ P`, the
morphism `τ : Z ⟶ Y₀` of the site underlying `b ≫ k₁`, and an injectively indexed finite
family `z₁, …, z_m` of points of the underlying scheme of `Z` such that: the scheme morphism
underlying `τ` is locally of finite type and sends each `z_j` to the point of the base
corresponding to `u`; each `z_j` is isolated in its fibre; the `z_j` are exactly the points of
`|Z|` mapping into `{w₁, …, w_p}`; and every `wⱼ` is in the image of `b` on points.

This is the second paragraph of the proof of Stacks 082H together with the hypotheses Tag 02LN
needs. The chart is `AlgebraicGeometry.Space.exists_affine_etale_chart_at_finite_points` and
the finiteness of the preimage is Properties of Spaces 03IJ in the form
`AlgebraicGeometry.Space.finite_preimage_pointsMap_of_affine_etale_chart`, whose
quasi-compactness hypothesis on the relation is what separatedness over an affine base
supplies. Injectivity of the indexing comes from indexing the finite set by `Finset.equivFin`
of its `Set.Finite.toFinset` rather than by transporting an indexing of the `wⱼ`, which need
not be injective. Isolation in the fibre is
`AlgebraicGeometry.Space.quasiFiniteAt_toScheme_map_of_chart` followed by
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`. -/
theorem exists_affine_chart_isolated_fibre_points
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Y₀ : BigFppfOver B S hS} (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (k₁ : P ⟶ yoneda.obj Y₀) (hsep : IsSeparated B S hS k₁)
    (hft : IsLocallyOfFiniteType B S hS k₁)
    (u : points B S hS (yoneda.obj Y₀))
    {p : ℕ} (w : Fin p → points B S hS P)
    (hwu : ∀ j, pointsMap B S hS P k₁ (w j) = u)
    (hwqf : ∀ j, IsQuasiFiniteAt B S hS k₁ (w j)) :
    ∃ (Z : BigFppfOver B S hS) (b : yoneda.obj Z ⟶ P) (τ : Z ⟶ Y₀) (m : ℕ)
      (z : Fin m → ((BigFppfOver.toScheme B S hS).obj Z)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      IsEtale B S hS b ∧
      yoneda.map τ = b ≫ k₁ ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map τ) ∧
      Function.Injective z ∧
      (∀ j, (BigFppfOver.toScheme B S hS).map τ (z j) = pointsToScheme B S hS Y₀ u) ∧
      (∀ j, IsOpen {((BigFppfOver.toScheme B S hS).map τ).asFiber (z j)}) ∧
      (∀ a : (BigFppfOver.toScheme B S hS).obj Z,
        a ∈ Set.range z ↔
          pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a)
            ∈ Set.range w) ∧
      (∀ j, ∃ a : (BigFppfOver.toScheme B S hS).obj Z,
        pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a) = w j) := by
  classical
  obtain ⟨Z, b, hZaff, hbE, hbhit⟩ :=
    exists_affine_etale_chart_at_finite_points B S hS P hP w
  obtain ⟨τ, hτ⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (b ≫ k₁)
  have hτft : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map τ) :=
    locallyOfFiniteType_toScheme_map_of_chart B S hS hft b hbE hτ
  -- the preimage of the prescribed points in the chart is finite, by Tag 03IJ
  have hpre : (pointsMap B S hS (yoneda.obj Z) b ⁻¹' Set.range w).Finite :=
    finite_preimage_pointsMap_of_affine_etale_chart B S hS hY₀ hZaff hsep b
      (isEtale_of_presheaf_etale B S hS hbE) (Set.finite_range w)
  set T : Set ((BigFppfOver.toScheme B S hS).obj Z) :=
    pointsToScheme B S hS Z '' (pointsMap B S hS (yoneda.obj Z) b ⁻¹' Set.range w)
  have hTfin : T.Finite := hpre.image _
  set z : Fin hTfin.toFinset.card → (BigFppfOver.toScheme B S hS).obj Z :=
    fun j => ((hTfin.toFinset.equivFin.symm j : { a // a ∈ hTfin.toFinset }) :
      (BigFppfOver.toScheme B S hS).obj Z)
  have hrange : Set.range z = T := by
    have h1 : Set.range z = Set.range (Subtype.val :
        { a // a ∈ hTfin.toFinset } → (BigFppfOver.toScheme B S hS).obj Z) :=
      hTfin.toFinset.equivFin.symm.surjective.range_comp _
    rw [h1, Subtype.range_coe_subtype]
    ext a
    simp [Set.Finite.mem_toFinset]
  -- membership in `T` is exactly the condition on the image point
  have hmemT : ∀ a : (BigFppfOver.toScheme B S hS).obj Z, a ∈ T ↔
      pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a)
        ∈ Set.range w := by
    intro a
    refine ⟨?_, fun ha => ⟨(pointsEquivScheme B S hS Z).symm a, ha, ?_⟩⟩
    · rintro ⟨v, hv, rfl⟩
      have hvv : (pointsEquivScheme B S hS Z).symm (pointsToScheme B S hS Z v) = v :=
        (pointsEquivScheme B S hS Z).symm_apply_apply v
      rwa [hvv]
    · exact (pointsEquivScheme B S hS Z).apply_symm_apply a
  refine ⟨Z, b, τ, hTfin.toFinset.card, z, hZaff,
    isEtale_of_presheaf_etale B S hS hbE, hτ, hτft,
    fun j₁ j₂ h => hTfin.toFinset.equivFin.symm.injective (Subtype.ext h), ?_, ?_,
    fun a => by rw [hrange, hmemT], ?_⟩
  · -- every chosen point lies over `u`
    intro j
    obtain ⟨j', hj'⟩ := (hmemT (z j)).1 (hrange ▸ Set.mem_range_self j)
    have hvz : pointsToScheme B S hS Z ((pointsEquivScheme B S hS Z).symm (z j)) = z j :=
      (pointsEquivScheme B S hS Z).apply_symm_apply (z j)
    have hcompat := pointsToScheme_pointsMap_yoneda B S hS τ
      ((pointsEquivScheme B S hS Z).symm (z j))
    rw [hτ, pointsMap_comp_apply, ← hj', hwu j', hvz] at hcompat
    exact hcompat.symm
  · -- every chosen point is isolated in its fibre
    intro j
    obtain ⟨j', hj'⟩ := (hmemT (z j)).1 (hrange ▸ Set.mem_range_self j)
    have hqf : IsQuasiFiniteAt B S hS k₁ (pointsMap B S hS (yoneda.obj Z) b
        ((pointsEquivScheme B S hS Z).symm (z j))) := by rw [← hj']; exact hwqf j'
    have hq := (quasiFiniteAt_toScheme_map_of_chart B S hS hP hft b hbE hτ (z j)).1 hqf
    exact AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hq.2
  · -- every prescribed point is hit by the chart
    intro j
    obtain ⟨v, hv⟩ := hbhit j
    exact ⟨pointsEquivScheme B S hS Z v, by rwa [(pointsEquivScheme B S hS Z).symm_apply_apply]⟩

/-! ### The third paragraph: the scheme-level splitting -/

/-- **The elementary étale neighbourhood and the open-and-closed decomposition of the chart.**
In the situation of `AlgebraicGeometry.Space.exists_affine_chart_isolated_fibre_points` there
are moreover an elementary étale neighbourhood `U` of the point of the affine base
corresponding to `u` and a decomposition of `Z ×_{Y₀} U` into open-and-closed pieces indexed
by `Option (Fin m)`, the piece attached to `some i` being finite over `U` with fibre over the
distinguished point exactly one point lying over `z i`, and the piece attached to `none`
containing no point over the distinguished point which lies over any `z i`.

This is the third paragraph of the proof of Stacks 082H: More on Morphisms 02LN
(`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_decomposition`) applied to the morphism
of affine schemes underlying `τ`. Its hypotheses are supplied by
`AlgebraicGeometry.Space.exists_affine_chart_isolated_fibre_points`, except separatedness,
which instance search provides because both the chart and the base are affine. The residue
field clause of Tag 02LN is not carried: it is not used downstream, since the fibre of the
piece over the distinguished point is already pinned to a single point. -/
theorem exists_etaleNeighbourhood_decomposition_of_isQuasiFiniteAt
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Y₀ : BigFppfOver B S hS} (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (k₁ : P ⟶ yoneda.obj Y₀) (hsep : IsSeparated B S hS k₁)
    (hft : IsLocallyOfFiniteType B S hS k₁)
    (u : points B S hS (yoneda.obj Y₀))
    {p : ℕ} (w : Fin p → points B S hS P)
    (hwu : ∀ j, pointsMap B S hS P k₁ (w j) = u)
    (hwqf : ∀ j, IsQuasiFiniteAt B S hS k₁ (w j)) :
    ∃ (Z : BigFppfOver B S hS) (b : yoneda.obj Z ⟶ P) (τ : Z ⟶ Y₀) (m : ℕ)
      (z : Fin m → (BigFppfOver.toScheme B S hS).obj Z)
      (U : AlgebraicGeometry.EtaleNeighborhood ((BigFppfOver.toScheme B S hS).obj Y₀)
        (pointsToScheme B S hS Y₀ u)) (_ : U.IsElementary)
      (Q : Option (Fin m) → Scheme.{u})
      (ι : ∀ a, Q a ⟶ pullback ((BigFppfOver.toScheme B S hS).map τ) U.toBase)
      (_ : ∀ a, AlgebraicGeometry.IsOpenImmersion (ι a))
      (_ : ∀ a, AlgebraicGeometry.IsClosedImmersion (ι a))
      (_ : IsIso (Sigma.desc ι))
      (v : ∀ i, Q (some i))
      (_ : ∀ i, AlgebraicGeometry.IsFinite
        (ι (some i) ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ) U.toBase)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      IsEtale B S hS b ∧
      yoneda.map τ = b ≫ k₁ ∧
      (∀ i, (ι (some i) ≫
        pullback.fst ((BigFppfOver.toScheme B S hS).map τ) U.toBase) (v i) = z i) ∧
      (∀ i, {q : Q (some i) | (ι (some i) ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map τ) U.toBase) q = U.point} = {v i}) ∧
      (∀ q : Q none, (ι none ≫
          pullback.snd ((BigFppfOver.toScheme B S hS).map τ) U.toBase) q = U.point →
        ∀ i, (ι none ≫
          pullback.fst ((BigFppfOver.toScheme B S hS).map τ) U.toBase) q ≠ z i) ∧
      (∀ a : (BigFppfOver.toScheme B S hS).obj Z, a ∈ Set.range z ↔
        pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a)
          ∈ Set.range w) ∧
      (∀ j, ∃ a : (BigFppfOver.toScheme B S hS).obj Z,
        pointsMap B S hS (yoneda.obj Z) b
          ((pointsEquivScheme B S hS Z).symm a) = w j) := by
  obtain ⟨Z, b, τ, m, z, hZaff, hbE, hτ, hτft, hzinj, hzs, hziso, hzrange, hhit⟩ :=
    exists_affine_chart_isolated_fibre_points B S hS hP hY₀ k₁ hsep hft u w hwu hwqf
  obtain ⟨U, hUel, Q, ι, hιo, hιc, hιiso, v, hιfin, hv, hfib, -, hnone⟩ :=
    AlgebraicGeometry.exists_elementaryEtaleNeighborhood_decomposition
      ((BigFppfOver.toScheme B S hS).map τ) (pointsToScheme B S hS Y₀ u) m z hzs hzinj hziso
  exact ⟨Z, b, τ, m, z, U, hUel, Q, ι, hιo, hιc, hιiso, v, hιfin, hZaff, hbE, hτ, hv, hfib,
    hnone, hzrange, hhit⟩

/-! ### The affine shrinking of the étale neighbourhood, inside the site -/

/-- **A scheme quasi-compact and of finite type over an object of the site is contained in the
site.** This is Stacks 000R (5),
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`, at the size cutoff
of the big fppf site. Neither the strong-prelimit nor the cofinality field
of `AlgebraicGeometry.BigFppfSite` is needed for it. -/
theorem contains_of_locallyOfFiniteType_of_quasiCompact {Y₀ : BigFppfOver B S hS}
    {V : Scheme.{u}} (ν : V ⟶ (BigFppfOver.toScheme B S hS).obj Y₀)
    [AlgebraicGeometry.LocallyOfFiniteType ν] [AlgebraicGeometry.QuasiCompact ν] :
    B.Contains V :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact ν Y₀.left.property

/-- **A scheme contained in the site, with a morphism to an object of the site, is an object of
the big fppf category over `S`.** The underlying scheme of the object produced is the given
scheme itself, so the isomorphism in the conclusion may be taken to be the identity; it is
stated as an isomorphism because the equality of the two schemes is not available to a caller
which has only the existential.

The construction is the one of
`AlgebraicGeometry.BigFppfOver.exists_descent_of_exists_descent_scheme`: the structure morphism
over `S` is the composite with that of the target, and the morphism of the site is the preimage
of the given morphism of schemes under the fully faithful inclusion of the size-bounded
subcategory. -/
theorem exists_siteObject_toScheme_map_eq {Y₀ : BigFppfOver B S hS} {V : Scheme.{u}}
    (hV : B.Contains V) (ν : V ⟶ (BigFppfOver.toScheme B S hS).obj Y₀) :
    ∃ (Zu : BigFppfOver B S hS) (ν' : Zu ⟶ Y₀)
      (e : (BigFppfOver.toScheme B S hS).obj Zu ≅ V),
      (BigFppfOver.toScheme B S hS).map ν' = e.hom ≫ ν := by
  let Vleft : B.Schemes := B.obj hV
  let ν₀ : Vleft ⟶ Y₀.left := B.inclusion.preimage ν
  refine ⟨Over.mk (ν₀ ≫ Y₀.hom), Over.homMk ν₀, Iso.refl _, ?_⟩
  rw [Iso.refl_hom, Category.id_comp]
  exact B.inclusion.map_preimage (X := Vleft) (Y := Y₀.left) ν

/-- **"We may assume that `U` is affine."** Every étale neighbourhood of a point of the
underlying scheme of an object `Y₀` of the site with affine underlying scheme contains an
affine open neighbourhood of its distinguished point which is itself an object of the site,
étale over `Y₀`, by an open immersion into the neighbourhood carrying the distinguished point
to the distinguished point.

This is the sentence "we may assume that `U` is affine" of the proof of Stacks 082H. The affine
open is any member of the affine basis containing the distinguished point; it is quasi-compact
and of finite type over the affine `Y₀`, so
`AlgebraicGeometry.Space.contains_of_locallyOfFiniteType_of_quasiCompact` places it in the
site, and `AlgebraicGeometry.Space.exists_siteObject_toScheme_map_eq` turns it into an object
of the big fppf category over `S` together with the morphism. The open immersion is retained in
the conclusion because what remains of the proof of Stacks 082H restricts the decomposition of
Tag 02LN along it. -/
theorem exists_affine_siteObject_of_etaleNeighborhood
    {Y₀ : BigFppfOver B S hS} (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    {s : (BigFppfOver.toScheme B S hS).obj Y₀}
    (U : AlgebraicGeometry.EtaleNeighborhood
      ((BigFppfOver.toScheme B S hS).obj Y₀) s) :
    ∃ (Zu : BigFppfOver B S hS) (ν : Zu ⟶ Y₀)
      (κ : (BigFppfOver.toScheme B S hS).obj Zu ⟶ U.scheme)
      (u' : (BigFppfOver.toScheme B S hS).obj Zu),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Zu) ∧
      AlgebraicGeometry.IsOpenImmersion κ ∧
      κ ≫ U.toBase = (BigFppfOver.toScheme B S hS).map ν ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ν) ∧
      κ u' = U.point ∧
      (BigFppfOver.toScheme B S hS).map ν u' = s := by
  obtain ⟨W, hmem⟩ : ∃ W : U.scheme.affineOpens, U.point ∈ W.1 := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hmemV, -⟩ := U.scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ U.point) isOpen_univ
    exact ⟨⟨V, hV⟩, hmemV⟩
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have _ : AlgebraicGeometry.LocallyOfFiniteType (W.1.ι ≫ U.toBase) := inferInstance
  have _ : AlgebraicGeometry.QuasiCompact (W.1.ι ≫ U.toBase) :=
    quasiCompact_of_compactSpace_of_isAffine _ hY₀ inferInstance
  obtain ⟨Zu, ν, e, hν⟩ := exists_siteObject_toScheme_map_eq B S hS
    (contains_of_locallyOfFiniteType_of_quasiCompact B S hS (W.1.ι ≫ U.toBase))
    (W.1.ι ≫ U.toBase)
  have key : ∀ {T : Scheme.{u}} (f : (W.1 : Scheme.{u}) ⟶ T) (x : (W.1 : Scheme.{u})),
      (e.hom ≫ f) (e.inv x) = f x := fun f x => by
    simp
  refine ⟨Zu, ν, e.hom ≫ W.1.ι, e.inv ⟨U.point, hmem⟩, IsAffine.of_isIso e.hom, inferInstance,
    by rw [Category.assoc, hν], by rw [hν]; infer_instance, ?_, ?_⟩
  · exact key W.1.ι _
  · rw [hν]
    exact (key (W.1.ι ≫ U.toBase) _).trans
      ((Scheme.Hom.comp_apply W.1.ι U.toBase ⟨U.point, hmem⟩).trans U.map_point)

end AlgebraicGeometry.Space

end
