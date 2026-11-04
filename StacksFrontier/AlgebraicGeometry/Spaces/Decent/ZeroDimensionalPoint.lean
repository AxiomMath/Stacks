module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ConstructibleSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.Topology.Dimension.IsolatedPoint

/-!
# Conditions at a point of an algebraic space of finite type over a field

Let `X` be an algebraic space locally of finite type over a field `k` and let `x` be a point
of `|X|`. Stacks 0AC9 compares five conditions at `x`: that the local dimension of `|X|` at
`x` vanishes, that `x` is closed in `|X|` and admits no nontrivial generalization there, that
`x` is isolated in `|X|`, that `X` has dimension zero at `x`, and that `X → Spec k` is
quasi-finite at `x`. The last four are equivalent, and this file proves those three
equivalences. The first condition joins them when `X` is decent: that is the comparison of the
local dimension of `|X|` with the dimension of `X` at a point of a decent space, Stacks 0A4J,
which is not available in this repository yet, and once it is the resulting equivalence belongs
beside the three proved here.

Everything here is proved over an arbitrary base scheme `S`, for the structure morphism of a
presheaf towards a presheaf `yoneda.obj T` represented by an object of the site whose
underlying scheme is of finite type over a field. Taking `S = Spec k` and `T` terminal
recovers the statement of the source; the extra generality is what makes the same argument
serve at a field-valued fibre of a morphism over an arbitrary base, where the fibre is a
space over `S` and not over `Spec k`.

## Main results

* `AlgebraicGeometry.Space.isClosedNoGeneralization_iff_isIsolatedPoint_of_isLocallyOfFiniteType`
  compares conditions (2) and (3) of Stacks 0AC9.
* `AlgebraicGeometry.Space.isIsolatedPoint_iff_dimensionAtPoint_eq_zero_of_isLocallyOfFiniteType`
  compares conditions (3) and (4).
* `AlgebraicGeometry.Space.dimensionAtPoint_eq_zero_iff_isQuasiFiniteAt_of_subsingleton`
  compares conditions (4) and (5).
* `AlgebraicGeometry.Space.dimensionAtPoint_eq_zero_of_isQuasiFiniteAt_of_subsingleton` is the
  implication (5) ⟹ (4), which holds over any base object with subsingleton underlying
  scheme and needs no finiteness of the residue field.
* `AlgebraicGeometry.Space.isClosedNoGeneralization_iff_isIsolatedPoint_over_field`,
  `AlgebraicGeometry.Space.isIsolatedPoint_iff_dimensionAtPoint_eq_zero_over_field` and
  `AlgebraicGeometry.Space.dimensionAtPoint_eq_zero_iff_isQuasiFiniteAt_over_field` are the
  three equivalences in the situation of the source: the base scheme is the spectrum of the
  field and the structure morphism goes to the terminal object of the site.

## Implementation notes

Condition (2) is spelled as the conjunction of `IsClosed {x}` and `∀ x', x' ⤳ x → x' = x`,
which is the form the source uses; equivalently, `{x}` is stable both under specialization
and under generalization.

Only two things about the base object `T` are used. For the implications involving a
dimension of `|X|`, the underlying scheme of `T` must admit a morphism to the spectrum of a
field which is locally of finite type, so that an étale chart of `X` is a scheme locally of
finite type over a field and the local dimension at a closed point of it is the Krull
dimension of the local ring there (Stacks 0A21). For the comparison of conditions (4) and
(5), all that is used is that the underlying scheme of `T` is a subsingleton, so that every
fibre of a chart over `T` is the whole chart.

## References

* [Stacks Project, Tag 0AC9](https://stacks.math.columbia.edu/tag/0AC9)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0BAX](https://stacks.math.columbia.edu/tag/0BAX)
* [Stacks Project, Tag 06EF](https://stacks.math.columbia.edu/tag/06EF)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Charts of a structure morphism towards a represented presheaf -/

/-- The scheme morphism under an étale chart of a presheaf over `yoneda.obj T`, read as a
chart of the structure morphism over the identity chart of `yoneda.obj T`, is locally of
finite type as soon as the structure morphism is. -/
private theorem locallyOfFiniteType_chartMap {T : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g))) :=
  hg U T a (𝟙 _) (yoneda.preimage (a ≫ g)) ha
    (presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj T))) (by simp)

section FiniteTypeOverField

variable {k : Type u} [Field k] {T : BigFppfOver B S hS}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale chart of a presheaf whose structure morphism towards `yoneda.obj T` is locally of
finite type is a scheme locally of finite type over `k`, when the scheme underlying `T` is. -/
private theorem locallyOfFiniteType_chartMap_comp
    (base : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of k)) [LocallyOfFiniteType base]
    (g : X ⟶ yoneda.obj T) (hg : IsLocallyOfFiniteType B S hS g) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g)) ≫ base) :=
  have : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g))) :=
    locallyOfFiniteType_chartMap g hg U a ha
  inferInstance

/-- An étale chart of a presheaf whose structure morphism towards `yoneda.obj T` is locally of
finite type is locally Noetherian, when the scheme underlying `T` is locally of finite type over
a field. -/
private theorem isLocallyNoetherian_chart
    (base : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of k)) [LocallyOfFiniteType base]
    (g : X ⟶ yoneda.obj T) (hg : IsLocallyOfFiniteType B S hS g) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
  have := locallyOfFiniteType_chartMap_comp base g hg U a ha
  LocallyOfFiniteType.isLocallyNoetherian
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g)) ≫ base)

/-! ### From a locally closed point without generalizations to dimension zero -/

/-- A point whose singleton is locally closed and which has no nontrivial generalization is a
point at which the space has dimension zero.

A locally closed nonempty subset of the point space contains a finite type point (Stacks
06EK), so `x` itself is a finite type point and is therefore the image of a *closed* point of
an étale scheme chart (Stacks 06EF). Having no nontrivial generalization makes `x` itself the
codimension-zero point produced by Stacks 0BAX, so the local ring of `X` at `x` has dimension
zero; at a closed point of a scheme locally of finite type over a field the local dimension is
the Krull dimension of the local ring (Stacks 0A21), and that chart computes the dimension of
`X` at `x`. -/
private theorem dimensionAtPoint_eq_zero_of_isLocallyClosed_singleton
    (base : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of k)) [LocallyOfFiniteType base]
    (hX : IsAlgebraicSpace B S hS X) (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (x : points B S hS X)
    (hlc : IsLocallyClosed ({x} : Set (points B S hS X)))
    (hgen : ∀ x' : points B S hS X, x' ⤳ x → x' = x) :
    dimensionAtPoint B S hS X hX x = 0 := by
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) :=
    LocallyOfFiniteType.isLocallyNoetherian base
  have hNoeth : HasEtaleLocalProperty B S hS (yoneda.obj T)
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj T)
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) T (Iso.refl _)).2 inferInstance
  obtain ⟨ξ, -⟩ := exists_genericResidueFieldTranscendenceDegreeAt_eq B S hS g hX
    (isAlgebraicSpace_yoneda B S hS T) hNoeth hg x
  have hξ : ξ.val = x := hgen ξ.val (specializes_iff_mem_closure.mpr ξ.property.1)
  have hzero : localRingDimension B S hS x = 0 := hξ ▸ ξ.property.2
  obtain ⟨y, hy, hft⟩ :=
    inter_finiteTypePoints_nonempty B S hS X hX hlc (Set.singleton_nonempty x)
  have hyx : y = x := hy
  subst hyx
  obtain ⟨U, a, p, ha, hpclosed, hp⟩ :=
    (isFiniteTypePoint_iff_exists_isClosed_etaleChart B S hS X hX y).1 hft
  have ha' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a :=
    (isEtale_iff_presheaf_of_yoneda B S hS a).1 ha
  have : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g)) ≫ base) :=
    locallyOfFiniteType_chartMap_comp base g hg U a ha'
  have hring := (hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS hX y 0).1
    ((localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hX y 0).1 hzero)
    U a (schemePoint B S hS U p) ha' ⟨p, rfl, hp⟩
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX y U a ha' p hp]
  exact (topologicalKrullDimAt_eq_krullDimOfRing_stalk k
    ((BigFppfOver.toScheme B S hS).obj U)
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g)) ≫ base)
    (schemePoint B S hS U p) hpclosed).trans hring

/-! ### From dimension zero to isolation and closedness -/

/-- A point at which the space has dimension zero is isolated.

An étale chart at the point is locally Noetherian, being locally of finite type over a field,
so vanishing of its local dimension at the chart point means that chart point is isolated
(Stacks 0H7C); the chart is open on points, so the image of that chart point is isolated
too. -/
private theorem isIsolatedPoint_of_dimensionAtPoint_eq_zero
    (base : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of k)) [LocallyOfFiniteType base]
    (hX : IsAlgebraicSpace B S hS X) (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (x : points B S hS X)
    (hx : dimensionAtPoint B S hS X hX x = 0) :
    IsIsolatedPoint x := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  have := isLocallyNoetherian_chart base g hg U a ha
  have hz : IsIsolatedPoint (schemePoint B S hS U p) :=
    (topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint
      ((BigFppfOver.toScheme B S hS).obj U) (schemePoint B S hS U p)).1
      ((dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp).symm.trans hx)
  have hopen := isOpenMap_pointsMap_of_etale B S hS hX U a ha
  have himg := hopen _ ((schemePointsHomeomorph B S hS U).symm.isOpenMap _ hz)
  have hsymm : (schemePointsHomeomorph B S hS U).symm (schemePoint B S hS U p) =
      p.class B S hS (yoneda.obj U) := by
    apply (schemePointsHomeomorph B S hS U).injective
    rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply]
    rfl
  simpa only [IsIsolatedPoint, Set.image_singleton, hsymm, hp] using himg

/-- In a locally Noetherian Jacobson scheme every set of isolated points is closed.

Working inside an affine open, the subset is discrete and the ambient space is Noetherian, so
the subset is finite; each of its points is closed because an isolated point of a Jacobson
space spans a locally closed, hence closed, singleton. -/
private theorem isClosed_of_forall_isIsolatedPoint (U : Scheme.{u}) [IsLocallyNoetherian U]
    [JacobsonSpace U] (A : Set U) (hA : ∀ z ∈ A, IsIsolatedPoint z) : IsClosed A := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨_, ⟨V : U.Opens, hV, rfl⟩, hyV, -⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  set D : Set V := Subtype.val ⁻¹' A with hD
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have : _root_.AlgebraicGeometry.IsNoetherian V.toScheme := {}
  have : TopologicalSpace.NoetherianSpace V :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace V.toScheme)
  have hpre (z : V) : (Subtype.val : V → U) ⁻¹' {z.val} = {z} := by
    ext w
    exact ⟨Subtype.ext, congrArg Subtype.val⟩
  have hopen (z : V) (hz : z ∈ D) : IsOpen ({z} : Set V) :=
    (hpre z) ▸ (hA z.val hz).preimage continuous_subtype_val
  have : DiscreteTopology D := discreteTopology_subtype_iff'.2 fun z hz ↦
    ⟨{z}, hopen z hz, Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hz)⟩
  have : TopologicalSpace.NoetherianSpace D := TopologicalSpace.NoetherianSpace.set D
  have : Finite D := TopologicalSpace.NoetherianSpace.finite
  have hclosed : IsClosed D := by
    have hsingle (z : V) (hz : z ∈ D) : IsClosed ({z} : Set V) :=
      (hpre z) ▸ (isClosed_singleton_of_isLocallyClosed_singleton
        (hA z.val hz).isLocallyClosed).preimage continuous_subtype_val
    rw [← Set.biUnion_of_singleton D]
    exact (Set.toFinite D).isClosed_biUnion hsingle
  refine ⟨Subtype.val '' Dᶜ, ?_, V.isOpen.isOpenMap_subtype_val _ hclosed.isOpen_compl,
    ⟨⟨y, hyV⟩, hy, rfl⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hz

/-- A point at which the space has dimension zero is closed.

Pulled back to a surjective étale scheme chart, the singleton becomes a set of isolated points
of a locally Noetherian Jacobson scheme — isolated because the chart computes the dimension of
`X` at the point — hence closed, and the chart is a quotient map on points. -/
private theorem isClosed_singleton_of_dimensionAtPoint_eq_zero
    (base : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of k)) [LocallyOfFiniteType base]
    (hX : IsAlgebraicSpace B S hS X) (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (x : points B S hS X)
    (hx : dimensionAtPoint B S hS X hX x = 0) :
    IsClosed ({x} : Set (points B S hS X)) := by
  obtain ⟨U, a, hsurj, ha⟩ := hX.exists_atlas
  have := locallyOfFiniteType_chartMap_comp base g hg U a ha
  have := isLocallyNoetherian_chart base g hg U a ha
  have : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    LocallyOfFiniteType.jacobsonSpace
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g)) ≫ base)
  have hquot : Topology.IsQuotientMap (pointsMap B S hS (yoneda.obj U) a) :=
    (isOpenMap_pointsMap_of_etale B S hS hX U a ha).isQuotientMap
      (continuous_pointsMap B S hS a)
      ((surjective_iff_surjective_pointsMap B S hS X hX U a).1 hsurj)
  apply hquot.isCoinducing.isClosed_preimage.mp
  apply (schemePointsHomeomorph B S hS U).symm.isClosed_preimage.mp
  apply isClosed_of_forall_isIsolatedPoint ((BigFppfOver.toScheme B S hS).obj U)
  intro z hz
  obtain ⟨p, hp⟩ := Quot.exists_rep ((schemePointsHomeomorph B S hS U).symm z)
  have hp' : p.class B S hS (yoneda.obj U) = (schemePointsHomeomorph B S hS U).symm z := hp
  have hpz : schemePoint B S hS U p = z := by
    rw [show schemePoint B S hS U p =
      schemePointsHomeomorph B S hS U (p.class B S hS (yoneda.obj U)) from rfl, hp',
      Homeomorph.apply_symm_apply]
  have hpx : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x := by
    rw [hp']; exact hz
  apply (topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint
    ((BigFppfOver.toScheme B S hS).obj U) z).1
  rw [← hpz, ← dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hpx]
  exact hx

/-! ### The equivalences -/

/-- **Stacks 0AC9, conditions (3) and (4).** For an algebraic space whose structure morphism
towards a presheaf represented by an object of the site is locally of finite type, and whose
base object is locally of finite type over a field, a point is isolated in the point space
exactly when the space has dimension zero there. -/
theorem isIsolatedPoint_iff_dimensionAtPoint_eq_zero_of_isLocallyOfFiniteType
    (base : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of k)) [LocallyOfFiniteType base]
    (hX : IsAlgebraicSpace B S hS X) (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (x : points B S hS X) :
    IsIsolatedPoint x ↔ dimensionAtPoint B S hS X hX x = 0 := by
  refine ⟨fun hx ↦ ?_, isIsolatedPoint_of_dimensionAtPoint_eq_zero base hX g hg x⟩
  exact dimensionAtPoint_eq_zero_of_isLocallyClosed_singleton base hX g hg x hx.isLocallyClosed
    fun x' hx' ↦ hx'.mem_open hx (Set.mem_singleton x)

/-- **Stacks 0AC9, conditions (2) and (3).** For an algebraic space whose structure morphism
towards a presheaf represented by an object of the site is locally of finite type, and whose
base object is locally of finite type over a field, a point is closed with no nontrivial
generalization exactly when it is isolated. -/
theorem isClosedNoGeneralization_iff_isIsolatedPoint_of_isLocallyOfFiniteType
    (base : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of k)) [LocallyOfFiniteType base]
    (hX : IsAlgebraicSpace B S hS X) (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (x : points B S hS X) :
    (IsClosed ({x} : Set (points B S hS X)) ∧
        ∀ x' : points B S hS X, x' ⤳ x → x' = x) ↔ IsIsolatedPoint x := by
  constructor
  · rintro ⟨hc, hgen⟩
    exact isIsolatedPoint_of_dimensionAtPoint_eq_zero base hX g hg x
      (dimensionAtPoint_eq_zero_of_isLocallyClosed_singleton base hX g hg x
        hc.isLocallyClosed hgen)
  · intro hx
    refine ⟨isClosed_singleton_of_dimensionAtPoint_eq_zero base hX g hg x
      ((isIsolatedPoint_iff_dimensionAtPoint_eq_zero_of_isLocallyOfFiniteType
        base hX g hg x).1 hx), fun x' hx' ↦ hx'.mem_open hx (Set.mem_singleton x)⟩

end FiniteTypeOverField

/-! ### Dimension zero and quasi-finiteness over a one-point base -/

variable {T : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism to a presheaf represented by an object of the site with subsingleton underlying
scheme which is quasi-finite at a point has source of dimension zero there.

Quasi-finiteness at the point gives an open subspace containing it on which the morphism is
locally quasi-finite; being locally quasi-finite and locally of finite type is étale local on
source and target (Stacks 04R3), so it holds on a representative of the germ of an étale chart
at the point. The fibre of that representative through the chart point is the whole
representative, because the target has one point, so the representative is discrete and its
local dimension at the chart point vanishes. That chart computes the dimension of the source
at the point. -/
theorem dimensionAtPoint_eq_zero_of_isQuasiFiniteAt_of_subsingleton
    (hX : IsAlgebraicSpace B S hS X)
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] (g : X ⟶ yoneda.obj T)
    (x : points B S hS X) (hx : IsQuasiFiniteAt B S hS g x) :
    dimensionAtPoint B S hS X hX x = 0 := by
  have hat := (holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hX
    (isAlgebraicSpace_yoneda B S hS T) g x).2
      (by obtain ⟨V, hV, z, hz, hq⟩ := hx; exact ⟨V, hV, ⟨z, hz⟩, hq⟩)
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  let c : EtaleChartAtPoint B S hS g x :=
    { U := U
      V := T
      a := a
      b := 𝟙 (yoneda.obj T)
      h := yoneda.preimage (a ≫ g)
      a_etale := ha
      b_etale := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj T))
      comm := by simp
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := hp }
  have hVsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj c.V) :=
    inferInstanceAs (Subsingleton ((BigFppfOver.toScheme B S hS).obj T))
  obtain ⟨r, hr, hft, hq⟩ := hat c
  have : LocallyQuasiFinite r.hom := hq
  have : LocallyOfFiniteType r.hom := hft
  let z : r.source.toScheme := ⟨c.sourcePoint B S hS, r.mem_source⟩
  have hdiscrete :=
    (locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := r.hom)).1 hq (r.hom z)
  have hall : r.hom ⁻¹' {r.hom z} = Set.univ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [hall] at hdiscrete
  have : DiscreteTopology r.source.toScheme := isDiscrete_univ_iff.mp hdiscrete
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp]
  exact ((Scheme.Opens.ι r.source).isOpenEmbedding.topologicalKrullDimAt_eq z).trans
    (topologicalKrullDimAt_eq_zero_of_isIsolatedPoint z (isOpen_discrete _))

/-- **Stacks 0AC9, conditions (4) and (5).** For an algebraic space whose structure morphism
towards a presheaf represented by an object of the site with subsingleton underlying scheme is
locally of finite type, the space has dimension zero at a point exactly when the structure
morphism is quasi-finite there. -/
theorem dimensionAtPoint_eq_zero_iff_isQuasiFiniteAt_of_subsingleton
    (hX : IsAlgebraicSpace B S hS X)
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (x : points B S hS X) :
    dimensionAtPoint B S hS X hX x = 0 ↔ IsQuasiFiniteAt B S hS g x := by
  refine ⟨fun hx ↦ ?_, dimensionAtPoint_eq_zero_of_isQuasiFiniteAt_of_subsingleton hX g x⟩
  obtain ⟨w, hw⟩ := (mem_range_pointsMap_locallyQuasiFinitePart_iff B S hS hX
    (isAlgebraicSpace_yoneda B S hS T) g hg x).2
      (hasRelativeDimensionAt_zero_of_dimensionAtPoint_eq_zero B S hS hX T g x hx)
  exact ⟨(locallyQuasiFinitePart B S hS hX (isAlgebraicSpace_yoneda B S hS T) g hg).1,
    (locallyQuasiFinitePart B S hS hX (isAlgebraicSpace_yoneda B S hS T) g hg).2, w, hw,
    isLocallyQuasiFinite_locallyQuasiFinitePart B S hS hX
      (isAlgebraicSpace_yoneda B S hS T) g hg⟩

/-! ### The conditions of Stacks 0AC9 for a space over a field

Here the base scheme is the spectrum of the field itself and the base object of the site is the
terminal one, which is the situation of the source statement. The three equivalences are the
corresponding general ones with the identity of `Spec k` as the morphism to the spectrum of a
field.
-/

section BaseField

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of k)))

/-- **Stacks 0AC9, conditions (2) and (3).** A point of an algebraic space locally of finite
type over a field is closed with no nontrivial generalization exactly when it is isolated. -/
@[stacks 0AC9 "conditions (2) and (3)"]
theorem isClosedNoGeneralization_iff_isIsolatedPoint_over_field
    {Z : (BigFppfOver B (Spec (.of k)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hK Z)
    (f : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK))))
    (hf : IsLocallyOfFiniteType B (Spec (.of k)) hK f) (x : points B (Spec (.of k)) hK Z) :
    (IsClosed ({x} : Set (points B (Spec (.of k)) hK Z)) ∧
        ∀ x' : points B (Spec (.of k)) hK Z, x' ⤳ x → x' = x) ↔ IsIsolatedPoint x := by
  have : LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))) := inferInstance
  exact isClosedNoGeneralization_iff_isIsolatedPoint_of_isLocallyOfFiniteType (k := k)
    (T := Over.mk (𝟙 (B.obj hK))) (𝟙 (Spec (.of k))) hZ f hf x

/-- **Stacks 0AC9, conditions (3) and (4).** A point of an algebraic space locally of finite
type over a field is isolated exactly when the space has dimension zero there. -/
@[stacks 0AC9 "conditions (3) and (4)"]
theorem isIsolatedPoint_iff_dimensionAtPoint_eq_zero_over_field
    {Z : (BigFppfOver B (Spec (.of k)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hK Z)
    (f : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK))))
    (hf : IsLocallyOfFiniteType B (Spec (.of k)) hK f) (x : points B (Spec (.of k)) hK Z) :
    IsIsolatedPoint x ↔ dimensionAtPoint B (Spec (.of k)) hK Z hZ x = 0 := by
  have : LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))) := inferInstance
  exact isIsolatedPoint_iff_dimensionAtPoint_eq_zero_of_isLocallyOfFiniteType (k := k)
    (T := Over.mk (𝟙 (B.obj hK))) (𝟙 (Spec (.of k))) hZ f hf x

/-- **Stacks 0AC9, conditions (4) and (5).** An algebraic space locally of finite type over a
field has dimension zero at a point exactly when its structure morphism is quasi-finite
there. -/
@[stacks 0AC9 "conditions (4) and (5)"]
theorem dimensionAtPoint_eq_zero_iff_isQuasiFiniteAt_over_field
    {Z : (BigFppfOver B (Spec (.of k)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hK Z)
    (f : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK))))
    (hf : IsLocallyOfFiniteType B (Spec (.of k)) hK f) (x : points B (Spec (.of k)) hK Z) :
    dimensionAtPoint B (Spec (.of k)) hK Z hZ x = 0 ↔
      IsQuasiFiniteAt B (Spec (.of k)) hK f x := by
  have : Subsingleton
      ((BigFppfOver.toScheme B (Spec (.of k)) hK).obj (Over.mk (𝟙 (B.obj hK)))) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  exact dimensionAtPoint_eq_zero_iff_isQuasiFiniteAt_of_subsingleton
    (T := Over.mk (𝟙 (B.obj hK))) hZ f hf x

end BaseField

end AlgebraicGeometry.Space

end
