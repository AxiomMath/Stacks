module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.DominantGenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedSetFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Generically finite morphisms between integral algebraic spaces

Let `f : X ⟶ Y` be a dominant morphism locally of finite type of integral algebraic spaces
over a scheme `S`, and let `x` and `y` be the generic points of `|X|` and `|Y|`. Then `f` is
quasi-finite at `x` exactly when `x` is the only point of `|X|` above `y`. If moreover `f` is
proper, either condition makes `f` finite over a nonempty open subspace of `Y`.

## Main results

* `AlgebraicGeometry.Space.isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq`: conditions (4)
  and (5) of **Stacks 0AD5**.
* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_zero_of_isQuasiFiniteAt`: condition (4)
  implies condition (1) of **Stacks 0AD5**.
* `AlgebraicGeometry.Space.exists_isFinite_fromPreimage_of_isQuasiFiniteAt`: a proper
  dominant morphism of integral algebraic spaces which is quasi-finite at the generic point
  of its source is finite over a nonempty open subspace of its target.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_isFinite_fromPreimage`: conversely, finiteness
  over a nonempty open subspace of the target gives quasi-finiteness at the generic point.

## Implementation notes

A generic point is recorded as a point whose closure is the whole point space, which is
`IsGenericPoint _ Set.univ` for `AlgebraicGeometry.Space.pointTopology`; that topology is a
plain definition and is made a local instance here, as in the neighbouring files. Integrality
of the source is not used: what the comparison of conditions (4) and (5) needs of it is that
the chosen point of `|X|` be a generic point, which is part of the datum, so the statements
below ask for that and not for `AlgebraicGeometry.Space.IsIntegralSpace` on the source.

Conditions (2), (3) and (6) are *not* covered here. Conditions (1), (2) and (3) are compared at
the scheme level by Stacks 02NX, which this development now has in full —
`AlgebraicGeometry.tfae_trdeg_functionField_eq_zero` in
`StacksFrontier/AlgebraicGeometry/Morphisms/QuasiFinite/GenericallyFiniteDominant.lean` — but the
source's reduction of the space-level conditions to it, through the schematic loci of `X` and
`Y` (Stacks 03K6 and Stacks 086U), is not carried out here; and condition (6) is Stacks 0BBC,
which is not proved here either.

Conditions (4) and (5) are compared through condition (3) of Stacks 0ACB, which says that `f`
is quasi-finite at a point of the set-theoretic fibre `F = |f|^{-1}(\{y\})` exactly when that
point is closed in `F` and has no nontrivial generalization there. At the generic point of an
irreducible point space both halves collapse: the closure of `{x}` is everything, so `{x}` is
closed in `F` precisely when `F = \{x\}`, and then the generalization clause is automatic. The
source argues in the other direction, deducing from a second point of the fibre that `x` is
not isolated in it; the two readings of Stacks 0ACB are the same lemma.

Properness enters only to produce an open subspace of the target over which `f` becomes
finite, replacing the appeal to Stacks 0BBC in the source, which is not available here. The
locus of quasi-finiteness is open (Stacks 0ABM) and contains `x`; its complement is closed,
so its image under `|f|` is closed because a universally closed morphism is closed
(Stacks 03HI), and that image misses `y`, since every point above `y` is `x`. The open
subspace cut out by the complement of that image (Stacks 03BZ) therefore contains `y`, and
the restriction of `f` to it is quasi-finite at every point by Stacks 0ABM again, hence
locally quasi-finite by Stacks 040Z and finite by Stacks 0A4X, being also proper.

## References

* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
* [Stacks Project, Tag 0ACB](https://stacks.math.columbia.edu/tag/0ACB)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 040Z](https://stacks.math.columbia.edu/tag/040Z)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A generic point of a topological space lies in every nonempty open set. -/
private theorem mem_of_isGenericPoint_univ {α : Type*} [TopologicalSpace α] {z : α}
    (hz : IsGenericPoint z (Set.univ : Set α)) {V : Set α} (hV : IsOpen V)
    (hne : V.Nonempty) : z ∈ V :=
  (hz.mem_open_set_iff hV).2 (by simpa using hne)

/-! ### Conditions (4) and (5) of Stacks 0AD5 -/

/-- **Stacks 0AD5, conditions (4) and (5).** Let `f : X ⟶ Y` be a dominant morphism locally of
finite type of algebraic spaces over `S` with `Y` integral, and let `x` and `y` be generic
points of `|X|` and `|Y|`. Then `f` is quasi-finite at `x` exactly when `x` is the only point
of `|X|` mapping to `y`. -/
@[stacks 0AD5 "conditions (4) and (5)"]
theorem isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYint : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hdom : IsDominant B S hS f)
    {x : points B S hS X} (hx : IsGenericPoint x (Set.univ : Set (points B S hS X)))
    {y : points B S hS Y} (hy : IsGenericPoint y (Set.univ : Set (points B S hS Y))) :
    IsQuasiFiniteAt B S hS f x ↔
      ∀ x' : points B S hS X, pointsMap B S hS X f x' = y → x' = x := by
  have hxy : pointsMap B S hS X f x = y :=
    pointsMap_eq_of_isGenericPoint B S hS hY hYint.isDecentSpace f hdom hx hy
  rw [← isClosedNoGeneralization_fibre_iff_isQuasiFiniteAt B S hS hX hY f hf
    hYint.isDecentSpace y ⟨x, hxy⟩]
  constructor
  · rintro ⟨hclosed, -⟩ x' hx'
    by_contra hne
    obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.1 hclosed.isOpen_compl
    have hx'V : x' ∈ V := by
      have : (⟨x', hx'⟩ : ↥(pointsMap B S hS X f ⁻¹' {y})) ∈
          ({(⟨x, hxy⟩ : ↥(pointsMap B S hS X f ⁻¹' {y}))} : Set _)ᶜ := by
        simpa using fun h ↦ hne (congrArg Subtype.val h)
      rwa [← hVeq] at this
    have : (⟨x, hxy⟩ : ↥(pointsMap B S hS X f ⁻¹' {y})) ∈ Subtype.val ⁻¹' V :=
      mem_of_isGenericPoint_univ hx hVopen ⟨x', hx'V⟩
    rw [hVeq] at this
    exact this rfl
  · intro h
    have hsub : ∀ z : ↥(pointsMap B S hS X f ⁻¹' {y}),
        z = (⟨x, hxy⟩ : ↥(pointsMap B S hS X f ⁻¹' {y})) :=
      fun z ↦ Subtype.ext (h z.1 z.2)
    have huniv : ({(⟨x, hxy⟩ : ↥(pointsMap B S hS X f ⁻¹' {y}))} : Set _) = Set.univ :=
      Set.eq_univ_of_forall fun z ↦ (hsub z).symm ▸ rfl
    exact ⟨huniv ▸ isClosed_univ, fun z _ ↦ hsub z⟩

/-! ### Condition (4) implies condition (1) of Stacks 0AD5 -/

/-- The residue field extension of a morphism of schemes which is locally of finite type and
locally quasi-finite has transcendence degree zero at every point of the source: the extension
is finite, hence algebraic. -/
private theorem toENat_trdeg_residueField_eq_zero_of_locallyQuasiFinite {U V : Scheme.{u}}
    (p : U ⟶ V) [LocallyOfFiniteType p] [LocallyQuasiFinite p] (u : U) :
    letI : Algebra (V.residueField (p u)) (U.residueField u) :=
      (p.residueFieldMap u).hom.toAlgebra
    Cardinal.toENat (Algebra.trdeg (V.residueField (p u)) (U.residueField u)) = 0 := by
  let _ : Algebra (V.residueField (p u)) (U.residueField u) :=
    (p.residueFieldMap u).hom.toAlgebra
  have : Module.Finite (V.residueField (p u)) (U.residueField u) :=
    finite_residueField_of_locallyQuasiFinite' p u
  have : Algebra.IsAlgebraic (V.residueField (p u)) (U.residueField u) :=
    Algebra.IsAlgebraic.of_finite _ _
  rw [_root_.trdeg_eq_zero (R := V.residueField (p u)) (A := U.residueField u)]
  simp

/-- **Stacks 0AD5, condition (4) implies condition (1).** A morphism of algebraic spaces over
`S` which is quasi-finite at a point of its source has transcendence degree zero there: on an
open subspace containing the point the morphism is locally quasi-finite, so contributes a
finite residue field extension in every étale chart, and an open immersion does not change the
transcendence degree (Stacks 06RX). -/
@[stacks 0AD5 "condition (4) implies condition (1)"]
theorem hasTranscendenceDegreeAt_zero_of_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {x : points B S hS X} (h : IsQuasiFiniteAt B S hS f x) :
    HasTranscendenceDegreeAt B S hS f x 0 := by
  obtain ⟨U, hU, x', hx', hqf⟩ := h
  have hUf : HasTranscendenceDegreeAt B S hS (U.ι ≫ f) x' 0 := by
    obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hU.1 hY (U.ι ≫ f) x'
    rw [hasTranscendenceDegreeAt_iff_of_chart B S hS 0 (U.ι ≫ f) x' c]
    have hP := hqf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
    have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) := hP.1
    have : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map c.h) := hP.2
    exact toENat_trdeg_residueField_eq_zero_of_locallyQuasiFinite _ (c.sourcePoint B S hS)
  have hx := (hasTranscendenceDegreeAt_comp_iff_of_isLocallyQuasiFinite B S hS hU.1 hX hY
    U.ι f (isLocallyQuasiFinite_of_isEtale B S hS hX (isEtale_ι_of_isOpenSubspace hU)) x' 0).1
    hUf
  rwa [hx'] at hx

/-! ### Finiteness over a nonempty open subspace of the target -/

/-- Finiteness of a morphism of algebraic spaces over a nonempty open subspace of its target
makes it quasi-finite at every point above a generic point of the target: a nonempty open set
contains the generic point, a finite morphism is locally quasi-finite, and the inverse image
of the open subspace is an open subspace of the source containing the given point. -/
theorem isQuasiFiniteAt_of_isFinite_fromPreimage
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {x : points B S hS X}
    {y : points B S hS Y} (hy : IsGenericPoint y (Set.univ : Set (points B S hS Y)))
    (hxy : pointsMap B S hS X f x = y) (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVne : Nonempty (points B S hS V.toFunctor))
    (hfin : IsFinite B S hS (V.fromPreimage f)) :
    IsQuasiFiniteAt B S hS f x := by
  have hP : IsOpenSubspace B S hS (V.preimage f) := isOpenSubspace_preimage B S hS f V hY hX hV
  -- The generic point of the target lies in the nonempty open subspace `V`.
  have hyV : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) :=
    mem_of_isGenericPoint_univ hy (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2)
      ⟨pointsMap B S hS V.toFunctor V.ι hVne.some, ⟨hVne.some, rfl⟩⟩
  obtain ⟨p, hp⟩ : x ∈ Set.range (pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι) := by
    rw [range_pointsMap_ι_preimage' B S hS f V]
    exact Set.mem_preimage.2 (hxy ▸ hyV)
  refine ⟨V.preimage f, hP, p, hp, ?_⟩
  rw [← Subfunctor.fromPreimage_ι V f]
  exact isLocallyQuasiFinite_comp B S hS hP.1 hV.1 hY _ _
    (isQuasiFinite_of_isFinite B S hS (V.fromPreimage f) hP.1 hV.1 hfin).1
    (isLocallyQuasiFinite_of_isEtale B S hS hY (isEtale_ι_of_isOpenSubspace hV))

/-- A proper dominant morphism of algebraic spaces over `S` with integral target which is
quasi-finite at a generic point of its source is finite over a nonempty open subspace of its
target.

This stands in for condition (6) of Stacks 0AD5, which the source obtains from Stacks 0BBC
without assuming properness; see the module docstring for the argument used here. -/
theorem exists_isFinite_fromPreimage_of_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYint : IsIntegralSpace B S hS Y) (f : X ⟶ Y) (hp : IsProper B S hS f)
    (hdom : IsDominant B S hS f)
    {x : points B S hS X} (hx : IsGenericPoint x (Set.univ : Set (points B S hS X)))
    {y : points B S hS Y} (hy : IsGenericPoint y (Set.univ : Set (points B S hS Y)))
    (hqf : IsQuasiFiniteAt B S hS f x) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      Nonempty (points B S hS V.toFunctor) ∧ IsFinite B S hS (V.fromPreimage f) := by
  have hlft : IsLocallyOfFiniteType B S hS f := hp.isFiniteType.1
  have h5 := (isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq B S hS hX hY hYint f hlft hdom
    hx hy).1 hqf
  -- The closed complement of the quasi-finite locus has closed image missing `y`.
  have hEclosed : IsClosed (pointsMap B S hS X f ''
      {z : points B S hS X | IsQuasiFiniteAt B S hS f z}ᶜ) :=
    isClosed_of_universallyClosed B S hS hY f hp.universallyClosed _
      (isOpen_setOf_isQuasiFiniteAt B S hS f).isClosed_compl
  have hyE : y ∉ pointsMap B S hS X f ''
      {z : points B S hS X | IsQuasiFiniteAt B S hS f z}ᶜ := by
    rintro ⟨x', hx'W, hx'y⟩
    exact hx'W (h5 x' hx'y ▸ hqf)
  set V : Subfunctor Y := openSubspaceOfPoints B S hS Y
    (pointsMap B S hS X f '' {z : points B S hS X | IsQuasiFiniteAt B S hS f z}ᶜ)ᶜ
  have hV : IsOpenSubspace B S hS V :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY _ hEclosed.isOpen_compl
  have hVpts : Set.range (pointsMap B S hS V.toFunctor V.ι) =
      (pointsMap B S hS X f '' {z : points B S hS X | IsQuasiFiniteAt B S hS f z}ᶜ)ᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hyV : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
    rw [hVpts]
    exact hyE
  refine ⟨V, hV, ⟨hyV.choose⟩, ?_⟩
  have hsq : IsPullback (V.fromPreimage f) (V.preimage f).ι V.ι f :=
    Subfunctor.isPullback_preimage f V
  have hP : IsOpenSubspace B S hS (V.preimage f) := isOpenSubspace_preimage B S hS f V hY hX hV
  -- Every point of the inverse image is one where `f` is quasi-finite.
  have hpts : ∀ p : points B S hS (V.preimage f).toFunctor,
      IsQuasiFiniteAt B S hS (V.fromPreimage f) p := by
    intro p
    rw [isQuasiFiniteAt_iff_of_isPullback B S hS hsq hX hY hV.1 hlft p]
    have hmem : pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι p ∈
        pointsMap B S hS X f ⁻¹' Set.range (pointsMap B S hS V.toFunctor V.ι) := by
      rw [← range_pointsMap_ι_preimage' B S hS f V]
      exact ⟨p, rfl⟩
    rw [hVpts] at hmem
    by_contra hw
    exact hmem ⟨_, hw, rfl⟩
  have hsqA : IsPullback
      (ObjectProperty.homMk (V.fromPreimage f) :
        (⟨(V.preimage f).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V.toFunctor, hV.1⟩)
      (ObjectProperty.homMk (V.preimage f).ι) (ObjectProperty.homMk V.ι)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsq
  have hproperV : IsProper B S hS (V.fromPreimage f) :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hsqA.flip hp
  exact isFinite_of_isProper_of_isLocallyQuasiFinite B S hS hP.1 hV.1 (V.fromPreimage f)
    hproperV
    ((isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS hP.1 hV.1
      (V.fromPreimage f)).2 hpts)

end AlgebraicGeometry.Space

end
