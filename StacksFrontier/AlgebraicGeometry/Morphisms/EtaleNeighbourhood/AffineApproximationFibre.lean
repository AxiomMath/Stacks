module

public import StacksFrontier.AlgebraicGeometry.Fibres.ReducedFibreLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineApproximation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.Constructible
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricComponentCountConstructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.ComponentCount
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparableClosure
public import StacksCore.Tactic.StacksAttribute

/-!
# Noetherian approximation of an affine morphism with geometrically good fibres

A morphism of affine schemes of finite presentation all of whose fibres are geometrically
irreducible, respectively geometrically connected, respectively geometrically reduced, is the base
change of such a morphism between affine schemes over a base of finite type over `Spec ℤ`.

## Main results

* `AlgebraicGeometry.exists_finiteTypeAffineModel_geometricallyIrreducible`: the affine
  finite-type model can be chosen with geometrically irreducible fibres.
* `AlgebraicGeometry.exists_finiteTypeAffineModel_geometricallyConnected`: the affine finite-type
  model can be chosen with geometrically connected fibres.
* `AlgebraicGeometry.exists_finiteTypeAffineModel_geometricallyReduced`: the affine finite-type
  model can be chosen with geometrically reduced fibres.

## Implementation notes

The approximation diagram is `AlgebraicGeometry.FiniteTypeAffineModel` and the limit argument is
`AlgebraicGeometry.exists_finiteTypeAffineModel_fiberwise`: what has to be supplied for a
fibrewise condition is its compatibility with base change and the local constructibility of its
locus. In the irreducible case these are Tag 0555 and Tag 055B, the latter through the
identification of the locus of geometrically irreducible fibres with the level set at `1` of the
number of geometrically irreducible components of the fibres; in the connected case they are
Tag 055F and Tag 055I, through the analogous identification for the number of geometric
connected components.

Tag 055B is used in the form carrying the conclusions of Tags 0554 and 0559 as hypotheses, with
those two supplied here, rather than in its assembled form, so that this file does not depend on
the whole chain of consequences drawn from them.

In the reduced case the two ingredients are Tag 0576 and Tag 0579; the latter is available in its
affine Noetherian case, which is exactly the case the limit argument asks for, as
`AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine`.

## References

* [Stacks Project, Tag 05FG](https://stacks.math.columbia.edu/tag/05FG)
* [Stacks Project, Tag 05FH](https://stacks.math.columbia.edu/tag/05FH)
* [Stacks Project, Tag 05FI](https://stacks.math.columbia.edu/tag/05FI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- A fibre is geometrically irreducible exactly when its number of geometrically irreducible
components is one: both say that the base change of the fibre to a separable closure of the
residue field is irreducible. -/
@[ega "IV 4.5.2" "more general"]
private theorem geometricallyIrreducible_fiber_iff_componentCount_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    GeometricallyIrreducible (f.fiberToSpecResidueField y) ↔
      geometricIrreducibleComponentCount f y = 1 := by
  let k := Y.residueField y
  let ksep := SeparableClosure k
  let g := f.fiberToSpecResidueField y
  let Z := pullback g (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))
  have hgeom : GeometricallyIrreducible g ↔ IrreducibleSpace ↥Z := by
    simpa [Z] using
      (geometricallyIrreducible_tfae_of_isSepClosure k (f.fiber y) g ksep).out 1 3
  have hcount : geometricIrreducibleComponentCount f y = 1 ↔ IrreducibleSpace ↥Z := by
    rw [← encard_irreducibleComponents_geometricFiber f y ksep]
    show (irreducibleComponents Z).encard = 1 ↔ IrreducibleSpace ↥Z
    rw [Set.encard_eq_one]
    constructor
    · rintro ⟨C, hC⟩
      have hCmem : C ∈ irreducibleComponents Z := by simp [hC]
      obtain rfl : C = Set.univ := by simpa [hC] using sUnion_irreducibleComponents (X := Z)
      exact (irreducibleSpace_def Z).2 hCmem.1
    · exact fun _ => ⟨_, irreducibleComponents_eq_singleton⟩
  exact hgeom.trans hcount.symm

/-- The locus of geometrically irreducible fibres is the level set at `1` of the number of
geometrically irreducible components of the fibres, hence locally constructible by Tag 055B. -/
@[ega "IV 9.7.7"]
theorem isLocallyConstructible_geometricallyIrreducible_fiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : FinitePresentation f) :
    IsLocallyConstructible
      {y : Y | GeometricallyIrreducible (f.fiberToSpecResidueField y)} := by
  simp_rw [geometricallyIrreducible_fiber_iff_componentCount_eq_one]
  exact isLocallyConstructible_geometricIrreducibleComponentCount_fiber
    irreducibleComponentsLowerBoundAfterShrinking geometricallyIrreducibleAfterShrinking f hf 1

/-- A morphism of affine schemes of finite presentation all of whose fibres satisfy `P`, a condition
compatible with base change and locally constructible, has an affine finite-type model satisfying
`P` fibrewise. -/
private theorem nonempty_finiteTypeAffineModel_of_fiber
    (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ↔ ∀ y, P (f.fiberToSpecResidueField y))
    (hbc : ∀ {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X) (g : Y' ⟶ Y),
      IsPullback i f' f g → {y' : Y' | P (f'.fiberToSpecResidueField y')} =
        g ⁻¹' {y : Y | P (f.fiberToSpecResidueField y)})
    (hloc : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsAffine X → IsAffine Y → IsLocallyNoetherian Y →
      FinitePresentation f → IsLocallyConstructible {y : Y | P (f.fiberToSpecResidueField y)})
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hf : FinitePresentation f) (hfib : P f) :
    Nonempty (FiniteTypeAffineModel P f) := by
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  obtain ⟨m, hm⟩ := exists_finiteTypeAffineModel_fiberwise
    (fun _ S' g => {y : S' | P (g.fiberToSpecResidueField y)})
    (fun _ hp => hbc _ _ _ _ hp) (fun _ _ g => hloc g)
    (finiteTypeAffineModel f hf) ((hP f).mp hfib)
  exact ⟨{ m with property := (hP m.f₀).mpr hm }⟩

/-- **Stacks Project, Tag 05FH.** A morphism of affine schemes of finite presentation with
geometrically irreducible fibres admits an affine finite-type model over a base of finite type
over `ℤ` whose fibres are geometrically irreducible as well. -/
@[stacks 05FH]
theorem exists_finiteTypeAffineModel_geometricallyIrreducible
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hf : FinitePresentation f) (hfib : GeometricallyIrreducible f) :
    Nonempty (FiniteTypeAffineModel @GeometricallyIrreducible f) :=
  nonempty_finiteTypeAffineModel_of_fiber _
    GeometricallyIrreducible.iff_geometricallyIrreducible_fiber
    geometricallyIrreducibleFiberLocus_eq_preimage_of_isPullback
    (fun g _ _ _ hg => isLocallyConstructible_geometricallyIrreducible_fiber g hg) f hf hfib

/-- The locus of geometrically connected fibres pulls back exactly under an arbitrary cartesian
square, because the number of geometric connected components of the fibres does (Tag 055F). -/
private theorem geometricallyConnectedFiberLocus_eq_preimage_of_isPullback
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X) (g : Y' ⟶ Y)
    (h : IsPullback i f' f g) :
    {y' : Y' | GeometricallyConnected (f'.fiberToSpecResidueField y')} =
      g ⁻¹' {y : Y | GeometricallyConnected (f.fiberToSpecResidueField y)} := by
  ext y'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage,
    geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
  rw [congrFun (numGeometricConnectedComponents_eq_of_isPullback f f' i g h) y']
  exact Iff.rfl

/-- The locus of geometrically connected fibres is the level set at `1` of the number of
geometric connected components of the fibres, hence locally constructible by Tag 055I. -/
@[ega "IV 9.7.7", ega "IV 9.7.9" "special case"]
private theorem isLocallyConstructible_geometricallyConnected_fiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : FinitePresentation f) :
    IsLocallyConstructible
      {y : Y | GeometricallyConnected (f.fiberToSpecResidueField y)} := by
  simp_rw [geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
  exact isLocallyConstructible_numGeometricConnectedComponents f hf 1

/-- **Stacks Project, Tag 05FI.** A morphism of affine schemes of finite presentation with
geometrically connected fibres admits an affine finite-type model over a base of finite type
over `ℤ` whose fibres are geometrically connected as well. -/
@[stacks 05FI]
theorem exists_finiteTypeAffineModel_geometricallyConnected
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hf : FinitePresentation f) (hfib : GeometricallyConnected f) :
    Nonempty (FiniteTypeAffineModel @GeometricallyConnected f) :=
  nonempty_finiteTypeAffineModel_of_fiber _
    GeometricallyConnected.iff_geometricallyConnected_fiber
    geometricallyConnectedFiberLocus_eq_preimage_of_isPullback
    (fun g _ _ _ hg => isLocallyConstructible_geometricallyConnected_fiber g hg) f hf hfib

/-- **Stacks Project, Tag 05FG.** A morphism of affine schemes of finite presentation with
geometrically reduced fibres admits an affine finite-type model over a base of finite type over
`ℤ` whose fibres are geometrically reduced as well.

The limit argument is `AlgebraicGeometry.exists_finiteTypeAffineModel_fiberwise`, applied to the
locus of geometrically reduced fibres. Its compatibility with base change is Tag 0576,
`AlgebraicGeometry.geometricallyReduced_fiber_set_eq_preimage_of_isPullback`, and its local
constructibility over an affine Noetherian base is Tag 0579,
`AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine`. -/
@[stacks 05FG, ega "IV 8.9.1" "(i), special case"]
theorem exists_finiteTypeAffineModel_geometricallyReduced
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hf : FinitePresentation f) (hfib : GeometricallyReduced f) :
    Nonempty (FiniteTypeAffineModel @GeometricallyReduced f) :=
  nonempty_finiteTypeAffineModel_of_fiber _
    GeometricallyReduced.iff_geometricallyReduced_fiber
    geometricallyReduced_fiber_set_eq_preimage_of_isPullback
    (fun g _ _ _ hg => isLocallyConstructible_geometricallyReduced_fiber_of_isAffine g hg) f hf hfib

end AlgebraicGeometry
