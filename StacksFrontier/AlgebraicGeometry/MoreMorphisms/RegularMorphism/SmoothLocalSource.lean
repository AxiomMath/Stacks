module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularMorphism.FppfLocalTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularNoetherian
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.SmoothLocalSource

/-!
# Regular morphisms with locally Noetherian fibres are smooth local on the source

For a morphism of schemes, the property of having locally Noetherian fibres and being regular may
be tested after a smooth covering of the source.

## Main results

* `AlgebraicGeometry.isGeometricallyRegular_iff_isRegular_baseChange`: for a locally Noetherian
  scheme over a field, geometric regularity is regularity of every base change to a finitely
  generated field extension.
* `AlgebraicGeometry.isGeometricallyRegular_iff_of_smoothZeroHypercover`: geometric regularity
  over a field may be tested on a smooth covering family.
* `AlgebraicGeometry.regularWithLocallyNoetherianFibers_isLocalAtSource_smooth`: the property is
  local on the source for the smooth topology.

## Implementation notes

The property splits into three conjuncts: locally Noetherian fibres, flatness, and geometric
regularity of every fibre. The first is Tag 0392 and the second Tag 036K, each transferred from
the fppf, respectively fpqc, topology along the comparison of covering families; so only the
third needs an argument.

Regularity of schemes is a smooth local condition, which is
`AlgebraicGeometry.isRegular_isLocal_smooth`. Geometric regularity over a field is regularity of
all base changes to finitely generated extensions, and a smooth covering family of the scheme
base changes to a smooth covering family of each of those, so that locality applies to each
fibre separately.

## References

* [Stacks Project, Tag 07RA](https://stacks.math.columbia.edu/tag/07RA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 038V**, the equivalence of conditions (1) and (2). For a locally
Noetherian scheme over a field, geometric regularity is regularity of every base change to a
finitely generated field extension. -/
public theorem isGeometricallyRegular_iff_isRegular_baseChange (k : Type u) [Field k]
    (X : Scheme.{u}) [IsLocallyNoetherian X] (f : X ⟶ Spec (.of k)) :
    IsGeometricallyRegular f ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
        IsRegular (pullback f (Spec.map (ofHom (algebraMap k K)))) := by
  refine ⟨fun h K _ _ _ => ?_, fun h x K _ _ _ x' _ => ?_⟩
  · have _ : IsLocallyNoetherian (pullback f (Spec.map (ofHom (algebraMap k K)))) :=
      (isLocallyNoetherian_baseChange_iff k K X f).mp inferInstance
    exact (isRegular_iff_regular_stalks _).mpr ⟨inferInstance, fun z =>
      h (pullback.fst f (Spec.map (ofHom (algebraMap k K))) z) K z rfl⟩
  · exact ((isRegular_iff_regular_stalks _).mp (h K)).2 x'

/-- The members of a smooth covering family are smooth. -/
private theorem smooth_zeroHypercover_f {X : Scheme.{u}}
    (𝒰 : (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).ZeroHypercover X) (i) :
    Smooth (𝒰.f i) := by
  have hm := 𝒰.mem₀
  change Presieve.ofArrows _ 𝒰.f ∈
    (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).coverings X at hm
  exact ((Scheme.ofArrows_mem_precoverage_iff
    (P := @Smooth) (S := X) (X := 𝒰.X) (f := 𝒰.f)).mp hm).2 i

/-- **Stacks Project, Tag 036D.** Geometric regularity of a locally Noetherian scheme over a
field may be tested on a smooth covering family of the scheme. -/
public theorem isGeometricallyRegular_iff_of_smoothZeroHypercover {k : Type u} [Field k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of k))
    (𝒰 : (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).ZeroHypercover X) :
    IsGeometricallyRegular f ↔ ∀ i, IsGeometricallyRegular (𝒰.f i ≫ f) := by
  have hNi (i) : IsLocallyNoetherian (𝒰.X i) := by
    have := smooth_zeroHypercover_f 𝒰 i
    exact LocallyOfFiniteType.isLocallyNoetherian (𝒰.f i)
  have _ := hNi
  have key : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
      IsRegular (pullback f (Spec.map (ofHom (algebraMap k K)))) ↔
        ∀ i, IsRegular (pullback (𝒰.f i ≫ f) (Spec.map (ofHom (algebraMap k K)))) := by
    intro K _ _ _
    refine (ObjectProperty.iff_of_zeroHypercover (P := fun Z : Scheme.{u} => IsRegular Z)
      (𝒰.pullback₁ (pullback.fst f (Spec.map (ofHom (algebraMap k K)))))).trans
      (forall_congr' fun i => ?_)
    exact ObjectProperty.prop_iff_of_iso _
      (compPullbackIso f (Spec.map (ofHom (algebraMap k K))) (𝒰.f i))
  rw [isGeometricallyRegular_iff_isRegular_baseChange k X f]
  refine ⟨fun h i => ?_, fun h K _ _ _ => ?_⟩
  · exact (isGeometricallyRegular_iff_isRegular_baseChange k (𝒰.X i) (𝒰.f i ≫ f)).mpr
      fun K _ _ _ => (key K).mp (h K) i
  · refine (key K).mpr fun i => ?_
    exact (isGeometricallyRegular_iff_isRegular_baseChange k (𝒰.X i) (𝒰.f i ≫ f)).mp (h i) K

/-- A fibre of a morphism of schemes is geometrically regular exactly when the corresponding
fibres of the members of a smooth covering family of the source are. -/
private theorem isGeometricallyRegular_fiber_iff_of_smoothZeroHypercover {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (𝒰 : (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).ZeroHypercover X)
    (y : Y) (hnoeth : IsLocallyNoetherian (f.fiber y)) :
    IsGeometricallyRegular (f.fiberToSpecResidueField y) ↔
      ∀ i, IsGeometricallyRegular ((𝒰.f i ≫ f).fiberToSpecResidueField y) := by
  refine (isGeometricallyRegular_iff_of_smoothZeroHypercover
    (f.fiberToSpecResidueField y) (𝒰.pullback₁ (f.fiberι y))).trans
    (forall_congr' fun i => ?_)
  show IsGeometricallyRegular (pullback.fst (pullback.fst f (Y.fromSpecResidueField y))
      (𝒰.f i) ≫ pullback.snd f (Y.fromSpecResidueField y)) ↔
    IsGeometricallyRegular (pullback.snd (𝒰.f i ≫ f) (Y.fromSpecResidueField y))
  exact isGeometricallyRegular_iff_of_isoOver
    (compPullbackIso f (Y.fromSpecResidueField y) (𝒰.f i)) _ _
    (compPullbackIso_hom_snd f (Y.fromSpecResidueField y) (𝒰.f i)).symm

/-- **Stacks Project, Tag 07RA.** Having locally Noetherian fibres and being regular is local on
the source for the smooth topology. -/
@[stacks 07RA "smooth local on the source"]
public instance regularWithLocallyNoetherianFibers_isLocalAtSource_smooth :
    (regularWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtSource
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) := by
  have _ := regularWithLocallyNoetherianFibers_respectsIso.{u}
  have hnoethLocal : MorphismProperty.IsLocalAtSource
      (locallyNoetherianFibers : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hflatLocal : MorphismProperty.IsLocalAtSource
      (@Flat : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.smoothPrecoverage_le_fpqcPrecoverage
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ?_
  have hnoeth_iff : locallyNoetherianFibers f ↔ ∀ i, locallyNoetherianFibers (𝒰.f i ≫ f) :=
    MorphismProperty.IsLocalAtSource.iff_of_zeroHypercover (P := locallyNoetherianFibers) 𝒰
  have hflat_iff : Flat f ↔ ∀ i, Flat (𝒰.f i ≫ f) :=
    MorphismProperty.IsLocalAtSource.iff_of_zeroHypercover (P := @Flat) 𝒰
  constructor
  · rintro ⟨hn, hr⟩ i
    obtain ⟨hflat, hgeom⟩ :=
      (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers f).mp hr
    exact ⟨hnoeth_iff.mp hn i,
      (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers (𝒰.f i ≫ f)).mpr
        ⟨hflat_iff.mp hflat i, fun y =>
          (isGeometricallyRegular_fiber_iff_of_smoothZeroHypercover f 𝒰 y (hn y)).mp
            (hgeom y) i⟩⟩
  · intro h
    have hn : locallyNoetherianFibers f := hnoeth_iff.mpr fun i => (h i).1
    refine ⟨hn, (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers f).mpr
      ⟨hflat_iff.mpr fun i =>
        ((Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers
          (𝒰.f i ≫ f)).mp (h i).2).1, fun y => ?_⟩⟩
    exact (isGeometricallyRegular_fiber_iff_of_smoothZeroHypercover f 𝒰 y (hn y)).mpr
      fun i => ((Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers
        (𝒰.f i ≫ f)).mp (h i).2).2 y

end AlgebraicGeometry
