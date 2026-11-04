module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.MinusAdamsOperator
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.PullbackTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.MixedDerivedTensorOnARingedSpace

/-!
# Pullback of short exact sequences of modules, and the pullback homomorphism of `K₀(Vect(-))`

Let `f : X ⟶ Y` be a morphism of schemes. The pullback of a short exact sequence of sheaves of
modules on `Y` whose third term is flat is short exact (Stacks Tag 0G6R). The ring homomorphism

`f^* : K₀(Vect(Y)) ⟶ K₀(Vect(X))`

with `f^*[ℰ] = [f^*ℰ]` is `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isFlat`: the pullback along a
  morphism of schemes of a short exact sequence of sheaves of modules whose third term is flat
  is short exact.
* `AlgebraicGeometry.VectorBundleKZero.exists_pullback_ringHom`: `K₀(Vect(-))` admits a pullback
  homomorphism sending `[ℰ]` to `[f^*ℰ]`.

## References

* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.FiniteLocallyFree
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace

universe u

namespace AlgebraicGeometry

/-! ### Stacks 0G6R for a morphism of schemes -/

/-- The pullback along a morphism of schemes of a short exact sequence of sheaves of modules
whose third term is flat is short exact. -/
theorem Scheme.Modules.shortExact_map_pullback_of_isFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : ShortComplex Y.Modules) (hT : T.ShortExact)
    (hflat : Stacks.SheafOfModules.IsFlat (C := TopologicalSpace.Opens Y.toTopCat)
      (J := Opens.grothendieckTopology Y.toTopCat) (O := Y.sheaf) T.X₃) :
    (T.map (Scheme.Modules.pullback f)).ShortExact :=
  RingedToposSiteHom.pullbackPreservesShortExact (ringedToposSiteHom f.toLRSHom.toShHom)
    (isMorphismOfSites f.toLRSHom.toShHom) T hT hflat

namespace VectorBundleKZero

/-- `K₀(Vect(-))` admits a ring homomorphism `K₀(Vect(Y)) →+* K₀(Vect(X))` along `f : X ⟶ Y`
sending `[ℰ]` to `[f^*ℰ]` for every finite locally free `ℰ`. -/
theorem exists_pullback_ringHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ κ : VectorBundleKZero Y →+* VectorBundleKZero X,
      ∀ E : Y.Modules, IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
        κ (classOf Y E) = classOf X ((Scheme.Modules.pullback f).obj E) :=
  ⟨pullbackRingHom f, pullbackRingHom_classOf f⟩

end VectorBundleKZero

end AlgebraicGeometry

end
