module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEOfIsLESingle

/-!
# The top cohomology of a derived pullback of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces. For a module `M` on `Y` placed in degree `d`,
the degree-`d` cohomology of `Lf^*(M[-d])` is the inverse image `f^*M`; and for an object `K` of
`D(𝒪_Y)` with no cohomology above degree `d`, `H^d(Lf^*K) ≅ f^*H^d(K)`. This is the step of
Stacks 0EX3 (c) used in the proof of Stacks 0E1J (3), for the small étale site of an algebraic
space.

The proof is the one for ringed spaces in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPullbackTopDegree.lean`: `M[-d]` has a
flat representative with zero terms above `d`
(`AlgebraicGeometry.Space.exists_flat_representative_of_isLE`), on which `Lf^*` is computed
degreewise, and the right exact functor `f^*` commutes with the top cohomology of such a complex
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapTopHomologyIso`). Right t-exactness of `Lf^*`
(`AlgebraicGeometry.Space.isLE_smallEtaleDerivedModulePullback_obj`) then reduces the case of
`K` to that of `H^d(K)[-d]` (`Stacks.TopDegreeComparison.topDegreeIso`).

## Main results

* `AlgebraicGeometry.Space.nonempty_homology_smallEtaleDerivedModulePullback_singleFunctor_iso`:
  `H^d(Lf^*(M[-d])) ≅ f^*M`.
* `AlgebraicGeometry.Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE`:
  `H^d(Lf^*K) ≅ f^*H^d(K)` for `K` with no cohomology above `d`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- **`H^d(Lf^*(M[-d])) ≅ f^*M`** for a morphism `f` of algebraic spaces and a module `M` on the
target placed in degree `d`. -/
theorem nonempty_homology_smallEtaleDerivedModulePullback_singleFunctor_iso (f : X ⟶ Y)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (d : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor _ d).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ d).obj M)) ≅ (modulePullback B S hS f).obj M) := by
  obtain ⟨K, hflat, hKLE, ⟨e⟩⟩ := exists_flat_representative_of_isLE
    ((DerivedCategory.singleFunctor _ d).obj M) d inferInstance
  have := hKLE
  obtain ⟨e'⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback f K d hflat
  have : (modulePullback B S hS f).Additive := modulePullback_additive f
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS f) :=
    (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (modulePullback B S hS f) := inferInstance
  exact ⟨(DerivedCategory.homologyFunctor _ d).mapIso
      ((smallEtaleDerivedModulePullback B S hS f).mapIso e.symm ≪≫ e') ≪≫
    (DerivedCategory.homologyFunctorFactors _ d).app _ ≪≫
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapTopHomologyIso (modulePullback B S hS f) K d
      hKLE ≪≫
    (modulePullback B S hS f).mapIso (((DerivedCategory.homologyFunctorFactors _ d).app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ d).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ d).app M)⟩

/-- **`H^d(Lf^*K) ≅ f^*H^d(K)`** for an object `K` of `D(𝒪_Y)` with no cohomology above degree
`d`: the top cohomology of a derived pullback is the inverse image of the top cohomology. -/
theorem nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (d : ℤ)
    (hK : K.IsLE d) :
    Nonempty ((DerivedCategory.homologyFunctor _ d).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj K) ≅
      (modulePullback B S hS f).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) d).obj K)) := by
  obtain ⟨e⟩ := nonempty_homology_smallEtaleDerivedModulePullback_singleFunctor_iso f
    ((DerivedCategory.homologyFunctor _ d).obj K) d
  have : DerivedCategory.TStructure.t.IsLE K d := hK
  exact ⟨Stacks.TopDegreeComparison.topDegreeIso (smallEtaleDerivedModulePullback B S hS f)
      (fun E n hE => isLE_smallEtaleDerivedModulePullback_obj f E n hE) K d
      (DerivedCategory.truncGEIsoSingleHomologyOfIsLE K d) ≪≫ e⟩

end AlgebraicGeometry.Space

end
