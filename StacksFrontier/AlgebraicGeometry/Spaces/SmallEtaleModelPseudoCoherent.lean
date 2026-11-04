module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Pseudo-coherence and boundedness across the equi-universe model of an algebraic space

The derived equivalence `E : D(𝒪_X) ≌ D(𝒪_model)` of an algebraic space with its equi-universe
model carries pseudo-coherent objects (Stacks 08FT) to pseudo-coherent objects, and cohomologically
bounded below objects to cohomologically bounded below objects: it is induced by an equivalence
of ringed sites, and it commutes with the cohomology sheaves.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleModelDerivedEquivalence_functor_obj`.
* `AlgebraicGeometry.Space.isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj`.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The derived equivalence with the model carries pseudo-coherent objects to pseudo-coherent
objects.** -/
theorem isPseudoCoherent_smallEtaleModelDerivedEquivalence_functor_obj
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E) :
    RingedSite.IsPseudoCoherent (smallEtaleModelRingedSite B S hS X.1 X.2)
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E) :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun n =>
    RingedSite.isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso
      (X := smallEtaleModelRingedSite B S hS X.1 X.2) (Y := smallEtaleRingedSite B S hS X.1 X.2)
      (smallEtaleModelEquivalence B S hS X.1)
      (hfun := smallEtaleModelRingedSite_functor_isContinuous B S hS X.1 X.2)
      (hinv := smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)
      (𝟙 _) (hρ := IsIso.id _) E n
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 hE n)

/-- **The derived equivalence with the model carries cohomologically bounded below objects to
cohomologically bounded below objects**: it commutes with the cohomology sheaves. -/
theorem isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K) := by
  obtain ⟨n₀, hn₀⟩ := hK
  exact ⟨n₀, fun n hn => ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (smallEtaleModelModulesEquivalence B S hS X).functor n).app K).isZero_iff.mpr
      ((smallEtaleModelModulesEquivalence B S hS X).functor.map_isZero (hn₀ n hn))⟩

end AlgebraicGeometry.Space

end
