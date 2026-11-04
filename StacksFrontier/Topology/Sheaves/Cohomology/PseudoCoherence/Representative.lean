module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.LocalRepresentation

/-!
# Pseudo-coherence does not depend on the representative

Let `X` be a ringed space and let `E` be an object of the derived category of `𝒪_X`-modules.

* If `E` is represented by a complex `K` which, on a neighbourhood of every point, receives a
  map *in the derived category* from a strictly perfect complex that is an isomorphism on
  cohomology above `m` and an epimorphism in degree `m`, then `E` is `m`-pseudo-coherent.
* Conversely, if `E` is `m`-pseudo-coherent, then *every* complex representing `E` is
  `m`-pseudo-coherent.

The content of both statements is that a map in the derived category out of a strictly perfect
complex is, after shrinking the neighbourhood, induced by an actual map of complexes
(`Stacks.Cohomology.exists_local_complex_map`, Stacks 08C9), and that this replacement does not
destroy the two conditions on cohomology, because restriction to an open subspace is exact. The
second statement follows from the first: the isomorphism between two representatives of `E`
restricts to an isomorphism in the derived category of the open subspace, along which the given
derived map is transported.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_of_derived_map`: the
  shrinking step above, which is the content of both statements. The two statements themselves
  are `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derived_approximation` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_iso`.

## Implementation notes

The shrinking happens inside the restricted ringed space `X|_U`, and the result is a statement
about an open subspace of `X|_U`; `AlgebraicGeometry.RingedSpace.nestedModulesEquivalence` and
`AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_of_nested` move it back to
the corresponding open subspace of `X`. The latter is stated with a bound on the degrees of the
approximating complex, which is harmless here: a strictly perfect complex is bounded, so such a
bound always exists.

A derived category of `𝒪_V`-modules is needed for each open subspace `V` of `X|_U` as well. No
hypothesis is imposed for those: `HasDerivedCategory.standard` is used, which is legitimate
because the universe at which 08C9 is applied is free.

## References

* [Stacks Project, Lemma 20.46.9 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.46.8 (08C9)](https://stacks.math.columbia.edu/tag/08C9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace CategoryTheory.Functor

universe u v

/-- Transfer of the two conditions defining a strictly perfect approximation from a map in the
derived category to a complex-level map inducing its image under an exact functor. -/
theorem homologyMap_bounds_of_mapDerivedCategory {C : Type u} [Category* C] [Abelian C]
    [HasDerivedCategory C] {D : Type v} [Category* D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex C ℤ} (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q)
    (β : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
    (hβ : F.mapDerivedCategory.map α ≫ F.mapDerivedCategoryFactors.hom.app Q =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map β)
    (m : ℤ) (hαgt : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor C j).map α))
    (hαepi : Epi ((DerivedCategory.homologyFunctor C m).map α)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
      Epi (HomologicalComplex.homologyMap β m) := by
  have hcomm (i : ℤ) :
      (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategory.map α) ≫
          (DerivedCategory.homologyFunctor D i).map
            (F.mapDerivedCategoryFactors.hom.app Q) =
        (DerivedCategory.homologyFunctor D i).map
            (F.mapDerivedCategoryFactors.hom.app P) ≫
          (DerivedCategory.homologyFunctor D i).map (DerivedCategory.Q.map β) := by
    simpa only [Functor.map_comp] using
      congrArg ((DerivedCategory.homologyFunctor D i).map) hβ
  refine ⟨fun j hj => ?_, ?_⟩
  · have hFα : IsIso ((DerivedCategory.homologyFunctor D j).map
        (F.mapDerivedCategory.map α)) := by
      refine (NatIso.isIso_map_iff
        (F.mapDerivedCategoryCompHomologyFunctorIso j) α).mpr ?_
      have := hαgt j hj
      exact Functor.map_isIso F _
    have hcomp : IsIso ((DerivedCategory.homologyFunctor D j).map
        (F.mapDerivedCategoryFactors.hom.app P) ≫
        (DerivedCategory.homologyFunctor D j).map (DerivedCategory.Q.map β)) := by
      rw [← hcomm j]
      infer_instance
    refine (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D j) β).mp ?_
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor D j).map (F.mapDerivedCategoryFactors.hom.app P))
      ((DerivedCategory.homologyFunctor D j).map (DerivedCategory.Q.map β))
  · have hFα : Epi ((DerivedCategory.homologyFunctor D m).map
        (F.mapDerivedCategory.map α)) := by
      refine (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso
        (F.mapDerivedCategoryCompHomologyFunctorIso m) α).mpr ?_
      have := hαepi
      exact preserves_epi_of_preservesColimit F _
    have hcomp : Epi ((DerivedCategory.homologyFunctor D m).map
        (F.mapDerivedCategoryFactors.hom.app P) ≫
        (DerivedCategory.homologyFunctor D m).map (DerivedCategory.Q.map β)) := by
      rw [← hcomm m]
      exact epi_comp' hFα (IsIso.epi_of_iso _)
    refine (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso
      (DerivedCategory.homologyFunctorFactors D m) β).mp ?_
    exact (epi_comp_iff_of_epi _ _).mp hcomp

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSpace

universe u d d'

variable {X : RingedSpace.{u, u}}

/-- A strictly perfect complex has no terms above some degree. -/
theorem exists_isZero_X_of_lt {Y : RingedSpace.{u, u}}
    {P : CochainComplex (OXMod.{u, u} Y) ℤ} (hP : IsStrictlyPerfect P) :
    ∃ r : ℤ, ∀ i : ℤ, r < i → IsZero (P.X i) := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  refine ⟨r, fun i hi => ?_⟩
  by_contra h
  exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)

/-- A map in the derived category of `𝒪_U`-modules from a strictly perfect complex to the
restriction of `K`, which is an isomorphism on cohomology above `m` and an epimorphism in
degree `m`, becomes an actual strictly perfect approximation after shrinking `U`. -/
@[sga "6 I 2.2" "b)"]
theorem exists_strictlyPerfect_approximation_of_derived_map
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (m : ℤ) (K : CochainComplex (OXMod.{u, u} X) ℤ) (x : X.carrier)
    (U : Opens X.carrier) (hxU : x ∈ U)
    (P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (restrictComplex K U))
    (hαgt : ∀ j : ℤ, m < j →
      IsIso ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) j).map α))
    (hαepi : Epi ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) m).map α)) :
    ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ P' : CochainComplex (OXMod.{u, u} (X.restrict W.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P' ∧
        ∃ β : P' ⟶ restrictComplex K W,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
          Epi (HomologicalComplex.homologyMap β m) := by
  have : ∀ V : Opens (X.restrict U.isOpenEmbedding).carrier,
      HasDerivedCategory.{max u (u + 1)} (OXMod.{u, u}
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) :=
    fun _ => HasDerivedCategory.standard _
  obtain ⟨V, hxV, hadd, hlim, hcolim, β, hβ⟩ :=
    Stacks.Cohomology.exists_local_complex_map hP α ⟨x, hxU⟩
  have hbounds := Functor.homologyMap_bounds_of_mapDerivedCategory
    (restrictModules (X.restrict U.isOpenEmbedding) V) α β hβ m hαgt hαepi
  obtain ⟨r, hr⟩ := exists_isZero_X_of_lt (isStrictlyPerfect_restrictComplex hP V)
  obtain ⟨P', hP', -, γ, hγiso, hγepi⟩ :=
    exists_strictlyPerfect_approximation_of_nested U V K m r
      (restrictComplex P V) (isStrictlyPerfect_restrictComplex hP V) hr β
      hbounds.1 hbounds.2
  exact ⟨U.isOpenEmbedding.functor.obj V, ⟨⟨x, hxU⟩, hxV, rfl⟩, P', hP', γ, hγiso, hγepi⟩

end AlgebraicGeometry.RingedSpace

end
