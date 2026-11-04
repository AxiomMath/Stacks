module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSite

/-!
# The components of the small étale site of a simplicial algebraic space are the
spaces-étale sites of its terms

The component of degree `n` of the small étale site `U_étale` of an augmented simplicial
algebraic space (`AlgebraicGeometry.Space.EtaleComponent`) is a strict model of
`U_{n, spaces, étale}`: its realization functor is an equivalence of categories. This file shows
that it is an equivalence of *sites*, so that sheaves on the component are sheaves on
`U_{n, spaces, étale}`, as Section 0DE7 of the Stacks project requires.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.toGrothendieck_precoverage_eq_inducedTopology`: the
  topology of the component is induced from the spaces-étale topology of `U_n` along the
  realization functor.
* `AlgebraicGeometry.Space.EtaleComponent.sheafEquiv`: sheaves on the component are sheaves on
  `U_{n, spaces, étale}`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-- The realization functor of the component of degree `n` is cover-dense for the spaces-étale
topology of `U_n`. -/
instance (n : SimplexCategory) :
    (realizeFunctor (A := A) n).IsCoverDense (SpacesEtale.topology B S hS (A.left.obj (op n))) :=
  inferInstance

/-- **Section 0DE7.** The topology of the component of degree `n` is the topology induced from
the spaces-étale site of `U_n` along the realization functor. -/
theorem toGrothendieck_precoverage_eq_inducedTopology (n : SimplexCategory) :
    (precoverage (A := A) n).toGrothendieck =
      (realizeFunctor n).inducedTopology (SpacesEtale.topology B S hS (A.left.obj (op n))) := by
  refine le_antisymm ?_ fun x T hT => ?_
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro y R hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Functor.mem_inducedTopology_iff_of_isCoverDense]
    refine (SpacesEtale.topology B S hS _).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck hR)
    rintro W _ ⟨Z, h, g, hg, rfl⟩
    cases hg with
    | of hg' => exact ⟨_, _, h, Sieve.le_generate R _ _ hg', rfl⟩
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT
  obtain ⟨R, hR, hle⟩ := hT
  refine (precoverage (A := A) n).toGrothendieck.superset_covering (S := Sieve.generate T.arrows)
    (by rw [Sieve.generate_sieve]) (Precoverage.generate_mem_toGrothendieck ?_)
  rw [precoverage, Precoverage.mem_comap_iff, SpacesEtale.map_mem_precoverage_iff]
  rw [SpacesEtale.mem_precoverage_iff_forall_exists_point] at hR
  intro p
  obtain ⟨Z, g, hg, y, hy⟩ := hR p
  obtain ⟨Z', s, h, hs, rfl⟩ := hle _ _ hg
  refine ⟨Z', s, hs, pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS _).map h).hom y, ?_⟩
  rw [← hy, Functor.map_comp]
  exact (congrFun (pointsMap_comp B S hS _ ((SpacesEtale.toSpaces B S hS _).map h).hom
    ((SpacesEtale.toSpaces B S hS _).map ((realizeFunctor n).map s)).hom) y).symm

/-- The realization functor exhibits the component of degree `n` as a dense subsite of the
spaces-étale site of `U_n`. -/
instance (n : SimplexCategory) :
    (realizeFunctor (A := A) n).IsDenseSubsite (precoverage n).toGrothendieck
      (SpacesEtale.topology B S hS (A.left.obj (op n))) := by
  rw [toGrothendieck_precoverage_eq_inducedTopology]
  infer_instance

/-- **Section 0DE7.** Sheaves on the component of degree `n` of the small étale site of a
simplicial algebraic space are sheaves on `U_{n, spaces, étale}`, by the comparison lemma at the
dense subsite given by the realization functor. -/
def sheafEquiv (n : SimplexCategory) (C : Type*) [Category C]
    [∀ Y, HasLimitsOfShape (StructuredArrow Y (realizeFunctor (A := A) n).op) C] :
    Sheaf (precoverage (A := A) n).toGrothendieck C ≌
      Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) C :=
  Functor.IsDenseSubsite.sheafEquiv _ _ (realizeFunctor n) C

end AlgebraicGeometry.Space.EtaleComponent

end
