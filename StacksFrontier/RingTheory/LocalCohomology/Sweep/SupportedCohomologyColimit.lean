module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.RingTheory.LocalCohomology.BoundedComparison

/-!
# `H^i_T(K) = R^i H^0_T(K) = colim_{Z ⊆ T closed} H^i_Z(K)`

Let `A` be a Noetherian ring and `T ⊆ Spec(A)` a subset stable under specialization. Tag 0EF4
records, besides the two adjunctions, the identification
$$
H^i_T(K) \;=\; H^i(R\Gamma_T(K)) \;=\; R^iH^0_T(K) \;=\;
\operatorname*{colim}_{Z \subseteq T\text{ closed}} H^i_Z(K)
$$
for `K` in `D^+(A)`, and also for `K` in `D(A)` when `dim(A) < ∞`. This file states that
identification, in both the bounded-below and the unbounded case.

The closed subsets `Z ⊆ T` are indexed by `ClosedSupportIdeal A T`, the ideals `I` with
`V(I) ⊆ T` ordered by reverse inclusion, which is a filtered category
(`closedSupportIdeal_isFiltered`); the stage at `I` is `H^i_{V(I)}(K)`
(`closedSupportDiagram_obj_obj`) and the transition maps and the maps into `H^i_T(K)` are the
ones induced by the inclusions of supported sections. So
`isColimitClosedSupportCocone` below says exactly that `H^i_T(K)` is the filtered colimit of
`H^i_Z(K)` over the closed subsets `Z` of `T`, along the canonical maps.

## Main results

* `Stacks.LocalCohomology.isColimitClosedSupportCocone` — the canonical cocone from
  closed-support local cohomology to `H^i_T(K)` is a colimit cocone, for `K` in `D(A)`.
* `Stacks.LocalCohomology.colimitClosedSupportIso` — the resulting isomorphism
  `colim_{Z ⊆ T closed} H^i_Z(K) ≅ H^i_T(K)`.
* `Stacks.LocalCohomology.nonempty_colimitClosedSupportIsoPlus` — the same formula for `K` in
  `D^+(A)`, whose `H^i_T` is the homology of the bounded-below derived functor.
* `Stacks.LocalCohomology.rightDerivedPlus_sectionsWithSupportInFunctor_obj` — the `i`-th right
  derived functor of `H^0_T` in the classical sense of `CategoryTheory.Functor.rightDerivedPlus`
  ([Stacks, Tag 015A]) is, by definition, local cohomology with support in `T` of the module
  placed in degree `0`.

## Implementation notes

The colimit statement is Tag 0EF1's `colimitClosedSupportComparison_isIso` read backwards: that
theorem says the map out of the colimit induced by the canonical cocone is invertible, which by
`CategoryTheory.Limits.IsColimit.ofPointIso` is the same as the canonical cocone being a colimit
cocone. Nothing is reproved here; what is added is the statement in the form the remark asserts
it, under the remark's hypotheses.

The identifications `H^i_T(K) = H^i(RΓ_T(K)) = R^iH^0_T(K)`, which compare the derived functor
of `H^0_T` into `Mod_A` used here with the adjoint `RΓ_T` derived into `Mod_{A,T}`, are in
`StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedUpshot`.

The finite-dimensionality hypothesis of the remark's second adjunction is *not* needed for the
colimit formula: Tag 0EF1 holds for every `K` in `D(A)` because the unbounded `RΓ_T` is built
from K-injective resolutions rather than from bounded cohomological dimension. The hypotheses
carried here are therefore the ones Tag 0EF1 and the remark share, `A` Noetherian and `T` stable
under specialization.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0EF1](https://stacks.math.columbia.edu/tag/0EF1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-- **Stacks Project, Tag 0EF4, the colimit formula.** Let `A` be a Noetherian ring and
`T ⊆ Spec(A)` stable under specialization. For every `K` in `D(A)` and every `i`, the canonical
cocone on the diagram of local cohomology `H^i_Z(K)` indexed by the closed subsets `Z ⊆ T` is a
colimit cocone with vertex `H^i_T(K) = H^i(RΓ_T(K))`. That is,
`H^i_T(K) = colim_{Z ⊆ T closed} H^i_Z(K)`, the index category being filtered. -/
@[stacks 0EF4 "cohomology_colimit"]
def isColimitClosedSupportCocone [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    IsColimit (closedSupportCocone.{u, v} A T i K) :=
  haveI := colimitClosedSupportComparison_isIso.{u, v} A T hT i
  haveI : IsIso ((colimit.isColimit ((closedSupportDiagram.{u, v} A T i).obj K)).desc
      (closedSupportCocone.{u, v} A T i K)) :=
    inferInstanceAs (IsIso ((colimitClosedSupportComparison.{u, v} A T i).app K))
  IsColimit.ofPointIso (colimit.isColimit _)

/-- **Stacks Project, Tag 0EF4, the colimit formula.** The isomorphism
`colim_{Z ⊆ T closed} H^i_Z(K) ≅ H^i_T(K)` for `K` in `D(A)`, induced by the canonical maps
`H^i_Z(K) ⟶ H^i_T(K)`. -/
@[stacks 0EF4 "cohomology_colimit"]
def colimitClosedSupportIso [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    colimit ((closedSupportDiagram.{u, v} A T i).obj K) ≅
      localCohomologyWithSupportIn A T K i :=
  haveI := colimitClosedSupportComparison_isIso.{u, v} A T hT i
  asIso ((colimitClosedSupportComparison.{u, v} A T i).app K)

/-- `colimitClosedSupportIso` restricts on the stage at `Z = V(I)` to the canonical map
`H^i_Z(K) ⟶ H^i_T(K)`. -/
@[reassoc (attr := simp)]
theorem colimit_ι_colimitClosedSupportIso_hom [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (J : ClosedSupportIdeal A T) :
    colimit.ι ((closedSupportDiagram.{u, v} A T i).obj K) J ≫
        (colimitClosedSupportIso.{u, v} A T hT i K).hom =
      (closedSupportStageComparison A T i J).app K :=
  colimit_ι_colimitClosedSupportComparison A T i K J

/-- **Stacks Project, Tag 0EF4, the colimit formula on `D^+(A)`.** Let `A` be a Noetherian ring
and `T ⊆ Spec(A)` stable under specialization. For `K` in `D^+(A)`, local cohomology with support
in `T` computed by the bounded-below derived functor is again the filtered colimit of `H^i_Z(K)`
over the closed subsets `Z ⊆ T`. -/
@[stacks 0EF4 "cohomology_colimit"]
theorem nonempty_colimitClosedSupportIsoPlus [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (i : ℤ)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) :
    Nonempty
      (colimit ((closedSupportDiagram.{u, v} A T i).obj (DerivedCategory.Plus.ι.obj K)) ≅
        localCohomologyWithSupportInPlus A T K i) := by
  obtain ⟨e⟩ := nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso.{u, v} A T
  exact ⟨colimitClosedSupportIso.{u, v} A T hT i (DerivedCategory.Plus.ι.obj K) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso (e.app K)).symm⟩

/-- The `i`-th right derived functor of `H^0_T` in the classical sense of
`Functor.rightDerivedPlus` ([Stacks, Tag 015A]) is, by definition, local cohomology with support
in `T` of the module placed in degree `0`. -/
theorem rightDerivedPlus_sectionsWithSupportInFunctor_obj (i : ℤ)
    (M : ModuleCat.{max u v} A) :
    letI : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
    ((sectionsWithSupportInFunctor.{u, v} A T).rightDerivedPlus i).obj M =
      localCohomologyWithSupportInPlus A T
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i :=
  rfl

end Stacks.LocalCohomology
