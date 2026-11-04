module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherent.Characterization
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherent objects of `D_QCoh(𝒪_{ℙⁿ_A})`

Let `A` be a ring, `n ≥ 0`, `X = ℙⁿ_A` and `K ∈ D_QCoh(𝒪_X)`. Then `K` is pseudo-coherent if and
only if `RΓ(X, E ⊗^𝐋 K)` is a pseudo-coherent object of `D(A)` for every pseudo-coherent `E`, if
and only if the same holds for every perfect `E`, if and only if `RHom(E, K) = RΓ(X, R𝓗om(E, K))`
is pseudo-coherent for every perfect `E`, if and only if `RΓ(X, K ⊗^𝐋 𝒪(d))` is pseudo-coherent
for `d = 0, 1, …, n`.

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.isPseudoCoherent_tfae`: [Stacks, Tag 0CSG].

## Implementation notes

The derived categories of `𝒪_X`-modules (at each of the three spellings of that category that the
statement meets) and of `A`-modules are the standard model `HasDerivedCategory.standard`, fixed in
the statement by `letI`, as in the implications of
`StacksFrontier/AlgebraicGeometry/Perfect/ProjectiveSpacePseudoCoherent/Characterization.lean`.
`RHom(E, K)` is `RΓ(X, R𝓗om(E, K))` read in `D(A)`, which is its definition in the source
([Stacks, Tag 0B6A]).

## References

* [Stacks Project, Tag 0CSG](https://stacks.math.columbia.edu/tag/0CSG)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherent

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **[Stacks, Tag 0CSG].** Let `A` be a ring, `n ≥ 0` and `K ∈ D_QCoh(𝒪_{ℙⁿ_A})`. The following
are equivalent:
1. `K` is pseudo-coherent;
2. `RΓ(ℙⁿ_A, E ⊗^𝐋 K)` is a pseudo-coherent object of `D(A)` for each pseudo-coherent `E` of
   `D(𝒪_{ℙⁿ_A})`;
3. `RΓ(ℙⁿ_A, E ⊗^𝐋 K)` is a pseudo-coherent object of `D(A)` for each perfect `E`;
4. `RHom_{ℙⁿ_A}(E, K) = RΓ(ℙⁿ_A, R𝓗om(E, K))` is a pseudo-coherent object of `D(A)` for each
   perfect `E`;
5. `RΓ(ℙⁿ_A, K ⊗^𝐋 𝒪(d))` is a pseudo-coherent object of `D(A)` for `d = 0, 1, …, n`. -/
@[stacks 0CSG]
theorem isPseudoCoherent_tfae :
    letI : HasDerivedCategory (Proj (polyGrading A n)).Modules := HasDerivedCategory.standard _
    letI : HasDerivedCategory (StrictlyPerfect.OXMod (Proj (polyGrading A n)).toRingedSpace) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory
        (Stacks.DerivedTensor.RingedSite.Modules (Proj (polyGrading A n)).sheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
    ∀ K : DerivedCategory (Proj (polyGrading A n)).Modules, quasicoherentObject A n K →
      List.TFAE
        [RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) K,
          ∀ E : DerivedCategory (Proj (polyGrading A n)).Modules,
            RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) E →
              StacksDraft.PseudoCoherence.IsPseudoCoherent
                ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
                  (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)),
          ∀ E : DerivedCategory (Proj (polyGrading A n)).Modules,
            Stacks.Cohomology.PerfectComplexes.IsPerfect
                (X := (Proj (polyGrading A n)).toRingedSpace) E →
              StacksDraft.PseudoCoherence.IsPseudoCoherent
                ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
                  (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)),
          ∀ E : DerivedCategory (Proj (polyGrading A n)).Modules,
            Stacks.Cohomology.PerfectComplexes.IsPerfect
                (X := (Proj (polyGrading A n)).toRingedSpace) E →
              StacksDraft.PseudoCoherence.IsPseudoCoherent
                ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
                  (((Stacks.SheafOfModules.derivedSheafHom (Proj (polyGrading A n)).sheaf).obj
                    (Opposite.op E)).obj K)),
          ∀ d : Fin (n + 1), StacksDraft.PseudoCoherence.IsPseudoCoherent
            ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
              (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj K).obj
                ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
                  (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))))] := by
  intro K hK
  tfae_have 1 → 2 := isPseudoCoherent_tensor_of_isPseudoCoherent A n K
  tfae_have 2 → 3 := isPseudoCoherent_tensor_of_isPerfect A n K
  tfae_have 3 → 4 := isPseudoCoherent_derivedSheafHom_of_isPerfect A n K
  tfae_have 4 → 3 := isPseudoCoherent_tensor_of_isPseudoCoherent_derivedSheafHom A n K
  tfae_have 3 → 5 := fun h3 d => isPseudoCoherent_tensor_twist_of_isPerfect A n K h3 d
  tfae_have 5 → 1 := isPseudoCoherent_of_isPseudoCoherent_twist A n K hK
  tfae_finish

end AlgebraicGeometry.ProjectiveSpacePseudoCoherent

end
