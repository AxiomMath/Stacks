module

public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Truncation
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistComparisonCompact

/-!
# The twisted-section module of a sheaf recovers the sheaf, in nonnegative degrees

Let `A` be a graded ring, `X = Proj A`, and let `ℱ` be a quasi-coherent `𝒪_X`-module on a
quasi-compact `X`. Tag 0AG5 says that the comparison

`(⨁_{n ∈ ℤ} Γ(X, ℱ(n)))~ ⟶ ℱ`

is an isomorphism. Stacks 0BXF names `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))` as the quasi-inverse of its
equivalence, with the sum running over the **nonnegative** degrees only. Truncating a graded
module does not change its associated sheaf, so the nonnegative part has the same associated
sheaf as the whole, and

`(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ≅ ℱ`

for every `k`, in particular for `k = 0`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.truncatedTwistedSectionsIso`: **the
  isomorphism `(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ≅ ℱ`** for `ℱ` quasi-coherent on a quasi-compact `Proj`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.truncatedTwistedSectionsIsoOfNoetherian`:
  the same with quasi-compactness replaced by Noetherianity of `A`.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedGlobalSectionsGrading
  twistedGlobalSectionsModule twistedGlobalSectionsAssociatedSheaf)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- **The isomorphism `(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ≅ ℱ`** for `ℱ` quasi-coherent on a quasi-compact
`Proj A`. -/
public def truncatedTwistedSectionsIso [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) (k : ℤ) :
    letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
    associatedModuleSheaf 𝒮
        (truncationAboveGrading 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k) ≅ F := by
  letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
  letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
  exact (associatedModuleSheafTruncationAboveIso 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k).trans
    (@asIso _ _ _ _ (ProjTwistIntegerComparison.integerComparison 𝒮 F
      (twistedGlobalSectionsModule 𝒮 F))
      (ProjTwistComparisonCompact.isIso_integerComparison 𝒮 F hqc))

/-- **The isomorphism `(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ≅ ℱ`** for `ℱ` quasi-coherent on `Proj A`, with
`A` a Noetherian graded ring. -/
public def truncatedTwistedSectionsIsoOfNoetherian [IsNoetherianRing S]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) (k : ℤ) :
    letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
    associatedModuleSheaf 𝒮
        (truncationAboveGrading 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k) ≅ F := by
  haveI := Stacks.AlgebraicGeometry.Proj.isNoetherian_proj 𝒮
  haveI : CompactSpace (AlgebraicGeometry.Proj 𝒮) := inferInstance
  exact truncatedTwistedSectionsIso 𝒮 F hqc k

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
