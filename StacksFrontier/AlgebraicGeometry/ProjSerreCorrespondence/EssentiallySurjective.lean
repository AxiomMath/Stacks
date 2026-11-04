module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TwistedFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.CoherentTarget
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.QuasiInverseFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The arrow of Stacks 0BXF is essentially surjective

Let `A` be a graded ring which is Noetherian as a ring, let `X = Proj A` and let `d` be a
positive integer. Stacks 0BXF's arrow is

`Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Coh(𝒪_X)`,  `M ↦ M̃`,

and the source names `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))` as its quasi-inverse. This file proves that the
arrow is **essentially surjective**, by exhibiting that assignment as a functor into `Mod^fg_A`
and its associated sheaf as `ℱ`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentTruncatedTwistedSectionsFunctor`:
  **the quasi-inverse of Stacks 0BXF at its own source and target**, the functor
  `Coh(𝒪_X) ⥤ Mod^fg_A`, `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))`.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.moduleFinite_truncatedTwistedSectionsObj`:
  `⨁_{n ≥ k} Γ(X, ℱ(n))` is a finite `A`-module for `ℱ` coherent — clause (4) of Tag 0B5Q at the
  spelling of the truncation that the quasi-inverse functor is built from.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentTruncatedTwistedSectionsObj_iso`:
  `(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ≅ ℱ` inside `Coh(𝒪_X)`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.essSurj_coherentIrrelevantQuotientFunctor`:
  **the arrow of Stacks 0BXF is essentially surjective.**

## Implementation notes

Clause (4) of Tag 0B5Q is stated at
`Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule.truncation`, cut out by
the vanishing of the summands below the cut, while the quasi-inverse functor is built from
`Stacks.GradedModule.truncationAbove`, cut out by the vanishing of the homogeneous components of
the *grading* below the cut; `truncation_eq_truncationAbove` identifies the two submodules.

The grading carrier `σ` is in the same universe as the ring, as clause (4) of Tag 0B5Q requires.

The quasi-inverse is produced for every cut `k`; the source's quasi-inverse is the case `k = 0`.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedGlobalSectionsGrading
  twistedGlobalSectionsModule homogeneousScalarTwistedSections
  gradedActionTruncation_eq_truncationAbove)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (truncationAbove)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] [IsNoetherianRing S] {d : ℕ}

/-! ### Clause (4) of Tag 0B5Q at the quasi-inverse's spelling of the truncation -/

/-- **The two spellings of `⨁_{n ≥ k} Γ(X, ℱ(n))` are the same submodule** of the twisted global
sections: the one clause (4) of Tag 0B5Q is stated at, cut out by the vanishing of the summands
below `k`, and the one the quasi-inverse functor is built from, cut out by the vanishing of the
homogeneous components of the grading below `k`. -/
public theorem truncation_eq_truncationAbove (F : SheafOfModules.{u} (projRingSheaf 𝒮)) (k : ℤ) :
    letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
    (twistedGlobalSectionsModule 𝒮 F).truncation 𝒮 F k =
      truncationAbove 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k := by
  let := (twistedGlobalSectionsModule 𝒮 F).moduleInst
  let := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
  exact SetLike.coe_injective
    (gradedActionTruncation_eq_truncationAbove 𝒮 (homogeneousScalarTwistedSections 𝒮 F)
      (twistedGlobalSectionsModule 𝒮 F).smul_homogeneous k)

/-- **Clause (4) of Tag 0B5Q at the truncation of the grading**: for `ℱ` coherent on
`X = Proj A` with `A` Noetherian graded, `⨁_{n ≥ k} Γ(X, ℱ(n))` is a finite `A`-module. -/
@[sga "2 XII 5.3" "clause (a), special case"]
public theorem moduleFinite_truncationAbove_twistedGlobalSectionsGrading
    (F : SheafOfModules.{u} (projRingSheaf 𝒮)) (hF : _root_.SheafOfModules.IsCoherent F)
    (k : ℤ) :
    letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
    Module.Finite S (truncationAbove 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k) := by
  let := (twistedGlobalSectionsModule 𝒮 F).moduleInst
  let := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
  have := ProjCoherentII.moduleFinite_truncation_of_isCoherent 𝒮 F hF k
  exact Module.Finite.equiv
    (LinearEquiv.ofEq _ _ (truncation_eq_truncationAbove 𝒮 F k))

/-- **The graded `A`-module `⨁_{n ≥ k} Γ(X, ℱ(n))` is finite** for `ℱ` coherent. -/
public theorem moduleFinite_truncatedTwistedSectionsObj
    (F : SheafOfModules.{u} (projRingSheaf 𝒮)) (hF : _root_.SheafOfModules.IsCoherent F)
    (k : ℤ) :
    Module.Finite S (truncatedTwistedSectionsObj.{u, u} 𝒮 F k).carrier :=
  moduleFinite_truncationAbove_twistedGlobalSectionsGrading 𝒮 F hF k

/-! ### The quasi-inverse as a functor into `Mod^fg_A` -/

/-- **The quasi-inverse of Stacks 0BXF, `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))`, as a functor
`Coh(𝒪_X) ⥤ Mod^fg_A`.** The source's quasi-inverse is the case `k = 0`. -/
public def coherentTruncatedTwistedSectionsFunctor (k : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮) ⥤
      FiniteGradedModules.{u, u, u} 𝒮 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ truncatedTwistedSectionsFunctor.{u, u} 𝒮 k)
    fun F => moduleFinite_truncatedTwistedSectionsObj 𝒮 F.obj F.property k

/-- The value of the quasi-inverse, as an object of `Mod^fg_A`. -/
public theorem coherentTruncatedTwistedSectionsFunctor_obj (k : ℤ)
    (F : _root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮)) :
    ((coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 k).obj F).obj =
      truncatedTwistedSectionsObj.{u, u} 𝒮 F.obj k := rfl

/-- **`(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ≅ ℱ` inside `Coh(𝒪_X)`**, the lift of the isomorphism
`truncatedTwistedSectionsIsoOfNoetherian` of underlying sheaves of modules, so that its `hom` is
that comparison morphism itself. -/
public def coherentTruncatedTwistedSectionsObj_iso (k : ℤ)
    (F : _root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮)) :
    (coherentAssociatedSheafFunctor.{u, u} 𝒮).obj
        ((coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 k).obj F) ≅ F :=
  ObjectProperty.isoMk (P := fun M : _root_.SheafOfModules.{u} (projRingSheaf 𝒮) =>
      M.IsCoherent)
    (truncatedTwistedSectionsIsoOfNoetherian 𝒮 F.obj (isQuasicoherent_of_isCoherent F.obj) k)

/-! ### Essential surjectivity -/

/-- **The arrow of Stacks 0BXF is essentially surjective**: every coherent `𝒪_X`-module is the
associated sheaf of a finitely generated graded `A`-module, namely of
`⨁_{n ≥ 0} Γ(X, ℱ(n))`. -/
public theorem essSurj_coherentIrrelevantQuotientFunctor (hd : 0 < d) :
    (coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd).EssSurj where
  mem_essImage F :=
    ⟨(toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj
        ((coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 0).obj F),
      ⟨(coherentIrrelevantQuotientFunctorFac.{u, u} 𝒮 hd).app
          ((coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 0).obj F) ≪≫
        coherentTruncatedTwistedSectionsObj_iso 𝒮 0 F⟩⟩

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
