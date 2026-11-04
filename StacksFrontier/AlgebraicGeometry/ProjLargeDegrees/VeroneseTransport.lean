module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseGlobalSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistedSections
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Basic
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.ShiftTransport

/-!
# Transporting the comparison of Equation 01MR across the Veronese isomorphism

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾`, `i : X = Proj S ≅ X' = Proj S'` the Veronese
isomorphism of [Stacks, Tag 0B5J] and `M` a graded `S`-module with Veronese part `M' = M⁽ᵈ⁾`.
Assertion (1) of that tag, at the shift, is an isomorphism `M(nd)~ ≅ i^*(M'(n)~)`
(`Stacks.Veronese.veroneseShiftedModuleIso`), and
`Stacks.Veronese.veroneseGlobalSectionsModuleMapCompatibility_homogeneous` says that it carries
the map of Equation 01MR on `X` to the one on `X'`. Consequently, if the comparison
`M'_n ⟶ Γ(X', M'(n)~)` is bijective, so is `M_{nd} ⟶ Γ(X, M(nd)~)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.veroneseGradingEquiv`: the degree-`n` piece of the
  Veronese part is the degree-`nd` piece of `M`.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.veroneseShiftedModuleIso_degreeNToGlobalSections`:
  the commuting square, with both comparisons written as
  `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.bijective_degreeNToGlobalSections_of_veronese`: if
  the comparison is bijective for `M'` in degree `n`, it is bijective for `M` in degree `nd`.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent degreeNToGlobalSections globalSectionsModuleMap)
open Stacks.GradedModule (shiftedGrading)
open Stacks.Veronese (bijective_sheafIsoSections bijective_modulesPullbackUnit veroneseSubring
  veroneseGrading veroneseGradingGradedRing veroneseSubmodule
  veroneseModuleGrading veroneseModuleGradingDecomposition mem_veroneseModuleGrading
  mem_veroneseSubmodule_iff mem_veroneseModuleSet_iff veroneseProjIso veroneseShiftedModuleIso
  veroneseGlobalSectionsModuleMapCompatibility_homogeneous)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegrees

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S M : Type u} {σ : Type w} [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- The degree-`n` piece of the Veronese part `M⁽ᵈ⁾` is the degree-`nd` piece of `M`, as the
same set of elements of `M`. -/
def veroneseGradingEquiv (d : ℕ) (n : ℤ) :
    veroneseModuleGrading 𝒮 𝒨 d n ≃ 𝒨 (n * d) where
  toFun x := ⟨((x : veroneseSubmodule 𝒮 𝒨 d) : M), (mem_veroneseModuleGrading 𝒮 𝒨).mp x.2⟩
  invFun z := ⟨⟨(z : M), (mem_veroneseSubmodule_iff 𝒮 𝒨 d).mpr
      (AddSubgroup.subset_closure ((mem_veroneseModuleSet_iff 𝒨).mpr ⟨n, z.2⟩))⟩,
    (mem_veroneseModuleGrading 𝒮 𝒨).mpr z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The isomorphism `M(nd)~ ≅ i^*(M⁽ᵈ⁾(n)~)` of [Stacks, Tag 0B5J] carries the canonical global
section of a homogeneous element of degree `nd` to the pullback of the canonical global section
of that same element, read in degree `n` on `Proj S⁽ᵈ⁾`. -/
theorem veroneseShiftedModuleIso_degreeNToGlobalSections (d : ℕ) (hd : 0 < d) (n : ℤ)
    (x : letI := veroneseGradingGradedRing 𝒮 d hd
      veroneseModuleGrading 𝒮 𝒨 d n) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
        (degreeNToGlobalSections 𝒮 𝒨 (n * d) (veroneseGradingEquiv 𝒮 𝒨 d n x)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
        (degreeNToGlobalSections (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d) n x) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  have hk : ((x : veroneseSubmodule 𝒮 𝒨 d) : M) ∈ 𝒨 (n * d) :=
    (mem_veroneseModuleGrading 𝒮 𝒨).mp x.2
  have h1 : DirectSum.component ℤ ℤ (shiftedSectionsComponent 𝒮 𝒨) (n * d)
        ((globalSectionsModuleMap 𝒮 𝒨).hom ((x : veroneseSubmodule 𝒮 𝒨 d) : M)) =
      degreeNToGlobalSections 𝒮 𝒨 (n * d) (veroneseGradingEquiv 𝒮 𝒨 d n x) := by
    rw [ProjCoherentII.globalSectionsModuleMap_hom_component]
    exact congrArg (degreeNToGlobalSections 𝒮 𝒨 (n * d))
      (Subtype.ext (DirectSum.decompose_of_mem_same 𝒨 hk))
  have h2 : DirectSum.component ℤ ℤ
        (shiftedSectionsComponent (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)) n
        ((globalSectionsModuleMap (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d)).hom (x : veroneseSubmodule 𝒮 𝒨 d)) =
      degreeNToGlobalSections (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d) n x := by
    rw [ProjCoherentII.globalSectionsModuleMap_hom_component]
    exact congrArg (degreeNToGlobalSections (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d) n)
      (Subtype.ext (DirectSum.decompose_of_mem_same (veroneseModuleGrading 𝒮 𝒨 d) x.2))
  rw [← h1, ← h2]
  exact veroneseGlobalSectionsModuleMapCompatibility_homogeneous 𝒮 𝒨 d hd n n
    ((x : veroneseSubmodule 𝒮 𝒨 d) : M) hk (x : veroneseSubmodule 𝒮 𝒨 d).2

/-- If the comparison `M⁽ᵈ⁾_n ⟶ Γ(Proj S⁽ᵈ⁾, M⁽ᵈ⁾(n)~)` of Equation 01MR is bijective, so is
`M_{nd} ⟶ Γ(Proj S, M(nd)~)`. -/
theorem bijective_degreeNToGlobalSections_of_veronese (d : ℕ) (hd : 0 < d) (n : ℤ)
    (h : letI := veroneseGradingGradedRing 𝒮 d hd
      letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
      Function.Bijective
        (degreeNToGlobalSections (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d) n)) :
    Function.Bijective (degreeNToGlobalSections 𝒮 𝒨 (n * d)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  have : IsIso (veroneseProjIso 𝒮 d hd).hom := (veroneseProjIso 𝒮 d hd).isIso_hom
  have hΦ : Function.Bijective fun t : shiftedSectionsComponent 𝒮 𝒨 (n * d) =>
      (veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op ⊤) t :=
    bijective_sheafIsoSections (veroneseShiftedModuleIso 𝒮 𝒨 d hd n) (op ⊤)
  have hΨ := bijective_modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
  rw [← hΦ.of_comp_iff', ← (veroneseGradingEquiv 𝒮 𝒨 d n).bijective.of_comp_iff]
  exact (congrArg Function.Bijective
    (funext (veroneseShiftedModuleIso_degreeNToGlobalSections 𝒮 𝒨 d hd n))).mpr (hΨ.comp h)

end Stacks.AlgebraicGeometry.ProjLargeDegrees

end
