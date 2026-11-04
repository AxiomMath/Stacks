module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.PowerComposition
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization

/-!
# Powers of a section on an affine chart

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)`, `𝒢` a quasi-coherent
`𝒪_X`-module and `A` an affine open on which `s|_A = r · l` for a function `r` and a section `l`
of `ℒ`. Then:

* a section `x` of `𝒢` over `A` vanishing on `D(r)` satisfies `x ⊗ sᴺ|_A = 0` for some `N`
  ([Stacks, Tag 01I9] for a quasi-coherent module);
* for every section `y` of `𝒢` over `D(r)` some `y ⊗ sᴺ|_{D(r)}` is the restriction of a section
  of `𝒢 ⊗ ℒ^{⊗ N}` over `A` ([Stacks, Tag 01P7] for a quasi-coherent module).

## Main results

* `Stacks.SheafOfModules.SectionPowerComposition.exists_tensorSectionAtOpen_eq_zero`: a section
  of `𝒢` over `A` vanishing on `D(r)` is killed by a power of `s`.
* `Stacks.SheafOfModules.SectionPowerComposition.exists_restrict_eq_tensorSectionAtOpen`: a
  section of `𝒢` over `D(r)` times a power of `s` extends to `A`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.Cohomology.TwistedGradedModule

universe u

namespace Stacks.SheafOfModules.SectionPowerComposition

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] moduleOfSections

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections)

/-- Restricting a global section of a module to an open and then to a smaller open is
restricting it to the smaller open. -/
theorem map_map_terminal (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {U V : Opens X.toRingedSpace} (h : V ≤ U)
    (m : M.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    M.val.map (homOfLE h).op (M.val.map (terminal.from U).op m) =
      M.val.map (terminal.from V).op m := by
  rw [← PresheafOfModules.map_comp_apply,
    Subsingleton.elim ((terminal.from U).op ≫ (homOfLE h).op) (terminal.from V).op]

/-- Let `A` be an affine open with `s|_A = r • l`. If a section `x` of `G` over `A` vanishes on
`D(r)`, then `x ⊗ sᴺ|_A = 0` for some `N`. -/
theorem exists_tensorSectionAtOpen_eq_zero (G : X.Modules) [G.IsQuasicoherent]
    {A : Opens X.toRingedSpace} (hA : IsAffineOpen A) (r : (sectionSiteRing X).obj (op A))
    (l : L.val.obj (op A)) (hs : s.eval (op A) = r • l) (x : G.val.obj (op A))
    (hx : G.val.map (homOfLE (X.basicOpen_le r)).op x = 0) :
    ∃ N : ℕ, tensorSectionAtOpen X L G A N x
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
        (terminal.from A).op (sectionPower X L s N)) = 0 := by
  obtain ⟨N, hN⟩ := Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero G hA r x hx
  obtain ⟨q, hq⟩ := sectionPower_restrict_dvd_smul X L s A r l hs N
  refine ⟨N, ?_⟩
  rw [hq]
  refine (tensorSectionsAt_smul_comm X G _ (op A) (r ^ N) x q).symm.trans ?_
  have h0 : (r ^ N • x : G.val.obj (op A)) = 0 := hN
  rw [h0]
  exact (congrArg _ (TensorProduct.zero_tmul _ q)).trans (map_zero _)

/-- Let `A` be an affine open with `s|_A = r • l`. For every section `y` of `G` over `D(r)`
there is an `N` such that `y ⊗ sᴺ|_{D(r)}` is the restriction of a section of `G ⊗ L^{⊗ N}`
over `A`. -/
theorem exists_restrict_eq_tensorSectionAtOpen (G : X.Modules) [G.IsQuasicoherent]
    {A : Opens X.toRingedSpace} (hA : IsAffineOpen A) (r : (sectionSiteRing X).obj (op A))
    (l : L.val.obj (op A)) (hs : s.eval (op A) = r • l) (y : G.val.obj (op (X.basicOpen r))) :
    ∃ (N : ℕ) (a : (twist X L G (N : ℤ)).val.obj (op A)),
      (twist X L G (N : ℤ)).val.map (homOfLE (X.basicOpen_le r)).op a =
        tensorSectionAtOpen X L G (X.basicOpen r) N y
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
            (terminal.from (X.basicOpen r)).op (sectionPower X L s N)) := by
  obtain ⟨N, c, hc⟩ := Stacks.ModuleSectionExtension.exists_pow_smul_eq_res G hA r y
  obtain ⟨q, hq⟩ := sectionPower_restrict_dvd_smul X L s A r l hs N
  refine ⟨N, tensorSectionAtOpen X L G A N c q, ?_⟩
  have hc' : (G.val.map (homOfLE (X.basicOpen_le r)).op c : G.val.obj (op (X.basicOpen r))) =
      (sectionSiteRing X).map (homOfLE (X.basicOpen_le r)).op (r ^ N) • y := by
    rw [map_pow]
    exact hc.symm
  have hq' : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
      (terminal.from (X.basicOpen r)).op (sectionPower X L s N) =
      (sectionSiteRing X).map (homOfLE (X.basicOpen_le r)).op (r ^ N) •
        (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
          (homOfLE (X.basicOpen_le r)).op q := by
    rw [← map_map_terminal X _ (X.basicOpen_le r) (sectionPower X L s N), hq,
      PresheafOfModules.map_smul]
    rfl
  refine (tensorSectionsAt_restrict X G _ (homOfLE (X.basicOpen_le r)).op c q).trans ?_
  refine (congrArg (fun z => tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op (X.basicOpen r)) G _ z
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
        (homOfLE (X.basicOpen_le r)).op q)) hc').trans ?_
  refine (tensorSectionsAt_smul_comm X G _ (op (X.basicOpen r)) _ y _).trans ?_
  exact congrArg (fun z => tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op (X.basicOpen r)) G _ y z) hq'.symm

end Stacks.SheafOfModules.SectionPowerComposition

end
