module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType

/-!
# The support of the quotient `F / I ^ n • F`

Where the quasi-coherent ideal sheaf `I` is the unit ideal, the subsheaf `I ^ n • F` has all the
sections of `F`, so the quotient `F / I ^ n • F` vanishes there. This file turns that into the
statement about supports that the splitting of [Stacks, Tag 01YD] needs: if `I` is the unit
ideal on every affine open inside an open `U`, then no point of `U` lies in the support of
`cokernel ((I ^ n • F).ι)`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmulModule`: `I ^ n • F` as an `𝒪_X`-module.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmulHom`: its inclusion into `F`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerSmul.isLocallyIn_of_ideal_eq_top`: a section of `F` over an
  open on which `I` is the unit ideal is a section of `I ^ n • F`.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.notMem_supp_cokernel`: a point with a neighbourhood on
  which `I` is the unit ideal is outside the support of `F / I ^ n • F`.

## Implementation notes

The argument is made on germs, not on sections: the stalk of the quotient at `x` is shown to be
zero by exhibiting every germ as the germ of a section which is already zero on a smaller
neighbourhood. That avoids both the exactness of global sections on an affine open and the
separatedness argument that the statement `Γ(F / I ^ n • F, U) = 0` would need.

The surjectivity of `cokernel.π` on small enough neighbourhoods is
`AlgebraicGeometry.SheafOfModules.isLocallySurjective_toSheaf_of_epi`, read through
`TopologicalSpace.Opens.mem_grothendieckTopology`, which turns membership of the image sieve in
the covering sieves into the pointwise statement.

## References

* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.GabberColimit

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerSmul

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) [F.IsQuasicoherent]

/-- `I ^ n • F`, as an `𝒪_X`-module. -/
def idealPowSmulModule : X.Modules :=
  compatibleModule F (idealPowFamily I n F) (isCompatible_idealPowFamily I n F)

/-- The inclusion of `I ^ n • F` into `F`. -/
def idealPowSmulHom : idealPowSmulModule I n F ⟶ F :=
  (idealPowSmul I n F).ι

omit [F.IsQuasicoherent] in
/-- A section of `F` over an open on which `I` is the unit ideal lies locally in the family
defining `I ^ n • F`, hence is a section of `I ^ n • F`. -/
theorem isLocallyIn_of_ideal_eq_top {U : X.Opens}
    (hU : ∀ W : X.affineOpens, W.1 ≤ U → I.ideal W = ⊤) {V : X.Opens} (hV : V ≤ U)
    (s : Γ(F, V)) : IsLocallyIn F (idealPowFamily I n F) s := by
  intro W hW
  rw [idealPowFamily_eq_top I n F (hU W (hW.trans hV))]
  exact Submodule.mem_top

/-- The inclusion sends the section of `I ^ n • F` attached to a section of `F` back to it. -/
theorem idealPowSmulHom_app_mkSection {V : X.Opens} (s : Γ(F, V))
    (hs : IsLocallyIn F (idealPowFamily I n F) s) :
    (idealPowSmulHom I n F).app V
        (mkSection F (idealPowFamily I n F) (isCompatible_idealPowFamily I n F) s hs) = s :=
  rfl

/-- **A point with a neighbourhood on which `I` is the unit ideal is outside the support of
`F / I ^ n • F`.** -/
theorem notMem_supp_cokernel {U : X.Opens} (x : X) (hxU : x ∈ U)
    (hU : ∀ W : X.affineOpens, W.1 ≤ U → I.ideal W = ⊤) :
    x ∉ SheafOfModules.supp (cokernel (idealPowSmulHom I n F)) := by
  have hzero : ∀ m : ↑(TopCat.Presheaf.stalk
      (cokernel (idealPowSmulHom I n F)).val.presheaf x), m = 0 := by
    intro m
    obtain ⟨V, hVU, hxV, t, ht⟩ := TopCat.Presheaf.exists_le_germ_eq
      (cokernel (idealPowSmulHom I n F)).val.presheaf m hxU
    have hepi : Epi (cokernel.π (idealPowSmulHom I n F)) :=
      inferInstanceAs (Epi (coequalizer.π (idealPowSmulHom I n F) 0))
    let hepi' : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _
      (cokernel.π (idealPowSmulHom I n F)) := hepi
    have hls := SheafOfModules.isLocallySurjective_toSheaf_of_epi
      (cokernel.π (idealPowSmulHom I n F))
    have hsieve := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (cokernel.π (idealPowSmulHom I n F))).hom (U := op V) t
    rw [Opens.mem_grothendieckTopology] at hsieve
    obtain ⟨W, f, ⟨u, hu⟩, hxW⟩ := hsieve x hxV
    -- `u` is a section of `I ^ n • F`, so its image under `cokernel.π` is zero.
    have hu2 : (cokernel (idealPowSmulHom I n F)).val.presheaf.map f.op t =
        (cokernel.π (idealPowSmulHom I n F)).app W u := hu.symm
    have hres : (cokernel (idealPowSmulHom I n F)).val.presheaf.map f.op t = 0 := by
      rw [hu2]
      have hcond := cokernel.condition (idealPowSmulHom I n F)
      have happ : ∀ y : Γ(idealPowSmulModule I n F, W),
          (cokernel.π (idealPowSmulHom I n F)).app W ((idealPowSmulHom I n F).app W y) = 0 := by
        intro y
        have h1 : (idealPowSmulHom I n F ≫ cokernel.π (idealPowSmulHom I n F)).app W y = 0 := by
          rw [hcond]
          simp
        simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h1
        exact h1
      have hgu : IsLocallyIn F (idealPowFamily I n F) u :=
        isLocallyIn_of_ideal_eq_top I n F hU (f.le.trans hVU) u
      rw [← idealPowSmulHom_app_mkSection I n F u hgu]
      exact happ _
    rw [← ht, ← TopCat.Presheaf.germ_res_apply
      (cokernel (idealPowSmulHom I n F)).val.presheaf f x hxW t, hres]
    exact map_zero _
  intro hmem
  exact (not_nontrivial_iff_subsingleton.mpr
      ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩)
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mp hmem)

end Stacks.AlgebraicGeometry.IdealPowerSmul

end
