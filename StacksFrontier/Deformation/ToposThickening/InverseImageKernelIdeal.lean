module

public import StacksFrontier.Deformation.ToposThickening.InverseImageExtensionSolutions
public import StacksFrontier.Deformation.ToposThickening.LiftingBetweenThickenings

/-!
# The inverse image of an ideal identified with a module

Let `π : 𝒜' ⟶ 𝒜` be a morphism of sheaves of commutative rings on a site, and let `ℱ` be an
`𝒜`-module together with an `𝒜'`-linear inclusion `ι : ℱ ⟶ 𝒜'` whose sections are exactly the
sections of `𝒜'` killed by `π`: the situation of the ideal of a first order thickening, or of the
inverse image of the ideal of a base thickening, in the identified-topoi convention of
`Deformation.ToposThickening.RingedToposExtensionProblem`.

This file records two facts about that situation.

* The kernel of `π` has square zero on every object: a product `ι(m) ι(n)` is `ι(π(ι m) · n)`,
  which vanishes. This is `Deformation.ToposThickening.sq_ker_eq_bot_of_kernelIncl`.
* Along a morphism of ringed topoi `g`, the inverse image `g⁻¹ℱ` is again identified with the
  kernel of `g⁻¹π : g⁻¹𝒜' ⟶ g⁻¹𝒜`, through the inverse image of `ι`. This is the left exactness of
  `g⁻¹`, `existsUnique_invKernelInclOf`. It is the argument of
  `Deformation.ToposThickening.InverseImageExtension.existsUnique_invKernelIncl`, stated there for
  the ideal of a solution of a problem with trivial base, carried out for an arbitrary such
  `(π, ℱ, ι)`.

## Main definitions

* `Deformation.ToposThickening.InverseImageExtension.invKernelInclOf`: the inclusion
  `g⁻¹ℱ ⟶ g⁻¹𝒜'`.

## Main results

* `Deformation.ToposThickening.InverseImageExtension.invKernelInclOf_mem` and
  `existsUnique_invKernelInclOf`: `g⁻¹ℱ` is the kernel of `g⁻¹π`, section by section.
* `Deformation.ToposThickening.sq_ker_eq_bot_of_kernelIncl`: an ideal identified with a module
  in this way has square zero.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.ToposPullback (pullbackRingSheafMap pullbackModuleUnitIso
  isPullback_terminal_of_sections existsUnique_sections_of_isPullback
  sections_comp_eq_zero_of_isPullback)
open Stacks.Sheaves.RingedToposModules (inverseImageModules pullbackModuleObjRestrictScalarsIso)

universe v u w

namespace Deformation.ToposThickening

section SquareZero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A' A : Sheaf J CommRingCat.{w}} (π : A' ⟶ A)
  {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf A)}
  (ι : (SheafOfModules.restrictScalars (R := Stacks.SheafOfModules.Tensor.ringSheaf A')
      (R' := Stacks.SheafOfModules.Tensor.ringSheaf A)
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map π)).obj F ⟶
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A'))

/-- A section of `𝒜'` times the image of a section of `ℱ` is the image of the product, the
section of `𝒜'` acting on `ℱ` through `π`. -/
theorem mul_kernelIncl {U : Cᵒᵖ} (a : A'.obj.obj U) (m : F.val.obj U) :
    a * (show A'.obj.obj U from ι.val.app U m) =
      (show A'.obj.obj U from ι.val.app U (toRingSection J (π.hom.app U a) • m)) :=
  ((ι.val.app U).hom.map_smul' (toRingSection J a) m).symm

/-- **An ideal identified with a module has square zero.** If the inclusion `ι : ℱ ⟶ 𝒜'` is
`𝒜'`-linear, lands in the kernel of `π` and exhausts it, then that kernel has square zero on
every object. -/
theorem sq_ker_eq_bot_of_kernelIncl
    (hzero : ∀ (U : Cᵒᵖ) (m : F.val.obj U),
      π.hom.app U (show A'.obj.obj U from ι.val.app U m) = 0)
    (huniv : ∀ (U : Cᵒᵖ) (a : A'.obj.obj U), π.hom.app U a = 0 →
      ∃! m : F.val.obj U, (show A'.obj.obj U from ι.val.app U m) = a)
    (U : Cᵒᵖ) : (RingHom.ker (π.hom.app U).hom) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  obtain ⟨m, rfl, -⟩ := huniv U r (RingHom.mem_ker.1 hr)
  obtain ⟨n, rfl, -⟩ := huniv U s (RingHom.mem_ker.1 hs)
  rw [Ideal.mem_bot, mul_kernelIncl π ι, hzero U m]
  have h0 : toRingSection J (0 : A.obj.obj U) = 0 := rfl
  rw [h0, zero_smul]
  exact map_zero _

end SquareZero

namespace InverseImageExtension

variable {Y X : RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]
  {A' A : Sheaf X.J CommRingCat.{u}} (π : A' ⟶ A)
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)}
  (ι : (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map π)).obj F ⟶
    SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj A'))

/-- The inclusion `ℱ ⟶ 𝒜'`, on underlying sheaves of sets. -/
noncomputable def kernelInclSheafSetsOf :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf A')
        ((SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{u} RingCat.{u})).map π)).obj F) ⟶
      Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf A') :=
  (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf A')).map ι

variable {π ι}
  (hzero : ∀ (U : X.Cᵒᵖ) (m : F.val.obj U),
    π.hom.app U (show A'.obj.obj U from ι.val.app U m) = 0)
  (huniv : ∀ (U : X.Cᵒᵖ) (a : A'.obj.obj U), π.hom.app U a = 0 →
    ∃! m : F.val.obj U, (show A'.obj.obj U from ι.val.app U m) = a)

omit [X.J.HasSheafCompose (forget CommRingCat.{u})] in
include hzero huniv in
/-- **`ℱ` is the kernel of `π`**, as a pullback square of sheaves of sets: the fibre of
`𝒜' ⟶ 𝒜` over the zero section. -/
theorem isPullback_kernelInclSheafSetsOf :
    IsPullback (kernelInclSheafSetsOf π ι) (terminal.from _)
      ((sheafCompose X.J (forget RingCat.{u})).map
        ((Stacks.forgetCommRingSheaf X.J).map π))
      (Sheaf.ringZeroHom (Stacks.SheafOfModules.Tensor.ringSheaf A)) := by
  refine isPullback_terminal_of_sections _ _ _ ?_ (fun U b b' h ↦ ?_) fun U a ha ↦ ?_
  · refine Sheaf.hom_ext_sections fun U b ↦ ?_
    rw [(Sheaf.sectionsFunctor X.J U).map_comp_apply]
    exact hzero U b
  · obtain ⟨n, -, hn⟩ := huniv U (ι.val.app U b) (hzero U b)
    exact (hn b rfl).trans (hn b' h.symm).symm
  · obtain ⟨n, hn, -⟩ := huniv U a ha
    exact ⟨n, hn⟩

variable [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] (g : RingedToposHom Y X)

/-- `g⁻¹ℱ`, as a `g⁻¹𝒜`-module. -/
noncomputable abbrev invIdealOf (F : SheafOfModules.{u}
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj A)) :=
  (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf A)).obj F

variable (π ι) in
/-- **The inclusion `g⁻¹ℱ ⟶ g⁻¹𝒜'`**: the inverse image of `ι`, read through the comparison of
the inverse image of a restriction of scalars with the restriction of scalars of the inverse
image, and the identification of the inverse image of a unit module with the unit module of the
inverse image. -/
noncomputable def invKernelInclOf :
    (SheafOfModules.restrictScalars ((sheafCompose Y.J
          (forget₂ CommRingCat.{u} RingCat.{u})).map ((invImage g).map π))).obj
        (invIdealOf g F) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj A')) :=
  eqToHom (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj (invIdealOf g F))
      (ringMap_invImage_map g π)) ≫
    (pullbackModuleObjRestrictScalarsIso Y.J g.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf X.J).map π) F).hom ≫
      (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf A')).map ι ≫
        (pullbackModuleUnitIso Y.J g.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf A')).inv

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] in
variable (π ι) in
/-- The inclusion of `g⁻¹ℱ` is, on sections, the inverse image of the inclusion of `ℱ`. -/
theorem invKernelInclOf_val_app (U : Y.Cᵒᵖ) (a : (invIdealOf g F).val.obj U) :
    (invKernelInclOf π ι g).val.app U a =
      (Sheaf.sectionsFunctor Y.J U).map
        (g.toToposHom.inverseImage.map (kernelInclSheafSetsOf π ι)) a :=
  congrArg (fun y ↦ (((pullbackModuleObjRestrictScalarsIso Y.J g.toToposHom.inverseImage
      ((Stacks.forgetCommRingSheaf X.J).map π) F).hom ≫
      (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf A')).map ι ≫
        (pullbackModuleUnitIso Y.J g.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf A')).inv).val.app U) y)
    (restrictScalars_eqToHom_val_app (ringMap_invImage_map g π) (invIdealOf g F) U a)

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] in
include hzero huniv in
/-- **The inclusion of `g⁻¹ℱ` is killed by `g⁻¹π`.** -/
theorem invKernelInclOf_mem (U : Y.Cᵒᵖ) (a : (invIdealOf g F).val.obj U) :
    ((invImage g).map π).hom.app U
        (show ((invImage g).obj A').obj.obj U from (invKernelInclOf π ι g).val.app U a) = 0 := by
  rw [invKernelInclOf_val_app]
  have h := sections_comp_eq_zero_of_isPullback Y.J g.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf X.J).map π) _ (isPullback_kernelInclSheafSetsOf hzero huniv) U a
  rw [← ringMap_invImage_map g π] at h
  exact h

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] in
include hzero huniv in
/-- **A section of `g⁻¹𝒜'` killed by `g⁻¹π` is the image of exactly one section of `g⁻¹ℱ`**:
the left exactness of `g⁻¹`. -/
theorem existsUnique_invKernelInclOf (U : Y.Cᵒᵖ) (x : ((invImage g).obj A').obj.obj U)
    (hx : ((invImage g).map π).hom.app U x = 0) :
    ∃! a : (invIdealOf g F).val.obj U,
      (show ((invImage g).obj A').obj.obj U from (invKernelInclOf π ι g).val.app U a) = x := by
  have hx' : (Sheaf.sectionsFunctor Y.J U).map ((sheafCompose Y.J (forget RingCat.{u})).map
      (pullbackRingSheafMap Y.J g.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf X.J).map π))) x = 0 := by
    rw [← ringMap_invImage_map g π]
    exact hx
  obtain ⟨a, ha, huniq⟩ := existsUnique_sections_of_isPullback Y.J g.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf X.J).map π) _ (isPullback_kernelInclSheafSetsOf hzero huniv) U x
    hx'
  exact ⟨a, (invKernelInclOf_val_app π ι g U a).trans ha,
    fun b hb ↦ huniq b ((invKernelInclOf_val_app π ι g U b).symm.trans hb)⟩

end InverseImageExtension

end Deformation.ToposThickening

end
