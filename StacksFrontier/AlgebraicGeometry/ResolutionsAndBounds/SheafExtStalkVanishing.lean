module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.LocalFreeChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.RingCatStalk
public import StacksFrontier.AlgebraicGeometry.Modules.StalkRingComparison
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension

/-!
# Stalks of modules on a scheme along the local resolution

Let `X` be a scheme and `y ∈ X`. This file records the facts about the stalk functor
`M ↦ M_y`, from `𝒪_X`-modules to modules over the stalk of the structure sheaf, that the local
computation of the sheaf Ext's consumes:

* a module vanishing on a neighbourhood of `y` has zero stalk at `y`;
* a morphism whose kernel and cokernel vanish near `y` induces an isomorphism on stalks at `y`;
* the stalk of a finite free module is a finite free module;
* the syzygy sequence of `Stacks.SheafHomInjective.exists_syzygy` is short exact on stalks.

## Main results

* `Stacks.SheafHomInjective.isZero_stalk_of_vanishesOn`
* `Stacks.SheafHomInjective.isIso_stalk_map_of_vanishesOn`
* `Stacks.SheafHomInjective.projective_stalk_free`
* `Stacks.SheafHomInjective.shortExact_stalk_kernel`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafHomInjective

variable {X : Scheme.{u}}

/-- The stalk functor at `y` on `𝒪_X`-modules. -/
abbrev stk (y : X) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) y

/-- A module vanishing on a neighbourhood of `y` has zero stalk at `y`. -/
theorem isZero_stalk_of_vanishesOn
    {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)} {U : X.Opens}
    (h : VanishesOn E U) {y : X} (hy : y ∈ U) : IsZero ((stk y).obj E) := by
  have : Subsingleton ((stk y).obj E) := by
    refine ⟨fun a b => ?_⟩
    suffices ∀ m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.val.presheaf y, m = 0 by
      rw [this a, this b]
    intro m
    obtain ⟨V, hyV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq E.val.presheaf m
    rw [← TopCat.Presheaf.germ_res_apply E.val.presheaf (homOfLE (inf_le_left : V ⊓ U ≤ V)) y
      ⟨hyV, hy⟩ s]
    rw [h (V ⊓ U) inf_le_right (E.val.presheaf.map (homOfLE inf_le_left).op s)]
    exact map_zero _
  exact ModuleCat.isZero_of_subsingleton _

/-- A morphism whose kernel and cokernel vanish near `y` induces an isomorphism on stalks at
`y`. -/
theorem isIso_stalk_map_of_vanishesOn
    {E E' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)} (f : E ⟶ E')
    {U : X.Opens} (hk : VanishesOn (kernel f) U) (hc : VanishesOn (cokernel f) U) {y : X}
    (hy : y ∈ U) : IsIso ((stk y).map f) := by
  have hm : Mono ((stk y).map f) := Preadditive.mono_of_isZero_kernel _
    ((isZero_stalk_of_vanishesOn hk hy).of_iso (PreservesKernel.iso (stk y) f).symm)
  have he : Epi ((stk y).map f) := Preadditive.epi_of_isZero_cokernel _
    ((isZero_stalk_of_vanishesOn hc hy).of_iso (PreservesCokernel.iso (stk y) f).symm)
  exact isIso_of_mono_of_epi _

/-- On stalks, the sequence `0 ⟶ ker π ⟶ P ⟶ A ⟶ 0` is short exact at `y` when the cokernel of
`π` vanishes near `y`. -/
theorem shortExact_stalk_kernel
    {P A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)} (π : P ⟶ A)
    {U : X.Opens} (hc : VanishesOn (cokernel π) U) {y : X} (hy : y ∈ U) :
    ((ShortComplex.mk (kernel.ι π) π (kernel.condition π)).map (stk y)).ShortExact := by
  have hex : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
  have he : Epi ((stk y).map π) := Preadditive.epi_of_isZero_cokernel _
    ((isZero_stalk_of_vanishesOn hc hy).of_iso (PreservesCokernel.iso (stk y) π).symm)
  refine ShortComplex.ShortExact.mk' (hex.map (stk y)) ?_ he
  show Mono ((stk y).map (kernel.ι π))
  infer_instance

/-- **The stalk of a finite free module is free** on the same index type. -/
def basisStalkFree (ι : Type u) [Finite ι] (y : X) :
    Module.Basis ι (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj y)
      (ToType (TopCat.Presheaf.stalk
        (SheafOfModules.free (R := X.ringCatSheaf) ι).val.presheaf y)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let b := Module.Basis.ofEquivFun
    (Stacks.SheafOfModules.freeStalkEquiv (Osharp := X.sheaf) (ι := ι) y).symm
  exact Stacks.StalkFiniteType.basisRingCatStalk
    (SheafOfModules.free (R := X.ringCatSheaf) ι : X.Modules) y b

/-- **The stalk of a finite free module is projective.** -/
theorem projective_stalk_free (ι : Type u) [Finite ι] (y : X) :
    Projective ((stk y).obj (SheafOfModules.free ι)) :=
  ModuleCat.projective_of_free (basisStalkFree ι y)

/-- **Stalks on a regular scheme have bounded projective dimension**: if `𝒪_{X,y}` is a regular
local ring of dimension at most `d`, then every module over the stalk of the structure sheaf
has projective dimension at most `d` ([Stacks, Tag 00O7]). -/
theorem hasProjectiveDimensionLE_stalk (y : X) [IsRegularLocalRing (X.presheaf.stalk y)] {d : ℕ}
    (hd : ringKrullDim (X.presheaf.stalk y) ≤ d)
    (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj y)) :
    HasProjectiveDimensionLE M d := by
  have : IsRegularLocalRing ((TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj y : RingCat.{u}) : Type u) :=
    IsRegularLocalRing.of_ringEquiv (StacksDraft.StalkRingComparison.stalkRingEquiv X y).symm
  have hd' : ringKrullDim ((TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj y : RingCat.{u}) : Type u) ≤ d := by
    rw [ringKrullDim_eq_of_ringEquiv (StacksDraft.StalkRingComparison.stalkRingEquiv X y)]
    exact hd
  exact (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE hd').2 M

/-- A projective quotient of a finite free module over the stalk ring is free on a finite basis:
the stalk ring is local. -/
theorem exists_basis_of_projective [IsLocallyNoetherian X] {y : X}
    {F M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj y)}
    {ι : Type u} [Finite ι]
    (b : Module.Basis ι (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj y) F)
    (p : F ⟶ M) (hp : Epi p) (hM : Projective M) :
    ∃ (ρ : Type u) (_ : Finite ρ), Nonempty (Module.Basis ρ (TopCat.Presheaf.stalk
      (C := RingCat.{u}) X.ringCatSheaf.obj y) M) := by
  let e := Stacks.StalkFiniteType.ringCatStalkRingEquiv (X := X) y
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} e.symm
  let F' := E.functor.obj F
  let M' := E.functor.obj M
  have hM' : Projective M' := E.toAdjunction.map_projective M inferInstance
  let : Module (X.presheaf.stalk y) F := F'.isModule
  let bF : Module.Basis ι (X.presheaf.stalk y) F' := b.mapCoeffs e (fun c x => by
    show e.symm (e c) • x = c • x
    rw [RingEquiv.symm_apply_apply])
  have : Module.Finite (X.presheaf.stalk y) F' := Module.Finite.of_basis bF
  have hp' : Epi (E.functor.map p) := inferInstance
  have : Module.Finite (X.presheaf.stalk y) M' :=
    Module.Finite.of_surjective (E.functor.map p).hom
      ((ModuleCat.epi_iff_surjective (E.functor.map p)).1 hp')
  have : Module.Projective (X.presheaf.stalk y) M' := ModuleCat.projective_of_module_projective M'
  have : Module.Free (X.presheaf.stalk y) M' := Module.free_of_flat_of_isLocalRing
  let b₀ := Module.Free.chooseBasis (X.presheaf.stalk y) M'
  let : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj y) M' := M.isModule
  exact ⟨Module.Free.ChooseBasisIndex (X.presheaf.stalk y) M', inferInstance,
    ⟨b₀.mapCoeffs e.symm (fun c x => rfl)⟩⟩

end Stacks.SheafHomInjective

end
