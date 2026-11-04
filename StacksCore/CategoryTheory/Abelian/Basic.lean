module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.RegularCategory.Basic
import StacksCore.Tactic.StacksAttribute

/-! ## Abelian Categories -/

add_to_stacks 0109 CategoryTheory.Abelian
add_to_stacks 010D CategoryTheory.Abelian.hasFiniteLimits
add_to_stacks 010D CategoryTheory.Abelian.hasFiniteColimits
add_to_stacks 05PJ CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct
add_to_stacks 05PJ CategoryTheory.Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout
add_to_stacks 05PK CategoryTheory.Abelian.epi_pullback_of_epi_f
add_to_stacks 05PK CategoryTheory.Abelian.mono_pushout_of_mono_g

@[expose] public section

/-! ### Ported from mathlib#41769

**Everything below is temporary and is expected to be deleted.** It is the
`Abelian/Basic` part of mathlib#41769 (mckoen, `feat(CategoryTheory/Abelian/Subobject):
correspondence theorem for subobjects in abelian categories`, open as of 2026-09-11), ported
with the upstream names, statements and proofs: the comparison of a monomorphism with the
kernel of its cokernel (and dually), and the pullback of a monomorphism as a kernel. Delete
everything below this header once the pin includes that pull request; every name then
resolves to the mathlib declaration. -/

namespace CategoryTheory.Abelian

open Limits

variable {C : Type*} [Category* C] [Abelian C]

section

variable {X Y : C} (f : X ⟶ Y)

@[simp]
lemma inv_factorThruImage_comp [Mono f] :
    inv (Abelian.factorThruImage f) ≫ f = kernel.ι (cokernel.π f) := by
  rw [← cancel_epi (Abelian.factorThruImage f)]
  simp

@[simp]
lemma comp_inv_factorThruCoimage [Epi f] :
    f ≫ inv (Abelian.factorThruCoimage f) = cokernel.π (kernel.ι f) := by
  rw [← cancel_mono (Abelian.factorThruCoimage f)]
  simp

end

/-- If `f : X ⟶ Y` is a monomorphism in an abelian category, then `X ≅ kernel (cokernel.π f)`.
Ported from mathlib#41769; delete when the pin includes it. -/
noncomputable def isoKernelCokernel {X Y : C} (f : X ⟶ Y) [Mono f] :
    X ≅ kernel (cokernel.π f) :=
  IsLimit.conePointUniqueUpToIso
    (t := KernelFork.ofι (kernel.ι (cokernel.π f)) (kernel.condition (cokernel.π f)))
    (monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)) (cokernelIsCokernel f))
    (kernelIsKernel (cokernel.π f))

/-- If `f : X ⟶ Y` is an epimorphism in an abelian category, then `Y ≅ cokernel (kernel.ι f)`.
Ported from mathlib#41769; delete when the pin includes it. -/
noncomputable def isoCokernelKernel {X Y : C} (f : X ⟶ Y) [Epi f] :
    Y ≅ cokernel (kernel.ι f) :=
  IsColimit.coconePointUniqueUpToIso
    (t := CokernelCofork.ofπ (cokernel.π (kernel.ι f)) (cokernel.condition (kernel.ι f)))
    (epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι f) (kernel.condition f)) (kernelIsKernel f))
    (cokernelIsCokernel (kernel.ι f))

@[simp]
lemma isoKernelCokernel_hom_comp {X Y : C} (f : X ⟶ Y) [Mono f] :
    (isoKernelCokernel f).hom ≫ kernel.ι (cokernel.π f) = f :=
  (IsLimit.conePointUniqueUpToIso_hom_comp _ _) WalkingParallelPair.zero

@[simp]
lemma isoKernelCokernel_inv_comp {X Y : C} (f : X ⟶ Y) [Mono f] :
    (isoKernelCokernel f).inv ≫ f = kernel.ι (cokernel.π f) :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _) WalkingParallelPair.zero

@[simp]
lemma comp_isoCokernelKernel_hom {X Y : C} (f : X ⟶ Y) [Epi f] :
    f ≫ (isoCokernelKernel f).hom = cokernel.π (kernel.ι f) :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom
    (epiIsCokernelOfKernel _ (kernelIsKernel f)) (cokernelIsCokernel _)) WalkingParallelPair.one

@[simp]
lemma comp_isoCokernelKernel_inv {X Y : C} (f : X ⟶ Y) [Epi f] :
    cokernel.π (kernel.ι f) ≫ (isoCokernelKernel f).inv = f :=
  (IsColimit.comp_coconePointUniqueUpToIso_inv
    (epiIsCokernelOfKernel _ (kernelIsKernel f)) (cokernelIsCokernel _)) WalkingParallelPair.one

section PullbackKernel

variable {P X' Y' Z : C} {fst : P ⟶ X'} {snd : P ⟶ Y'} {i : X' ⟶ Z} {j : Y' ⟶ Z}

/-- In an abelian category, the pullback of a monomorphism `i` along `j` is a kernel of
`j ≫ cokernel.π i`. Ported from mathlib#41769; delete when the pin includes it. -/
noncomputable def isLimitKernelForkOfIsPullback (sq : IsPullback fst snd i j) [Mono i] :
    IsLimit (KernelFork.ofι (f := j ≫ cokernel.π i) snd (by simp [← sq.w_assoc])) := by
  let : Mono snd := PullbackCone.mono_snd_of_is_pullback_of_mono sq.isLimit
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  exact ⟨sq.lift (monoLift i (k ≫ j) (by rwa [← Category.assoc] at hk)) k (by simp), by simp⟩

/-- In an abelian category, the pullback of a monomorphism `i` along `j` is isomorphic to the
kernel of `j ≫ cokernel.π i`. Ported from mathlib#41769; delete when the pin includes it. -/
noncomputable def isoKernelOfIsPullback (sq : IsPullback fst snd i j) [Mono i] :
    P ≅ kernel (j ≫ cokernel.π i) :=
  IsLimit.conePointUniqueUpToIso
    (t := KernelFork.ofι (kernel.ι (j ≫ cokernel.π i)) (kernel.condition (j ≫ cokernel.π i)))
    (isLimitKernelForkOfIsPullback sq) (kernelIsKernel (j ≫ cokernel.π i))

@[simp]
lemma isoKernelOfIsPullback_hom_comp (sq : IsPullback fst snd i j) [Mono i] :
    (isoKernelOfIsPullback sq).hom ≫ kernel.ι (j ≫ cokernel.π i) = snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

@[simp]
lemma isoKernelOfIsPullback_inv_comp (sq : IsPullback fst snd i j) [Mono i] :
    (isoKernelOfIsPullback sq).inv ≫ snd = kernel.ι (j ≫ cokernel.π i) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

end PullbackKernel

end CategoryTheory.Abelian

/-! ### Ported from mathlib#41424

**Everything in this section is temporary and is expected to be deleted.** It is the
`Abelian/Basic` part of mathlib#41424 (mckoen, `feat(CategoryTheory/Abelian): subobjects in an
abelian category form a modular lattice`, stacked on #41769, open as of 2026-09-15), ported with
the upstream name and statement. The proof is in term mode rather than upstream's tactic block,
whose goal `MorphismProperty.regularEpi C g` is not type-correct at implicit transparency. Delete
it once the pin includes that pull request; the name then resolves to the mathlib declaration. -/

namespace CategoryTheory.Abelian

open Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- An abelian category is regular: every epimorphism is regular, and epimorphisms are stable
under pullback. Ported from mathlib#41424; delete when the pin includes it. -/
instance (priority := 100) abelianRegular : Regular C where
  hasCoequalizer_of_isKernelPair := inferInstance
  regularEpiIsStableUnderBaseChange := .mk' fun _ _ _ f g _ hg ↦
    have := (MorphismProperty.regularEpi_iff g).1 hg
    (MorphismProperty.regularEpi_iff _).2 (IsRegularEpiCategory.regularEpiOfEpi (pullback.fst f g))

end CategoryTheory.Abelian
