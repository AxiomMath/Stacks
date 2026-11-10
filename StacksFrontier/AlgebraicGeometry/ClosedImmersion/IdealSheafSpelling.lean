module

public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two spellings of the ideal sheaf of a morphism of schemes

The ideal sheaf of a morphism `i : Z ⟶ X` of schemes is written in this development in two ways
that are *different objects*, not two names for one:

* as the **categorical kernel** of `𝒪_X ⟶ i_*𝒪_Z` in `CategoryTheory.SheafOfModules`, which is
  `Stacks.ClosedImmersion.idealSheaf` and is what `Stacks.Conormal.conormalSheaf` of Morphisms,
  Definition 01R2 pulls back; and
* as a **submodule of the structure sheaf given pointwise by `RingHom.ker`**, that is as a
  `(CategoryTheory.SheafOfModules.unit _).Submodule` whose ideal of sections over an open is the
  kernel of the ring map on sections.  This is the shape the sheaves of ideals of algebraic
  spaces are in — `AlgebraicGeometry.Space.definingIdealSheaf` of Stacks 03MB and
  `AlgebraicGeometry.Space.kernelIdealSheaf` — and the shape Stacks 01QQ states its third
  condition in.

This file identifies them, with no hypothesis on `i`.

## Main results

* `Stacks.Divisors.kernel_structureModuleHom_eq_idealSheaf`: the kernel of
  `Stacks.Divisors.structureModuleHom` is `Stacks.ClosedImmersion.idealSheaf` of the underlying
  morphism of ringed spaces.
* `Stacks.Divisors.mem_kerSubmodule_structureModuleHom_iff`: a section of `𝒪_X` lies in the
  sectionwise-kernel submodule of the structure map exactly when the ring map on sections kills
  it, so that submodule is pointwise `RingHom.ker (i.app V)`.
* `Stacks.Divisors.idealSheafIsoKerSubmodule`: the ideal sheaf of `i` is isomorphic to the
  sectionwise-kernel submodule of its structure map, compatibly with the two inclusions into
  `𝒪_X` (`Stacks.Divisors.idealSheafIsoKerSubmodule_hom_comp_ι`).
* `Stacks.Divisors.isIso_toIdealSheafOfKer` and
  `Stacks.Divisors.submoduleIsoIdealSheafOfKer`: any sheaf of ideals of `𝒪_X` whose ideal of
  sections over every open `V` is `RingHom.ker (i.app V)` is isomorphic to the ideal sheaf of `i`,
  compatibly with the inclusions (`Stacks.Divisors.submoduleIsoIdealSheafOfKer_hom_comp_ι`).

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Divisors

variable {Z X : Scheme.{u}}

/-! ### The two spellings of the categorical kernel -/

/-- **The ideal sheaf of Stacks 01QQ and the ideal sheaf of Stacks 01C2 are the same object.**
The kernel of `Stacks.Divisors.structureModuleHom i`, against which the equivalence
`Stacks.Divisors.isQuasicoherent_ideal_tfae` is stated, is
`Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of ringed spaces, against which
`Stacks.Conormal.conormalSheaf` is stated. -/
theorem kernel_structureModuleHom_eq_idealSheaf (i : Z ⟶ X) :
    kernel (structureModuleHom i) = Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom :=
  rfl

/-! ### The sections of the sectionwise-kernel submodule -/

/-- **The sectionwise-kernel submodule of the structure map is pointwise `RingHom.ker`.**  A
section of `𝒪_X` over an open `V` lies in `CategoryTheory.SheafOfModules.kerSubmodule` of the
structure map of `i` exactly when the ring map `Γ(X, V) ⟶ Γ(Z, i⁻¹V)` induced by `i` kills it. -/
theorem mem_kerSubmodule_structureModuleHom_iff (i : Z ⟶ X) (V : X.Opens) (s : Γ(X, V)) :
    s ∈ (SheafOfModules.kerSubmodule (structureModuleHom i)).obj (op V) ↔
      i.app V s = 0 :=
  SheafOfModules.mem_kerSubmodule (structureModuleHom i) (op V) s

/-! ### The ideal sheaf as a sectionwise kernel -/

/-- **The ideal sheaf of a morphism of schemes is the sectionwise-kernel submodule of its
structure map.** -/
@[sga "3 VIIA 1.3" "partial"]
def idealSheafIsoKerSubmodule (i : Z ⟶ X) :
    Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom ≅
      (SheafOfModules.kerSubmodule (structureModuleHom i)).toSheafOfModules :=
  Stacks.SheafOfModules.kernelIsoKerObj (structureModuleHom i)

/-- The isomorphism `Stacks.Divisors.idealSheafIsoKerSubmodule` is compatible with the two
inclusions into `𝒪_X`. -/
theorem idealSheafIsoKerSubmodule_hom_comp_ι (i : Z ⟶ X) :
    (idealSheafIsoKerSubmodule i).hom ≫
        (SheafOfModules.kerSubmodule (structureModuleHom i)).ι =
      kernel.ι (structureModuleHom i) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel (structureModuleHom i))
    (SheafOfModules.kerIsLimit (structureModuleHom i)) WalkingParallelPair.zero

/-! ### Sheaves of ideals presented pointwise by kernels -/

variable (J : (SheafOfModules.unit X.ringCatSheaf).Submodule)

/-- **A sheaf of ideals whose sections are the pointwise kernels of a morphism of schemes is its
ideal sheaf**, with no hypothesis on the morphism.  The comparison
`Stacks.Divisors.toIdealSheafOfKer` supplied by the universal property of the kernel is an
isomorphism. -/
theorem isIso_toIdealSheafOfKer (i : Z ⟶ X)
    (hJ : ∀ V : X.Opens, RingHom.ker (i.app V).hom = J.obj (op V)) :
    IsIso (toIdealSheafOfKer J i fun V => (hJ V).ge) := by
  have hmem : ∀ (V : X.Opens) (s : Γ(X, V)), s ∈ J.obj (op V) ↔ i.app V s = 0 := fun V s => by
    rw [← hJ V]; exact RingHom.mem_ker
  set φ := toIdealSheafOfKer J i fun V => (hJ V).ge with hφ
  have hfac : φ ≫ kernel.ι (structureModuleHom i) = J.ι := toIdealSheafOfKer_ι J i _
  have hmono : Mono φ := mono_of_mono_fac hfac
  have hepi : Epi φ := by
    refine Stacks.SheafOfModules.ComplexLocality.epi_of_isLocallySurjective φ
      (Presheaf.isLocallySurjective_of_surjective _ _ fun V y => ?_)
    have hy : i.app V.unop ((kernel.ι (structureModuleHom i)).val.app V y) = 0 :=
      Stacks.SheafOfModules.ComplexLocality.app_kernel_ι_app (structureModuleHom i) V y
    refine ⟨⟨_, (hmem V.unop _).2 hy⟩, ?_⟩
    have key := congrArg (fun f : J.toSheafOfModules ⟶ SheafOfModules.unit X.ringCatSheaf =>
      f.val.app V ⟨_, (hmem V.unop _).2 hy⟩) hfac
    exact Stacks.SheafOfModules.ComplexLocality.injective_kernel_ι_app
      (structureModuleHom i) V key
  exact isIso_of_mono_of_epi φ

/-- A sheaf of ideals of `𝒪_X` whose ideal of sections over every open is the kernel of the ring
map induced by `i` there is isomorphic, as a sheaf of `𝒪_X`-modules, to the ideal sheaf of `i`. -/
def submoduleIsoIdealSheafOfKer (i : Z ⟶ X)
    (hJ : ∀ V : X.Opens, RingHom.ker (i.app V).hom = J.obj (op V)) :
    J.toSheafOfModules ≅ Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom :=
  @asIso _ _ _ _ _ (isIso_toIdealSheafOfKer J i hJ)

/-- The isomorphism of `Stacks.Divisors.submoduleIsoIdealSheafOfKer` carries the inclusion of
the ideal sheaf into `𝒪_X` to the inclusion of the given sheaf of ideals. -/
theorem submoduleIsoIdealSheafOfKer_hom_comp_ι (i : Z ⟶ X)
    (hJ : ∀ V : X.Opens, RingHom.ker (i.app V).hom = J.obj (op V)) :
    (submoduleIsoIdealSheafOfKer J i hJ).hom ≫ kernel.ι (structureModuleHom i) = J.ι :=
  toIdealSheafOfKer_ι J i fun V => (hJ V).ge

end Stacks.Divisors

end
