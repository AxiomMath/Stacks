module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality

/-!
# Sections of the ideal sheaf over an open are the kernel of the map on sections

The ideal sheaf `Stacks.ClosedImmersion.idealSheaf f` of a morphism of schemes `f : A ⟶ B` is by
definition a kernel in `SheafOfModules`, namely of the structure-sheaf map
`𝒪_B ⟶ f_* 𝒪_A`. Its sections over an open are determined by their images in the structure
sheaf (`Stacks.Conormal.Locality.idealSheaf_section_injective`); this file says which sections of
the structure sheaf arise, namely exactly those killed by `f` on sections.

So over every open `O` of `B` the sections of the ideal sheaf are precisely
`RingHom.ker (f.app O).hom`, and over an affine open of `B`, for `f` quasi-compact, they are
precisely the sections of Mathlib's `AlgebraicGeometry.Scheme.Hom.ker`.

## Main results

* `Stacks.Conormal.AffineCotangent.Sections.exists_section_of_app_eq_zero`: for an arbitrary
  morphism of sheaves of modules over an arbitrary Grothendieck topology, a section of the source
  killed by the morphism lifts to the kernel.
* `Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero`: the image in the
  structure sheaf of a section of the ideal sheaf is killed by `f`.
* `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff`: a section `r` of `𝒪_B`
  over `O` is the image of a section of the ideal sheaf if and only if `f.app O r = 0`.
* `Stacks.Conormal.AffineCotangent.Sections.idealSheafSectionsEquivKer`: the resulting bijection
  of the sections of the ideal sheaf over `O` with `RingHom.ker (f.app O).hom`, whose underlying
  map is the inclusion (`idealSheafSectionsEquivKer_coe`).
* `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker_ideal`: over an
  affine open `V` of `B`, and for `f` quasi-compact, the sections of the ideal sheaf are the
  elements of `f.ker.ideal ⟨V, hV⟩`.

## Implementation notes

Evaluation of sheaves of modules at an object preserves finite limits
(`SheafOfModules.Finite.evaluationPreservesFiniteLimits`), hence kernels. The
comparison `CategoryTheory.Limits.PreservesKernel.iso` identifies the sections of a kernel with
the kernel of the map on sections, and `ModuleCat.kernelIsoKer` identifies the latter with
`LinearMap.ker`. `CategoryTheory.Limits.PreservesKernel.iso` needs
`CategoryTheory.Functor.PreservesZeroMorphisms` for the evaluation functor, which holds by `rfl`
and is the instance `evaluationPreservesZeroMorphisms`.

The ideal sheaf is written as `CategoryTheory.Limits.kernel` of
`SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toLRSHom.toShHom)`
rather than with `Stacks.IdealSheafRestrict.structureMap`. The two spellings of the category of
modules, `AlgebraicGeometry.Scheme.Modules B` and
`SheafOfModules (structureSheafRing B.toSheafedSpace)`, agree definitionally but not at the
elaborator's implicit transparency, so `exists_section_of_app_eq_zero` is used by application
rather than by `rw`, and `structureMap_app_eq` and `idealSheaf_ι_eq` record the `rfl`
identifications between the spellings.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe v u₁ v₁ u

namespace Stacks.Conormal.AffineCotangent.Sections

/-! ### Sections of a kernel of sheaves of modules -/

/-- Evaluation of sheaves of modules at an object preserves zero morphisms: the zero morphism is
zero in every section, definitionally.

Mathlib declares that `SheafOfModules.evaluation` preserves finite limits but not
that it preserves zero morphisms, and `CategoryTheory.Limits.PreservesKernel.iso` needs the
latter. -/
instance evaluationPreservesZeroMorphisms {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}} (X : Cᵒᵖ) :
    (SheafOfModules.evaluation R X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **A section killed by a morphism of sheaves of modules lifts to its kernel.**

Evaluation at `X` preserves kernels, so the sections of `kernel g` over `X` are the kernel of the
map on sections. `CategoryTheory.Limits.kernelComparison_comp_ι` describes the preservation
comparison through `CategoryTheory.Limits.kernel.ι`, and
`ModuleCat.kernelIsoKer_inv_kernel_ι` does the same for Mathlib's identification of a kernel in
`ModuleCat` with `LinearMap.ker`; composing the two inverses on the element `⟨r, hr⟩` produces
the lift. -/
theorem exists_section_of_app_eq_zero {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}} {M N : SheafOfModules.{v} R}
    (g : M ⟶ N) (X : Cᵒᵖ) (r : M.val.obj X) (hr : (g.val.app X).hom r = 0) :
    ∃ y : (kernel g).val.obj X, (kernel.ι g).val.app X y = r := by
  set G := SheafOfModules.evaluation R X with hG
  have hcomp : G.map (kernel.ι g) =
      (PreservesKernel.iso G g).hom ≫ kernel.ι (G.map g) := by
    rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  have hinv : ∀ z, (PreservesKernel.iso G g).hom.hom
      ((PreservesKernel.iso G g).inv.hom z) = z :=
    fun z => congr($((PreservesKernel.iso G g).inv_hom_id).hom z)
  refine ⟨((PreservesKernel.iso G g).inv.hom
    ((ModuleCat.kernelIsoKer (G.map g)).inv.hom ⟨r, hr⟩)), ?_⟩
  refine Eq.trans (congr($(hcomp).hom _)) ?_
  refine Eq.trans (congrArg (kernel.ι (G.map g)).hom (hinv _)) ?_
  exact congr($(ModuleCat.kernelIsoKer_inv_kernel_ι (G.map g)).hom (⟨r, hr⟩ : LinearMap.ker _))

/-- The image in the kernel's target of a section of a kernel is killed by the morphism. This is
`CategoryTheory.Limits.kernel.condition` read on sections. -/
theorem app_kernel_section_eq_zero {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}} {M N : SheafOfModules.{v} R}
    (g : M ⟶ N) (X : Cᵒᵖ) (y : (kernel g).val.obj X) :
    (g.val.app X).hom ((kernel.ι g).val.app X y) = 0 :=
  congr($(kernel.condition g).val.app X y)

/-! ### The ideal sheaf of a morphism of schemes -/

variable {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens)

/-- The structure-sheaf map of `f`, on sections over `O`, is the map on sections of `f`. This is
`Stacks.IdealSheafRestrict.structureMap_app` with the morphism spelled
`SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toLRSHom.toShHom)`. -/
theorem structureMap_app_eq (x : Γ(B, O)) :
    (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom f.toLRSHom.toShHom)).val.app (.op O) x = (f.app O).hom x :=
  rfl

/-- The ideal sheaf of `f` is the kernel of the structure-sheaf map
`SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toLRSHom.toShHom)`, so its
inclusion is `CategoryTheory.Limits.kernel.ι` of that morphism. -/
theorem idealSheaf_ι_eq :
    Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom =
      kernel (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom f.toLRSHom.toShHom)) :=
  rfl

/-- The image in the structure sheaf of a section of the ideal sheaf is killed by `f` on
sections. -/
theorem app_idealSheaf_section_eq_zero
    (x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O)) :
    (f.app O).hom ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom f.toLRSHom.toShHom))).val.app (.op O) x) = 0 :=
  app_kernel_section_eq_zero _ (.op O) x

/-- **The sections of the ideal sheaf over an open are the kernel of the map on sections.** A
section `r` of `𝒪_B` over `O` is the image of a section of the ideal sheaf exactly when
`f.app O r = 0`.

The lifting section is unique by `Stacks.Conormal.Locality.idealSheaf_section_injective`, so this
identifies the sections of the ideal sheaf with `RingHom.ker (f.app O).hom`; see
`idealSheafSectionsEquivKer`. -/
theorem exists_idealSheaf_section_iff (r : Γ(B, O)) :
    (∃ x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toLRSHom.toShHom))).val.app (.op O) x = r) ↔
      (f.app O).hom r = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact app_idealSheaf_section_eq_zero f O x
  · intro hr
    -- The morphism is named rather than left to unification: at the ideal sheaf the two
    -- spellings of the category of modules make `_` resolve in the wrong one.
    exact exists_section_of_app_eq_zero
      (g := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toLRSHom.toShHom))
      (.op O) r hr

/-- `exists_idealSheaf_section_iff` in `RingHom.ker` form. -/
theorem exists_idealSheaf_section_iff_mem_ker (r : Γ(B, O)) :
    (∃ x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toLRSHom.toShHom))).val.app (.op O) x = r) ↔
      r ∈ RingHom.ker (f.app O).hom :=
  exists_idealSheaf_section_iff f O r

/-- **The sections of the ideal sheaf over an open are `RingHom.ker (f.app O)`.** The map is the
inclusion into the structure sheaf, with its target cut down to the kernel; injectivity is
`Stacks.Conormal.Locality.idealSheaf_section_injective` — the inclusion is a monomorphism — and
surjectivity is `exists_idealSheaf_section_iff`.

This is a bijection and not a `LinearEquiv`: the sections of the ideal sheaf are a module over
`(structureSheafRing B.toSheafedSpace).val.obj (.op O)`, which is `Γ(B, O)` definitionally but not
syntactically, so the `Module Γ(B, O)` instance the linear-equivalence spelling asks for is not
found. The underlying map is `(kernel.ι _).val.app (.op O)`, a morphism of `ModuleCat`, hence
additive and `Γ(B, O)`-linear. -/
noncomputable def idealSheafSectionsEquivKer :
    (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O) ≃
      RingHom.ker (f.app O).hom :=
  Equiv.ofBijective
    (fun x => ⟨(kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom f.toLRSHom.toShHom))).val.app (.op O) x,
      app_idealSheaf_section_eq_zero f O x⟩)
    ⟨fun _ _ h => Locality.idealSheaf_section_injective f O (congrArg Subtype.val h),
      fun r => by
        obtain ⟨x, hx⟩ := (exists_idealSheaf_section_iff f O r.1).2 r.2
        exact ⟨x, Subtype.ext hx⟩⟩

/-- `idealSheafSectionsEquivKer` is the inclusion into the structure sheaf, on underlying
elements. -/
theorem idealSheafSectionsEquivKer_coe
    (x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O)) :
    (idealSheafSectionsEquivKer f O x : Γ(B, O)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom f.toLRSHom.toShHom))).val.app (.op O) x :=
  rfl

/-- **The sections of the ideal sheaf over an affine open are Mathlib's
`AlgebraicGeometry.Scheme.Hom.ker`.** For `f` quasi-compact, a section `r` of `𝒪_B` over an affine
open `O` is the image of a section of the ideal sheaf if and only if `r ∈ f.ker.ideal ⟨O, hO⟩`. -/
theorem exists_idealSheaf_section_iff_mem_ker_ideal [QuasiCompact f] (hO : IsAffineOpen O)
    (r : Γ(B, O)) :
    (∃ x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toLRSHom.toShHom))).val.app (.op O) x = r) ↔
      r ∈ f.ker.ideal ⟨O, hO⟩ := by
  rw [exists_idealSheaf_section_iff_mem_ker, f.ker_apply ⟨O, hO⟩]

end Stacks.Conormal.AffineCotangent.Sections

end
