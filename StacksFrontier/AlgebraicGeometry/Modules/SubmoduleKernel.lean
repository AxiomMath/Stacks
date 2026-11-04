module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# The embedded kernel of a morphism of sheaves of modules is its categorical kernel

`Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule f` is the sectionwise kernel of a
morphism `f` of
sheaves of modules, packaged as an embedded submodule sheaf of the source. This file identifies
it with the categorical `CategoryTheory.Limits.kernel f`, and provides the identification both
for a general sheaf of modules and in the spelling used for modules on a scheme.

## Main definitions

* `Stacks.AlgebraicGeometry.kernelSubmoduleIso`: the embedded kernel of a morphism of sheaves of
  modules is its categorical kernel.
* `AlgebraicGeometry.SheafOfModules.Submodule.asModules`,
  `AlgebraicGeometry.SheafOfModules.Submodule.ιModules`,
  `AlgebraicGeometry.SheafOfModules.Submodule.zeroHom` and
  `AlgebraicGeometry.SheafOfModules.Submodule.kernelIso`: a submodule sheaf as an object of
  `X.Modules`, its inclusion into the ambient module, the zero morphism out of it, and the
  identification of the embedded kernel with the categorical kernel, all stated for the category
  `X.Modules` of modules on a scheme.

## Main results

* `Stacks.AlgebraicGeometry.kernelSubmodule_ι_comp`: the inclusion of the embedded kernel
  composed with the morphism is zero.
* `Stacks.AlgebraicGeometry.isIso_kernelSubmodule_lift`: the induced map from the embedded kernel
  to the categorical kernel is an isomorphism.
* `AlgebraicGeometry.SheafOfModules.Submodule.kernelIso_hom_comp_ι`: that identification is
  compatible with the two inclusions into the source.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, `AlgebraicGeometry.Scheme.Modules.Hom` is a second
`def`, and `AlgebraicGeometry.Scheme.ringCatSheaf` has type `TopCat.Sheaf RingCat ↑X` which is
only definitionally — not reducibly — `Sheaf (Opens.grothendieckTopology ↥X) RingCat`. Instance
search therefore cannot assign a metavariable of type `Sheaf ?J RingCat` to `X.ringCatSheaf`, so
a term that mixes `X.Modules` with the generic `SheafOfModules X.ringCatSheaf` has no
`HasZeroMorphisms`, no `Mono` and no `HasKernel` instance available to it: the very first symptom
is that the numeral `0` has no `OfNat` instance at the type
`(kernelSubmodule f).toSheafOfModules ⟶ G`.

The way around it taken here is to prove everything with the ring sheaf a *variable*
`R : Sheaf J RingCat`, where no such spelling mismatch can arise, and then to restate each
result with its source object ascribed at `X.Modules`, the ascription being accepted because a
definition body is checked at default transparency. `asModules`, `ιModules`, `zeroHom` and
`kernelIso` are those restatements; downstream files should use them rather than mixing the two
spellings.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

noncomputable section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : CategoryTheory.Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}

/-- A morphism of sheaves of modules which is an isomorphism on every object of the site is an
isomorphism. -/
public lemma isIso_of_isIso_val_app {f : M ⟶ N} (h : ∀ U, IsIso (f.val.app U)) : IsIso f := by
  rw [← isIso_iff_of_reflects_iso f (SheafOfModules.forget R),
    ← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf R.obj),
    NatTrans.isIso_iff_isIso_app]
  intro U
  have := h U
  exact Functor.map_isIso (forget₂ (ModuleCat _) AddCommGrpCat) (f.val.app U)

/-- The inclusion of a submodule sheaf into the ambient sheaf of modules is a monomorphism.

This restates the `Mono` instance with the ring sheaf a variable, so that it can be applied to a
concrete ring sheaf whose type is only definitionally a sheaf for the relevant topology. -/
public lemma mono_ι (P : SheafOfModules.Submodule M) : Mono P.ι := inferInstance

/-- The inclusion of the embedded kernel of `f`, followed by `f`, is zero. -/
public lemma kernelSubmodule_ι_comp (f : M ⟶ N) : (kernelSubmodule f).ι ≫ f = 0 := by
  ext U s
  change (f.val.app U).hom (((kernelSubmodule f).ι.val.app U).hom s) = 0
  exact LinearMap.mem_ker.mp s.property

/-- The map from the embedded kernel of `f` to its categorical kernel induced by the inclusion is
an isomorphism.

Sectionwise it is the inclusion of `LinearMap.ker (f.val.app U)`, which is injective, and its
image is all of the kernel because the sections of the categorical kernel inject into those of
the source with image the sectionwise kernel. -/
public lemma isIso_kernelSubmodule_lift (f : M ⟶ N) :
    IsIso (kernel.lift f (kernelSubmodule f).ι (kernelSubmodule_ι_comp f)) := by
  set K := kernelSubmodule f with hK
  set e := kernel.lift f K.ι (kernelSubmodule_ι_comp f) with he
  have heq : e ≫ kernel.ι f = K.ι := kernel.lift_ι f K.ι (kernelSubmodule_ι_comp f)
  apply isIso_of_isIso_val_app
  intro U
  let E := SheafOfModules.evaluation.{u} R U
  have hE : E.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let k : E.obj (kernel f) ≅ kernel (E.map f) := PreservesKernel.iso E f
  have hfac : E.map (kernel.ι f) = k.hom ≫ kernel.ι (E.map f) := by
    calc
      E.map (kernel.ι f) = 𝟙 _ ≫ E.map (kernel.ι f) := by simp
      _ = k.hom ≫ k.inv ≫ E.map (kernel.ι f) := by simp
      _ = k.hom ≫ kernel.ι (E.map f) := by rw [PreservesKernel.iso_inv_ι]
  have hmonoE : Mono (E.map (kernel.ι f)) := by rw [hfac]; infer_instance
  have hmono : Mono ((kernel.ι f).val.app U) := hmonoE
  have hinj : Function.Injective ((kernel.ι f).val.app U).hom :=
    (ModuleCat.mono_iff_injective _).1 hmono
  have happ : ∀ {A B C : SheafOfModules.{u} R} (a : A ⟶ B) (b : B ⟶ C) (x : ↑(A.val.obj U)),
      (b.val.app U).hom ((a.val.app U).hom x) = ((a ≫ b).val.app U).hom x := fun _ _ _ => rfl
  have hcomp : ∀ x : ↑(K.toSheafOfModules.val.obj U),
      ((kernel.ι f).val.app U).hom ((e.val.app U).hom x) = x.val := fun x => by
    rw [happ, heq]; rfl
  have hzero : ∀ y : ↑((kernel f).val.obj U),
      (f.val.app U).hom (((kernel.ι f).val.app U).hom y) = 0 := fun y => by
    rw [happ, kernel.condition]; rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => Subtype.ext ?_,
    fun y => ⟨⟨_, LinearMap.mem_ker.2 (hzero y)⟩, hinj (hcomp _)⟩⟩
  rw [← hcomp a, ← hcomp b, hab]

/-- The embedded kernel of a morphism of sheaves of modules is its categorical kernel. -/
public def kernelSubmoduleIso (f : M ⟶ N) : (kernelSubmodule f).toSheafOfModules ≅ kernel f :=
  have := isIso_kernelSubmodule_lift f
  asIso (kernel.lift f (kernelSubmodule f).ι (kernelSubmodule_ι_comp f))

/-- The identification of the embedded kernel with the categorical kernel is compatible with the
two inclusions into the source. -/
public lemma kernelSubmoduleIso_hom_comp_ι (f : M ⟶ N) :
    (kernelSubmoduleIso f).hom ≫ kernel.ι f = (kernelSubmodule f).ι :=
  kernel.lift_ι f (kernelSubmodule f).ι (kernelSubmodule_ι_comp f)

end

end Stacks.AlgebraicGeometry

namespace AlgebraicGeometry.SheafOfModules.Submodule

noncomputable section

open Stacks.AlgebraicGeometry

variable {X : Scheme.{u}} {M : X.Modules}

/-- The sheaf of modules associated to a submodule of a sheaf of modules on a scheme, as an
object of `X.Modules`.

The type of `SheafOfModules.Submodule.toSheafOfModules` is the generic
`SheafOfModules X.ringCatSheaf`, and no instance registered for `X.Modules` applies to that
spelling; being an `abbrev` whose stated type is `X.Modules`, this does not have that defect. -/
public noncomputable abbrev asModules (N : SheafOfModules.Submodule M) : X.Modules :=
  N.toSheafOfModules

/-- The inclusion of a submodule sheaf into the ambient module, with its source ascribed at
`X.Modules`.

`SheafOfModules.Submodule.ι` has the generic `SheafOfModules X.ringCatSheaf` as the type of its
source, and no instance of `X.Modules` applies to that spelling; this re-export is what makes
the inclusion usable in a term that also mentions `X.Modules`. -/
public def ιModules (N : SheafOfModules.Submodule M) : N.asModules ⟶ M :=
  N.ι

/-- The underlying morphism of presheaves of `N.ιModules` is the inclusion of the submodule
presheaf `N.toSubmodule`. -/
@[simp]
public lemma ιModules_val (N : SheafOfModules.Submodule M) :
    N.ιModules.val = N.toSubmodule.ι :=
  rfl

/-- The inclusion of a submodule sheaf is a monomorphism, stated at `X.Modules`. -/
public instance mono_ιModules (N : SheafOfModules.Submodule M) : Mono N.ιModules :=
  mono_ι N

/-- A section of a submodule sheaf whose inclusion into the ambient module vanishes is zero. -/
public lemma eq_zero_of_ιModules_app_eq_zero (N : _root_.SheafOfModules.Submodule M)
    (W : X.Opens)
    (s : Γ(N.asModules, W)) (h : (N.ιModules).app W s = 0) : s = 0 :=
  Subtype.ext h

/-- The inclusion of a submodule sheaf carries a section into the submodule of sections. -/
public lemma mem_of_ιModules_app (N : _root_.SheafOfModules.Submodule M) (W : X.Opens)
    (s : Γ(N.asModules, W)) : (N.ιModules).app W s ∈ N.toSubmodule.obj (op W) :=
  s.2

/-- The zero morphism out of a submodule sheaf, with its source ascribed at `X.Modules`.

At the generic spelling of the source the numeral `0` has no `OfNat` instance, because instance
search cannot see that `X.ringCatSheaf` is a sheaf for `Opens.grothendieckTopology ↥X`. -/
public def zeroHom (N : SheafOfModules.Submodule M) (P : X.Modules) : N.asModules ⟶ P :=
  0

/-- The morphism `N.zeroHom P` is the zero morphism. -/
@[simp]
public lemma zeroHom_eq_zero (N : SheafOfModules.Submodule M) (P : X.Modules) :
    N.zeroHom P = 0 :=
  rfl

variable {F G : X.Modules}

/-- The inclusion of the embedded kernel of `f`, followed by `f`, is zero, stated at
`X.Modules`. -/
public lemma ιModules_kernelSubmodule_comp (f : F ⟶ G) :
    (kernelSubmodule f).ιModules ≫ f = 0 :=
  kernelSubmodule_ι_comp f

/-- The map from the embedded kernel of `f` to its categorical kernel is an isomorphism, stated
at `X.Modules`. -/
public lemma isIso_kernelLift (f : F ⟶ G) :
    IsIso (kernel.lift f (kernelSubmodule f).ιModules (ιModules_kernelSubmodule_comp f)) :=
  isIso_kernelSubmodule_lift f

/-- The embedded kernel
`Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule f` of a morphism of modules on
a scheme is its categorical kernel. -/
public def kernelIso (f : F ⟶ G) : (kernelSubmodule f).asModules ≅ kernel f :=
  have := isIso_kernelLift f
  asIso (kernel.lift f (kernelSubmodule f).ιModules (ιModules_kernelSubmodule_comp f))

/-- The forward map of `kernelIso f` is the lift through `kernel.ι f` of the inclusion of the
embedded kernel. -/
@[simp]
public lemma kernelIso_hom (f : F ⟶ G) : (kernelIso f).hom =
    kernel.lift f (kernelSubmodule f).ιModules (ιModules_kernelSubmodule_comp f) :=
  rfl

/-- The identification of the embedded kernel with the categorical kernel is compatible with the
two inclusions into the source, stated at `X.Modules`. -/
public lemma kernelIso_hom_comp_ι (f : F ⟶ G) :
    (kernelIso f).hom ≫ kernel.ι f = (kernelSubmodule f).ιModules := by
  rw [kernelIso_hom]
  exact kernel.lift_ι f (kernelSubmodule f).ιModules (ιModules_kernelSubmodule_comp f)

end

end AlgebraicGeometry.SheafOfModules.Submodule

end
