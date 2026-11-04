module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers

/-!
# The ideal action on a sheaf of modules, and sectionwise kernels

Let `X` be a scheme. This file builds the two pieces of infrastructure that the quasi-coherence
of the ideal-power subsheaf `I ^ n F` is assembled from.

The first is the kernel of a morphism of sheaves of modules presented as a *submodule of the
source* rather than as an abstract limit. The ideal-power subsheaf `I ^ n F` is by definition an
infimum of submodules, so identifying it with a kernel is a statement about submodules, and the
categorical `kernel` is only isomorphic to the sectionwise one; `kernelSubmoduleIso` is that
isomorphism. The sectionwise kernel is obtained as the preimage of the zero submodule, which
supplies its locality for free.

The second is the multiplication map `J ⊗ F ⟶ F` by an ideal `J` of the structure sheaf, through
the sheafified tensor product of Stacks 01CA, together with its corestriction to any submodule of
`F` containing all the products. `I ^ n F` is the image of this map for `J = I ^ n`, which is how
quasi-coherence of `I ^ n F` is proved.

## Main definitions

* `Stacks.Algebraization.kernelSubmodule` — the kernel of a morphism of sheaves of modules, as a
  submodule of the source.
* `Stacks.Algebraization.idealAction` — the multiplication `J ⊗ F ⟶ F` by an ideal `J` of the
  structure sheaf.
* `Stacks.Algebraization.idealActionLift` — its corestriction to a submodule of `F` containing
  every product.

## Main results

* `Stacks.Algebraization.kernelSubmoduleIso` — the sectionwise kernel agrees with the categorical
  one.
* `Stacks.Algebraization.kernelSubmodule_obj_affine` — on an affine open the sections of the ideal
  sheaf of `I` are `I`'s own ideal of sections.
* `Stacks.Algebraization.idealKernel_isQuasicoherent` — the ideal sheaf attached to a
  quasi-coherent ideal sheaf datum is quasi-coherent.
* `Stacks.Algebraization.mem_submodule_of_affine` — membership in a submodule is affine-local.
* `Stacks.Algebraization.idealActionLift_fac` — the corestriction composed with the inclusion is
  the action.

## Implementation notes

Quasi-coherence of the ideal itself is `isQuasicoherent_kernel_unitToPushforwardObjUnit`
(Stacks 01R8, the kernel of `𝒪_Y ⟶ f_* 𝒪_X` for quasi-compact `f`), applied to the quasi-compact
morphism `I.subschemeι`. That is strictly more than Stacks 01IN asks for here, and it makes the
ringed-space closed-immersion theory unnecessary.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared category instances. A composite mixing them is not
type-correct at the transparency `rw` builds its motive at, so several proofs below are written as
explicit chains of `Category.assoc` and `congrArg` terms where a rewrite would be more natural.
For the same reason the scalar action on sections needs its instances supplied at the spelling the
elaborator actually meets; those are the `local instance`s in the middle of the file, each of which
is an existing instance restated at the other spelling.

## References

* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open TopologicalSpace Scheme.Modules

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- The kernel of a morphism of sheaves of modules on a scheme, as a submodule of the source.

Sectionwise this is the kernel of the map on sections; it is a subsheaf because a section whose
image vanishes locally has vanishing image, by separatedness of the target. -/
public noncomputable def kernelSubmodule {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) : F.Submodule :=
  AlgebraicGeometry.sheafSubmoduleComap f ⊥

/-- The sections of `kernelSubmodule f` over any open are the kernel of `f` on sections. -/
public lemma kernelSubmodule_toSubmodule_obj {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    (kernelSubmodule f).toSubmodule.obj U = (f.val.app U).hom.ker :=
  (congrArg (fun s => Submodule.comap (ModuleCat.Hom.hom (f.val.app U)) s)
    (SheafOfModules.Submodule.bot_obj G U)).trans (Submodule.comap_bot _)

/-- Every section of the categorical kernel lies in the sectionwise kernel. -/
public lemma top_le_comap_kernelSubmodule {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    (⊤ : (kernel (C := X.Modules) f).Submodule) ≤
      AlgebraicGeometry.sheafSubmoduleComap (kernel.ι (C := X.Modules) f) (kernelSubmodule f) := by
  refine SheafOfModules.Submodule.le_iff.mpr fun U x _ => ?_
  have hz : (f.val.app U).hom (((kernel.ι (C := X.Modules) f).val.app U).hom x) = 0 :=
    congrArg (fun t : (kernel (C := X.Modules) f) ⟶ G => (t.val.app U).hom x)
      (kernel.condition (C := X.Modules) f)
  have hmem : (f.val.app U).hom (((kernel.ι (C := X.Modules) f).val.app U).hom x) ∈
      (⊥ : G.Submodule).toSubmodule.obj U :=
    hz ▸ Submodule.zero_mem _
  exact hmem

/-- The lift of the sectionwise kernel's inclusion through the categorical kernel. -/
public noncomputable def kernelSubmoduleLift {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) :
    ((kernelSubmodule f).toSheafOfModules : X.Modules) ⟶ kernel (C := X.Modules) f :=
  kernel.lift (C := X.Modules) f (kernelSubmodule f).ι (by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.Hom.ext
    ext s
    have hs : s.1 ∈ (f.val.app U).hom.ker :=
      (kernelSubmodule_toSubmodule_obj f U) ▸ s.property
    exact LinearMap.mem_ker.mp hs)

/-- The corestriction of the categorical kernel's inclusion into the sectionwise kernel. -/
public noncomputable def kernelSubmoduleCorestrict {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) :
    (kernel (C := X.Modules) f) ⟶ ((kernelSubmodule f).toSheafOfModules : X.Modules) :=
  (AlgebraicGeometry.sheafTopIso (kernel (C := X.Modules) f)).inv ≫
    AlgebraicGeometry.sheafSubmoduleMap (kernel.ι (C := X.Modules) f) ⊤ (kernelSubmodule f)
      (top_le_comap_kernelSubmodule f)

/-- The corestriction followed by the inclusion is the kernel inclusion.

Proved as an explicit chain of `Category.assoc` terms rather than by `rw`: the composite mixes
the `X.Modules` and `SheafOfModules X.ringCatSheaf` category instances, and a rewrite motive is
not type-correct at the transparency `rw` uses. -/
public lemma kernelSubmoduleCorestrict_comp_ι {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    kernelSubmoduleCorestrict f ≫ (kernelSubmodule f).ι = kernel.ι (C := X.Modules) f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun g => (AlgebraicGeometry.sheafTopIso (kernel (C := X.Modules) f)).inv ≫ g)
        (AlgebraicGeometry.sheafSubmoduleMap_comp_ι _ _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ kernel.ι (C := X.Modules) f)
            (AlgebraicGeometry.sheafTopIso (kernel (C := X.Modules) f)).inv_hom_id).trans
          (Category.id_comp _))))

/-- The composite `hom ≫ inv` agrees with the identity after the inclusion. -/
public lemma kernelSubmoduleInvIdAux {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    (kernelSubmoduleLift f ≫ kernelSubmoduleCorestrict f) ≫ (kernelSubmodule f).ι =
      (kernelSubmodule f).ι :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun g => kernelSubmoduleLift f ≫ g)
      (kernelSubmoduleCorestrict_comp_ι f)).trans
      (kernel.lift_ι (C := X.Modules) f (kernelSubmodule f).ι _))

/-- The composite `inv ≫ hom` agrees with the identity after the kernel inclusion. -/
public lemma kernelSubmoduleIdAux {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    (kernelSubmoduleCorestrict f ≫ kernelSubmoduleLift f) ≫ kernel.ι (C := X.Modules) f =
      kernel.ι (C := X.Modules) f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun g => kernelSubmoduleCorestrict f ≫ g)
        (kernel.lift_ι (C := X.Modules) f (kernelSubmodule f).ι _)).trans
      (kernelSubmoduleCorestrict_comp_ι f))

/-- The sectionwise kernel agrees with the categorical kernel. -/
public noncomputable def kernelSubmoduleIso {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) : (kernelSubmodule f).toSheafOfModules ≅ kernel (C := X.Modules) f where
  hom := kernelSubmoduleLift f
  inv := kernelSubmoduleCorestrict f
  hom_inv_id := AlgebraicGeometry.cancel_sheafSubmodule_ι (kernelSubmodule f) _ _
    ((kernelSubmoduleInvIdAux f).trans (Category.id_comp _).symm)
  inv_hom_id := (cancel_mono (kernel.ι (C := X.Modules) f)).1
    ((kernelSubmoduleIdAux f).trans (Category.id_comp _).symm)

/-- On an affine open, the sections of the ideal sheaf of `I` are `I`'s own ideal of sections. -/
public lemma kernelSubmodule_obj_affine {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    (kernelSubmodule
      (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).toSubmodule.obj
        (op U) = I.ideal U :=
  (kernelSubmodule_toSubmodule_obj _ (op U.1)).trans (I.ker_subschemeι_app U)

/-- Membership in a submodule of a sheaf of modules is affine-local. -/
public lemma mem_submodule_of_affine {X : Scheme.{u}} {F : X.Modules}
    (N : F.Submodule) (U : X.Opens) (s : Γ(F, U))
    (h : ∀ (V : X.affineOpens) (i : V.1 ⟶ U),
      F.val.map i.op s ∈ N.toSubmodule.obj (op V.1)) :
    s ∈ N.toSubmodule.obj (op U) := by
  apply N.isSheaf
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨V, homOfLE hVU, h ⟨V, hV⟩ (homOfLE hVU), hxV⟩

/-- The ideal sheaf attached to a quasi-coherent ideal sheaf datum is quasi-coherent.

This is the kernel of `𝒪_X ⟶ (I)_* 𝒪`, quasi-coherent because `I.subschemeι` is quasi-compact. -/
public lemma idealKernel_isQuasicoherent {X : Scheme.{u}} (I : X.IdealSheafData) :
    (kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom)).toSheafOfModules.IsQuasicoherent := by
  have h : (kernel (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelSubmoduleIso _).symm h

/-! ### Scalar action on sections

The module structure on `Γ(M, U)` is declared over `X.ringCatSheaf.obj.obj U`; the instances
below restate it over `X.presheaf.obj U`, the same ring. -/

/-- The sections `M(U)` of an `𝒪_X`-module form a module over `Γ(X, U)`. -/
local instance sectionsModuleΓ {X : Scheme.{u}} (M : X.Modules) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) (M.val.obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- The sections `M(U)` of a sheaf of `𝒪_X`-modules form a module over `Γ(X, U)`. -/
local instance sectionsModuleΓSheaf {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) (M.val.obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- The sections `M(U)` of an `𝒪_X`-module form a module over `𝒪_X(U)`. -/
local instance sectionsModuleRingCatSheaf {X : Scheme.{u}} (M : X.Modules) (U : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (M.presheaf.obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- Scalar multiplications by elements of `Γ(X, U)` on the sections `M(U)` commute. -/
local instance sectionsSMulCommClassΓ {X : Scheme.{u}} (M : X.Modules) (U : (Opens X)ᵒᵖ) :
    SMulCommClass (X.presheaf.obj U) (X.presheaf.obj U) (M.val.obj U) :=
  ⟨fun a b m => by
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, mul_comm]⟩

/-- The inclusion of a submodule of a sheaf of modules is a monomorphism. -/
local instance monoSubmoduleι {X : Scheme.{u}} {M : X.Modules} (P : M.Submodule) :
    Mono (C := X.Modules) P.ι :=
  ⟨fun {_} f g h => AlgebraicGeometry.cancel_sheafSubmodule_ι P f g h⟩

/-- Multiplication by an ideal of the structure sheaf, before sheafification. -/
public def idealActionPresheaf {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules) :
    (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (J.toSheafOfModules.val)
      (F.val)) ⟶ F.val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun a m ↦ (show X.presheaf.obj U from a.1) • m)
    (by intros; exact add_smul (R := X.presheaf.obj U) _ _ _)
    (by intros; exact mul_smul (α := X.presheaf.obj U) _ _ _)
    (by intros; exact smul_add (M := X.presheaf.obj U) _ _ _)
    (by intros; exact smul_comm (M := X.presheaf.obj U) (N := X.presheaf.obj U) _ _ _)
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext fun a m ↦
    (F.val.map_smul i a.1 m).symm

/-- Multiplication `J ⊗ F ⟶ F` by an ideal `J` of the structure sheaf. -/
public def idealAction {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (J.toSheafOfModules)).obj
      (F)) ⟶
      F :=
  (PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).symm
      (idealActionPresheaf J F)

/-- The sheafification hom-equivalence undoes its inverse on maps out of the tensor presheaf. -/
private theorem sheafificationHomEquiv_apply_symm {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F G : X.Modules)
    (g : (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (J.toSheafOfModules.val)
      (F.val)) ⟶ G.val) :
    PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).symm g) = g :=
  Equiv.apply_symm_apply _ _

/-- On a tensor of sections, the ideal action is multiplication. -/
public lemma idealAction_tmul {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (U : (Opens X)ᵒᵖ) (a : J.toSheafOfModules.val.obj U) (m : F.val.obj U) :
    (idealAction J F).val.app U
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
        J.toSheafOfModules F U
        (a ⊗ₜ[X.presheaf.obj U] m)) = (show X.presheaf.obj U from a.1) • m :=
  congrArg (fun k ↦ (k.app U).hom (a ⊗ₜ[X.presheaf.obj U] m))
    (sheafificationHomEquiv_apply_symm J F F (idealActionPresheaf J F))

/-- The corestriction of `idealActionPresheaf` to a submodule containing every product. -/
public def idealActionLiftPresheaf {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (N : F.Submodule)
    (h : ∀ (U : (Opens X)ᵒᵖ) (a : J.toSheafOfModules.val.obj U) (m : F.val.obj U),
      (show X.presheaf.obj U from a.1) • m ∈ N.toSubmodule.obj U) :
    (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (J.toSheafOfModules.val)
      (F.val)) ⟶
      N.toSheafOfModules.val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun a m ↦ ⟨(show X.presheaf.obj U from a.1) • m, h U a m⟩)
    (by intros; exact Subtype.ext (add_smul (R := X.presheaf.obj U) _ _ _))
    (by intros; exact Subtype.ext (mul_smul (α := X.presheaf.obj U) _ _ _))
    (by intros; exact Subtype.ext (smul_add (M := X.presheaf.obj U) _ _ _))
    (by intros; exact Subtype.ext ((sectionsSMulCommClassΓ F U).smul_comm _ _ _))
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext fun a m ↦
    Subtype.ext (F.val.map_smul i a.1 m).symm

/-- The corestriction of `idealAction` to a submodule containing every product. -/
public def idealActionLift {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (N : F.Submodule)
    (h : ∀ (U : (Opens X)ᵒᵖ) (a : J.toSheafOfModules.val.obj U) (m : F.val.obj U),
      (show X.presheaf.obj U from a.1) • m ∈ N.toSubmodule.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (J.toSheafOfModules)).obj
      (F)) ⟶
      N.toSheafOfModules :=
  (PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).symm
      (idealActionLiftPresheaf J F N h)

/-- The corestriction composed with the inclusion is the action. -/
public lemma idealActionLift_fac {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (N : F.Submodule)
    (h : ∀ (U : (Opens X)ᵒᵖ) (a : J.toSheafOfModules.val.obj U) (m : F.val.obj U),
      (show X.presheaf.obj U from a.1) • m ∈ N.toSubmodule.obj U) :
    idealActionLift J F N h ≫ N.ι = idealAction J F := by
  apply (PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).injective
  have nat : PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj) (idealActionLift J F N h ≫ N.ι) =
      PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj) (idealActionLift J F N h) ≫ N.ι.val :=
    (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right
        (idealActionLift J F N h) N.ι
  have key : idealActionLiftPresheaf J F N h ≫ N.ι.val = idealActionPresheaf J F := by
    ext U : 1
    exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl
  exact nat.trans ((congrArg (fun g => g ≫ N.ι.val)
    (sheafificationHomEquiv_apply_symm J F N.toSheafOfModules _)).trans
    (key.trans (sheafificationHomEquiv_apply_symm J F F _).symm))

end Stacks.Algebraization

end

end
