module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveFlasqueModules
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# The ideal-power multiples of a sheaf of modules are quasi-coherent

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals on `X` presented by its affine-local
ideal data, and `M` a sheaf of modules on `X`. The subsheaf `I ^ n • M` is defined as a least
subsheaf, so nothing about its sections is immediate. This file computes its sections over an
affine open, `(I ^ n • 𝒪_X)(U) = I(U) ^ n`, and deduces that `I ^ n • 𝒪_X` is quasi-coherent, by
identifying it with the ideal sheaf of the closed subscheme cut out by `I ^ n`.

The affine-local comparison tool is `submodule_eq_of_obj_affineOpens_eq`: two subsheaves of a
sheaf of modules with the same sections over every affine open are equal. This holds for an
arbitrary sheaf of modules on a scheme, with no quasi-coherence hypothesis, because the affine
opens form a basis and a subsheaf is determined by a covering family.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.kernelSubmodule` is the kernel of a morphism of sheaves of
  modules, realised as a subsheaf of the source rather than as a categorical limit.

## Main results

* `SheafOfModules.Submodule.toSubmodule_top`: the top subsheaf has all sections.
* `AlgebraicGeometry.Scheme.Modules.submodule_eq_of_obj_affineOpens_eq` and
  `AlgebraicGeometry.Scheme.Modules.submodule_eq_top_of_affineOpens`: a subsheaf of a sheaf of
  modules on a scheme is determined by its sections over the affine opens.
* `AlgebraicGeometry.Scheme.Modules.kernelSubmoduleIso`: that kernel subsheaf is the categorical
  kernel.
* `AlgebraicGeometry.Scheme.Modules.kernelSubmodule_obj_affineOpens`: for the canonical map
  `𝒪_X ⟶ i_* 𝒪_Z` of the closed subscheme attached to `I`, the kernel subsheaf has sections
  `I(U)` over an affine open `U`.
* `AlgebraicGeometry.idealPowerMultiple_obj_affineOpens`: `(I ^ n • 𝒪_X)(U) = I(U) ^ n` over an
  affine open `U`.
* `AlgebraicGeometry.idealPowerMultiple_isQuasicoherent`: `I ^ n • 𝒪_X` is quasi-coherent.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, so a morphism of `X.Modules` is only
definitionally a morphism of sheaves of modules; equalities of morphisms therefore have to be
transported with `congrArg` rather than `rw`, whose motive check fails. The same reason makes
`kernelSubmoduleIso` go through `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app` and
the evaluation functor, instead of comparing the two kernels directly.

## References

* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN) supplies the
  quasi-coherence of the ideal sheaf of a closed immersion, which is what makes the ideal-power
  multiples of the structure sheaf quasi-coherent.
* [Stacks Project, Tag 01QO](https://stacks.math.columbia.edu/tag/01QO)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace SheafOfModules.Submodule

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
  {M : SheafOfModules R}

/-- The top subsheaf of a sheaf of modules has every section over every object. -/
public lemma toSubmodule_top : (⊤ : M.Submodule).toSubmodule = ⊤ := by
  rw [← sInf_empty (α := M.Submodule), SheafOfModules.Submodule.toSubmodule_sInf]
  simp

end SheafOfModules.Submodule

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A section lies in a subsheaf of a sheaf of modules on a scheme as soon as its restriction to
every affine open inside the domain does. -/
private theorem mem_of_restrict_mem_affineOpens {M : X.Modules} (P : M.Submodule)
    {V : (Opens X)ᵒᵖ} (s : M.val.obj V)
    (h : ∀ (W : X.affineOpens) (hWV : W.1 ≤ V.unop),
      M.val.map (homOfLE hWV).op s ∈ P.toSubmodule.obj (op W.1)) :
    s ∈ P.toSubmodule.obj V := by
  refine P.isSheaf s ?_
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨_, ⟨W, hWaff, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.unop.2
  exact ⟨(⟨W, hWaff⟩ : X.affineOpens), homOfLE hWV, h ⟨W, hWaff⟩ hWV, hxW⟩

/-- Two subsheaves of a sheaf of modules on a scheme with the same sections over every affine
open are equal: the affine opens form a basis, and a subsheaf contains any section that lies in
it locally. -/
public theorem submodule_eq_of_obj_affineOpens_eq {M : X.Modules} (N P : M.Submodule)
    (h : ∀ U : X.affineOpens, N.toSubmodule.obj (op U) = P.toSubmodule.obj (op U)) : N = P := by
  have key : ∀ (A B : M.Submodule),
      (∀ U : X.affineOpens, A.toSubmodule.obj (op U) = B.toSubmodule.obj (op U)) →
      ∀ (V : (Opens X)ᵒᵖ) (s : M.val.obj V), s ∈ A.toSubmodule.obj V →
        s ∈ B.toSubmodule.obj V := fun A B hAB V s hs =>
    mem_of_restrict_mem_affineOpens B s fun W _ => by
      rw [← hAB W]
      exact A.toSubmodule.map_mem _ hs
  exact SheafOfModules.Submodule.ext <| PresheafOfModules.Submodule.ext fun V =>
    le_antisymm (key N P h V) (key P N (fun U => (h U).symm) V)

/-- A subsheaf of a sheaf of modules on a scheme which has all sections over every affine open is
the top subsheaf. -/
public theorem submodule_eq_top_of_affineOpens {M : X.Modules} (P : M.Submodule)
    (hP : ∀ U : X.affineOpens,
      (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤ P.toSubmodule.obj (op U.1)) : P = ⊤ := by
  refine le_antisymm le_top (SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun U => ?_))
  have htop : P.toSubmodule.obj U = ⊤ :=
    Submodule.eq_top_iff'.2 fun s =>
      mem_of_restrict_mem_affineOpens P s fun W _ => hP W Submodule.mem_top
  simp [htop]

/-- The kernel of a morphism of sheaves of modules on a scheme, as a subsheaf of the source.
Its sections over an open are the sections killed by the morphism; this is a subsheaf because a
section of the target that vanishes locally vanishes. -/
public noncomputable def kernelSubmodule {F G : X.Modules} (f : F ⟶ G) : F.Submodule where
  toSubmodule :=
    { obj U := (f.val.app U).hom.ker
      map := by
        intro U V g s hs
        have hz : ConcreteCategory.hom (f.val.app U) s = 0 := hs
        have hpoint : ConcreteCategory.hom (f.val.app V)
            (ConcreteCategory.hom (F.val.map g) s) =
            ConcreteCategory.hom (G.val.map g) (ConcreteCategory.hom (f.val.app U) s) :=
          PresheafOfModules.naturality_apply f.val g s
        change ConcreteCategory.hom (f.val.app V) (ConcreteCategory.hom (F.val.map g) s) = 0
        rw [hpoint, hz]
        exact map_zero _ }
  isSheaf := by
    intro V s hs
    rw [Opens.mem_grothendieckTopology] at hs
    change ConcreteCategory.hom (f.val.app V) s = 0
    refine Stacks.Cohomology.InjectiveRestriction.eq_zero_of_locally_zero G
      (ConcreteCategory.hom (f.val.app V) s) fun x hx => ?_
    obtain ⟨W, g, hgS, hxW⟩ := hs x hx
    refine ⟨W, leOfHom g, hxW, ?_⟩
    have hmem : ConcreteCategory.hom (f.val.app (op W))
        (ConcreteCategory.hom (F.val.map (homOfLE (leOfHom g)).op) s) = 0 := by
      have : (homOfLE (leOfHom g)).op = g.op := Subsingleton.elim _ _
      rw [this]
      exact hgS
    have hpoint : ConcreteCategory.hom (f.val.app (op W))
        (ConcreteCategory.hom (F.val.map (homOfLE (leOfHom g)).op) s) =
        ConcreteCategory.hom (G.val.map (homOfLE (leOfHom g)).op)
          (ConcreteCategory.hom (f.val.app V) s) :=
      PresheafOfModules.naturality_apply f.val (homOfLE (leOfHom g)).op s
    exact hpoint.symm.trans hmem

/-- Membership in the kernel subsheaf is the vanishing of the morphism on the section. -/
@[simp]
public lemma mem_kernelSubmodule {F G : X.Modules} (f : F ⟶ G) (V : (Opens X)ᵒᵖ)
    (s : F.val.obj V) :
    s ∈ (kernelSubmodule f).toSubmodule.obj V ↔ (f.val.app V).hom s = 0 :=
  Iff.rfl

/-- The kernel subsheaf of a morphism of sheaves of modules on a scheme is its categorical
kernel. -/
public noncomputable def kernelSubmoduleIso {F G : X.Modules} (f : F ⟶ G) :
    (show X.Modules from (kernelSubmodule f).toSheafOfModules) ≅ kernel f := by
  let K : X.Modules := (kernelSubmodule f).toSheafOfModules
  let ιK : K ⟶ F := (kernelSubmodule f).ι
  have hzero : ιK ≫ f = 0 := by
    ext U s
    exact s.property
  let e : K ⟶ kernel f := kernel.lift f ιK hzero
  have heq : e ≫ kernel.ι f = ιK := kernel.lift_ι f ιK hzero
  have hIso : IsIso e := by
    rw [AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
    have : E.PreservesZeroMorphisms := ⟨by intros; rfl⟩
    let k : E.obj (kernel f) ≅ kernel (E.map f) := PreservesKernel.iso E f
    let m : E.obj (kernel f) ≅ ModuleCat.of _ (LinearMap.ker (E.map f).hom) :=
      k ≪≫ ModuleCat.kernelIsoKer (E.map f)
    have hki : k.inv ≫ E.map (kernel.ι f) = kernel.ι (E.map f) := PreservesKernel.iso_inv_ι E f
    have hfac : E.map (kernel.ι f) = k.hom ≫ kernel.ι (E.map f) := by
      rw [← hki]
      exact (Iso.hom_inv_id_assoc k (E.map (kernel.ι f))).symm
    have hmono : Mono (E.map (kernel.ι f)) := by
      refine ⟨fun {Z} g h hgh => ?_⟩
      have e1 : (g ≫ k.hom) ≫ kernel.ι (E.map f) = g ≫ E.map (kernel.ι f) :=
        (Category.assoc g k.hom _).trans (congrArg (fun t => g ≫ t) hfac.symm)
      have e2 : (h ≫ k.hom) ≫ kernel.ι (E.map f) = h ≫ E.map (kernel.ι f) :=
        (Category.assoc h k.hom _).trans (congrArg (fun t => h ≫ t) hfac.symm)
      have h2 : g ≫ k.hom = h ≫ k.hom :=
        (cancel_mono (kernel.ι (E.map f))).1 (e1.trans (hgh.trans e2.symm))
      have hgg : g ≫ k.hom ≫ k.inv = g :=
        (congrArg (fun t => g ≫ t) k.hom_inv_id).trans (Category.comp_id g)
      have hhh : h ≫ k.hom ≫ k.inv = h :=
        (congrArg (fun t => h ≫ t) k.hom_inv_id).trans (Category.comp_id h)
      refine hgg.symm.trans (Eq.trans ?_ hhh)
      exact ((Category.assoc g k.hom k.inv).symm.trans
        (congrArg (fun t => t ≫ k.inv) h2)).trans (Category.assoc h k.hom k.inv)
    have hleft : E.map e ≫ E.map (kernel.ι f) = E.map ιK :=
      (E.map_comp e (kernel.ι f)).symm.trans (congrArg (fun t => E.map t) heq)
    have hright : m.inv ≫ E.map (kernel.ι f) = E.map ιK := by
      have h2 : m.inv ≫ E.map (kernel.ι f)
          = (ModuleCat.kernelIsoKer (E.map f)).inv ≫ (k.inv ≫ E.map (kernel.ι f)) := by
        simp [m]
      rw [h2, hki, ModuleCat.kernelIsoKer_inv_kernel_ι]
      rfl
    have he : E.map e = m.inv :=
      hmono.right_cancellation _ _ (hleft.trans hright.symm)
    have heiso : IsIso (E.map e) := by
      rw [he]
      exact ⟨m.hom, m.inv_hom_id, m.hom_inv_id⟩
    dsimp [AlgebraicGeometry.Scheme.Modules.Hom.app]
    exact Functor.map_isIso (forget₂ _ AddCommGrpCat) (E.map e)
  exact asIso e

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

open AlgebraicGeometry.Scheme.Modules

/-- The kernel subsheaf of the canonical map `𝒪_X ⟶ i_* 𝒪_Z` for the closed subscheme `Z` cut
out by the ideal data `I` has, over an affine open `U`, exactly the sections `I(U)`. -/
public lemma kernelSubmodule_subschemeι_obj_affineOpens (I : X.IdealSheafData)
    (U : X.affineOpens) :
    (kernelSubmodule
        (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).toSubmodule.obj
        (op U.1) = I.ideal U :=
  I.ker_subschemeι_app U

/-- The ideal `J` of sections of `𝒪_X` over an open, times the whole of `𝒪_X` there, is `J`
again. The point of the statement is that the structure sheaf carries two module structures
over itself which are definitionally but not syntactically the same: the submodules of
`Γ(𝒪_X, U)` over `Γ(X, U)` and the ideals of `Γ(X, U)`. -/
public lemma ideal_smul_top_unit (U : X.Opens) (J : Ideal Γ(X, U)) :
    J • (⊤ : Submodule Γ(X, U)
        Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, U)) =
      (show Submodule Γ(X, U)
        Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, U) from J) := by
  show J • (⊤ : Ideal Γ(X, U)) = J
  simp

/-- The sections of `I ^ n • 𝒪_X` over an affine open `U` are the `n`-th power `I(U) ^ n` of the
ideal of sections of `I` there. -/
public lemma idealPowerMultiple_unit_obj_affineOpens (I : X.IdealSheafData) (n : ℕ)
    (U : X.affineOpens) :
    (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1) =
      I.ideal U ^ n := by
  have hPK : idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf) ≤
      kernelSubmodule
        (SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom) := by
    refine (idealPowerMultiple_le_iff I n (SheafOfModules.unit X.ringCatSheaf) _).2 fun V => ?_
    rw [kernelSubmodule_subschemeι_obj_affineOpens (I ^ n) V,
      Scheme.IdealSheafData.ideal_pow, ideal_smul_top_unit]
    exact le_rfl
  refine le_antisymm ?_ ?_
  · have hle := hPK (op U.1)
    rwa [kernelSubmodule_subschemeι_obj_affineOpens (I ^ n) U,
      Scheme.IdealSheafData.ideal_pow] at hle
  · refine le_trans (le_of_eq ?_)
      (le_idealPowerMultiple_obj I n (SheafOfModules.unit X.ringCatSheaf) U)
    exact (ideal_smul_top_unit U.1 (I.ideal U ^ n)).symm

/-- The ideal-power multiple `I ^ n • 𝒪_X` of the structure sheaf is quasi-coherent: it is the
ideal sheaf of the closed subscheme cut out by `I ^ n`, and the ideal sheaf of a closed immersion
is quasi-coherent. -/
public lemma idealPowerMultiple_unit_isQuasicoherent (I : X.IdealSheafData) (n : ℕ) :
    (((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules :
      X.Modules)).IsQuasicoherent := by
  have hEq : idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf) =
      kernelSubmodule
        (SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom) := by
    refine submodule_eq_of_obj_affineOpens_eq _ _ fun U => ?_
    rw [idealPowerMultiple_unit_obj_affineOpens,
      kernelSubmodule_subschemeι_obj_affineOpens (I ^ n) U, Scheme.IdealSheafData.ideal_pow]
    rfl
  rw [hEq]
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelSubmoduleIso _).symm
    (Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf
      (I ^ n).subschemeι)

end AlgebraicGeometry

end

end
