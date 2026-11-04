module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesIdealPowerComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesMultipleTwist
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.PushforwardPullbackQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleTwistVanishing.Basic
public import StacksCore.CategoryTheory.Abelian.CommSq

/-!
# The adic layer of a twist is the direct image of a twisted layer on the fibre

Let `X` be a scheme, `ℐ` a quasi-coherent sheaf of ideals on `X`, `ℱ` a quasi-coherent
`𝒪_X`-module and `ℒ` an invertible one, and let `v : V ⟶ X` be a closed immersion with ideal
sheaf `ℐ`. This file identifies

`ker(ℱ(d)/ℐ ⁿ⁺¹ℱ(d) ⟶ ℱ(d)/ℐ ⁿℱ(d))`  with  `v_*((v^*(ℐ ⁿℱ)) ⊗ (v^*ℒ)^{⊗ d})`

for every `n : ℕ` and every `d : ℤ`.

The left-hand side is the shape in which the hypothesis `hgr` of
`Stacks.Cohomology.FormalFunctions.exists_surjective_fibreCohomology_twistModule` is stated —
the transition kernel of the
adic tower of the twist. The right-hand side is the direct image along the fibre's closed
immersion of the degree-`n` piece of
`Stacks.AssociatedGradedFibre.fibreAssociatedGradedModule`, twisted by the restriction of `ℒ`,
which is what part (2) of [Stacks, Tag 0897] concludes about. Composed with
`Stacks.Cohomology.FormalFunctions.isZero_rightDerived_pushforward_iff_isZero_hgroup` — the
comparison of the two cohomologies across a closed immersion — this is the last step between
the two.

## The four steps

1. **The layer is a transition kernel.** `ℐ ⁿM/ℐ ⁿ⁺¹M ≅ ker(M/ℐ ⁿ⁺¹M ⟶ M/ℐ ⁿM)` is the third
   isomorphism theorem `CategoryTheory.Abelian.cokernelIsoKernelCokernelMap` at the inclusions
   `ℐ ⁿ⁺¹M ⊆ ℐ ⁿM ⊆ M`, together with the observation that the induced map on the two quotients
   by `ℐ ⁿ⁺¹M` and `ℐ ⁿM` is `Stacks.Algebraization.idealPowerQuotientDrop`: both are determined
   by their compatibility with the quotient projection out of `M`.
2. **The layer is a direct image.** [Stacks, Tag 0EL1] in the form
   `Stacks.Algebraization.idealQuotientPushforwardIso` says `N/ℐ N ≅ v_* v^* N` for every
   quasi-coherent `N`; at `N = ℐ ⁿM` the subsheaf `ℐ·(ℐ ⁿM)` is `ℐ ⁿ⁺¹M` read inside `ℐ ⁿM`
   (`Stacks.AlgebraicGeometry.IdealPowerColimit.idealSmul_idealPowSmul_eq`), so the quotient is
   the layer of step 1.
3. **The layer commutes with the twist.** `(ℐ ⁿℱ)(d) ≅ ℐ ⁿ(ℱ(d))` is
   `Stacks.Blowup.reesMultipleTwistIso`, read at `Stacks.Algebraization.idealPowerMultiple`
   through `Stacks.Blowup.reesMultiple_eq_idealPowerMultiple`.
4. **The twist commutes with the restriction.** `v^*(𝒩(d)) ≅ (v^*𝒩)(d)` is [Stacks, Tag 0EGK],
   `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistModuleIso`.

## Main definitions

* `Stacks.Algebraization.subComapIso`: for subsheaves `A ⊆ A'` of `M`, the preimage of `A` in
  `A'` is `A`.
* `Stacks.Algebraization.idealPowerLayerKernelIso`: **step 1.**
* `Stacks.Algebraization.idealPowerLayerPushforwardIso`: **step 2**, in the form
  `ker(M/ℐ ⁿ⁺¹M ⟶ M/ℐ ⁿM) ≅ v_* v^*(ℐ ⁿM)`.
* `Stacks.Algebraization.idealPowerMultipleTwistIso`: **step 3.**
* `Stacks.Algebraization.kernelIdealPowerQuotientDropTwistIso`: **the composite.**

## Implementation notes

The two models of the subsheaf `ℐ ⁿM` — `Stacks.Algebraization.idealPowerMultiple`, which the
adic quotients are built from, and `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`,
which the Artin–Rees identity of
`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/PushforwardPullbackQuotient.lean` is stated at —
are the same definition under two names and are interchangeable by `rfl`; the third,
`Stacks.Blowup.reesMultiple`, is a genuinely different construction and is crossed only through
`Stacks.Blowup.reesMultiple_eq_idealPowerMultiple`.

Step 2 has to compare two monomorphisms into `ℐ ⁿM`: the inclusion of `ℐ·(ℐ ⁿM)`, which is what
[Stacks, Tag 0EL1] divides by, and the inclusion of `ℐ ⁿ⁺¹M`, which is what step 1 divides by.
The Artin–Rees identity equates the first subsheaf with the *preimage* of the second along
`ℐ ⁿM ⟶ M`, because `SheafOfModules.Submodule` has a preimage and no image; `subComapIso`
is what turns that preimage back into `ℐ ⁿ⁺¹M`, and `Limits.cokernelEpiComp` then identifies
the two cokernels.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and the two
presentations carry separately declared category instances, so — exactly as in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/AdicQuotientMap.lean` — composites name
the category with `(obj := X.Modules)` or `(C := X.Modules)`, and the monomorphism property of a
submodule inclusion and the invertibility of an isomorphism's forward map are supplied by hand
where instance resolution does not cross that `def`.

Step 1 is stated with the comparison isomorphism of cokernels on the *left*, as
`(cokernelIsoOfEq _).inv ≫ _ = idealPowerQuotientDrop _ _ _`, so that the epimorphism cancelled
in its proof is `cokernel.π` of a submodule inclusion, for which
`Stacks.Algebraization.epi_cokernel_π_submodule_ι` is the instance; the other orientation
follows by `CategoryTheory.Iso.inv_comp_eq`.

Nothing here carries a `@[stacks]` attribute: steps 1–4 are library results used as they stand,
and the composite is an identification internal to this development.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
* [Stacks Project, Tag 0129](https://stacks.math.columbia.edu/tag/0129)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### The preimage of a subsheaf in a larger subsheaf -/

section SubComap

variable {X : Scheme.{u}} {M : X.Modules} {A A' : M.Submodule} (hle : A ≤ A')

/-- The inclusion of `A'` into `M`, at the `X.Modules` presentation. -/
abbrev subIota (A' : M.Submodule) : (A'.toSheafOfModules : X.Modules) ⟶ M := A'.ι

/-- Monomorphy of a submodule inclusion at the `X.Modules` presentation, which instance
resolution does not find through the `def` `AlgebraicGeometry.Scheme.Modules`. -/
theorem mono_subIota (A' : M.Submodule) : Mono (subIota A') :=
  Stacks.AlgebraicGeometry.IdealPowerColimit.mono_submoduleι A'

/-- The preimage of `A` along the inclusion of `A'`, as a subsheaf of `A'`. -/
abbrev subComap (A : M.Submodule) (A' : M.Submodule) :
    (A'.toSheafOfModules : X.Modules).Submodule :=
  AlgebraicGeometry.sheafSubmoduleComap (subIota A') A

/-- The preimage of `A` along the inclusion of `A'` maps to `A`. -/
def subComapHom (A A' : M.Submodule) :
    ((subComap A A').toSheafOfModules : X.Modules) ⟶ (A.toSheafOfModules : X.Modules) :=
  AlgebraicGeometry.sheafSubmoduleMap (subIota A') (subComap A A') A le_rfl

include hle in
/-- A section of `A` is, read inside `A'`, a section of the preimage of `A`. -/
theorem top_le_sheafSubmoduleComap_homOfLE :
    (⊤ : (A.toSheafOfModules : X.Modules).Submodule) ≤
      AlgebraicGeometry.sheafSubmoduleComap (SheafOfModules.Submodule.homOfLE hle)
        (subComap A A') := by
  refine SheafOfModules.Submodule.le_iff.mpr ?_
  intro U x _
  exact x.2

/-- `A` maps to the preimage of `A` along the inclusion of `A'`. -/
def subComapInv :
    (A.toSheafOfModules : X.Modules) ⟶ ((subComap A A').toSheafOfModules : X.Modules) :=
  (AlgebraicGeometry.sheafTopIso (A.toSheafOfModules : X.Modules)).inv ≫
    AlgebraicGeometry.sheafSubmoduleMap (SheafOfModules.Submodule.homOfLE hle) ⊤
      (subComap A A') (top_le_sheafSubmoduleComap_homOfLE hle)

/-- Reassociation for `X.Modules`: `g ≫ k = m` gives `(f ≫ g) ≫ k = f ≫ m`. -/
private theorem assoc_eq_of_comp_eq {Y Z W T : X.Modules} {f : Y ⟶ Z} {g : Z ⟶ W} {k : W ⟶ T}
    {m : Z ⟶ T} (h : g ≫ k = m) : (f ≫ g) ≫ k = f ≫ m :=
  (Category.assoc (obj := X.Modules) _ _ _).trans (congrArg (f ≫ ·) h)

/-- `subComapInv` is the inclusion `A ⟶ A'`, read into the preimage. -/
@[reassoc]
theorem subComapInv_comp_ι :
    subComapInv hle ≫ (subComap A A').ι = SheafOfModules.Submodule.homOfLE hle := by
  exact (assoc_eq_of_comp_eq (AlgebraicGeometry.sheafSubmoduleMap_comp_ι
    (SheafOfModules.Submodule.homOfLE hle) ⊤ (subComap A A')
    (top_le_sheafSubmoduleComap_homOfLE hle))).trans
    ((AlgebraicGeometry.sheafTopIso (A.toSheafOfModules : X.Modules)).inv_hom_id_assoc _)

/-- `subComapHom` is the inclusion of the preimage, read into `A`. -/
@[reassoc]
theorem subComapHom_comp_ι :
    subComapHom A A' ≫ subIota A = (subComap A A').ι ≫ subIota A' :=
  AlgebraicGeometry.sheafSubmoduleMap_comp_ι (subIota A') (subComap A A') A le_rfl

include hle in
/-- `subComapHom` is the inclusion of the preimage, read into `A'`. -/
@[reassoc]
theorem subComapHom_comp_homOfLE :
    subComapHom A A' ≫ SheafOfModules.Submodule.homOfLE hle = (subComap A A').ι := by
  have := mono_subIota A'
  refine (cancel_mono (subIota A')).1 ?_
  exact (assoc_eq_of_comp_eq (SheafOfModules.Submodule.homOfLE_ι hle)).trans
    (subComapHom_comp_ι (A := A) (A' := A'))

/-- **The preimage of a subsheaf `A` in a larger subsheaf `A'` is `A`.** -/
def subComapIso :
    ((subComap A A').toSheafOfModules : X.Modules) ≅ (A.toSheafOfModules : X.Modules) where
  hom := subComapHom A A'
  inv := subComapInv hle
  hom_inv_id := by
    refine AlgebraicGeometry.cancel_sheafSubmodule_ι _ _ _ ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => subComapHom A A' ≫ z) (subComapInv_comp_ι hle)) ?_
    exact (subComapHom_comp_homOfLE hle).trans (Category.id_comp (obj := X.Modules) _).symm
  inv_hom_id := by
    have := mono_subIota A
    refine (cancel_mono (subIota A)).1 ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => subComapInv hle ≫ z)
      (subComapHom_comp_ι (A := A) (A' := A'))) ?_
    exact ((subComapInv_comp_ι_assoc hle (subIota A')).trans
      (SheafOfModules.Submodule.homOfLE_ι hle)).trans
      (Category.id_comp (obj := X.Modules) _).symm

/-- The forward map of `subComapIso` is `subComapHom`. -/
@[simp] theorem subComapIso_hom : (subComapIso hle).hom = subComapHom A A' := rfl

/-- The inverse map of `subComapIso` is `subComapInv`. -/
@[simp] theorem subComapIso_inv : (subComapIso hle).inv = subComapInv hle := rfl

include hle in
/-- The forward map of `subComapIso` is invertible at the `X.Modules` presentation. -/
theorem isIso_subComapHom : IsIso (C := X.Modules) (subComapHom A A') :=
  ⟨subComapInv hle, (subComapIso hle).hom_inv_id, (subComapIso hle).inv_hom_id⟩

include hle in
/-- The forward map of `subComapIso` is an epimorphism at the `X.Modules` presentation. -/
theorem epi_subComapHom : Epi (C := X.Modules) (subComapHom A A') :=
  @CategoryTheory.IsIso.epi_of_iso X.Modules _ _ _ (subComapHom A A') (isIso_subComapHom hle)

end SubComap

/-! ### The adic layer as a transition kernel -/

section Layer

variable {X : Scheme.{u}} (J : X.IdealSheafData) (M : X.Modules) (n : ℕ)

/-- The inclusion `ℐ ⁿ⁺¹M ⟶ ℐ ⁿM`, at the `X.Modules` presentation. -/
abbrev layerIncl : ((idealPowerMultiple J (n + 1) M).toSheafOfModules : X.Modules) ⟶
    ((idealPowerMultiple J n M).toSheafOfModules : X.Modules) :=
  SheafOfModules.Submodule.homOfLE
    (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_antitone J M (Nat.le_succ n))

/-- The inclusion `ℐ ⁿ⁺¹M ⟶ ℐ ⁿM ⟶ M` is the inclusion `ℐ ⁿ⁺¹M ⟶ M`. -/
theorem layerIncl_comp_ι :
    layerIncl J M n ≫ subIota (idealPowerMultiple J n M) =
      subIota (idealPowerMultiple J (n + 1) M) :=
  SheafOfModules.Submodule.homOfLE_ι _

/-- The exponent-lowering map read on the cokernel of the composite inclusion
`ℐ ⁿ⁺¹M ⟶ ℐ ⁿM ⟶ M`: both this and `Stacks.Algebraization.idealPowerQuotientDrop` are
determined by their compatibility with the quotient projection out of `M`. -/
theorem cokernelIsoOfEq_inv_comp_cokernel_map :
    (cokernelIsoOfEq (C := X.Modules) (layerIncl_comp_ι J M n)).inv ≫
        cokernel.map (C := X.Modules)
          (layerIncl J M n ≫ subIota (idealPowerMultiple J n M))
          (subIota (idealPowerMultiple J n M)) (layerIncl J M n) (𝟙 M)
          (Category.comp_id (obj := X.Modules) _) =
      idealPowerQuotientDrop J (Nat.le_succ n) M := by
  have : Epi (cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) M).ι) :=
    epi_cokernel_π_submodule_ι _
  refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) M).ι)).1 ?_
  refine Eq.trans (π_comp_cokernelIsoOfEq_inv_assoc _ _) ?_
  refine Eq.trans (cokernel.π_desc (C := X.Modules) _ _ _) ?_
  refine Eq.trans (Category.id_comp (obj := X.Modules) _) ?_
  exact (idealPowerQuotientDrop_π J (Nat.le_succ n) M).symm

/-- **The adic layer is the transition kernel**: `ℐ ⁿM/ℐ ⁿ⁺¹M ≅ ker(M/ℐ ⁿ⁺¹M ⟶ M/ℐ ⁿM)`.

The third isomorphism theorem `CategoryTheory.Abelian.cokernelIsoKernelCokernelMap` at
`ℐ ⁿ⁺¹M ⊆ ℐ ⁿM ⊆ M`, whose induced map on the quotients is
`Stacks.Algebraization.idealPowerQuotientDrop` by
`cokernelIsoOfEq_inv_comp_cokernel_map`. -/
def idealPowerLayerKernelIso :
    cokernel (C := X.Modules) (layerIncl J M n) ≅
      kernel (idealPowerQuotientDrop J (Nat.le_succ n) M) :=
  haveI : Mono (subIota (idealPowerMultiple J n M)) :=
    mono_subIota (idealPowerMultiple J n M)
  haveI : IsIso (C := X.Modules)
      (cokernelIsoOfEq (C := X.Modules) (layerIncl_comp_ι J M n)).hom :=
    Iso.isIso_hom (C := X.Modules) _
  CategoryTheory.Abelian.cokernelIsoKernelCokernelMap (C := X.Modules) (layerIncl J M n)
      (subIota (idealPowerMultiple J n M)) ≪≫
    kernelIsoOfEq (C := X.Modules)
      ((Iso.inv_comp_eq _).1 (cokernelIsoOfEq_inv_comp_cokernel_map J M n)) ≪≫
    kernelIsIsoComp (C := X.Modules) _ _

/-! ### The adic layer as a direct image from the closed subscheme -/

/-- The Artin–Rees identity `ℐ·(ℐ ⁿM) = ℐ ⁿ⁺¹M`, read as an equality of cokernels: dividing
`ℐ ⁿM` by `ℐ·(ℐ ⁿM)` is dividing it by the preimage of `ℐ ⁿ⁺¹M`. -/
theorem idealPowerQuotient_one_eq [M.IsQuasicoherent] :
    idealPowerQuotient J 1 ((idealPowerMultiple J n M).toSheafOfModules : X.Modules) =
      cokernel (C := X.Modules)
        ((subComap (idealPowerMultiple J (n + 1) M) (idealPowerMultiple J n M)).ι) :=
  congrArg
    (fun T : ((idealPowerMultiple J n M).toSheafOfModules : X.Modules).Submodule =>
      cokernel (C := X.Modules) (T.ι))
    (Stacks.AlgebraicGeometry.IdealPowerColimit.idealSmul_idealPowSmul_eq J n M)

variable [M.IsQuasicoherent] {V : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v]
  (hv : v.ker = J ^ 1)

include hv in
/-- **The adic layer is the direct image of the restriction of `ℐ ⁿM`**:
`ker(M/ℐ ⁿ⁺¹M ⟶ M/ℐ ⁿM) ≅ v_* v^*(ℐ ⁿM)` for a closed immersion `v` with ideal sheaf `ℐ`.

[Stacks, Tag 0EL1] at the quasi-coherent module `ℐ ⁿM`, whose quotient by `ℐ` is the layer by
the Artin–Rees identity and `Stacks.Algebraization.subComapIso`. -/
def idealPowerLayerPushforwardIso :
    kernel (idealPowerQuotientDrop J (Nat.le_succ n) M) ≅
      (Scheme.Modules.pushforward v).obj ((Scheme.Modules.pullback v).obj
        ((idealPowerMultiple J n M).toSheafOfModules : X.Modules)) :=
  haveI : ((idealPowerMultiple J n M).toSheafOfModules : X.Modules).IsQuasicoherent :=
    idealPowerMultiple_isQuasicoherent J n M
  haveI : Epi (C := X.Modules)
      (subComapHom (idealPowerMultiple J (n + 1) M) (idealPowerMultiple J n M)) :=
    epi_subComapHom
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_antitone J M (Nat.le_succ n))
  (idealPowerLayerKernelIso J M n).symm ≪≫
    (cokernelEpiComp (C := X.Modules)
      (subComapHom (idealPowerMultiple J (n + 1) M) (idealPowerMultiple J n M))
      (layerIncl J M n)).symm ≪≫
    cokernelIsoOfEq (C := X.Modules) (subComapHom_comp_homOfLE
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_antitone J M (Nat.le_succ n))) ≪≫
    eqToIso (idealPowerQuotient_one_eq J M n).symm ≪≫
    idealQuotientPushforwardIso J 1
      ((idealPowerMultiple J n M).toSheafOfModules : X.Modules) v hv

end Layer

/-! ### The layer of a twist -/

section Twist

variable {X : Scheme.{u}} (J : X.IdealSheafData) (L F : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L] (n : ℕ) (d : ℤ)

/-- **Forming the adic layer commutes with twisting**: `(ℐ ⁿℱ)(d) ≅ ℐ ⁿ(ℱ(d))`.

`Stacks.Blowup.reesMultipleTwistIso`, read at `Stacks.Algebraization.idealPowerMultiple` through
`Stacks.Blowup.reesMultiple_eq_idealPowerMultiple`. -/
def idealPowerMultipleTwistIso :
    twistModule X L ((idealPowerMultiple J n F).toSheafOfModules : X.Modules) d ≅
      ((idealPowerMultiple J n (twistModule X L F d)).toSheafOfModules : X.Modules) :=
  eqToIso (congrArg
      (fun N : F.Submodule => twistModule X L (N.toSheafOfModules : X.Modules) d)
      (Stacks.Blowup.reesMultiple_eq_idealPowerMultiple J F n).symm) ≪≫
    Stacks.Blowup.reesMultipleTwistIso J L (n : ℤ) d F ≪≫
    eqToIso (congrArg
      (fun N : (twistModule X L F d).Submodule => (N.toSheafOfModules : X.Modules))
      (Stacks.Blowup.reesMultiple_eq_idealPowerMultiple J (twistModule X L F d) n))

variable [F.IsQuasicoherent] {V : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v]
  (hv : v.ker = J ^ 1)

include hv in
/-- **The transition kernel of the adic tower of a twist is the direct image of a twisted
layer on the closed subscheme.**

`ker(ℱ(d)/ℐ ⁿ⁺¹ℱ(d) ⟶ ℱ(d)/ℐ ⁿℱ(d)) ≅ v_*((v^*(ℐ ⁿℱ)) ⊗ (v^*ℒ)^{⊗ d})`.

The composite of the four steps: the layer is a transition kernel
(`idealPowerLayerKernelIso`), it is a direct image ([Stacks, Tag 0EL1], through
`idealPowerLayerPushforwardIso`), it commutes with the twist
(`idealPowerMultipleTwistIso`), and the twist commutes with the restriction
([Stacks, Tag 0EGK]). -/
def kernelIdealPowerQuotientDropTwistIso :
    kernel (idealPowerQuotientDrop J (Nat.le_succ n) (twistModule X L F d)) ≅
      (Scheme.Modules.pushforward v).obj
        (tensorModules V
          ((Scheme.Modules.pullback v).obj
            ((idealPowerMultiple J n F).toSheafOfModules : X.Modules))
          (tensorPowModule V ((Scheme.Modules.pullback v).obj L) d)) :=
  haveI : (twistModule X L F d).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ _ ‹F.IsQuasicoherent›
      (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L d)
  idealPowerLayerPushforwardIso J (twistModule X L F d) n v hv ≪≫
    (Scheme.Modules.pushforward v).mapIso
      ((Scheme.Modules.pullback v).mapIso (idealPowerMultipleTwistIso J L F n d).symm ≪≫
        pullbackTwistModuleIso v L
          ((idealPowerMultiple J n F).toSheafOfModules : X.Modules) d)

include hv in
/-- **The same identification, with the layer written as `Stacks.Blowup.reesMultiple`.**

This is the spelling in which the degree-`n` piece of
`Stacks.AssociatedGradedFibre.fibreAssociatedGradedModule` is stated
(`fibreAssociatedGradedModule_piece`, which holds by `rfl`), so this is the form that meets the
conclusion of part (2) of [Stacks, Tag 0897] at the fibre. -/
def kernelIdealPowerQuotientDropTwistReesIso :
    kernel (idealPowerQuotientDrop J (Nat.le_succ n) (twistModule X L F d)) ≅
      (Scheme.Modules.pushforward v).obj
        (tensorModules V
          ((Scheme.Modules.pullback v).obj
            ((Stacks.Blowup.reesMultiple J (n : ℤ) F).toSheafOfModules : X.Modules))
          (tensorPowModule V ((Scheme.Modules.pullback v).obj L) d)) :=
  kernelIdealPowerQuotientDropTwistIso J L F n d v hv ≪≫
    eqToIso (congrArg
      (fun N : F.Submodule =>
        (Scheme.Modules.pushforward v).obj
          (tensorModules V
            ((Scheme.Modules.pullback v).obj (N.toSheafOfModules : X.Modules))
            (tensorPowModule V ((Scheme.Modules.pullback v).obj L) d)))
      (Stacks.Blowup.reesMultiple_eq_idealPowerMultiple J F n).symm)

end Twist

end Stacks.Algebraization

end
