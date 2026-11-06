module

public import StacksFrontier.Algebra.Module.Reflexive.PlaneSubalgebra
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentTensor
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineDualSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.TildeReflexiveRank
public import Mathlib.Algebra.Field.ULift

/-!
# Rank-one coherent reflexive modules need not be invertible

Let `X` be an integral locally Noetherian scheme and `𝒞` the category of coherent reflexive
`𝒪_X`-modules, with its hull tensor product `ℱ ⊗_𝒞 𝒢 = (ℱ ⊗_{𝒪_X} 𝒢)^∨∨` and its internal Hom.
A rank-one object of `𝒞` need not be invertible for that tensor product: the two assertions of
[Stacks, Tag 0EBH] that fail are

* the unit law `ℱ ⊗_𝒞 ℱ^∨ ≅ 𝒪_X`, and
* the tensor–Hom identity `ℋom_{𝒪_X}(ℱ, 𝒢) ≅ ℱ^∨ ⊗_𝒞 𝒢`.

Both fail already on the affine scheme attached to the nonnormal Noetherian domain
`R = k[y, x², xy, x³] ⊆ k[x, y] = P` of [Stacks, Tag 0EBB], with `ℱ = P~` the sheaf associated
to `P` viewed as an `R`-module.  Writing `m = (y, x², xy, x³)` for the distinguished maximal
ideal of `R`, Example 0EBB computes the two successive `R`-duals of `P` to be `m` and `P`; so
`P~` is coherent, reflexive and of rank one, while

* `P~ ⊗_𝒞 (P~)^∨ ≅ m~`, and `m ≅ R` would force `R ≅ P` and hence Serre's condition `(S₂)`
  for `R`, which fails;
* `ℋom_{𝒪_X}(P~, P~) ≅ P~`, because every `R`-endomorphism of `P` is multiplication by its
  value at `1`, whereas `(P~)^∨ ⊗_𝒞 P~ ≅ m~`, and `P ≅ m` is impossible because the polynomial
  generating the corresponding functional would have to divide both `y` and `x²`.

## Main definitions

* `planeRing`, `planeModule`, `planeIdealModule`: the ring `R`, the module `P` and the module
  `m` of Example 0EBB, at the types `CommRingCat` and `ModuleCat`.
* `planeSheaf`: `P~` as an object of the category of coherent reflexive modules on `Spec R`.

## Main results

* `not_forall_fiberRank_one_tensorObj_dualObj_iso_unit`: **the unit clause of
  [Stacks, Tag 0EBH]** — it is not the case that every rank-one coherent reflexive module on an
  integral locally Noetherian scheme has its dual as a tensor inverse.
* `not_forall_rank_one_sheafHom_iso_dualObj_tensorObj`: **the internal-Hom clause of
  [Stacks, Tag 0EBH]** — it is not the case that the sheaf Hom of two rank-one coherent
  reflexive modules is the hull tensor product of the dual of the first with the second.
* `tensorObj_planeSheaf_dualObj_iso`, `tensorObj_dualObj_planeSheaf_iso`,
  `sheafHom_planeSheaf_iso`: the three computations behind those failures, namely
  `P~ ⊗_𝒞 (P~)^∨ ≅ m~`, `(P~)^∨ ⊗_𝒞 P~ ≅ m~` and `ℋom(P~, P~) ≅ P~`.
* `fiberRank_planeSheaf`, `rank_stalk_planeSheaf`: `P~` has rank one, at the generic point and
  in fact at every point.

Rank one is measured at the generic point by `fiberRank`, the rank function of
[Stacks, Tag 05P2], in the unit clause, and by the rank of the stalk over the local ring at every
point in the internal-Hom clause. The nonisomorphisms are of the underlying `𝒪_X`-modules.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0EBB](https://stacks.math.columbia.edu/tag/0EBB)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive unitModule dualSheaf)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules)
open AlgebraicGeometry.CoherentReflexive (tensorObj dualObj)
open Stacks.PlaneSubalgebra

universe u

namespace AlgebraicGeometry

/-! ### The example of Stacks Tag 0EBB as a sheaf on an affine scheme -/

/-- The base field of the counterexample, a copy of the rationals in the ambient universe. -/
abbrev planeBase : Type u := ULift.{u} ℚ

/-- The nonnormal Noetherian domain `R = k[y, x², xy, x³] ⊆ k[x, y]` of [Stacks, Tag 0EBB],
as an object of `CommRingCat`. -/
noncomputable abbrev planeRing : CommRingCat.{u} :=
  CommRingCat.of (adjoinGenerators planeBase.{u})

/-- The polynomial ring `k[x, y]`, as a module over `R = k[y, x², xy, x³]`. -/
noncomputable abbrev planeModule : ModuleCat.{u} planeRing.{u} :=
  ModuleCat.of planeRing.{u} (plane planeBase.{u})

/-- The ideal `m` is a module over `planeRing`, through its carrier `adjoinGenerators`
(instance search no longer finds it through `CommRingCat.of`). -/
noncomputable instance moduleGeneratorIdeal :
    Module planeRing.{u} (generatorIdeal planeBase.{u}) :=
  Submodule.module (generatorIdeal planeBase.{u})

/-- The distinguished maximal ideal `m = (y, x², xy, x³)` of `R`, as an `R`-module. -/
noncomputable abbrev planeIdealModule : ModuleCat.{u} planeRing.{u} :=
  ModuleCat.of planeRing.{u} (generatorIdeal planeBase.{u})

/-- The element `y` of the distinguished maximal ideal `m` of `R`. -/
noncomputable def planeIdealGenerator : generatorIdeal planeBase.{u} :=
  ⟨⟨MvPolynomial.X 1, y_mem planeBase.{u}⟩, y_mem_generatorIdeal planeBase.{u}⟩

/-- The `R`-linear functional on `k[x, y]` corresponding to `y ∈ m` under the duality of
Example 0EBB: multiplication by `y`, which lands in `R`. -/
noncomputable def planeFunctional : Module.Dual planeRing.{u} planeModule.{u} :=
  (dualPlaneEquiv planeBase.{u}).symm planeIdealGenerator.{u}

/-- The functional attached to `y` multiplies by `y`. -/
theorem coe_planeFunctional_apply (q : plane planeBase.{u}) :
    ((planeFunctional.{u} q : adjoinGenerators planeBase.{u}) : plane planeBase.{u}) =
      MvPolynomial.X (1 : Fin 2) * q := by
  have h := dualPlaneEquiv_mul_apply planeBase.{u} planeFunctional.{u} q
  rw [planeFunctional, LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The functional of Example 0EBB attached to `y` is injective. -/
theorem injective_planeFunctional : Function.Injective planeFunctional.{u} := by
  intro a b hab
  refine mul_left_cancel₀ (MvPolynomial.X_ne_zero (1 : Fin 2)) ?_
  rw [← coe_planeFunctional_apply, ← coe_planeFunctional_apply, hab]

/-- The `R`-rank of `k[x, y]` is one. -/
theorem finrank_planeModule : Module.finrank planeRing.{u} planeModule.{u} = 1 :=
  finrank_eq_one_of_injective (Algebra.linearMap planeRing.{u} planeModule.{u})
    Subtype.val_injective planeFunctional.{u} injective_planeFunctional.{u}

/-- `P~` is coherent on `Spec R`. -/
instance isCoherent_tilde_planeModule :
    _root_.SheafOfModules.IsCoherent (tilde planeModule.{u}) :=
  tilde_isCoherent_of_finite planeModule.{u}

/-- `P~` is a reflexive `𝒪_{Spec R}`-module. -/
theorem isReflexive_tilde_planeModule : IsReflexive (tilde planeModule.{u}) :=
  isReflexive_tilde planeModule.{u}

/-- The sheaf `P~` associated to `k[x, y]` on `Spec R`, as a coherent reflexive module. -/
noncomputable def planeSheaf : CoherentReflexiveModules (Spec planeRing.{u}) :=
  ⟨⟨tilde planeModule.{u}, isCoherent_tilde_planeModule.{u}⟩, isReflexive_tilde_planeModule.{u}⟩

/-- `P~` has fibre rank one at the generic point of `Spec R`. -/
theorem fiberRank_planeSheaf :
    Scheme.Modules.fiberRank (tilde planeModule.{u}) (genericPoint (Spec planeRing.{u})) = 1 :=
  fiberRank_tilde_genericPoint_eq_one planeModule.{u} planeFunctional.{u}
    injective_planeFunctional.{u}

/-- `P~` has rank one at *every* point of `Spec R`, not only at the generic point. -/
theorem rank_stalk_planeSheaf (x : Spec planeRing.{u}) :
    Module.rank ((Spec planeRing.{u}).presheaf.stalk x)
      ((tilde planeModule.{u}).presheaf.stalk x) = 1 :=
  rank_stalk_tilde_eq_one planeModule.{u} finrank_planeModule.{u} x

/-! ### The three computations -/

/-- **The dual of `P~` is `m~`.** -/
noncomputable def dualSheaf_tilde_planeModule_iso :
    dualSheaf (tilde planeModule.{u}) ≅ tilde planeIdealModule.{u} :=
  have : Module.FinitePresentation planeRing.{u} planeModule.{u} :=
    Module.finitePresentation_of_finite _ _
  dualSheafTildeIso planeRing.{u} planeModule.{u} ≪≫
    (tilde.functor planeRing.{u}).mapIso (dualPlaneEquiv planeBase.{u}).toModuleIso

/-- The ideal `m` is a finitely generated `R`-module. -/
instance finite_planeIdealModule : Module.Finite planeRing.{u} planeIdealModule.{u} :=
  Module.IsNoetherian.finite _ _

/-- **`P~ ⊗_𝒞 (P~)^∨ ≅ m~`.**  The hull tensor product of the rank-one coherent reflexive
module `P~` with its dual is the sheaf associated to the ideal `m`. -/
noncomputable def tensorObj_planeSheaf_dualObj_iso :
    (tensorObj planeSheaf.{u} (dualObj planeSheaf.{u})).obj.obj ≅ tilde planeIdealModule.{u} :=
  doubleDualTensorTildeIso planeRing.{u} (Iso.refl (tilde planeModule.{u}))
      dualSheaf_tilde_planeModule_iso.{u} ≪≫
    (tilde.functor planeRing.{u}).mapIso
      (((TensorProduct.comm planeRing.{u} (plane planeBase.{u})
        (generatorIdeal planeBase.{u})).dualMap.dualMap).trans
        (nonempty_dual_dual_tensor_equiv planeBase.{u}).some).toModuleIso

/-- **`(P~)^∨ ⊗_𝒞 P~ ≅ m~`.**  The hull tensor product of the dual of `P~` with `P~` is the
sheaf associated to the ideal `m`. -/
noncomputable def tensorObj_dualObj_planeSheaf_iso :
    (tensorObj (dualObj planeSheaf.{u}) planeSheaf.{u}).obj.obj ≅ tilde planeIdealModule.{u} :=
  doubleDualTensorTildeIso planeRing.{u} dualSheaf_tilde_planeModule_iso.{u}
      (Iso.refl (tilde planeModule.{u})) ≪≫
    (tilde.functor planeRing.{u}).mapIso
      (nonempty_dual_dual_tensor_equiv planeBase.{u}).some.toModuleIso

/-- **`ℋom_{𝒪_X}(P~, P~) ≅ P~`.** -/
noncomputable def sheafHom_planeSheaf_iso :
    Stacks.SheafOfModules.sheafHomSpace (Spec planeRing.{u}).toRingedSpace
        (tilde planeModule.{u}) (tilde planeModule.{u}) ≅ tilde planeModule.{u} :=
  have : Module.FinitePresentation planeRing.{u} planeModule.{u} :=
    Module.finitePresentation_of_finite _ _
  (internalHomTildeIso planeRing.{u} planeModule.{u} planeModule.{u}
      (sheafHomPackage (Spec planeRing.{u}) (tilde planeModule.{u})
        (tilde planeModule.{u}))).iso ≪≫
    (tilde.functor planeRing.{u}).mapIso
      ((ModuleCat.homLinearEquiv (M := planeModule.{u}) (N := planeModule.{u})
        (S := planeRing.{u})).trans (endEquiv planeBase.{u})).toModuleIso

/-! ### The two failures -/

/-- An isomorphism of associated sheaves on `Spec R` gives a linear equivalence of modules. -/
private theorem nonempty_linearEquiv_of_tilde_iso {M N : ModuleCat.{u} planeRing.{u}}
    (e : tilde M ≅ tilde N) : Nonempty (M ≃ₗ[planeRing.{u}] N) :=
  ⟨((tilde.fullyFaithfulFunctor (R := planeRing.{u})).preimageIso e).toLinearEquiv⟩

/-- On an integral locally Noetherian scheme a coherent reflexive module of rank one at the
generic point need not have its dual as a tensor inverse for the hull tensor product. -/
@[stacks 0EBH "unit_failure"]
theorem not_forall_fiberRank_one_tensorObj_dualObj_iso_unit :
    ¬ ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
        (F : CoherentReflexiveModules X),
        Scheme.Modules.fiberRank (F.obj.obj : X.Modules) (genericPoint X) = 1 →
        Nonempty ((tensorObj F (dualObj F)).obj.obj ≅ unitModule X) := by
  intro h
  obtain ⟨e⟩ := h (Spec planeRing.{u}) planeSheaf.{u} fiberRank_planeSheaf.{u}
  exact not_nonempty_linearEquiv_generatorIdeal_self planeBase.{u}
    (nonempty_linearEquiv_of_tilde_iso
      (tensorObj_planeSheaf_dualObj_iso.{u}.symm ≪≫ e ≪≫ tildeSelf.symm))

/-- On an integral locally Noetherian scheme the sheaf Hom of two coherent reflexive modules of
rank one at every point need not be the hull tensor product of the dual of the first with the
second. -/
@[stacks 0EBH "hom_failure"]
theorem not_forall_rank_one_sheafHom_iso_dualObj_tensorObj :
    ¬ ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
        (F G : CoherentReflexiveModules X),
        (∀ x : X, Module.rank (X.presheaf.stalk x)
          ((show X.Modules from F.obj.obj).presheaf.stalk x) = 1) →
        (∀ x : X, Module.rank (X.presheaf.stalk x)
          ((show X.Modules from G.obj.obj).presheaf.stalk x) = 1) →
        Nonempty (Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace F.obj.obj G.obj.obj ≅
          (tensorObj (dualObj F) G).obj.obj) := by
  intro h
  obtain ⟨e⟩ := h (Spec planeRing.{u}) planeSheaf.{u} planeSheaf.{u}
    rank_stalk_planeSheaf.{u} rank_stalk_planeSheaf.{u}
  exact not_nonempty_linearEquiv_plane_generatorIdeal planeBase.{u}
    (nonempty_linearEquiv_of_tilde_iso
      (sheafHom_planeSheaf_iso.{u}.symm ≪≫ e ≪≫ tensorObj_dualObj_planeSheaf_iso.{u}))

end AlgebraicGeometry

end
