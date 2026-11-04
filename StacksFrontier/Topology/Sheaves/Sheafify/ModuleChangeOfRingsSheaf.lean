module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor

/-!
# The universal property of the change-of-rings tensor product of sheaves

Let `X` be a topological space and let `α : O ⟶ O'` be a morphism of sheaves of commutative
rings on `X`. For a sheaf of `O`-modules `G` and a sheaf of `O'`-modules `F` there is a canonical
bijection
$$
  \mathrm{Hom}_{O}(G, F_{O}) = \mathrm{Hom}_{O'}(O' \otimes_{O} G, F),
$$
where `O' ⊗_O G := (O' ⊗_{p,O} G)^#` is the sheafification
`Stacks.Sheafify.ModuleStalkTensor.tensorSheaf` of the sectionwise tensor product presheaf
`U ↦ O'(U) ⊗_{O(U)} G(U)` (`Stacks.Sheafify.ModuleStalkTensor.tensorPresheafOfModules`).

## Main results

* `Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafHomEquiv`: the presheaf-level universal
  property `Hom_{O'}(O' ⊗_{p,O} G, M) ≃ Hom_O(G, M_O)`.
* `Stacks.Sheafify.ChangeOfRingsAdjunction.tensorSheafHomEquiv`: the bijection
  `Hom_{O'}(O' ⊗_O G, F) ≃ Hom_O(G, F_O)` for sheaves of modules.
* `Stacks.Sheafify.ChangeOfRingsAdjunction.nonempty_tensorSheafHomEquiv`: existence form.
-/

@[expose] public section

open CategoryTheory TensorProduct Stacks.Sheafify.ModuleStalkTensor

namespace Stacks.Sheafify.ChangeOfRingsAdjunction

section Presheaf

variable {X : TopCat} (O O' : TopCat.Presheaf CommRingCat X) (α : O ⟶ O')
  (F : PresheafOfModules (ringPresheaf O)) (M : PresheafOfModules (ringPresheaf O'))

/-- The morphism `ringPresheaf O ⟶ ringPresheaf O'` of presheaves of (not necessarily
commutative) rings underlying a morphism `α : O ⟶ O'` of presheaves of commutative rings. -/
abbrev ringPresheafMap : ringPresheaf O ⟶ ringPresheaf O' :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-- Restriction of scalars along `α` of a presheaf of `O'`-modules: the presheaf of
`O`-modules `M_O`, which sectionwise is `M(U)` with `O(U)` acting through
`α.app U : O(U) ⟶ O'(U)`. -/
noncomputable abbrev restrictPresheaf : PresheafOfModules (ringPresheaf O) :=
  (PresheafOfModules.restrictScalars (ringPresheafMap O O' α)).obj M

/-- Sectionwise form of the universal property: over a single open `U`, the `O'(U)`-linear maps
`O'(U) ⊗_{O(U)} F(U) ⟶ M(U)` are in bijection with the `O(U)`-linear maps `F(U) ⟶ M(U)_{O(U)}`. -/
noncomputable def sectionEquiv (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    ((tensorPresheafOfModules O O' α F).obj U ⟶ M.obj U) ≃
      (F.obj U ⟶ (restrictPresheaf O O' α M).obj U) :=
  letI : Algebra (O.obj U) (O'.obj U) := (α.app U).hom.toAlgebra
  letI : Module (O'.obj U) ((restrictPresheaf O O' α M).obj U) :=
    inferInstanceAs (Module (O'.obj U) (M.obj U))
  letI : IsScalarTower (O.obj U) (O'.obj U) ((restrictPresheaf O O' α M).obj U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  ModuleCat.homEquiv.trans
    (((LinearMap.liftBaseChangeEquiv (O'.obj U) (R := O.obj U) (M := F.obj U)
        (N := (restrictPresheaf O O' α M).obj U)).toEquiv.symm).trans ModuleCat.homEquiv.symm)

/-- The `O'(U)`-linear map `O'(U) ⊗_{O(U)} F(U) ⟶ M(U)`, `s ⊗ m ↦ s • g m`, induced by an
`O(U)`-linear map `g : F(U) ⟶ M(U)_{O(U)}`. -/
noncomputable def liftLin (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (g : F.obj U ⟶ (restrictPresheaf O O' α M).obj U) :
    letI : Algebra (O.obj U) (O'.obj U) := (α.app U).hom.toAlgebra
    letI : Module (O'.obj U) (ToType ((restrictPresheaf O O' α M).obj U)) :=
      inferInstanceAs (Module (O'.obj U) (ToType (M.obj U)))
    TensorProduct (O.obj U) (O'.obj U) (F.obj U) →ₗ[O'.obj U]
      ToType ((restrictPresheaf O O' α M).obj U) :=
  letI : Algebra (O.obj U) (O'.obj U) := (α.app U).hom.toAlgebra
  letI : Module (O'.obj U) (ToType ((restrictPresheaf O O' α M).obj U)) :=
    inferInstanceAs (Module (O'.obj U) (ToType (M.obj U)))
  letI : IsScalarTower (O.obj U) (O'.obj U) (ToType ((restrictPresheaf O O' α M).obj U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange (O'.obj U) (N := ToType ((restrictPresheaf O O' α M).obj U)) g.hom

/-- `liftLin` on a pure tensor. -/
theorem liftLin_tmul (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (g : F.obj U ⟶ (restrictPresheaf O O' α M).obj U) (s : O'.obj U) (m : F.obj U) :
    letI : Algebra (O.obj U) (O'.obj U) := (α.app U).hom.toAlgebra
    letI : Module (O'.obj U) (ToType ((restrictPresheaf O O' α M).obj U)) :=
      inferInstanceAs (Module (O'.obj U) (ToType (M.obj U)))
    liftLin O O' α F M U g (s ⊗ₜ[O.obj U] m) = s • g.hom m := rfl

/-- The value of `sectionEquiv` on a section: `Φ ↦ (m ↦ Φ (1 ⊗ m))`. -/
theorem sectionEquiv_apply (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (Φ : (tensorPresheafOfModules O O' α F).obj U ⟶ M.obj U) (m : F.obj U) :
    letI : Algebra (O.obj U) (O'.obj U) := (α.app U).hom.toAlgebra
    (sectionEquiv O O' α F M U Φ).hom m = Φ.hom (1 ⊗ₜ[O.obj U] m) := rfl

/-- Restriction along `i` of a pure tensor, as a map of the underlying `ModuleCat` objects. -/
theorem tensorMap_tmul {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : O'.obj U) (m : F.obj U) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    (tensorPresheafOfModules O O' α F).map i (s ⊗ₜ[O.obj U] m)
      = (O'.map i).hom s ⊗ₜ[O.obj V] (F.restrictₛₗ i m) := by
  let := (α.app U).hom.toAlgebra
  let := (α.app V).hom.toAlgebra
  show (TensorProduct.map (o'Semilin O O' α U V i) (fSemilin O F U V i)) (s ⊗ₜ m) = _
  rw [TensorProduct.map_tmul]
  rfl

/-- Restriction along `i` of a pure tensor, as the semilinear map `tensorSemilin`. -/
theorem tensorSemilin_tmul {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : O'.obj U) (m : F.obj U) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    tensorSemilin O O' α F U V i (s ⊗ₜ[O.obj U] m)
      = (O'.map i).hom s ⊗ₜ[O.obj V] (F.restrictₛₗ i m) := by
  exact tensorMap_tmul O O' α F i s m

/-- The family of lifts `liftLin` of the components of a morphism `g : F ⟶ M_O` is compatible
with the restriction maps. -/
theorem liftLin_naturality (g : F ⟶ restrictPresheaf O O' α M)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    ∀ t : TensorProduct (O.obj U) (O'.obj U) (F.obj U),
      liftLin O O' α F M V (g.app V) (tensorSemilin O O' α F U V i t)
        = (restrictPresheaf O O' α M).restrictₛₗ i (liftLin O O' α F M U (g.app U) t) := by
  let := (α.app U).hom.toAlgebra
  let := (α.app V).hom.toAlgebra
  let : Module (O'.obj U) (ToType ((restrictPresheaf O O' α M).obj U)) :=
    inferInstanceAs (Module (O'.obj U) (ToType (M.obj U)))
  let : Module (O'.obj V) (ToType ((restrictPresheaf O O' α M).obj V)) :=
    inferInstanceAs (Module (O'.obj V) (ToType (M.obj V)))
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [tensorSemilin_tmul, liftLin_tmul, liftLin_tmul]
      have h1 : (restrictPresheaf O O' α M).restrictₛₗ i (s • ((g.app U).hom m))
          = (O'.map i).hom s • ((restrictPresheaf O O' α M).restrictₛₗ i ((g.app U).hom m)) :=
        PresheafOfModules.map_smul M i s ((g.app U).hom m)
      refine Eq.trans ?_ h1.symm
      exact congrArg (fun y => (O'.map i).hom s • y) (PresheafOfModules.naturality_apply g i m)
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- **The universal property of the tensor product presheaf.** For presheaves of commutative rings
`α : O ⟶ O'` on `X`, a presheaf of `O`-modules `F` and a presheaf of `O'`-modules `M`, the
morphisms `O' ⊗_{p,O} F ⟶ M` of presheaves of `O'`-modules are in canonical bijection with the
morphisms `F ⟶ M_O` of presheaves of `O`-modules. The bijection sends `Φ` to `m ↦ Φ(1 ⊗ m)` and its
inverse sends `g` to the sectionwise lift `s ⊗ m ↦ s • g(m)`. -/
noncomputable def tensorPresheafHomEquiv :
    (tensorPresheafOfModules O O' α F ⟶ M) ≃ (F ⟶ restrictPresheaf O O' α M) where
  toFun Φ :=
    { app := fun U => sectionEquiv O O' α F M U (Φ.app U)
      naturality := fun {U V} i => by
        let := (α.app U).hom.toAlgebra
        let := (α.app V).hom.toAlgebra
        ext m
        have h := PresheafOfModules.naturality_apply Φ i (1 ⊗ₜ[O.obj U] m)
        have e := tensorMap_tmul O O' α F i (1 : O'.obj U) m
        rw [map_one] at e
        rw [e] at h
        exact h }
  invFun g :=
    { app := fun U => (sectionEquiv O O' α F M U).symm (g.app U)
      naturality := fun {U V} i => by
        ext t
        exact liftLin_naturality O O' α F M g i t }
  left_inv Φ :=
    PresheafOfModules.hom_ext fun U => (sectionEquiv O O' α F M U).symm_apply_apply _
  right_inv g :=
    PresheafOfModules.hom_ext fun U => (sectionEquiv O O' α F M U).apply_symm_apply _

/-- Existence form of `tensorPresheafHomEquiv`. -/
theorem nonempty_tensorPresheafHomEquiv :
    Nonempty ((tensorPresheafOfModules O O' α F ⟶ M) ≃ (F ⟶ restrictPresheaf O O' α M)) :=
  ⟨tensorPresheafHomEquiv O O' α F M⟩

end Presheaf

section Sheaf

variable {X : TopCat} (O O' : TopCat.Sheaf CommRingCat X) (α : O ⟶ O')

/-- The morphism `ringSheaf O ⟶ ringSheaf O'` of sheaves of (not necessarily commutative)
rings underlying a morphism `α : O ⟶ O'` of sheaves of commutative rings. -/
noncomputable abbrev ringSheafMap : ringSheaf O ⟶ ringSheaf O' :=
  (CategoryTheory.sheafCompose _ (forget₂ CommRingCat RingCat)).map α

variable (G : SheafOfModules (ringSheaf O)) (F : SheafOfModules (ringSheaf O'))

/-- Let `α : O ⟶ O'` be a morphism of sheaves of commutative rings on a topological space `X`,
let `G` be a sheaf of `O`-modules and let `F` be a sheaf of `O'`-modules. There is a canonical
bijection `Hom_{O'}(O' ⊗_O G, F) ≃ Hom_O(G, F_O)`, where `O' ⊗_O G = (O' ⊗_{p,O} G)^#` is
`Stacks.Sheafify.ModuleStalkTensor.tensorSheaf`, the sheafification of the sectionwise tensor
product presheaf, and `F_O` is restriction of scalars along `α`. -/
@[stacks 008A]
noncomputable def tensorSheafHomEquiv :
    (tensorSheaf O O' α G ⟶ F) ≃
      (G ⟶ (SheafOfModules.restrictScalars (ringSheafMap O O' α)).obj F) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf O').obj)).trans
    ((tensorPresheafHomEquiv O.presheaf O'.presheaf (αp O O' α) G.val
        ((PresheafOfModules.restrictScalars (𝟙 (ringSheaf O').obj)).obj F.val)).trans
      ((SheafOfModules.fullyFaithfulForget (ringSheaf O)).homEquiv (X := G)
        (Y := (SheafOfModules.restrictScalars (ringSheafMap O O' α)).obj F)).symm)

/-- Existence form of `tensorSheafHomEquiv`: the sets `Hom_{O'}(O' ⊗_O G, F)` and
`Hom_O(G, F_O)` are in bijection. -/
@[stacks 008A]
theorem nonempty_tensorSheafHomEquiv :
    Nonempty ((tensorSheaf O O' α G ⟶ F) ≃
      (G ⟶ (SheafOfModules.restrictScalars (ringSheafMap O O' α)).obj F)) :=
  ⟨tensorSheafHomEquiv O O' α G F⟩

end Sheaf

end Stacks.Sheafify.ChangeOfRingsAdjunction
