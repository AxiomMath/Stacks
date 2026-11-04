module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectAcyclic

/-!
# `Hom_R(N, I)` of an injective sheaf of `R`-modules is acyclic

Let `(C, J)` be a site, `R` a ring, `N` an `R`-module and `I` an injective sheaf of `R`-modules.
The abelian sheaf `Hom_R(N, I) : U ↦ Hom_R(N, I(U))` has vanishing higher cohomology. Its
functor `Hom_R(N, -)` from sheaves of `R`-modules to abelian sheaves has the left adjoint
`X ↦ N ⊗_ℤ X` (sheafified), which keeps the inclusion of a short exact sequence of abelian
sheaves with sectionwise torsion-free quotient a monomorphism; so the argument of
[Stacks, Tag 03FD] for the underlying abelian sheaf of `I`
(`Stacks.InjectiveAcyclic.subsingleton_H_forget₂`, the case `N = R`) applies verbatim
(`ModuleSheafCohomology.ext_eq_zero_of_adjunction`).

This is the acyclicity input of Step 7 of the proof of [Stacks, Tag 03UG]: there `N` is the
dual of the stalk of the locally constant sheaf, over the group ring `A[G]`, and the functor
`Hom_{A[G]}(N, -)` computes the locally constant sheaf from `f_* A`.

## Main definitions

* `Stacks.HomAcyclic.tensorAb`: the functor `X ↦ N ⊗_ℤ X` from abelian groups to `R`-modules.
* `Stacks.HomAcyclic.homAb`: the functor `Y ↦ Hom_R(N, Y)` to abelian groups.
* `Stacks.HomAcyclic.homSheaf`: the abelian sheaf `Hom_R(N, F)` of a sheaf of `R`-modules.

## Main results

* `Stacks.HomAcyclic.subsingleton_H_homSheaf`: `Hⁿ⁺¹(Hom_R(N, I)) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian TensorProduct

universe w v u r w'

namespace Stacks.HomAcyclic

section Algebra

variable {R : Type r} [Ring R] (N : ModuleCat.{max r v} R)

/-- **`X ↦ N ⊗_ℤ X`**, from abelian groups to `R`-modules, `R` acting on `N`. -/
@[simps obj]
def tensorAb : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} R where
  obj X := ModuleCat.of R (N ⊗[ℤ] X)
  map f := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor R N f.hom.toIntLinearMap)
  map_id _ := ModuleCat.hom_ext (TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl)
  map_comp _ _ := ModuleCat.hom_ext (TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl)

/-- **`Y ↦ Hom_R(N, Y)`**, from `R`-modules to abelian groups. -/
abbrev homAb : ModuleCat.{max r v} R ⥤ AddCommGrpCat.{max r v} :=
  preadditiveCoyoneda.obj (op N)

/-- The tensor-hom adjunction `Hom_R(N ⊗_ℤ X, Y) ≃ Hom_ℤ(X, Hom_R(N, Y))`. -/
def tensorHomEquiv (X : AddCommGrpCat.{max r v}) (Y : ModuleCat.{max r v} R) :
    ((tensorAb N).obj X ⟶ Y) ≃ (X ⟶ (homAb N).obj Y) where
  toFun f := AddCommGrpCat.ofHom
    { toFun := fun x => ModuleCat.ofHom
        { toFun := fun n => f (n ⊗ₜ x)
          map_add' := fun a b => by
            rw [TensorProduct.add_tmul]
            exact map_add f.hom _ _
          map_smul' := fun r a => by
            change f.hom (r • (a ⊗ₜ[ℤ] x)) = r • f.hom (a ⊗ₜ[ℤ] x)
            exact map_smul f.hom _ _ }
      map_zero' := by
        refine ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
        change f.hom (n ⊗ₜ[ℤ] (0 : X)) = 0
        rw [TensorProduct.tmul_zero]
        exact map_zero f.hom
      map_add' := fun x y => by
        refine ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
        change f.hom (n ⊗ₜ[ℤ] (x + y)) = f.hom (n ⊗ₜ[ℤ] x) + f.hom (n ⊗ₜ[ℤ] y)
        rw [TensorProduct.tmul_add]
        exact map_add f.hom _ _ }
  invFun g := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lift
    { toFun := fun n =>
        { toFun := fun x => (g x).hom n
          map_add' := fun x y => by rw [map_add]; rfl
          map_smul' := fun z x => by rw [map_zsmul]; rfl }
      map_add' := fun a b => by ext x; simp
      map_smul' := fun r a => by ext x; simp })
  left_inv f := ModuleCat.hom_ext (TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl)
  right_inv g := rfl

/-- **`N ⊗_ℤ -` is left adjoint to `Hom_R(N, -)`.** -/
def tensorHomAdj : tensorAb N ⊣ homAb N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv N
      homEquiv_naturality_left_symm := fun f g =>
        ModuleCat.hom_ext (TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl)
      homEquiv_naturality_right := fun f g => by
        ext x
        exact ModuleCat.hom_ext (LinearMap.ext fun n => rfl) }

/-- **`N ⊗_ℤ -` keeps a monomorphism with torsion-free cokernel a monomorphism.** -/
lemma injective_tensorAb_map {A B P : AddCommGrpCat.{max r v}} (f : A ⟶ B) (g : B ⟶ P)
    [Module.IsTorsionFree ℤ P] (hf : Function.Injective f) (h : Function.Exact f g) :
    Function.Injective ((tensorAb N).map f) :=
  ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree f.hom.toIntLinearMap
    g.hom.toIntLinearMap hf h N

end Algebra

section Site

variable {C : Type u} [Category.{w} C] (J : GrothendieckTopology C) {R : Type r} [Ring R]
  (N : ModuleCat.{max r v} R)
  [HasSheafify J AddCommGrpCat.{max r v}] [HasSheafify J (ModuleCat.{max r v} R)]
  [J.HasSheafCompose (homAb N)]

/-- The sheafified `X ↦ N ⊗_ℤ X` from abelian sheaves to sheaves of `R`-modules. -/
abbrev sheafTensor : Sheaf J AddCommGrpCat.{max r v} ⥤ Sheaf J (ModuleCat.{max r v} R) :=
  Sheaf.composeAndSheafify J (tensorAb N)

/-- **The abelian sheaf `Hom_R(N, F)`** of a sheaf `F` of `R`-modules. -/
abbrev homSheaf : Sheaf J (ModuleCat.{max r v} R) ⥤ Sheaf J AddCommGrpCat.{max r v} :=
  sheafCompose J (homAb N)

/-- The sheafified `N ⊗_ℤ -` is left adjoint to `Hom_R(N, -)`. -/
def sheafTensorHomAdj : sheafTensor J N ⊣ homSheaf J N :=
  Sheaf.adjunction J (tensorHomAdj N)

omit [J.HasSheafCompose (homAb N)] in
/-- **The sheafified `N ⊗_ℤ -` keeps the inclusion of a short exact sequence with sectionwise
torsion-free quotient a monomorphism.** -/
lemma mono_sheafTensor_map (S : ShortComplex (Sheaf J AddCommGrpCat.{max r v}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono ((sheafTensor J N).map S.f) := by
  have := hS.mono_f
  have hpre : Mono (Functor.whiskerRight S.f.hom (tensorAb N)) := by
    have (U : Cᵒᵖ) : Mono ((tensorAb N).map (S.f.hom.app U)) := by
      have := hP U
      let E := sheafToPresheaf J AddCommGrpCat.{max r v} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max r v}).obj U
      obtain ⟨hE, hEm⟩ :=
        (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp inferInstance S hS
      rw [ModuleCat.mono_iff_injective]
      exact injective_tensorAb_map N (S.f.hom.app U) (S.g.hom.app U)
        ((AddCommGrpCat.mono_iff_injective _).mp hEm)
        ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp hE)
    exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ this
  show Mono ((presheafToSheaf J _).map (Functor.whiskerRight S.f.hom (tensorAb N)))
  infer_instance

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max r v})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max r v})]

/-- **`Hom_R(N, I)` is `Ext`-acyclic against every sectionwise torsion-free abelian sheaf**, for
an injective sheaf `I` of `R`-modules. -/
lemma ext_homSheaf_eq_zero_of_isTorsionFree (I : Sheaf J (ModuleCat.{max r v} R)) [Injective I]
    (X : Sheaf J AddCommGrpCat.{max r v}) (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U))
    (n : ℕ) (e : Ext.{w'} X ((homSheaf J N).obj I) (n + 1)) : e = 0 := by
  let P : Sheaf J AddCommGrpCat.{max r v} → Prop :=
    fun F => ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)
  have key := ModuleSheafCohomology.ext_eq_zero_of_adjunction (sheafTensor J N) (homSheaf J N)
    (sheafTensorHomAdj J N) P (fun f _ hY => ModuleSheafCohomology.isTorsionFree_of_mono J f hY)
    (ModuleSheafCohomology.exists_isTorsionFree_epi J)
    (fun S hS hP => mono_sheafTensor_map J N S hS hP) I n X hX
  exact key e

/-- **`Hⁿ⁺¹(Hom_R(N, I)) = 0`** for an injective sheaf `I` of `R`-modules. -/
lemma subsingleton_H_homSheaf (I : Sheaf J (ModuleCat.{max r v} R)) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H.{w'} ((homSheaf J N).obj I) (n + 1)) := by
  refine ⟨fun a b => ?_⟩
  have hX : ∀ U, Module.IsTorsionFree ℤ
      (((constantSheaf J AddCommGrpCat.{max r v}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.obj U) :=
    ModuleSheafCohomology.isTorsionFree_sheafify J _ (fun U => by
      show Module.IsTorsionFree ℤ (ULift ℤ)
      exact Function.Injective.moduleIsTorsionFree (fun x : ULift ℤ => x.down)
        ULift.down_injective (fun _ _ => rfl))
  rw [ext_homSheaf_eq_zero_of_isTorsionFree J N I _ hX n a,
    ext_homSheaf_eq_zero_of_isTorsionFree J N I _ hX n b]

end Site

end Stacks.HomAcyclic

end
