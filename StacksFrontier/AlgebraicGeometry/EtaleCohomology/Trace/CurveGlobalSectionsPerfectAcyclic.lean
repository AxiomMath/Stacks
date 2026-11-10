module

public import StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalarsInt
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.Homology.Perfect.BalancedDerivedTensor

/-!
# The underlying abelian sheaf of an injective sheaf of modules is acyclic

Let `(C, J)` be a site and `Λ` a ring, not necessarily commutative. For an injective object `I`
of the category of sheaves of `Λ`-modules, the underlying sheaf of abelian groups has vanishing
higher cohomology: `Hⁿ(I) = 0` for `n ≥ 1`, with `CategoryTheory.Sheaf.H` computed in the
category of abelian sheaves. This is the acyclicity input of [Stacks, Tag 03FD], here for an
arbitrary ring and at every coefficient universe.

The argument is the one of the source. Forgetting to abelian groups has the left adjoint
`F ↦ Λ ⊗[ℤ] F` (sheafified), built from `Stacks.NoncommChangeOfRings.extendScalars`; on a short
exact sequence of abelian sheaves whose quotient is sectionwise torsion-free this left adjoint
keeps the inclusion a monomorphism, so `ModuleSheafCohomology.ext_eq_zero_of_adjunction` gives the
vanishing of `Extⁿ⁺¹(X, I)` for every sectionwise torsion-free abelian sheaf `X`, in particular for
the constant sheaf `ℤ` which corepresents global sections.

## Main results

* `Stacks.InjectiveAcyclic.ext_forget₂_eq_zero_of_isTorsionFree`: the `Ext`-vanishing against a
  sectionwise torsion-free abelian sheaf.
* `Stacks.InjectiveAcyclic.subsingleton_H_forget₂`: `Hⁿ⁺¹(I) = 0`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe w v u r w'

namespace Stacks.InjectiveAcyclic

/-! ### Abelian groups as `ℤ`-modules -/

/-- An abelian group read as a `ℤ`-module, as an explicit functor. -/
def ofAb : AddCommGrpCat.{v} ⥤ ModuleCat.{v} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Reading abelian groups as `ℤ`-modules is left adjoint to forgetting.** Both hom-sets are
the additive maps. -/
def ofAbAdj : ofAb ⊣ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => AddCommGrpCat.ofHom f.hom.toAddMonoidHom
          invFun := fun g => ModuleCat.ofHom (StacksDraft.Perfect.intLinearMapOfAddHom g.hom)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

/-! ### Extension of scalars from abelian groups -/

section ExtendScalars

variable (Λ : Type r) [Ring Λ]

/-- **`A ↦ Λ ⊗[ℤ] A`**, from abelian groups to left `Λ`-modules. -/
def extendScalarsAb : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} Λ :=
  (ofAb : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} ℤ) ⋙
    Stacks.NoncommChangeOfRings.extendScalars.{v} (Int.castRingHom Λ)

/-- `A ↦ Λ ⊗[ℤ] A` is left adjoint to forgetting a `Λ`-module to its abelian group. -/
def extendScalarsAbAdj : (extendScalarsAb Λ : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} Λ) ⊣
    (ModuleCat.restrictScalars.{max r v} (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{max r v} ℤ) AddCommGrpCat.{max r v}) :=
  (ofAbAdj : (ofAb : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} ℤ) ⊣ _).comp
    (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{v} (Int.castRingHom Λ))

/-- **`Λ ⊗[ℤ] -` keeps a monomorphism with torsion-free cokernel a monomorphism.** -/
lemma injective_extendScalarsAb_map {A B P : AddCommGrpCat.{max r v}} (f : A ⟶ B) (g : B ⟶ P)
    [Module.IsTorsionFree ℤ P] (hf : Function.Injective f) (h : Function.Exact f g) :
    Function.Injective
      ((extendScalarsAb Λ : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} Λ).map f) :=
  Stacks.NoncommChangeOfRings.map_intCast_injective (B := Λ) f.hom.toIntLinearMap
    g.hom.toIntLinearMap hf h

end ExtendScalars

/-! ### The acyclicity on a site -/

section Site

variable {C : Type u} [Category.{w} C] (J : GrothendieckTopology C) (Λ : Type r) [Ring Λ]
  [HasSheafify J AddCommGrpCat.{max r v}] [HasSheafify J (ModuleCat.{max r v} Λ)]
  [J.HasSheafCompose (ModuleCat.restrictScalars.{max r v} (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{max r v} ℤ) AddCommGrpCat.{max r v})]

/-- The sheafified extension of scalars `F ↦ Λ ⊗[ℤ] F` from abelian sheaves to sheaves of
`Λ`-modules. -/
abbrev sheafExtendScalars : Sheaf J AddCommGrpCat.{max r v} ⥤ Sheaf J (ModuleCat.{max r v} Λ) :=
  Sheaf.composeAndSheafify J (extendScalarsAb Λ)

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules. -/
abbrev sheafForget : Sheaf J (ModuleCat.{max r v} Λ) ⥤ Sheaf J AddCommGrpCat.{max r v} :=
  sheafCompose J (ModuleCat.restrictScalars.{max r v} (Int.castRingHom Λ) ⋙
    forget₂ (ModuleCat.{max r v} ℤ) AddCommGrpCat.{max r v})

/-- Sheafified extension of scalars is left adjoint to forgetting to the abelian sheaf. -/
def sheafExtendScalarsAdj : sheafExtendScalars J Λ ⊣ sheafForget J Λ :=
  Sheaf.adjunction J (extendScalarsAbAdj.{v} Λ)

omit [J.HasSheafCompose (ModuleCat.restrictScalars.{max r v} (Int.castRingHom Λ) ⋙
    forget₂ (ModuleCat.{max r v} ℤ) AddCommGrpCat.{max r v})] in
/-- **Sheafified extension of scalars keeps the inclusion of a short exact sequence with
sectionwise torsion-free quotient a monomorphism.** -/
lemma mono_sheafExtendScalars_map (S : ShortComplex (Sheaf J AddCommGrpCat.{max r v}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono ((sheafExtendScalars J Λ :
      Sheaf J AddCommGrpCat.{max r v} ⥤ Sheaf J (ModuleCat.{max r v} Λ)).map S.f) := by
  have := hS.mono_f
  have hpre : Mono (Functor.whiskerRight S.f.hom
      (extendScalarsAb Λ : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} Λ)) := by
    have (U : Cᵒᵖ) : Mono ((extendScalarsAb Λ :
        AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} Λ).map (S.f.hom.app U)) := by
      have := hP U
      let E := sheafToPresheaf J AddCommGrpCat.{max r v} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max r v}).obj U
      obtain ⟨hE, hEm⟩ :=
        (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp inferInstance S hS
      rw [ModuleCat.mono_iff_injective]
      exact injective_extendScalarsAb_map Λ (S.f.hom.app U) (S.g.hom.app U)
        ((AddCommGrpCat.mono_iff_injective _).mp hEm)
        ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp hE)
    exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ this
  change Mono ((presheafToSheaf J _).map (Functor.whiskerRight S.f.hom
    (extendScalarsAb Λ : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} Λ)))
  infer_instance

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max r v})] [HasInjectiveResolutions
  (Sheaf J AddCommGrpCat.{max r v})]

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules is `Ext`-acyclic against
every sectionwise torsion-free abelian sheaf.** -/
lemma ext_forget₂_eq_zero_of_isTorsionFree (I : Sheaf J (ModuleCat.{max r v} Λ)) [Injective I]
    (X : Sheaf J AddCommGrpCat.{max r v}) (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U))
    (n : ℕ) (e : Ext.{w'} X ((sheafForget J Λ).obj I) (n + 1)) : e = 0 :=
  ModuleSheafCohomology.ext_eq_zero_of_adjunction _ _ (sheafExtendScalarsAdj J Λ)
    (fun F : Sheaf J AddCommGrpCat.{max r v} => ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U))
    (fun f _ hY => ModuleSheafCohomology.isTorsionFree_of_mono J f hY)
    (ModuleSheafCohomology.exists_isTorsionFree_epi J)
    (fun S hS hP => mono_sheafExtendScalars_map J Λ S hS hP) I n X hX e

/-- **`Hⁿ⁺¹(I) = 0`** for the underlying abelian sheaf of an injective sheaf of `Λ`-modules: the
constant sheaf `ℤ` corepresenting cohomology is sectionwise torsion-free. -/
lemma subsingleton_H_forget₂ (I : Sheaf J (ModuleCat.{max r v} Λ)) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H.{w'} ((sheafForget J Λ).obj I) (n + 1)) := by
  refine ⟨fun a b => ?_⟩
  have hX : ∀ U, Module.IsTorsionFree ℤ
      (((constantSheaf J AddCommGrpCat.{max r v}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.obj U) :=
    ModuleSheafCohomology.isTorsionFree_sheafify J _ (fun U => by
      change Module.IsTorsionFree ℤ (ULift ℤ)
      exact Function.Injective.moduleIsTorsionFree (fun x : ULift ℤ => x.down)
        ULift.down_injective (fun _ _ => rfl))
  rw [ext_forget₂_eq_zero_of_isTorsionFree J Λ I _ hX n a,
    ext_forget₂_eq_zero_of_isTorsionFree J Λ I _ hX n b]

end Site

end Stacks.InjectiveAcyclic

end
