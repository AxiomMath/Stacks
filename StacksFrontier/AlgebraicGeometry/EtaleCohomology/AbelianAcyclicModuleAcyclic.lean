module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.HomSheafInjectiveAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.BimoduleHomFunctor

/-!
# Abelian acyclicity gives acyclicity for global sections of sheaves of modules

Let `Y` be a scheme, `Λ` a ring, not necessarily commutative, and `G` a sheaf of `Λ`-modules on
the small étale site of `Y` whose underlying abelian sheaf has vanishing higher cohomology
(`Ext^{n+1}(ℤ_Y, G) = 0`). Then `G` is right acyclic for the global sections functor of sheaves of
`Λ`-modules: the higher right derived functors are computed on an injective resolution `I` of `G`,
and `Hⁿ⁺¹(Γ(Y, I))` embeds into `Hⁿ⁺¹(Y, G)` of the underlying abelian sheaf
(`Stacks.EtaleResolution.exists_injective_homology_sections`).

In Step 7 of the proof of [Stacks, Tag 03UG] this applies to `Hom_{A[G]}(M^*, I)` for injective
sheaves `I` of `A[G]`-modules (`Stacks.HomAcyclic.subsingleton_H_homSheaf`), which therefore
compute the cohomology of the locally constant sheaf.

## Main results

* `Stacks.EtaleCohomology.rightAcyclic_etaleModuleGlobalSections_of_ext`
* `Stacks.EtaleCohomology.rightAcyclic_bimoduleHom_of_injective`: `Hom_R(N, I)` is acyclic for
  global sections, for an injective sheaf `I` of `R`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian AlgebraicGeometry

universe w u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (Λ : Type r) [Ring Λ] {Y : Scheme.{u}}
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})]
  [EnoughInjectives (EtaleModules.{u, r} Λ Y)]

/-- **A sheaf of modules whose underlying abelian sheaf is acyclic is acyclic for global
sections.** -/
theorem rightAcyclic_etaleModuleGlobalSections_of_ext (G : EtaleModules.{u, r} Λ Y)
    (h : ∀ n : ℕ, Subsingleton (Ext.{w} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((Stacks.EtaleResolution.sheafForget Λ Y).obj G) (n + 1))) :
    (etaleModuleGlobalSections.{u, r} Λ Y).rightAcyclic G := by
  rw [(Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _ G).2 inferInstance]
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  let Γ := etaleModuleGlobalSections.{u, r} Λ Y
  let J := InjectiveResolution.of G
  obtain ⟨f, hf⟩ := Stacks.EtaleResolution.exists_injective_homology_sections.{w} Λ Y G
    J.cochainComplex J.ι' n
  have hsub : Subsingleton ((((Γ ⋙ Stacks.EtaleResolution.forgetAb.{u + 1} Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J.cochainComplex).homology ((n : ℤ) + 1)) :=
    hf.subsingleton
  let K := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex
  have e1 : (Γ.rightDerivedPlus ((n : ℤ) + 1)).obj G ≅ K.homology ((n : ℤ) + 1) :=
    (DerivedCategory.homologyFunctor _ ((n : ℤ) + 1)).mapIso
        (InjectiveResolution.toRightDerivedIso Γ J).symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ ((n : ℤ) + 1)).app K
  have e2 : (Stacks.EtaleResolution.forgetAb.{u + 1} Λ).obj (K.homology ((n : ℤ) + 1)) ≅
      (((Γ ⋙ Stacks.EtaleResolution.forgetAb.{u + 1} Λ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J.cochainComplex).homology ((n : ℤ) + 1) :=
    ((K.sc ((n : ℤ) + 1)).mapHomologyIso (Stacks.EtaleResolution.forgetAb.{u + 1} Λ)).symm
  have : Subsingleton (K.homology ((n : ℤ) + 1)) :=
    e2.addCommGroupIsoToAddEquiv.subsingleton_congr.2 hsub
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) e1

/-- Composing with the functor `Hom_R(N, -)` to abelian groups takes sheaves on the small étale
site of `Y` to sheaves. -/
instance (priority := high) hasSheafCompose_homAb {R : Type r} [Ring R]
    (N : ModuleCat.{max (u + 1) r} R) :
    Y.smallEtaleTopology.HasSheafCompose (Stacks.HomAcyclic.homAb N) := by
  have : PreservesLimitsOfSize.{u, u + 1} (Stacks.HomAcyclic.homAb N) :=
    preservesLimitsOfSize_shrink.{u + 1, max (u + 1) r, u, max (u + 1) r} _
  infer_instance

/-- Composing with the functor `Hom_R(N, -)` from `R`-modules to `S`-modules takes sheaves on the
small étale site of `Y` to sheaves. -/
instance (priority := high) hasSheafCompose_bimoduleHom {R S : Type r} [Ring R] [Ring S]
    (N : Type (max (u + 1) r))
    [AddCommGroup N] [Module R N] [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ R N] :
    Y.smallEtaleTopology.HasSheafCompose (ModuleCat.BimoduleHom.functor R S N) := by
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.BimoduleHom.functor R S N) :=
    preservesLimitsOfSize_shrink.{u + 1, max (u + 1) r, u, max (u + 1) r} _
  infer_instance

/-- The underlying abelian sheaf of `Hom_R(N, F)`, computed sectionwise with values in
`S`-modules, is the abelian sheaf `Hom_R(N, F)`. -/
def sheafForgetBimoduleHomIso {R S : Type r} [Ring R] [Ring S] (N : Type (max (u + 1) r))
    [AddCommGroup N] [Module R N] [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ R N]
    (F : EtaleModules.{u, r} R Y) :
    (Stacks.EtaleResolution.sheafForget S Y).obj
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.BimoduleHom.functor R S N)).obj F) ≅
      (Stacks.HomAcyclic.homSheaf Y.smallEtaleTopology (ModuleCat.of R N)).obj F :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => AddEquiv.toAddCommGrpIso
      { toFun := fun f => ModuleCat.ofHom (ModuleCat.BimoduleHom.toLinearMap _ f)
        invFun := fun g => (ModuleCat.BimoduleHom.toLinearMap _).symm g.hom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }) (fun _ => rfl))

/-- **`Hom_R(N, I)` of an injective sheaf of `R`-modules is acyclic for global sections**, with
its `S`-module structure coming from a right action of `S` on `N`. -/
theorem rightAcyclic_bimoduleHom_of_injective {R S : Type r} [Ring R] [Ring S]
    [EnoughInjectives (EtaleModules.{u, r} S Y)] (N : Type (max (u + 1) r)) [AddCommGroup N]
    [Module R N] [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ R N] (I : EtaleModules.{u, r} R Y)
    [Injective I]
    [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})] :
    (etaleModuleGlobalSections.{u, r} S Y).rightAcyclic
      ((sheafCompose Y.smallEtaleTopology (ModuleCat.BimoduleHom.functor R S N)).obj I) := by
  refine rightAcyclic_etaleModuleGlobalSections_of_ext S _ fun n => ?_
  have := Stacks.HomAcyclic.subsingleton_H_homSheaf.{u, u + 1, u + 1, r, w} Y.smallEtaleTopology
    (ModuleCat.of R N) I n
  refine ⟨fun a b => ?_⟩
  let e := sheafForgetBimoduleHomIso (S := S) N I
  have h1 : a.comp (Ext.mk₀ e.hom) (add_zero _) = b.comp (Ext.mk₀ e.hom) (add_zero _) :=
    @Subsingleton.elim _ this _ _
  have h2 : ∀ x : Ext.{w} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((Stacks.EtaleResolution.sheafForget S Y).obj
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.BimoduleHom.functor R S N)).obj I)) (n + 1),
      (x.comp (Ext.mk₀ e.hom) (add_zero _)).comp (Ext.mk₀ e.inv) (add_zero _) = x := fun x => by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  rw [← h2 a, ← h2 b, h1]

end Stacks.EtaleCohomology

end
