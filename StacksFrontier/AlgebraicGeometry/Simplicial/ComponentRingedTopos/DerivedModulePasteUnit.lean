module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationLeftDerived
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Unit laws for the compositor of derived transition pullbacks

In a simplicial-site situation the derived pullback `Lf_𝟙^*` along the transition of an identity
simplex map is isomorphic to the identity functor, the transition being flat with identity
pullback of modules. The compositor `Lf_𝟙^* Lf_𝟙^* ≅ Lf_𝟙^*` is associative, so the unique
`u : Lf_𝟙^* ⟶ 𝟭` with `Lf_𝟙^*(u) = μ` is a unit for the compositors: pasting with an identity
simplex map on either side is `u`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIdUnitIso`:
  `u_X : Lf_𝟙^* X ≅ X`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedModulePasteIsoOfEq_comp_id`: right unit law.
* `CategoryTheory.SimplicialSiteSituation.derivedModulePasteIsoOfEq_id_comp`: left unit law.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-- Conjugating by units: if `y ≫ V = U ≫ α`, then a fivefold composite whose outer factors are
`x`, `U⁻¹`, `V`, `w` is `x ≫ α ≫ w`. -/
theorem comp_unit_conj {C : Type*} [Category* C] {A B B₁ D₁ D E : C} (x : A ⟶ B) (U : B₁ ≅ B)
    (y : B₁ ⟶ D₁) (V : D₁ ≅ D) (α : B ⟶ D) (w : D ⟶ E) (n : y ≫ V.hom = U.hom ≫ α)
    {p₁ : A ⟶ B} {p₂ : B ⟶ B₁} {p₃ : D₁ ⟶ D} {p₄ : D ⟶ E}
    (h₁ : p₁ = x) (h₂ : p₂ = U.inv) (h₃ : p₃ = V.hom) (h₄ : p₄ = w) :
    p₁ ≫ p₂ ≫ y ≫ p₃ ≫ p₄ = x ≫ α ≫ w := by
  subst h₁ h₂ h₃ h₄
  rw [reassoc_of% n, Iso.inv_hom_id_assoc]

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- `Lf_𝟙^*` is isomorphic to the identity functor. -/
theorem nonempty_derivedTransitionPullback_id_iso (n : SimplexCategory) :
    Nonempty (S.derivedTransitionPullback O (𝟙 n) ≅
      𝟭 (DerivedCategory (S.componentRingedTopos O n).Modules)) := by
  have hφ := S.isFlat_transitionRingedToposHom_id O n
  let : PreservesFiniteLimits (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O (𝟙 n) hφ)).1
  let : PreservesFiniteColimits
      (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
      (S.transitionRingedToposHom O (𝟙 n))
  exact ⟨S.derivedTransitionPullbackIsoMapDerivedCategory O (𝟙 n) hφ ≪≫
    derivedNatIso (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules
      (𝟭 ((S.componentRingedTopos O n).Modules)) (S.transitionPullbackModulesIdToposIso O n) ≪≫
    derivedIdIso⟩

/-- `Lf_𝟙^*` is fully faithful. -/
def derivedTransitionPullbackIdFullyFaithful (n : SimplexCategory) :
    (S.derivedTransitionPullback O (𝟙 n)).FullyFaithful :=
  (Functor.FullyFaithful.id _).ofIso
    (Classical.choice (S.nonempty_derivedTransitionPullback_id_iso O n)).symm

/-- **The unit `u_X : Lf_𝟙^* X ≅ X`**, the unique isomorphism whose image under `Lf_𝟙^*` is the
compositor `Lf_𝟙^* Lf_𝟙^* X ≅ Lf_𝟙^* X`. -/
def derivedTransitionPullbackIdUnitIso {n : SimplexCategory}
    (X : DerivedCategory (S.componentRingedTopos O n).Modules) :
    (S.derivedTransitionPullback O (𝟙 n)).obj X ≅ X :=
  (S.derivedTransitionPullbackIdFullyFaithful O n).preimageIso
    (S.derivedModulePasteIsoOfEq O (𝟙 n) (𝟙 n) (𝟙 n) (Category.id_comp _) X)

/-- `Lf_𝟙^*(u_X)` is the compositor. -/
theorem map_derivedTransitionPullbackIdUnitIso_hom {n : SimplexCategory}
    (X : DerivedCategory (S.componentRingedTopos O n).Modules) :
    (S.derivedTransitionPullback O (𝟙 n)).map (S.derivedTransitionPullbackIdUnitIso O X).hom =
      (S.derivedModulePasteIsoOfEq O (𝟙 n) (𝟙 n) (𝟙 n) (Category.id_comp _) X).hom :=
  (S.derivedTransitionPullbackIdFullyFaithful O n).map_preimage _

/-- The unit is natural. -/
theorem derivedTransitionPullbackIdUnitIso_naturality {n : SimplexCategory}
    {X Y : DerivedCategory (S.componentRingedTopos O n).Modules} (f : X ⟶ Y) :
    (S.derivedTransitionPullback O (𝟙 n)).map f ≫ (S.derivedTransitionPullbackIdUnitIso O Y).hom =
      (S.derivedTransitionPullbackIdUnitIso O X).hom ≫ f := by
  refine (S.derivedTransitionPullbackIdFullyFaithful O n).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, map_derivedTransitionPullbackIdUnitIso_hom,
    map_derivedTransitionPullbackIdUnitIso_hom]
  exact S.derivedModulePasteIsoOfEq_naturality O (𝟙 n) (𝟙 n) (𝟙 n) (Category.id_comp _) f

/-- **Right unit law**: the compositor of `ψ` and an identity simplex map is the unit. -/
theorem derivedModulePasteIsoOfEq_comp_id {l m : SimplexCategory} (ψ : l ⟶ m)
    (h : ψ ≫ 𝟙 m = ψ) (P : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedModulePasteIsoOfEq O ψ (𝟙 m) ψ h P).hom =
      (S.derivedTransitionPullbackIdUnitIso O ((S.derivedTransitionPullback O ψ).obj P)).hom := by
  refine (S.derivedTransitionPullbackIdFullyFaithful O m).map_injective ?_
  rw [map_derivedTransitionPullbackIdUnitIso_hom]
  exact (cancel_mono (S.derivedModulePasteIsoOfEq O ψ (𝟙 m) ψ h P).hom).1
    (S.derivedModulePasteIsoOfEq_assoc O ψ (𝟙 m) (𝟙 m) ψ (𝟙 m) ψ h (Category.id_comp _) h h P)

/-- **Left unit law**: the compositor of an identity simplex map and `ψ` is `Lf_ψ^*` of the
unit. -/
theorem derivedModulePasteIsoOfEq_id_comp {l m : SimplexCategory} (ψ : l ⟶ m)
    (h : 𝟙 l ≫ ψ = ψ) (P : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedModulePasteIsoOfEq O (𝟙 l) ψ ψ h P).hom =
      (S.derivedTransitionPullback O ψ).map (S.derivedTransitionPullbackIdUnitIso O P).hom := by
  have h4 :=
    S.derivedModulePasteIsoOfEq_assoc O (𝟙 l) (𝟙 l) ψ (𝟙 l) ψ ψ (Category.id_comp _) h h h P
  have hn := S.derivedModulePasteIsoOfEq_naturality O (𝟙 l) ψ ψ h
    (S.derivedTransitionPullbackIdUnitIso O P).hom
  rw [map_derivedTransitionPullbackIdUnitIso_hom] at hn
  exact (cancel_epi (S.derivedModulePasteIsoOfEq O (𝟙 l) ψ ψ h
    ((S.derivedTransitionPullback O (𝟙 l)).obj P)).hom).1 (h4.symm.trans hn)

/-- The descent datum read off two face transitions through identity simplex maps: for
`c = 𝟙`, `e = 𝟙` and the vertices `v₀ = δ¹₁`, `v₁ = δ¹₀`, the composite of the compositors with
`Lf_e^* α` is `α` conjugated by an isomorphism `Lf_c^* P ≅ P`. -/
theorem exists_iso_derivedModulePaste_conj
    (P : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj P ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj P)
    (c : ⦋0⦌ ⟶ ⦋0⦌) (hc : c = 𝟙 _) (e : ⦋0 + 1⦌ ⟶ ⦋0 + 1⦌) (he : e = 𝟙 _)
    (v₀ v₁ : ⦋0⦌ ⟶ ⦋0 + 1⦌) (hv₀ : v₀ = SimplexCategory.δ (1 : Fin 2))
    (hv₁ : v₁ = SimplexCategory.δ (0 : Fin 2))
    (h₀₁ : c ≫ SimplexCategory.δ (1 : Fin 2) = v₀) (h₀₂ : SimplexCategory.δ (1 : Fin 2) ≫ e = v₀)
    (h₁₁ : c ≫ SimplexCategory.δ (0 : Fin 2) = v₁) (h₁₂ : SimplexCategory.δ (0 : Fin 2) ≫ e = v₁) :
    ∃ j : (S.derivedTransitionPullback O c).obj P ≅ P,
      ((S.derivedModulePasteIsoOfEq O c (SimplexCategory.δ (1 : Fin 2)) v₀ h₀₁ P).hom ≫
          (S.derivedModulePasteIsoOfEq O (SimplexCategory.δ (1 : Fin 2)) e v₀ h₀₂ P).inv ≫
          (S.derivedTransitionPullback O e).map α.hom ≫
          (S.derivedModulePasteIsoOfEq O (SimplexCategory.δ (0 : Fin 2)) e v₁ h₁₂ P).hom) ≫
          (S.derivedModulePasteIsoOfEq O c (SimplexCategory.δ (0 : Fin 2)) v₁ h₁₁ P).inv =
        (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).map j.hom ≫ α.hom ≫
          (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).map j.inv := by
  subst hc he hv₀ hv₁
  simp only [Category.assoc]
  refine ⟨S.derivedTransitionPullbackIdUnitIso O P, ?_⟩
  have u₁ := S.derivedModulePasteIsoOfEq_id_comp O (SimplexCategory.δ (0 : Fin 2)) h₁₁ P
  have r₀ := S.derivedModulePasteIsoOfEq_comp_id O (SimplexCategory.δ (1 : Fin 2)) h₀₂ P
  have r₀' : (S.derivedModulePasteIsoOfEq O _ _ _ h₀₂ P).inv =
      (S.derivedTransitionPullbackIdUnitIso O
        ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj P)).inv :=
    (Iso.inv_eq_inv _ _).2 r₀
  have u₁' : (S.derivedModulePasteIsoOfEq O _ _ _ h₁₁ P).inv =
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).map
        (S.derivedTransitionPullbackIdUnitIso O P).inv :=
    (Iso.inv_eq_inv _ ((S.derivedTransitionPullback O _).mapIso _)).2 u₁
  exact comp_unit_conj _ _ _ _ _ _ (S.derivedTransitionPullbackIdUnitIso_naturality O α.hom)
    (S.derivedModulePasteIsoOfEq_id_comp O (SimplexCategory.δ (1 : Fin 2)) h₀₁ P) r₀'
    (S.derivedModulePasteIsoOfEq_comp_id O (SimplexCategory.δ (0 : Fin 2)) h₁₂ P) u₁'

/-- **The descent datum of the system of a pair is the isomorphism of the pair**: through an
isomorphism `j : K_0 ≅ K₀` of the degree-zero object of the system of Stacks 0GMF with the object
of the pair, `K_{δ¹₀}⁻¹ ∘ K_{δ¹₁}` is `Lf_{δ¹₁}^* j ≫ α ≫ Lf_{δ¹₀}^* j⁻¹`. -/
theorem exists_iso_pairDerivedModuleTransition_comp_inv (Pr : S.DerivedModuleCocyclePair O) :
    ∃ j : (S.pairDerivedModuleSystem O Pr).obj ⦋0⦌ ≅ Pr.obj,
      S.pairDerivedModuleTransition O Pr (SimplexCategory.δ (1 : Fin 2)) ≫
          (S.pairDerivedModuleTransitionIso O Pr (SimplexCategory.δ (0 : Fin 2))).inv =
        (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).map j.hom ≫ Pr.iso.hom ≫
          (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).map j.inv := by
  have h0 : S.pairDerivedModuleTransition O Pr (SimplexCategory.δ (0 : Fin 2)) =
      (S.derivedModuleVertexPaste O (SimplexCategory.δ (0 : Fin 2)) (Fin.last 0) Pr.obj).hom :=
    (congrArg (fun t ↦ (S.derivedModuleVertexPaste O (SimplexCategory.δ (0 : Fin 2))
      (Fin.last 0) Pr.obj).hom ≫ t) (S.derivedModuleEdgeTransport_self O Pr (n := 1) 1)).trans
      (Category.comp_id _)
  have hinv : (S.pairDerivedModuleTransitionIso O Pr (SimplexCategory.δ (0 : Fin 2))).inv =
      (S.derivedModuleVertexPaste O (SimplexCategory.δ (0 : Fin 2)) (Fin.last 0) Pr.obj).inv :=
    (Iso.inv_eq_inv _ _).2 h0
  have h1 : S.pairDerivedModuleTransition O Pr (SimplexCategory.δ (1 : Fin 2)) =
      (S.derivedModuleVertexPaste O (SimplexCategory.δ (1 : Fin 2)) (Fin.last 0) Pr.obj).hom ≫
        S.derivedModuleEdgeTransport O Pr.obj Pr.iso (n := (⦋0 + 1⦌ : SimplexCategory).len)
          ((SimplexCategory.δ (1 : Fin 2)).toOrderHom (Fin.last 0)) (Fin.last _) (Fin.le_last _) :=
    rfl
  rw [hinv, h1, derivedModuleEdgeTransport_eq]
  simp only [derivedEdgeSource, derivedEdgeTarget, derivedModuleVertexPaste]
  refine (S.exists_iso_derivedModulePaste_conj O Pr.obj Pr.iso
    (SimplexCategory.const ⦋0⦌ ⦋0⦌ (Fin.last 0))
    (SimplexCategory.Hom.ext _ _
      (OrderHom.ext _ _ (funext fun i ↦ Subsingleton.elim (α := Fin 1) _ _)))
    (SimplexCategory.mkOfLe (n := 0 + 1)
      ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ (1 : Fin 2))) (Fin.last 0))
      (Fin.last (0 + 1)) (Fin.le_last _))
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by fin_cases i <;> rfl)))
    (SimplexCategory.const ⦋0⦌ ⦋0 + 1⦌
      ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ (1 : Fin 2))) (Fin.last 0)))
    (SimplexCategory.const ⦋0⦌ ⦋0 + 1⦌ (Fin.last (0 + 1)))
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by fin_cases i; rfl)))
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by fin_cases i; rfl)))
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by fin_cases i; rfl)))
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by fin_cases i; rfl)))
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by fin_cases i; rfl)))
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by fin_cases i; rfl)))).elim
      fun j hj ↦ ⟨j, ?_⟩
  exact eq_of_heq (HEq.trans (by heq_congr_full) (HEq.trans (heq_of_eq hj) (by heq_congr_full)))

end CategoryTheory.SimplicialSiteSituation
