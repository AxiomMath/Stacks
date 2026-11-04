module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemHomExtension
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationLeftDerived

/-!
# Extending a degree-zero map to a morphism of simplicial systems, without flatness

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site, `T` a cartesian simplicial system of the derived category of modules (Stacks 0D9N)
and `V` any simplicial system with `V_𝟙` invertible in degree zero. A map `ψ₀ : T_0 ⟶ V_0` whose
two transports to degree one agree is the degree-zero component of a morphism of systems
(`CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.exists_hom_app_zero_eq`).
That statement assumes every structure-sheaf transition flat, but the argument only uses that
derived pullback along the transition of an identity simplex map is faithful, and that
transition is flat for every `O`
(`CategoryTheory.SimplicialSiteSituation.isFlat_transitionRingedToposHom_id`). This file records
the extension with **no flatness hypothesis**.

## Main results

* `SimplicialDerivedModuleSystem.exists_hom_app_zero_eq_of_vertexTransport_eq`: for `T` cartesian
  and `V_𝟙` invertible in degree zero, a map `T_0 ⟶ V_0` whose two transports to degree one agree
  is the degree-zero component of a morphism of systems `T ⟶ V`.

## References

* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

namespace SimplicialDerivedModuleSystem

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology CommRingCat.{u}}
  {T V : SimplicialDerivedModuleSystem S O} (hT : T.Cartesian)
  (ψ₀ : T.obj ⦋0⦌ ⟶ V.obj ⦋0⦌)

/-- **Extension of a degree-zero map to a morphism of simplicial systems, without flatness.** Let
`T` be cartesian and `V_𝟙` invertible in degree zero. A map `ψ₀ : T_0 ⟶ V_0` whose two transports
`T_{δ_i}⁻¹ ≫ Lf_{δ_i}^*ψ₀ ≫ V_{δ_i}` to degree one agree is the degree-zero component of a
morphism of simplicial systems `T ⟶ V`. -/
theorem exists_hom_app_zero_eq_of_vertexTransport_eq (hV : IsIso (V.map (𝟙 ⦋0⦌)))
    (h₁ : vertexTransport hT ψ₀ (SimplexCategory.δ (0 : Fin 2)) =
      vertexTransport hT ψ₀ (SimplexCategory.δ (1 : Fin 2))) :
    ∃ f : Hom T V, f.app ⦋0⦌ = ψ₀ := by
  refine ⟨⟨fun n ↦ vertexTransport hT ψ₀ (SimplexCategory.const ⦋0⦌ n 0), ?_⟩, ?_⟩
  · intro m n φ
    have := hT φ
    rw [vertexTransport_eq h₁ (SimplexCategory.const ⦋0⦌ n 0)
      (SimplexCategory.const ⦋0⦌ m 0 ≫ φ), vertexTransport_comp, IsIso.hom_inv_id_assoc]
  · refine (vertexTransport_eq h₁ (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌)).trans ?_
    have := hT (𝟙 ⦋0⦌)
    have := hV
    let : (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).Faithful := by
      have hφ := S.isFlat_transitionRingedToposHom_id O ⦋0⦌
      let : PreservesFiniteLimits
          (S.transitionRingedToposHom O (𝟙 ⦋0⦌)).toModulesHom.pullbackModules :=
        ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O (𝟙 ⦋0⦌) hφ)).1
      let : PreservesFiniteColimits
          (S.transitionRingedToposHom O (𝟙 ⦋0⦌)).toModulesHom.pullbackModules :=
        AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
          (S.transitionRingedToposHom O (𝟙 ⦋0⦌))
      exact Functor.Faithful.of_iso
        (S.derivedTransitionPullbackIsoMapDerivedCategory O (𝟙 ⦋0⦌) hφ ≪≫
          derivedNatIso (S.transitionRingedToposHom O (𝟙 ⦋0⦌)).toModulesHom.pullbackModules
            (𝟭 ((S.componentRingedTopos O ⦋0⦌).Modules))
            (S.transitionPullbackModulesIdToposIso O ⦋0⦌) ≪≫ derivedIdIso).symm
    have hTc := map_derivedTransitionPullback_map_id T hT ⦋0⦌
    have hVc : (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map (V.map (𝟙 ⦋0⦌)) =
        (S.derivedTransitionCompComparison O (𝟙 ⦋0⦌) (𝟙 ⦋0⦌)).app (V.obj ⦋0⦌) :=
      (cancel_mono (V.map (𝟙 ⦋0⦌))).1 (V.map_comp (𝟙 ⦋0⦌) (𝟙 ⦋0⦌)).symm
    have hnat := (S.derivedTransitionCompComparison O (𝟙 ⦋0⦌) (𝟙 ⦋0⦌)).naturality ψ₀
    have key : (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map
          ((S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map ψ₀ ≫ V.map (𝟙 ⦋0⦌)) =
        (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map (T.map (𝟙 ⦋0⦌) ≫ ψ₀) := by
      rw [Functor.map_comp, Functor.map_comp, hVc, hTc]
      exact hnat
    have h := (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map_injective key
    rw [vertexTransport, h, IsIso.inv_hom_id_assoc]

end SimplicialDerivedModuleSystem

end CategoryTheory.SimplicialSiteSituation

end
