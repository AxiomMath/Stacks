module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealization

/-!
# Extending a degree-zero map to a morphism of simplicial systems of derived modules

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of rings on its total site,
`T` a cartesian simplicial system of the derived category of modules (Stacks 0D9N) and `V` any
simplicial system. A map `ψ₀ : T_0 ⟶ V_0` can be transported along every vertex
`w : [0] ⟶ [n]` to a map `T_n ⟶ V_n`,
`T_w⁻¹ ≫ Lf_w^*ψ₀ ≫ V_w`.
If the two transports along the vertices of `[1]` agree, then all transports to a given degree
agree, and they form a morphism of simplicial systems `T ⟶ V` with component `ψ₀` in degree
zero, provided the transitions of `O` are flat (so that `Lf_𝟙^*` is the identity functor) and
`V_𝟙` is invertible in degree zero.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.vertexTransport`: the
  transport of `ψ₀` along a vertex.

## Main results

* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.vertexTransport_comp`:
  transport along `χ ≫ e` is transport along `χ` followed by conjugation with `T_e` and `V_e`.
* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.vertexTransport_eq`: all
  transports to a given degree agree as soon as the two transports to degree one do.
* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.exists_hom_app_zero_eq`:
  the extension of a degree-zero map whose two transports to degree one agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology CommRingCat.{u}}
  {T V : SimplicialDerivedModuleSystem S O} (hT : T.Cartesian) (ψ₀ : T.obj ⦋0⦌ ⟶ V.obj ⦋0⦌)

/-- The transport `T_w⁻¹ ≫ Lf_w^*ψ₀ ≫ V_w : T_n ⟶ V_n` of a degree-zero map `ψ₀` along a vertex
`w : [0] ⟶ [n]`, for a cartesian system `T`. -/
def vertexTransport {n : SimplexCategory} (w : ⦋0⦌ ⟶ n) : T.obj n ⟶ V.obj n :=
  haveI := hT w
  inv (T.map w) ≫ (S.derivedTransitionPullback O w).map ψ₀ ≫ V.map w

/-- For `χ : [0] ⟶ m` and `e : m ⟶ n`, the transport along `χ ≫ e` is
`T_e⁻¹ ≫ Lf_e^*(transport along χ) ≫ V_e`. -/
theorem vertexTransport_comp {m n : SimplexCategory} (χ : ⦋0⦌ ⟶ m) (e : m ⟶ n) :
    haveI := hT e
    vertexTransport hT ψ₀ (χ ≫ e) =
      inv (T.map e) ≫ (S.derivedTransitionPullback O e).map (vertexTransport hT ψ₀ χ) ≫
        V.map e := by
  have := hT χ
  have := hT e
  have := hT (χ ≫ e)
  have hc : (S.derivedTransitionCompComparison O χ e).app (T.obj ⦋0⦌) =
      ((S.derivedTransitionPullback O e).map (T.map χ) ≫ T.map e) ≫ inv (T.map (χ ≫ e)) :=
    (IsIso.eq_comp_inv _).2 (T.map_comp χ e)
  have hnat := (S.derivedTransitionCompComparison O χ e).naturality ψ₀
  simp only [Functor.comp_map] at hnat
  simp only [vertexTransport, Functor.map_comp, Functor.map_inv, Category.assoc]
  rw [← V.map_comp χ e, reassoc_of% hnat, hc]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-- A vertex `[0] ⟶ [n]` is the composite of the vertex `δ 1` of `[1]` with the edge from it
to any later vertex. -/
theorem δ_one_comp_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.mkOfLe i j h =
      SimplexCategory.const ⦋0⦌ ⦋n⦌ i := by
  ext x
  fin_cases x
  rfl

/-- A vertex `[0] ⟶ [n]` is the composite of the vertex `δ 0` of `[1]` with the edge to it from
any earlier vertex. -/
theorem δ_zero_comp_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.mkOfLe i j h =
      SimplexCategory.const ⦋0⦌ ⦋n⦌ j := by
  ext x
  fin_cases x
  rfl

variable {hT ψ₀} in
/-- All transports of `ψ₀` to a given degree agree as soon as the two transports to degree one
do. -/
theorem vertexTransport_eq
    (h₁ : vertexTransport hT ψ₀ (SimplexCategory.δ (0 : Fin 2)) =
      vertexTransport hT ψ₀ (SimplexCategory.δ (1 : Fin 2)))
    {n : SimplexCategory} (w w' : ⦋0⦌ ⟶ n) :
    vertexTransport hT ψ₀ w = vertexTransport hT ψ₀ w' := by
  obtain ⟨k, rfl⟩ : ∃ k, n = ⦋k⦌ := ⟨n.len, rfl⟩
  have key : ∀ i j : Fin (k + 1), i ≤ j →
      vertexTransport hT ψ₀ (SimplexCategory.const ⦋0⦌ ⦋k⦌ i) =
        vertexTransport hT ψ₀ (SimplexCategory.const ⦋0⦌ ⦋k⦌ j) := by
    intro i j hij
    rw [← δ_one_comp_mkOfLe i j hij, ← δ_zero_comp_mkOfLe i j hij, vertexTransport_comp,
      vertexTransport_comp, h₁]
  rw [SimplexCategory.eq_const_of_zero w, SimplexCategory.eq_const_of_zero w']
  exact (le_total _ _).elim (key _ _) fun h => (key _ _ h).symm

/-- Let the transitions of `O` be flat, `T` cartesian and `V_𝟙` invertible in degree zero. A map
`ψ₀ : T_0 ⟶ V_0` whose two transports `T_{δ_i}⁻¹ ≫ Lf_{δ_i}^*ψ₀ ≫ V_{δ_i}` to degree one agree is
the degree-zero component of a morphism of simplicial systems `T ⟶ V`. -/
theorem exists_hom_app_zero_eq
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hV : IsIso (V.map (𝟙 ⦋0⦌)))
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
    let := derivedTransitionPullbackId_faithful hflat ⦋0⦌
    have hTc := map_derivedTransitionPullback_map_id T hT ⦋0⦌
    have hVc : (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map (V.map (𝟙 ⦋0⦌)) =
        (S.derivedTransitionCompComparison O (𝟙 ⦋0⦌) (𝟙 ⦋0⦌)).app (V.obj ⦋0⦌) :=
      (cancel_mono (V.map (𝟙 ⦋0⦌))).1 (V.map_comp (𝟙 ⦋0⦌) (𝟙 ⦋0⦌)).symm
    have key : (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map
          ((S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map ψ₀ ≫ V.map (𝟙 ⦋0⦌)) =
        (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map (T.map (𝟙 ⦋0⦌) ≫ ψ₀) := by
      rw [Functor.map_comp, Functor.map_comp, hVc, hTc]
      exact (S.derivedTransitionCompComparison O (𝟙 ⦋0⦌) (𝟙 ⦋0⦌)).naturality ψ₀
    rw [vertexTransport, (S.derivedTransitionPullback O (𝟙 ⦋0⦌)).map_injective key,
      IsIso.inv_hom_id_assoc]

end CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem

end
