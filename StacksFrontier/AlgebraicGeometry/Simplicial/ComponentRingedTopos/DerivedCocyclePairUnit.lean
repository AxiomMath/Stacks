module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ShriekDatumKFlat

/-!
# The unit of the derived transitions, and the system of Stacks 0GMF in degrees zero and one

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site. The
derived pullback `Lf_𝟙^*` along the transition of an identity simplex map is fully faithful
(`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIdIsoOfKFlat`), and the
compositor of Stacks 0D6D makes it idempotent. This file extracts from these two facts the unit
`Lf_𝟙^* K ≅ K` that is *coherent* with the compositor: the compositor at a factorization through
an identity is the unit (`derivedModulePasteIsoOfEq_unit_right`,
`derivedModulePasteIsoOfEq_unit_left`). The arbitrary isomorphism `Lf_𝟙^* ≅ 𝟭` is not used for
this; the coherent unit is the preimage of the compositor `Lf_𝟙^* Lf_𝟙^* K ≅ Lf_𝟙^* K`.

The application is the system of Stacks 0GMF of a pair `(K₀, α)` in degrees zero and one: its
object in degree zero is identified with `K₀` (`derivedTransitionUnitIsoOfEq` at the last vertex
of `⦋0⦌`), and its two transitions along the faces of `⦋1⦌` differ by `α`
(`pairDerivedModuleTransition_delta_one`).

## Main results

* `CategoryTheory.idempotentUnitIso`: the unit of a fully faithful idempotent functor, with
  `CategoryTheory.idempotentUnit_right` and `CategoryTheory.idempotentUnit_left`, over arbitrary
  categories.
* `CategoryTheory.SimplicialSiteSituation.pairDerivedModuleTransition_delta_one`: the transition
  of the system of Stacks 0GMF along `δ¹₁` is the transition along `δ¹₀` preceded by `α`.

## References

* [Stacks Project, Tag 0GMF](https://stacks.math.columbia.edu/tag/0GMF)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ C} (hF : F.FullyFaithful)
  (m : ∀ X : C, F.obj (F.obj X) ≅ F.obj X)

/-- The unit `F X ≅ X` of a fully faithful functor `F` with an idempotence `m : F F ≅ F`: the
preimage of `m X`. -/
def idempotentUnitIso (X : C) : F.obj X ≅ X :=
  hF.preimageIso (m X)

/-- `F` applied to the unit `F X ≅ X` is the idempotence `m X`. -/
theorem map_idempotentUnitIso_hom (X : C) : F.map (idempotentUnitIso hF m X).hom = (m X).hom :=
  hF.map_preimage _

/-- The unit of a fully faithful idempotent functor is natural when the idempotence is. -/
theorem idempotentUnitIso_naturality
    (hm : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ (m Y).hom = (m X).hom ≫ F.map f)
    {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ (idempotentUnitIso hF m Y).hom = (idempotentUnitIso hF m X).hom ≫ f := by
  refine hF.map_injective ?_
  rw [F.map_comp, F.map_comp, map_idempotentUnitIso_hom, map_idempotentUnitIso_hom]
  exact hm f

/-- **Right unit law.** A natural `c : F G ≅ G` satisfying the associativity of
`F F G ⟶ F G ⟶ G` with `m` is the unit at `G`. -/
theorem idempotentUnit_right {C' : Type u₂} [Category.{v₂} C'] (G : C' ⥤ C)
    (c : ∀ Y : C', F.obj (G.obj Y) ≅ G.obj Y)
    (hc : ∀ Y : C', F.map (c Y).hom ≫ (c Y).hom = (m (G.obj Y)).hom ≫ (c Y).hom) (Y : C') :
    (c Y).hom = (idempotentUnitIso hF m (G.obj Y)).hom := by
  refine hF.map_injective ?_
  rw [map_idempotentUnitIso_hom]
  exact (cancel_mono (c Y).hom).mp (hc Y)

/-- **Left unit law.** A natural `c : H F ≅ H` satisfying the associativity of
`H F F ⟶ H F ⟶ H` with `m` is `H` of the unit. -/
theorem idempotentUnit_left {D : Type u₃} [Category.{v₃} D] (H : C ⥤ D)
    (c : ∀ X : C, H.obj (F.obj X) ≅ H.obj X)
    (hcn : ∀ {X Y : C} (f : X ⟶ Y), H.map (F.map f) ≫ (c Y).hom = (c X).hom ≫ H.map f)
    (hc : ∀ X : C, H.map (m X).hom ≫ (c X).hom = (c (F.obj X)).hom ≫ (c X).hom) (X : C) :
    (c X).hom = H.map (idempotentUnitIso hF m X).hom := by
  have h₁ : H.map (m X).hom = (c (F.obj X)).hom := (cancel_mono (c X).hom).mp (hc X)
  have h₂ := hcn (idempotentUnitIso hF m X).hom
  rw [map_idempotentUnitIso_hom, h₁] at h₂
  exact (cancel_epi (c (F.obj X)).hom).mp h₂

/-- A composite `A ≫ s⁻¹ ≫ l ≫ t` in which `A`, `s` and `t` are units followed by transports,
and `l` is natural against the units, is `a ≫ i` followed by a transport. -/
theorem comp_inv_comp_comp_eq_of_unit {X Y₁ Y₁' Y₀ W Z₁ Z₀ : C} (A : X ⟶ Y₁') (a : X ⟶ Y₁)
    (p₁ : Y₁ = Y₁') (hA : A = a ≫ eqToHom p₁) (s : Z₁ ≅ Y₁') (u₁ : Z₁ ≅ Y₁) (p₂ : Y₁ = Y₁')
    (hs : s.hom = u₁.hom ≫ eqToHom p₂) (t : Z₀ ≅ W) (u₀ : Z₀ ≅ Y₀) (p₃ : Y₀ = W)
    (ht : t.hom = u₀.hom ≫ eqToHom p₃) (l : Z₁ ⟶ Z₀) (i : Y₁ ⟶ Y₀)
    (hn : l ≫ u₀.hom = u₁.hom ≫ i) :
    A ≫ s.inv ≫ l ≫ t.hom = a ≫ i ≫ eqToHom p₃ := by
  subst p₁ p₃
  simp only [eqToHom_refl, Category.comp_id] at hA hs ht ⊢
  have hs' : s = u₁ := Iso.ext hs
  subst hs'
  rw [hA, ht, hn, Iso.inv_hom_id_assoc]

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The derived pullback along the transition of an identity simplex map is fully faithful, with
no flatness hypothesis. -/
def derivedTransitionIdFullyFaithful (n : SimplexCategory) :
    (S.derivedTransitionPullback O (𝟙 n)).FullyFaithful :=
  (Functor.FullyFaithful.id _).ofIso (S.derivedTransitionPullbackIdIsoOfKFlat O n).symm

/-- **The coherent unit `Lf_𝟙^* K ≅ K`**: the preimage under the fully faithful `Lf_𝟙^*` of the
compositor `Lf_𝟙^* Lf_𝟙^* K ≅ Lf_𝟙^* K`. -/
def derivedTransitionIdUnitIso (n : SimplexCategory)
    (K : DerivedCategory (S.componentRingedTopos O n).Modules) :
    (S.derivedTransitionPullback O (𝟙 n)).obj K ≅ K :=
  idempotentUnitIso (S.derivedTransitionIdFullyFaithful O n)
    (fun K ↦ S.derivedModulePasteIsoOfEq O (𝟙 n) (𝟙 n) (𝟙 n) (Category.comp_id _) K) K

/-- The coherent unit at a simplex map `v` equal to an identity. -/
def derivedTransitionUnitIsoOfEq {n : SimplexCategory} (v : n ⟶ n) (hv : v = 𝟙 n)
    (K : DerivedCategory (S.componentRingedTopos O n).Modules) :
    (S.derivedTransitionPullback O v).obj K ≅ K :=
  eqToIso (congrArg (fun t ↦ (S.derivedTransitionPullback O t).obj K) hv) ≪≫
    S.derivedTransitionIdUnitIso O n K

/-- The coherent unit is natural. -/
theorem derivedTransitionUnitIsoOfEq_naturality {n : SimplexCategory} (v : n ⟶ n)
    (hv : v = 𝟙 n) {K K' : DerivedCategory (S.componentRingedTopos O n).Modules} (f : K ⟶ K') :
    (S.derivedTransitionPullback O v).map f ≫ (S.derivedTransitionUnitIsoOfEq O v hv K').hom =
      (S.derivedTransitionUnitIsoOfEq O v hv K).hom ≫ f := by
  subst hv
  simp only [derivedTransitionUnitIsoOfEq, eqToIso_refl, Iso.refl_trans]
  exact idempotentUnitIso_naturality (S.derivedTransitionIdFullyFaithful O n) _
    (fun f ↦ S.derivedModulePasteIsoOfEq_naturality O (𝟙 n) (𝟙 n) (𝟙 n) (Category.comp_id _) f) f

/-- **Right unit law for the compositor**: the compositor of `ψ` and a simplex map `v = 𝟙` is the
coherent unit at `Lf_ψ^* K`. -/
theorem derivedModulePasteIsoOfEq_unit_right {j k : SimplexCategory} (ψ : j ⟶ k) (v : k ⟶ k)
    (hv : v = 𝟙 k) (θ : j ⟶ k) (h : ψ ≫ v = θ) (hθ : ψ = θ)
    (K : DerivedCategory (S.componentRingedTopos O j).Modules) :
    (S.derivedModulePasteIsoOfEq O ψ v θ h K).hom =
      (S.derivedTransitionUnitIsoOfEq O v hv ((S.derivedTransitionPullback O ψ).obj K)).hom ≫
        eqToHom (congrArg (fun t ↦ (S.derivedTransitionPullback O t).obj K) hθ) := by
  subst hv
  subst hθ
  simp only [derivedTransitionUnitIsoOfEq, eqToIso_refl, Iso.refl_trans, eqToHom_refl,
    Category.comp_id]
  exact idempotentUnit_right (S.derivedTransitionIdFullyFaithful O k) _
    (S.derivedTransitionPullback O ψ) (fun K ↦ S.derivedModulePasteIsoOfEq O ψ (𝟙 k) ψ h K)
    (fun K ↦ S.derivedModulePasteIsoOfEq_assoc O ψ (𝟙 k) (𝟙 k) ψ (𝟙 k) ψ h
      (Category.comp_id _) h h K) K

/-- **Left unit law for the compositor**: the compositor of a simplex map `v = 𝟙` and `φ` is
`Lf_φ^*` of the coherent unit. -/
theorem derivedModulePasteIsoOfEq_unit_left {k n : SimplexCategory} (v : k ⟶ k) (hv : v = 𝟙 k)
    (φ : k ⟶ n) (θ : k ⟶ n) (h : v ≫ φ = θ) (hθ : φ = θ)
    (K : DerivedCategory (S.componentRingedTopos O k).Modules) :
    (S.derivedModulePasteIsoOfEq O v φ θ h K).hom =
      (S.derivedTransitionPullback O φ).map (S.derivedTransitionUnitIsoOfEq O v hv K).hom ≫
        eqToHom (congrArg (fun t ↦ (S.derivedTransitionPullback O t).obj K) hθ) := by
  subst hv
  subst hθ
  simp only [derivedTransitionUnitIsoOfEq, eqToIso_refl, Iso.refl_trans, eqToHom_refl,
    Category.comp_id]
  exact idempotentUnit_left (S.derivedTransitionIdFullyFaithful O k) _
    (S.derivedTransitionPullback O φ) (fun K ↦ S.derivedModulePasteIsoOfEq O (𝟙 k) φ φ h K)
    (fun f ↦ S.derivedModulePasteIsoOfEq_naturality O (𝟙 k) φ φ h f)
    (fun K ↦ S.derivedModulePasteIsoOfEq_assoc O (𝟙 k) (𝟙 k) φ (𝟙 k) φ φ
      (Category.comp_id _) h h h K) K

/-- Edge transport between two equal vertices is the identity, read through their equality. -/
theorem derivedModuleEdgeTransport_of_eq (Pr : S.DerivedModuleCocyclePair O) {n : ℕ}
    (i j : Fin (n + 1)) (h : i ≤ j) (hij : i = j) :
    S.derivedModuleEdgeTransport O Pr.obj Pr.iso i j h =
      eqToHom (congrArg (fun t ↦ (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) t)).obj
          Pr.obj) hij) := by
  subst hij
  exact (S.derivedModuleEdgeTransport_self O Pr i).trans (eqToHom_refl _ _).symm

/-- The last vertex of `⦋0⦌` is its identity. -/
theorem const_zero_zero_last_eq_id :
    SimplexCategory.const (SimplexCategory.mk 0) ⦋0⦌ (Fin.last ⦋0⦌.len) = 𝟙 ⦋0⦌ :=
  SimplexCategory.Hom.ext_zero_left _ _

/-- A simplex map out of `⦋0⦌` is the constant map at the image of its last vertex. -/
private theorem hom_zero_eq_const {n : ℕ} (f : ⦋0⦌ ⟶ ⦋n⦌) :
    f = SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n)
      (f.toOrderHom (Fin.last ⦋0⦌.len)) :=
  SimplexCategory.Hom.ext_zero_left _ _

/-- The object in degree zero of the system of Stacks 0GMF attached to a pair is the object of
the pair, through the coherent unit. -/
def pairDerivedModuleObjZeroIso (Pr : S.DerivedModuleCocyclePair O) :
    S.pairDerivedModuleObj O Pr ⦋0⦌ ≅ Pr.obj :=
  S.derivedTransitionUnitIsoOfEq O _ const_zero_zero_last_eq_id Pr.obj

/-- The transition of the system of Stacks 0GMF along `δ¹₀` is the left unit law at `δ¹₀`. -/
theorem pairDerivedModuleTransition_delta_zero_eq (Pr : S.DerivedModuleCocyclePair O) :
    S.pairDerivedModuleTransition O Pr (SimplexCategory.δ (0 : Fin 2)) =
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).map
          (S.pairDerivedModuleObjZeroIso O Pr).hom ≫
        eqToHom (congrArg (fun t ↦ (S.derivedTransitionPullback O t).obj Pr.obj)
          (SimplexCategory.Hom.ext_zero_left _ _ :
            SimplexCategory.δ (0 : Fin 2) =
              SimplexCategory.const (SimplexCategory.mk 0) ⦋1⦌ (Fin.last ⦋1⦌.len))) := by
  change (S.derivedModuleVertexPaste O (SimplexCategory.δ (0 : Fin 2)) (Fin.last ⦋0⦌.len)
      Pr.obj).hom ≫ S.derivedModuleEdgeTransport O Pr.obj Pr.iso (n := 1)
        ((SimplexCategory.δ (0 : Fin 2)).toOrderHom (Fin.last ⦋0⦌.len)) (Fin.last 1)
        (Fin.le_last _) = _
  rw [S.derivedModuleEdgeTransport_of_eq O Pr (n := 1)
    ((SimplexCategory.δ (0 : Fin 2)).toOrderHom (Fin.last ⦋0⦌.len)) (Fin.last 1)
    (Fin.le_last _) rfl]
  simp only [derivedModuleVertexPaste]
  refine (congrArg (· ≫ _) (S.derivedModulePasteIsoOfEq_unit_left O _ const_zero_zero_last_eq_id
    _ _ _ (hom_zero_eq_const _) Pr.obj)).trans ?_
  simp only [pairDerivedModuleObjZeroIso, Category.assoc, eqToHom_trans]
  rfl

/-- The transition of the system of Stacks 0GMF along `δ¹₁` is the left unit law at `δ¹₁`
followed by the transport along the edge of `⦋1⦌`. -/
theorem pairDerivedModuleTransition_delta_one_eq (Pr : S.DerivedModuleCocyclePair O) :
    S.pairDerivedModuleTransition O Pr (SimplexCategory.δ (1 : Fin 2)) =
      (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).map
          (S.pairDerivedModuleObjZeroIso O Pr).hom ≫ Pr.iso.hom ≫
        eqToHom (congrArg (fun t ↦ (S.derivedTransitionPullback O t).obj Pr.obj)
          (SimplexCategory.Hom.ext_zero_left _ _ :
            SimplexCategory.δ (0 : Fin 2) =
              SimplexCategory.const (SimplexCategory.mk 0) ⦋1⦌ (Fin.last ⦋1⦌.len))) := by
  have hE : SimplexCategory.mkOfLe (n := 1)
      ((SimplexCategory.δ (1 : Fin 2)).toOrderHom (Fin.last ⦋0⦌.len)) (Fin.last ⦋1⦌.len)
      (Fin.le_last _) = 𝟙 ⦋1⦌ :=
    SimplexCategory.Hom.ext_one_left _ _
  have hw : SimplexCategory.δ (0 : Fin 2) =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) (Fin.last ⦋1⦌.len) :=
    SimplexCategory.Hom.ext_zero_left _ _
  change (S.derivedModuleVertexPaste O (SimplexCategory.δ (1 : Fin 2)) (Fin.last ⦋0⦌.len)
      Pr.obj).hom ≫
      ((S.derivedEdgeSource O Pr.obj (n := 1)
          ((SimplexCategory.δ (1 : Fin 2)).toOrderHom (Fin.last ⦋0⦌.len)) (Fin.last ⦋1⦌.len)
          (Fin.le_last _)).inv ≫
        (S.derivedTransitionPullback O (SimplexCategory.mkOfLe (n := 1)
          ((SimplexCategory.δ (1 : Fin 2)).toOrderHom (Fin.last ⦋0⦌.len)) (Fin.last ⦋1⦌.len)
          (Fin.le_last _))).map Pr.iso.hom ≫
          (S.derivedEdgeTarget O Pr.obj (n := 1)
            ((SimplexCategory.δ (1 : Fin 2)).toOrderHom (Fin.last ⦋0⦌.len)) (Fin.last ⦋1⦌.len)
            (Fin.le_last _)).hom) = _
  exact comp_inv_comp_comp_eq_of_unit _ _ _
    (S.derivedModulePasteIsoOfEq_unit_left O _ const_zero_zero_last_eq_id _ _ _
      (hom_zero_eq_const _) Pr.obj) _ _ _
    (S.derivedModulePasteIsoOfEq_unit_right O _ _ hE _ _ (hom_zero_eq_const _) Pr.obj) _ _ _
    (S.derivedModulePasteIsoOfEq_unit_right O _ _ hE _ _ hw Pr.obj) _ _
    (S.derivedTransitionUnitIsoOfEq_naturality O _ hE Pr.iso.hom)

/-- **The system of Stacks 0GMF in degree one**: its transition along `δ¹₁` is `α` followed by its
transition along `δ¹₀`, through the identification of its degree-zero object with `K₀`. -/
theorem pairDerivedModuleTransition_delta_one (Pr : S.DerivedModuleCocyclePair O) :
    S.pairDerivedModuleTransition O Pr (SimplexCategory.δ (1 : Fin 2)) =
      (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).map
          (S.pairDerivedModuleObjZeroIso O Pr).hom ≫ Pr.iso.hom ≫
        (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).map
          (S.pairDerivedModuleObjZeroIso O Pr).inv ≫
        S.pairDerivedModuleTransition O Pr (SimplexCategory.δ (0 : Fin 2)) := by
  rw [S.pairDerivedModuleTransition_delta_one_eq O Pr,
    S.pairDerivedModuleTransition_delta_zero_eq O Pr]
  exact congrArg (fun k ↦ _ ≫ _ ≫ k) (Iso.inv_hom_id_map_assoc _ _ _).symm

end CategoryTheory.SimplicialSiteSituation

end
