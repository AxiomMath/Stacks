module

public import StacksFrontier.CategoryTheory.Sites.Point.ExactPairingOfFibers
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChangeFiber
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse

/-!
# Exact pairings of modules are perfect, and fibres of tensor pairings at lifted points

Converse to `Stacks.SheafDuality.exactPairingOfPerfect`: the evaluation `M ⊗ M' ⟶ 𝟙` of an exact
pairing of modules (for the lifted monoidal structure `ModuleCat.liftedModuleMonoidal`) is a
perfect pairing, `M → Hom(M', R)` being bijective with inverse `λ ↦ (λ ⊗ id)(η(1))`. Together with
`CategoryTheory.ExactPairing.map` along monoidal functors (inverse images, fibre functors at
points) this is how fibrewise perfectness of a pairing of sheaves passes to inverse images.

The fibre at the universe lift `Φ.ulift` of a point of a morphism `F ⊗ G ⟶ H` out of a tensor
product of sheaves of modules defined by bilinear maps of sections
(`CategoryTheory.Sheaf.tensorDesc`) is, under
`CategoryTheory.GrothendieckTopology.Point.sheafFiberUliftNatIso`, its fibre at `Φ`.

## Main results

* `Stacks.SheafDuality.bijective_curry_evaluation_of_exactPairing`.
* `Stacks.SheafDuality.bijective_curry_tensorHom_comp`: perfectness is invariant under
  isomorphisms of the three modules.
* `Stacks.SheafDuality.presheafFiber_tensor_hom_ext`: maps out of a tensor product of fibres are
  determined on pairs of germs over a common object.
* `Stacks.SheafDuality.ulift_μ_map_tensorDesc`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Functor.LaxMonoidal

universe w' w v₁ u₁ u v

namespace Stacks.SheafDuality

/-! ### Exact pairings of modules -/

section Modules

variable {R : Type u} [CommRing R]

/-- **The first triangle identity of an exact pairing of modules**: writing `η(1) = Σ m'ᵢ ⊗ mᵢ`,
every `m : M` is `Σ ε(m, m'ᵢ) mᵢ`. -/
private theorem lift_lsmul_curry_evaluation_coevaluation (M M' : ModuleCat.{max v u} R)
    [ExactPairing M' M] (m : M) :
    TensorProduct.lift ((LinearMap.lsmul R M).comp ((ULift.moduleEquiv (R := R)).toLinearMap.comp
      (TensorProduct.curry (ε_ M' M).hom m))) ((η_ M' M).hom (ULift.up 1)) = m := by
  let e : M →ₗ[R] M' →ₗ[R] (𝟙_ (ModuleCat.{max v u} R)) := TensorProduct.curry (ε_ M' M).hom
  let d : (𝟙_ (ModuleCat.{max v u} R)) →ₗ[R] R := (ULift.moduleEquiv (R := R)).toLinearMap
  let c : (M' ⊗ M : ModuleCat.{max v u} R) := (η_ M' M).hom (ULift.up 1)
  show TensorProduct.lift ((LinearMap.lsmul R M).comp (d.comp (e m))) c = m
  have key : ∀ t : (M' ⊗ M : ModuleCat.{max v u} R),
      (λ_ M).hom.hom ((ε_ M' M ▷ M).hom ((α_ M M' M).inv.hom (m ⊗ₜ[R] t))) =
        TensorProduct.lift ((LinearMap.lsmul R M).comp (d.comp (e m))) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, ha, hb, map_add]
  have hz : (λ_ M).hom.hom ((M ◁ η_ M' M ≫ (α_ M M' M).inv ≫ ε_ M' M ▷ M).hom
      (m ⊗ₜ[R] (ULift.up 1 : (𝟙_ (ModuleCat.{max v u} R))))) = m := by
    rw [ExactPairing.coevaluation_evaluation]
    show ((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl R M)).trans
        (TensorProduct.lid R M)) (((TensorProduct.congr ULift.moduleEquiv
          (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)).symm
        (((TensorProduct.congr (LinearEquiv.refl R M) ULift.moduleEquiv).trans
          (TensorProduct.rid R M)) (m ⊗ₜ[R] (ULift.up 1 : ULift R)))) = m
    rw [LinearEquiv.apply_symm_apply]
    simp
  change (λ_ M).hom.hom ((ε_ M' M ▷ M).hom ((α_ M M' M).inv.hom (m ⊗ₜ[R] c))) = m at hz
  rwa [key c] at hz

/-- **The evaluation of an exact pairing of modules is a perfect pairing**: for an exact pairing
between `M'` and `M` in `ModuleCat.{max v u} R`, the map `M → Hom(M', 𝟙)` curried from the
evaluation `M ⊗ M' ⟶ 𝟙` is bijective. Writing `η(1) = Σ m'ᵢ ⊗ mᵢ`, the first triangle identity
says `m = Σ ε(m, m'ᵢ) mᵢ` and the second `m' = Σ ε(mᵢ, m') m'ᵢ`, so `λ ↦ Σ λ(m'ᵢ) mᵢ` is an
inverse. -/
theorem bijective_curry_evaluation_of_exactPairing (M M' : ModuleCat.{max v u} R)
    [ExactPairing M' M] :
    Function.Bijective (TensorProduct.curry (ε_ M' M).hom) := by
  let e : M →ₗ[R] M' →ₗ[R] (𝟙_ (ModuleCat.{max v u} R)) := TensorProduct.curry (ε_ M' M).hom
  let d : (𝟙_ (ModuleCat.{max v u} R)) →ₗ[R] R := (ULift.moduleEquiv (R := R)).toLinearMap
  let c : (M' ⊗ M : ModuleCat.{max v u} R) := (η_ M' M).hom (ULift.up 1)
  let ψ : (M' →ₗ[R] (𝟙_ (ModuleCat.{max v u} R))) → M := fun l =>
    TensorProduct.lift ((LinearMap.lsmul R M).comp (d.comp l)) c
  -- the first triangle identity, on `m ⊗ 1`
  have h₁ : ∀ m : M, ψ (e m) = m := lift_lsmul_curry_evaluation_coevaluation M M'
  -- the second triangle identity, on `1 ⊗ m'`
  have h₂ : ∀ (l : M' →ₗ[R] (𝟙_ (ModuleCat.{max v u} R))) (m' : M'), e (ψ l) m' = l m' := by
    intro l m'
    have key : ∀ t : (M' ⊗ M : ModuleCat.{max v u} R),
        e (TensorProduct.lift ((LinearMap.lsmul R M).comp (d.comp l)) t) m' =
          l ((ρ_ M').hom.hom ((M' ◁ ε_ M' M).hom ((α_ M' M M').hom.hom (t ⊗ₜ[R] m')))) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        show e ((d (l a)) • b) m' = l ((d (e b m')) • a)
        rw [map_smul, LinearMap.smul_apply, map_smul]
        refine ULift.ext ?_
        show (d (l a)) * (e b m').down = (d (e b m')) * (l a).down
        exact mul_comm _ _
      | add a b ha hb =>
        rw [map_add, map_add, LinearMap.add_apply, ha, hb, TensorProduct.add_tmul, map_add,
          map_add, map_add, map_add]
    have hz : (ρ_ M').hom.hom ((η_ M' M ▷ M' ≫ (α_ M' M M').hom ≫ M' ◁ ε_ M' M).hom
        ((ULift.up 1 : (𝟙_ (ModuleCat.{max v u} R))) ⊗ₜ[R] m')) = m' := by
      rw [ExactPairing.evaluation_coevaluation]
      show ((TensorProduct.congr (LinearEquiv.refl R M') ULift.moduleEquiv).trans
          (TensorProduct.rid R M')) (((TensorProduct.congr (LinearEquiv.refl R M')
            ULift.moduleEquiv).trans (TensorProduct.rid R M')).symm
          (((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl R M')).trans
            (TensorProduct.lid R M')) ((ULift.up 1 : ULift R) ⊗ₜ[R] m'))) = m'
      rw [LinearEquiv.apply_symm_apply]
      simp
    change (ρ_ M').hom.hom ((M' ◁ ε_ M' M).hom ((α_ M' M M').hom.hom (c ⊗ₜ[R] m'))) = m' at hz
    rw [key c, hz]
  exact ⟨Function.LeftInverse.injective h₁, fun l => ⟨ψ l, LinearMap.ext (h₂ l)⟩⟩

/-- **Perfectness of a pairing of modules is invariant under isomorphisms** of the two factors and
of the target. -/
theorem bijective_curry_tensorHom_comp {M N T M' N' T' : ModuleCat.{max v u} R}
    (φ : M ⊗ N ⟶ T) (iM : M' ≅ M) (iN : N' ≅ N) (iT : T ≅ T')
    (h : Function.Bijective (TensorProduct.curry φ.hom)) :
    Function.Bijective (TensorProduct.curry ((iM.hom ⊗ₘ iN.hom) ≫ φ ≫ iT.hom).hom) := by
  let eN : (N →ₗ[R] T) ≃ₗ[R] (N' →ₗ[R] T') :=
    iN.symm.toLinearEquiv.arrowCongr iT.toLinearEquiv
  have hc : (TensorProduct.curry ((iM.hom ⊗ₘ iN.hom) ≫ φ ≫ iT.hom).hom : M' → N' →ₗ[R] T') =
      eN ∘ (TensorProduct.curry φ.hom) ∘ iM.toLinearEquiv :=
    funext fun _ => LinearMap.ext fun _ => rfl
  rw [hc]
  exact eN.bijective.comp (h.comp iM.toLinearEquiv.bijective)

/-- **Perfectness of a pairing of modules is invariant under isomorphisms of the target.** -/
theorem bijective_curry_comp_iso {M N T T' : ModuleCat.{max v u} R} (φ : M ⊗ N ⟶ T) (iT : T ≅ T')
    (h : Function.Bijective (TensorProduct.curry φ.hom)) :
    Function.Bijective (TensorProduct.curry (φ ≫ iT.hom).hom) := by
  simpa using bijective_curry_tensorHom_comp φ (Iso.refl M) (Iso.refl N) iT h

end Modules

/-! ### Germs of tensor products of fibres -/

section Germs

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u} [Category.{v} A] [MonoidalCategory A] (Φ : J.Point.{w})
  [HasColimitsOfSize.{w, w} A] [LocallySmall.{w} C]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

/-- **Maps out of a tensor product of fibres are determined on pairs of germs** over a common
object: the tensor product of the fibres is the fibre of the tensor product. -/
theorem presheafFiber_tensor_hom_ext {P Q : Cᵒᵖ ⥤ A} {T : A}
    {f g : Φ.presheafFiber.obj P ⊗ Φ.presheafFiber.obj Q ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X),
      (Φ.toPresheafFiber X x P ⊗ₘ Φ.toPresheafFiber X x Q) ≫ f =
        (Φ.toPresheafFiber X x P ⊗ₘ Φ.toPresheafFiber X x Q) ≫ g) : f = g := by
  rw [← cancel_epi (inv (μ Φ.presheafFiber P Q))]
  refine Φ.presheafFiber_hom_ext fun X x => ?_
  have k : Φ.toPresheafFiber X x (P ⊗ Q) ≫ inv (μ Φ.presheafFiber P Q) =
      Φ.toPresheafFiber X x P ⊗ₘ Φ.toPresheafFiber X x Q :=
    (IsIso.comp_inv_eq (μ Φ.presheafFiber P Q)).2 (Φ.tensorHom_comp_toPresheafFiber_μ X x P Q).symm
  rw [← Category.assoc, ← Category.assoc, k]
  exact h X x

/-- `Stacks.SheafDuality.presheafFiber_tensor_hom_ext`, for the fibres of sheaves. -/
theorem sheafFiber_tensor_hom_ext [HasWeakSheafify J A] {F G : Sheaf J A} {T : A}
    {f g : Φ.sheafFiber.obj F ⊗ Φ.sheafFiber.obj G ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X),
      (Φ.toPresheafFiber X x F.obj ⊗ₘ Φ.toPresheafFiber X x G.obj) ≫ f =
        (Φ.toPresheafFiber X x F.obj ⊗ₘ Φ.toPresheafFiber X x G.obj) ≫ g) : f = g :=
  presheafFiber_tensor_hom_ext Φ h

end Germs

/-! ### Fibres at the universe lift of a point -/

section Ulift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type u} [CommRing R]
  (Φ : J.Point.{w}) [LocallySmall.{w} C] [LocallySmall.{max w w'} C]
  [HasColimitsOfSize.{w, w} (ModuleCat.{max v u} R)]
  [HasColimitsOfSize.{max w w', max w w'} (ModuleCat.{max v u} R)]
  [HasProducts.{w} (ModuleCat.{max v u} R)] [HasProducts.{max w w'} (ModuleCat.{max v u} R)]
  [∀ X : ModuleCat.{max v u} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{max v u} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [∀ X : ModuleCat.{max v u} R,
    PreservesFilteredColimitsOfSize.{max w w', max w w'} (tensorLeft X)]
  [∀ X : ModuleCat.{max v u} R,
    PreservesFilteredColimitsOfSize.{max w w', max w w'} (tensorRight X)]

attribute [local instance] Sheaf.monoidalCategory

variable [(J.W (A := ModuleCat.{max v u} R)).IsMonoidal]
  [HasWeakSheafify J (ModuleCat.{max v u} R)]

/-- **The fibre at `Φ.ulift` of a morphism `tensorDesc β hβ : F ⊗ G ⟶ H` is its fibre at `Φ`**,
under the identifications `CategoryTheory.GrothendieckTopology.Point.sheafFiberUliftNatIso` of the
fibres, compatibly with the monoidal structures of the two fibre functors. -/
theorem ulift_μ_map_tensorDesc {F G H : Sheaf J (ModuleCat.{max v u} R)}
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) :
    (μ (Φ.ulift.{w'}).sheafFiber F G ≫ (Φ.ulift.{w'}).sheafFiber.map (Sheaf.tensorDesc β hβ)) ≫
        (Φ.sheafFiberUliftNatIso (ModuleCat.{max v u} R)).hom.app H =
      ((Φ.sheafFiberUliftNatIso (ModuleCat.{max v u} R)).hom.app F ⊗ₘ
        (Φ.sheafFiberUliftNatIso (ModuleCat.{max v u} R)).hom.app G) ≫
        μ Φ.sheafFiber F G ≫ Φ.sheafFiber.map (Sheaf.tensorDesc β hβ) := by
  refine sheafFiber_tensor_hom_ext (Φ.ulift.{w'}) fun X x => ?_
  have hu : ∀ K : Sheaf J (ModuleCat.{max v u} R),
      (Φ.ulift.{w'}).toPresheafFiber X x K.obj ≫
          (Φ.sheafFiberUliftNatIso (ModuleCat.{max v u} R)).hom.app K =
        Φ.toPresheafFiber X x.down K.obj := fun K =>
    GrothendieckTopology.Point.toPresheafFiber_ulift_comp_presheafFiberUliftIso_hom Φ _ K.obj X x
  have h₁ := Sheaf.toPresheafFiber_tensorHom_μ_sheafFiber_map_tensorDesc (Φ.ulift.{w'}) β hβ X x
  have h₂ := Sheaf.toPresheafFiber_tensorHom_μ_sheafFiber_map_tensorDesc Φ β hβ X x.down
  let uF := (Φ.sheafFiberUliftNatIso (ModuleCat.{max v u} R)).hom.app F
  let uG := (Φ.sheafFiberUliftNatIso (ModuleCat.{max v u} R)).hom.app G
  let uH := (Φ.sheafFiberUliftNatIso (ModuleCat.{max v u} R)).hom.app H
  let gF := (Φ.ulift.{w'}).toPresheafFiber X x F.obj
  let gG := (Φ.ulift.{w'}).toPresheafFiber X x G.obj
  let m₁ := μ (Φ.ulift.{w'}).sheafFiber F G ≫ (Φ.ulift.{w'}).sheafFiber.map (Sheaf.tensorDesc β hβ)
  let m₂ := μ Φ.sheafFiber F G ≫ Φ.sheafFiber.map (Sheaf.tensorDesc β hβ)
  have e₁ : (gF ⊗ₘ gG) ≫ m₁ ≫ uH =
      (Sheaf.presheafTensorDesc β hβ).app (op X) ≫ Φ.toPresheafFiber X x.down H.obj :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ uH) h₁).trans
      ((Category.assoc _ _ _).trans (congrArg ((Sheaf.presheafTensorDesc β hβ).app (op X) ≫ ·)
        (hu H))))
  have e₂ : (gF ⊗ₘ gG) ≫ (uF ⊗ₘ uG) ≫ m₂ =
      (Sheaf.presheafTensorDesc β hβ).app (op X) ≫ Φ.toPresheafFiber X x.down H.obj :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m₂)
      ((tensorHom_comp_tensorHom gF gG uF uG).trans (congrArg₂ (· ⊗ₘ ·) (hu F) (hu G)))).trans h₂)
  exact e₁.trans e₂.symm

end Ulift

end Stacks.SheafDuality

end
