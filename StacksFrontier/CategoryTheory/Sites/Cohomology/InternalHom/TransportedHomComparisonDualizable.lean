module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomAdjunctionTransport
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizableAssociative

/-!
# The comparison with internal Homs of a transported tensor comparison, at dualizable objects

Let `eY : D_Y ≌ C_Y` and `eX : D_X ≌ C_X` be equivalences onto monoidal categories, let
`P : C_Y ⥤ C_X` carry a natural isomorphism `μ : P(A ⊗ B) ≅ P A ⊗ P B` compatible with the
associativity constraints, and let `F : D_Y ⥤ D_X` be identified with `P` through
`κ : eY ⋙ P ≅ F ⋙ eX`. The tensor products of `C_Y` and `C_X` read on `D_Y` and `D_X`
(`TensorHomAdjunction.transportTensor`) are compared along `F` by the transported comparison
`TensorHomAdjunction.transportTensorIso`. For tensor–internal-Hom adjunctions on `D_Y` and `D_X`
at those tensor products, the comparison

`F RHom(K, M) ⟶ RHom(F K, F M)`,

the transpose of `F RHom(K, M) ⊗ F K ≅ F(RHom(K, M) ⊗ K) ⟶ F M` (the transported comparison
followed by `F` of the evaluation), is an isomorphism as soon as `eY K` is dualizable in `C_Y`
(`TensorHomAdjunction.isIso_transportHomComparison_of_exactPairing`).

No compatibility of `μ` with the unit constraints is needed: any isomorphism `P 𝟙 ≅ 𝟙` is
enough (`StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizableAssociative`).

This is the shape of the comparison `g⁻¹ RHom(K, M) ⟶ RHom(g⁻¹K, g⁻¹M)` of Stacks 08JF on the
étale derived categories `D(X_étale, Λ)`, whose tensor products and comparison of Stacks 07A4
are read off the constant ringed sites.

## Main results

* `TensorHomAdjunction.tensorHomBijective_transport`: an internal Hom on `D_Y` is one on `C_Y`.
* `TensorHomAdjunction.bijective_transportTensorIso_inv_comp_map`: the transported comparison
  carries an internal Hom out of a dualizable object to an internal Hom.
* `TensorHomAdjunction.isIso_transportHomComparison_of_exactPairing`: the comparison is an
  isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace TensorHomAdjunction

/-- Composing with a bijection on either side does not change bijectivity. -/
private theorem bijective_of_eq_comp {α β γ δ : Sort*} {f : α → δ} {p : α → β} {g : β → γ}
    {q : γ → δ} (hf : f = q ∘ g ∘ p) (hp : Function.Bijective p) (hg : Function.Bijective g)
    (hq : Function.Bijective q) : Function.Bijective f := by
  rw [hf]
  exact hq.comp (hg.comp hp)

/-- Composition with an isomorphism is a bijection of Hom sets. -/
private theorem bijective_comp_iso {C : Type*} [Category C] {T A B : C} (i : A ≅ B) :
    Function.Bijective fun f : T ⟶ A => f ≫ i.hom :=
  ⟨fun x y h => by simpa using congrArg (· ≫ i.inv) h, fun f => ⟨f ≫ i.inv, by simp⟩⟩

/-- Precomposition with an isomorphism is a bijection of Hom sets. -/
private theorem bijective_iso_comp {C : Type*} [Category C] {T A B : C} (i : A ≅ B) :
    Function.Bijective fun f : B ⟶ T => i.hom ≫ f :=
  ⟨fun x y h => by simpa using congrArg (i.inv ≫ ·) h, fun f => ⟨i.inv ≫ f, by simp⟩⟩


variable {DY DX CY CX : Type*} [Category DY] [Category DX] [Category CY] [Category CX]
  [MonoidalCategory CY] [MonoidalCategory CX] (eY : DY ≌ CY) (eX : DX ≌ CX)

/-- **An internal Hom for the transported tensor product is an internal Hom upstairs.** If
`ev : e⁻¹(e H ⊗ e K) ⟶ M` represents maps out of the transported tensor product with `K`, then
`e H`, with the evaluation `e H ⊗ e K ≅ e e⁻¹(e H ⊗ e K) ⟶ e M`, is an internal Hom from `e K` to
`e M`. -/
theorem tensorHomBijective_transport {K H M : DY}
    (ev : ((transportTensor eY (curriedTensor CY)).obj H).obj K ⟶ M)
    (hev : ∀ T : DY, Function.Bijective fun w : T ⟶ H =>
      ((transportTensor eY (curriedTensor CY)).map w).app K ≫ ev) (T' : CY) :
    Function.Bijective fun v : T' ⟶ eY.functor.obj H =>
      v ▷ eY.functor.obj K ≫ eY.counitInv.app _ ≫ eY.functor.map ev := by
  let c : T' ⊗ eY.functor.obj K ≅
      eY.functor.obj (((transportTensor eY (curriedTensor CY)).obj
        (eY.inverse.obj T')).obj K) :=
    whiskerRightIso (eY.counitIso.app T').symm _ ≪≫ (eY.counitIso.app _).symm
  refine bijective_of_eq_comp (p := fun v : T' ⟶ eY.functor.obj H =>
      (eY.fullyFaithfulFunctor.homEquiv).symm ((eY.counitIso.app T').hom ≫ v))
    (g := fun w => ((transportTensor eY (curriedTensor CY)).map w).app K ≫ ev)
    (q := fun f => c.hom ≫ eY.functor.map f) ?_ ?_ (hev _) ?_
  · funext v
    simp only [Function.comp_apply, Functor.map_comp, transportTensor_map_app,
      Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.map_preimage,
      Equivalence.fun_inv_map, c, Iso.trans_hom, whiskerRightIso_hom, Iso.symm_hom,
      Iso.app_inv, Iso.app_hom, curriedTensor_map_app, Category.assoc]
    simp only [← Category.assoc]
    simp
  · exact (eY.fullyFaithfulFunctor.homEquiv).symm.bijective.comp (bijective_iso_comp _)
  · exact (bijective_iso_comp c).comp eY.fullyFaithfulFunctor.homEquiv.bijective

/-- **The transported comparison carries an internal Hom out of a dualizable object to an
internal Hom.** Let `μ : P(A ⊗ B) ≅ P A ⊗ P B` be compatible with the associativity
constraints, `ν : P 𝟙 ≅ 𝟙` any isomorphism, and `κ : eY ⋙ P ≅ F ⋙ eX`. If `eY K` has a right
dual and `ev` represents maps out of the transported tensor product with `K`, then
`F H ⊗ F K ≅ F(H ⊗ K) ⟶ F M`, read through the transported comparison, represents maps out of
the transported tensor product with `F K`. -/
theorem bijective_transportTensorIso_inv_comp_map (P : CY ⥤ CX) (F : DY ⥤ DX)
    (κ : eY.functor ⋙ P ≅ F ⋙ eX.functor)
    (μ : Functor.uncurry.obj (curriedTensor CY) ⋙ P ≅
      P.prod P ⋙ Functor.uncurry.obj (curriedTensor CX))
    (ha : ∀ A B E : CY, μ.hom.app (A ⊗ B, E) ≫ μ.hom.app (A, B) ▷ P.obj E ≫
        (α_ (P.obj A) (P.obj B) (P.obj E)).hom =
      P.map (α_ A B E).hom ≫ μ.hom.app (A, B ⊗ E) ≫ P.obj A ◁ μ.hom.app (B, E))
    (ν : P.obj (𝟙_ CY) ≅ 𝟙_ CX) {K H M : DY} (K' : CY) [ExactPairing (eY.functor.obj K) K']
    (ev : ((transportTensor eY (curriedTensor CY)).obj H).obj K ⟶ M)
    (hev : ∀ T : DY, Function.Bijective fun w : T ⟶ H =>
      ((transportTensor eY (curriedTensor CY)).map w).app K ≫ ev) (T : DX) :
    Function.Bijective fun u : T ⟶ F.obj H =>
      ((transportTensor eX (curriedTensor CX)).map u).app (F.obj K) ≫
        (transportTensorIso eX eY κ μ).inv.app (H, K) ≫ F.map ev := by
  let m : ∀ A B : CY, P.obj (A ⊗ B) ≅ P.obj A ⊗ P.obj B := fun A B => μ.app (A, B)
  have hl : ∀ {A A' : CY} (f : A ⟶ A') (B : CY),
      P.map (f ▷ B) ≫ (m A' B).hom = (m A B).hom ≫ P.map f ▷ P.obj B := by
    intro A A' f B
    have h := μ.hom.naturality ((f, 𝟙 B) : ((A, B) : CY × CY) ⟶ (A', B))
    simpa [m, Functor.uncurry_obj_map] using h
  have hr : ∀ (A : CY) {B B' : CY} (g : B ⟶ B'),
      P.map (A ◁ g) ≫ (m A B').hom = (m A B).hom ≫ P.obj A ◁ P.map g := by
    intro A B B' g
    have h := μ.hom.naturality ((𝟙 A, g) : ((A, B) : CY × CY) ⟶ (A, B'))
    simpa [m, Functor.uncurry_obj_map] using h
  have hP := tensorHomBijective_map_of_associative P m hl hr ha ν (eY.functor.obj K) K'
    (tensorHomBijective_transport eY ev hev) (eX.functor.obj T)
  let c₁ : eX.functor.obj (((transportTensor eX (curriedTensor CX)).obj T).obj (F.obj K)) ≅
      eX.functor.obj T ⊗ P.obj (eY.functor.obj K) :=
    eX.counitIso.app _ ≪≫ whiskerLeftIso _ (κ.app K).symm
  refine bijective_of_eq_comp (p := fun u : T ⟶ F.obj H => eX.functor.map u ≫ κ.inv.app H)
    (q := fun f => (eX.fullyFaithfulFunctor.homEquiv).symm (c₁.hom ≫ f ≫ κ.hom.app M))
    ?_ ?_ hP ?_
  · funext u
    apply eX.fullyFaithfulFunctor.homEquiv.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Functor.FullyFaithful.homEquiv_apply]
    simp only [transportTensorIso, transportInverseIso, uncurryTransportTensorIso, Iso.trans_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_inv, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app, Iso.refl_inv, Iso.refl_hom, Functor.map_comp,
      Category.id_comp, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, NatIso.prod_inv, Functor.comp_obj, Functor.prod_obj,
      transportTensor_map_app, Equivalence.fun_inv_map, Category.assoc, c₁, m, Iso.trans_hom,
      Iso.app_hom, whiskerLeftIso_hom, Iso.app_inv, Iso.symm_hom, Equivalence.counitInv_app_functor]
    simp only [Functor.whiskeringLeft_obj_obj, Functor.whiskeringRight_obj_obj, Functor.comp_obj,
      curriedTensor_obj_obj, Functor.id_obj, curriedTensor_map_app, Functor.uncurry_obj_obj,
      Functor.comp_map, Functor.uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd,
      curriedTensor_obj_map, Functor.map_comp, Equivalence.fun_inv_map, Category.assoc,
      Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_id, Category.id_comp, cancelIso,
      comp_whiskerRight, NatIso.cancel_natIso_hom_left]
    rw [whisker_exchange_assoc, whisker_exchange_assoc]
    congr 5
    exact (κ.hom.naturality ev).symm
  · exact (bijective_comp_iso (κ.app H).symm).comp eX.fullyFaithfulFunctor.homEquiv.bijective
  · exact eX.fullyFaithfulFunctor.homEquiv.symm.bijective.comp
      ((bijective_iso_comp c₁).comp (bijective_comp_iso (κ.app M)))

/-- Precomposition with `(homEquiv H K M).symm y` is bijective iff `u ↦ T(u)_K ≫ y` is. -/
private theorem bijective_comp_homEquiv_symm_iff {D : Type*} [Category D] {T : D ⥤ D ⥤ D}
    {H : Dᵒᵖ ⥤ D ⥤ D} (adj : TensorHomAdjunction T H) (A X K M : D) (y : (T.obj X).obj K ⟶ M) :
    Function.Bijective (fun x : A ⟶ X => x ≫ (adj.homEquiv X K M).symm y) ↔
      Function.Bijective fun u : A ⟶ X => (T.map u).app K ≫ y := by
  have h : (fun x : A ⟶ X => x ≫ (adj.homEquiv X K M).symm y) =
      (adj.homEquiv A K M).symm ∘ fun u : A ⟶ X => (T.map u).app K ≫ y := by
    funext x
    rw [Function.comp_apply, Equiv.eq_symm_apply, adj.homEquiv_naturality_source,
      Equiv.apply_symm_apply]
  rw [h]
  exact Function.Bijective.of_comp_iff' (adj.homEquiv A K M).symm.bijective _

/-- `isIso_transportHomComparison_of_exactPairing`, with the arguments of the bijection named. -/
private theorem isIso_transportHomComparison_aux (P : CY ⥤ CX) (F : DY ⥤ DX)
    (κ : eY.functor ⋙ P ≅ F ⋙ eX.functor)
    (μ : Functor.uncurry.obj (curriedTensor CY) ⋙ P ≅
      P.prod P ⋙ Functor.uncurry.obj (curriedTensor CX))
    (ha : ∀ A B E : CY, μ.hom.app (A ⊗ B, E) ≫ μ.hom.app (A, B) ▷ P.obj E ≫
        (α_ (P.obj A) (P.obj B) (P.obj E)).hom =
      P.map (α_ A B E).hom ≫ μ.hom.app (A, B ⊗ E) ≫ P.obj A ◁ μ.hom.app (B, E))
    (ν : P.obj (𝟙_ CY) ≅ 𝟙_ CX) {HY : DYᵒᵖ ⥤ DY ⥤ DY} {HX : DXᵒᵖ ⥤ DX ⥤ DX}
    (adjY : TensorHomAdjunction (transportTensor eY (curriedTensor CY)) HY)
    (adjX : TensorHomAdjunction (transportTensor eX (curriedTensor CX)) HX) (K M : DY)
    (K' : CY) [ExactPairing (eY.functor.obj K) K'] :
    IsIso ((adjX.homEquiv (F.obj ((HY.obj (op K)).obj M)) (F.obj K) (F.obj M)).symm
      ((transportTensorIso eX eY κ μ).inv.app ((HY.obj (op K)).obj M, K) ≫
        F.map (adjY.homEquiv ((HY.obj (op K)).obj M) K M (𝟙 _)))) := by
  have hev : ∀ T : DY, Function.Bijective fun w : T ⟶ (HY.obj (op K)).obj M =>
      ((transportTensor eY (curriedTensor CY)).map w).app K ≫
        adjY.homEquiv ((HY.obj (op K)).obj M) K M (𝟙 _) := fun T =>
    (bijective_comp_homEquiv_symm_iff adjY T _ K M _).1 (by
      simp only [Equiv.symm_apply_apply, Category.comp_id]; exact Function.bijective_id)
  have hb := bijective_transportTensorIso_inv_comp_map eY eX P F κ μ ha ν K' _ hev
  refine isIso_of_yoneda_map_bijective _ fun T => ?_
  exact (bijective_comp_homEquiv_symm_iff adjX T _ _ _ _).2 (hb T)

/-- **The comparison with internal Homs of a transported associative tensor comparison is an
isomorphism out of a dualizable object.** For tensor–internal-Hom adjunctions on `D_Y` and
`D_X` at the transported tensor products, the comparison
`F RHom(K, M) ⟶ RHom(F K, F M)`, the transpose of the transported comparison followed by `F` of
the evaluation, is an isomorphism as soon as `eY K` has a right dual.

The tensor products `T_Y`, `T_X` are taken as bifunctors equal to the tensor products of the
monoidal structures (`hTY`, `hTX`), and the associativity of `μ` is stated for prescribed
associativity morphisms `aY`, `aX` of `T_Y`, `T_X` which are the associators (`haY`, `haX`):
this is the form in which a tensor product given as a bifunctor, with a monoidal structure
re-seated onto it, is compared along a functor. -/
theorem isIso_transportHomComparison_of_exactPairing {TY : CY ⥤ CY ⥤ CY} {TX : CX ⥤ CX ⥤ CX}
    (hTY : curriedTensor CY = TY) (hTX : curriedTensor CX = TX) {P : CY ⥤ CX} {F : DY ⥤ DX}
    (α : Functor.uncurry.obj (transportTensor eY TY) ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj (transportTensor eX TX))
    (κ : eY.functor ⋙ P ≅ F ⋙ eX.functor)
    (μ : Functor.uncurry.obj TY ⋙ P ≅ P.prod P ⋙ Functor.uncurry.obj TX)
    (hα : α = transportTensorIso eX eY κ μ)
    (aY : ∀ A B E : CY, (TY.obj ((TY.obj A).obj B)).obj E ⟶ (TY.obj A).obj ((TY.obj B).obj E))
    (aX : ∀ A B E : CX, (TX.obj ((TX.obj A).obj B)).obj E ⟶ (TX.obj A).obj ((TX.obj B).obj E))
    (haY : ∀ A B E : CY, HEq (aY A B E) (α_ A B E).hom)
    (haX : ∀ A B E : CX, HEq (aX A B E) (α_ A B E).hom)
    (ha : ∀ A B E : CY, μ.hom.app ((TY.obj A).obj B, E) ≫
        (Functor.uncurry.obj TX).map (μ.hom.app (A, B) ×ₘ 𝟙 (P.obj E)) ≫
          aX (P.obj A) (P.obj B) (P.obj E) =
      P.map (aY A B E) ≫ μ.hom.app (A, (TY.obj B).obj E) ≫
        (Functor.uncurry.obj TX).map (𝟙 (P.obj A) ×ₘ μ.hom.app (B, E)))
    (ν : P.obj (𝟙_ CY) ≅ 𝟙_ CX) {HY : DYᵒᵖ ⥤ DY ⥤ DY} {HX : DXᵒᵖ ⥤ DX ⥤ DX}
    (adjY : TensorHomAdjunction (transportTensor eY TY) HY)
    (adjX : TensorHomAdjunction (transportTensor eX TX) HX) (K M : DY)
    (K' : CY) [ExactPairing (eY.functor.obj K) K'] :
    IsIso ((adjX.homEquiv (F.obj ((HY.obj (op K)).obj M)) (F.obj K) (F.obj M)).symm
      (α.inv.app ((HY.obj (op K)).obj M, K) ≫
        F.map (adjY.homEquiv ((HY.obj (op K)).obj M) K M (𝟙 _)))) := by
  subst hα hTY hTX
  refine isIso_transportHomComparison_aux eY eX P F κ μ (fun A B E => ?_) ν adjY adjX K M K'
  have h := ha A B E
  rw [eq_of_heq (haY A B E), eq_of_heq (haX _ _ _)] at h
  simpa [Functor.uncurry_obj_map] using h

end TensorHomAdjunction

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

end
