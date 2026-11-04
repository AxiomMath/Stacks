module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Functor.FlipObjOfUncurryIso

/-!
# Transporting the tensor–Hom diagonal along an equivalence

Let `e : C ≌ D` be an equivalence carrying a tensor bifunctor `T_C` to `T_D` through
`μ : e(A ⊗ B) ≅ e A ⊗ e B`, and let `- ⊗ P ⊣ H_D(P, -)` on `D`. Transporting the internal Hom
gives `H_C(M, K) = e⁻¹ H_D(e M, e K)` and an adjunction `- ⊗ M ⊣ H_C(M, -)` on `C`. If `μ` is
compatible with associators `α_C`, `α_D`, then the tensor–Hom diagonal
`P ⊗ H_C(M, K) ⟶ H_C(M, P ⊗ K)` built from `α_C` is the diagonal of `D` built from `α_D` at
`e P`, `e M`, `e K`, brought back along `e`. In particular one is invertible exactly when the
other is.

## Main results

* `CategoryTheory.PullbackInternalHom.assoc_of_natIso`: the compatibility of `μ` with the
  associators passes along an isomorphism of functors.
* `CategoryTheory.PullbackInternalHom.transportAdjunction_homEquiv_symm`: the bijection of the
  transported adjunction.
* `CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal_transport`: the diagonal of `C` is
  the transported diagonal of `D`.
* `CategoryTheory.PullbackInternalHom.isIso_leftTensorHomDiagonal_transport`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackInternalHom

open Opposite

variable {C D : Type*} {instC : Category C} {instD : Category D}

section Natural

variable {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
  (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))
  (αD : ∀ A B E : D, (TD.obj ((TD.obj A).obj B)).obj E ≅ (TD.obj A).obj ((TD.obj B).obj E))

/-- **The compatibility of `μ` with the associators passes along an isomorphism of functors**
`π : F ≅ F'`, for the comparison `μ'` of `F'` obtained by conjugating `μ` with `π`. -/
theorem assoc_of_natIso {F F' : C ⥤ D} (π : F ≅ F')
    (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
    (μ' : Functor.uncurry.obj TC ⋙ F' ≅ F'.prod F' ⋙ Functor.uncurry.obj TD)
    (hμ' : ∀ A B : C, μ'.hom.app (A, B) = π.inv.app ((TC.obj A).obj B) ≫ μ.hom.app (A, B) ≫
      (TD.map (π.hom.app A)).app (F.obj B) ≫ (TD.obj (F'.obj A)).map (π.hom.app B))
    (hαD : ∀ {A A' B B' E E' : D} (a : A ⟶ A') (b : B ⟶ B') (e : E ⟶ E'),
      ((TD.map ((TD.map a).app B ≫ (TD.obj A').map b)).app E ≫
          (TD.obj ((TD.obj A').obj B')).map e) ≫ (αD A' B' E').hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E) ≫
          (TD.obj A').map ((TD.map b).app E ≫ (TD.obj B').map e))
    (A B E : C)
    (h : F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom) :
    F'.map (αC A B E).hom ≫ μ'.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F'.obj A)).map (μ'.hom.app (B, E)) =
      μ'.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ'.hom.app (A, B))).app (F'.obj E) ≫
        (αD (F'.obj A) (F'.obj B) (F'.obj E)).hom := by
  have e1 : F'.map (αC A B E).hom =
      π.inv.app _ ≫ F.map (αC A B E).hom ≫ π.hom.app _ := by
    rw [π.hom.naturality, Iso.inv_hom_id_app_assoc]
  have nαD := hαD (π.hom.app A) (π.hom.app B) (π.hom.app E)
  simp only [Functor.map_comp, NatTrans.comp_app] at nαD
  simp only [hμ', e1, Functor.map_comp, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  have c : ∀ (Y : D) (W : C), (TD.obj Y).map (π.hom.app W) ≫ (TD.obj Y).map (π.inv.app W) =
      𝟙 _ := fun Y W => by simp [← Functor.map_comp]
  simp only [reassoc_of% c]
  have key : ∀ {W W' : D} (x : W ⟶ W') {Z Z' : D} (z : Z ⟶ Z'),
      (TD.obj W).map z ≫ (TD.map x).app Z' = (TD.map x).app Z ≫ (TD.obj W').map z :=
    fun x _ _ z => (TD.map x).naturality z
  have c2 : ∀ (W : C) (Z : D), (TD.map (π.hom.app W)).app Z ≫ (TD.map (π.inv.app W)).app Z =
      𝟙 _ := fun W Z => by simp [← NatTrans.comp_app, ← Functor.map_comp]
  have nA' : (TD.map (π.hom.app A)).app (F.obj ((TC.obj B).obj E)) ≫
      (TD.obj (F'.obj A)).map (μ.hom.app (B, E)) =
      (TD.obj (F.obj A)).map (μ.hom.app (B, E)) ≫
        (TD.map (π.hom.app A)).app ((TD.obj (F.obj B)).obj (F.obj E)) :=
    ((TD.map (π.hom.app A)).naturality (μ.hom.app (B, E))).symm
  rw [reassoc_of% nA', reassoc_of% h, ← nαD]
  simp only [reassoc_of% key, reassoc_of% c2, Category.assoc]
  rfl

end Natural

section Transport

variable (e : C ≌ D) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj TD)
  (HD : Dᵒᵖ ⥤ D ⥤ D) (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The bijection of the transported adjunction.** Transporting `- ⊗ e M ⊣ H_D(e M, -)` along
`e`, through an isomorphism `ρ : - ⊗ M ≅ e⁻¹(e(-) ⊗ e M)` whose components are the unit of `e`
followed by `e⁻¹ μ`, a morphism `g : A ⟶ e⁻¹ H_D(e M, e Z)` corresponds to the morphism
`A ⊗ M ⟶ Z` read off from the adjoint of `e g` through `μ`. -/
theorem transportAdjunction_homEquiv_symm (M : C)
    (ρ : TC.flip.obj M ≅ e.functor ⋙ TD.flip.obj (e.functor.obj M) ⋙ e.inverse)
    (hρ : ∀ A : C, ρ.hom.app A = e.unit.app ((TC.obj A).obj M) ≫ e.inverse.map (μ.hom.app (A, M)))
    (A Z : C)
    (g : A ⟶ e.inverse.obj ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj Z))) :
    ((((e.toAdjunction.comp (adjD (e.functor.obj M))).comp e.symm.toAdjunction).ofNatIsoLeft
        ρ.symm).homEquiv A Z).symm g =
      e.unit.app ((TC.obj A).obj M) ≫ e.inverse.map (μ.hom.app (A, M) ≫
        ((adjD (e.functor.obj M)).homEquiv (e.functor.obj A) (e.functor.obj Z)).symm
          (e.functor.map g ≫
            e.counit.app ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj Z)))) ≫
          e.unitInv.app Z := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply, Adjunction.comp_homEquiv,
    Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply, Adjunction.homEquiv_counit, Iso.symm_inv, hρ,
    Equivalence.toAdjunction_counit, Functor.map_comp, Category.assoc]
  rfl

/-- **The tensor–Hom diagonal of `C` is the transported diagonal of `D`.** Let
`- ⊗ M ⊣ H_C(M, -) = e⁻¹ H_D(e M, e -)` be an adjunction whose bijection is the transported one,
let `μ` be compatible with associators `α_C`, `α_D`, and let `α_D` be natural in its middle
variable. Then the diagonal `P ⊗ H_C(M, K) ⟶ H_C(M, P ⊗ K)` built from `α_C` is
`e⁻¹` of `e(P ⊗ H_C(M, K)) ≅ e P ⊗ H_D(e M, e K) ⟶ H_D(e M, e P ⊗ e K) ≅ H_D(e M, e(P ⊗ K))`,
the middle map being the diagonal of `D` built from `α_D`. -/
theorem leftTensorHomDiagonal_transport
    (adjC : ∀ P : C, TC.flip.obj P ⊣ (e.functor.op ⋙ HD ⋙
      (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse).obj (op P))
    (hφ : ∀ (M A Z : C)
      (g : A ⟶ e.inverse.obj ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj Z))),
      ((adjC M).homEquiv A Z).symm g =
        e.unit.app ((TC.obj A).obj M) ≫ e.inverse.map (μ.hom.app (A, M) ≫
          ((adjD (e.functor.obj M)).homEquiv (e.functor.obj A) (e.functor.obj Z)).symm
            (e.functor.map g ≫
              e.counit.app ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj Z)))) ≫
            e.unitInv.app Z)
    (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))
    (αD : ∀ A B E : D, (TD.obj ((TD.obj A).obj B)).obj E ≅ (TD.obj A).obj ((TD.obj B).obj E))
    (hassoc : ∀ A B E : C, e.functor.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (e.functor.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (e.functor.obj E) ≫
        (αD (e.functor.obj A) (e.functor.obj B) (e.functor.obj E)).hom)
    (hαD : ∀ (A : D) {B B' : D} (b : B ⟶ B') (E : D),
      (TD.map ((TD.obj A).map b)).app E ≫ (αD A B' E).hom =
        (αD A B E).hom ≫ (TD.obj A).map ((TD.map b).app E))
    (P M K : C) :
    leftTensorHomDiagonal TC (e.functor.op ⋙ HD ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse) adjC αC P M K =
      e.unit.app ((TC.obj P).obj
          (e.inverse.obj ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj K)))) ≫ e.inverse.map
        (μ.hom.app (P, e.inverse.obj ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj K))) ≫
          (TD.obj (e.functor.obj P)).map
            (e.counit.app ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj K))) ≫
          leftTensorHomDiagonal TD HD adjD αD (e.functor.obj P) (e.functor.obj M)
            (e.functor.obj K) ≫
          (HD.obj (op (e.functor.obj M))).map (μ.inv.app (P, K))) := by
  apply ((adjC M).homEquiv _ _).symm.injective
  have hε : (adjC M).counit.app K = ((adjC M).homEquiv _ _).symm (𝟙 _) := by
    simp [Adjunction.homEquiv_counit]
  rw [leftTensorHomDiagonal, Equiv.symm_apply_apply, hε, hφ, hφ]
  apply e.functor.map_injective
  have h2 : ∀ {W W' : C} (Z : e.functor.obj W ⟶ e.functor.obj W'),
      e.functor.map (e.unit.app W ≫ e.inverse.map Z ≫ e.unitInv.app W') = Z := by
    intro W W' Z
    simp [Equivalence.fun_inv_map]
  have hX : ∀ {W : C} {Y : D} (X : e.functor.obj W ⟶ Y),
      e.functor.map (e.unit.app W ≫ e.inverse.map X) ≫ e.counit.app Y = X := by
    intro W Y X
    simp [Equivalence.fun_inv_map]
  have hμP : ∀ {W W' : C} (w : W ⟶ W'), e.functor.map ((TC.obj P).map w) =
      μ.hom.app (P, W) ≫ (TD.obj (e.functor.obj P)).map (e.functor.map w) ≫ μ.inv.app (P, W') := by
    intro W W' w
    rw [← cancel_mono (μ.hom.app (P, W')), Category.assoc, Category.assoc, Iso.inv_hom_id_app]
    simpa using μ.hom.naturality ((𝟙 P, w) : ((P, W) : C × C) ⟶ (P, W'))
  rw [h2, Functor.map_comp, hμP, h2]
  simp only [Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj]
  rw [hX]
  simp only [leftTensorHomDiagonal, CategoryTheory.Functor.map_id, Category.id_comp,
    Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality]
  rw [reassoc_of% (hassoc P _ M)]
  have hm := hαD (e.functor.obj P)
    (e.counit.app ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj K))) (e.functor.obj M)
  simp only [Functor.flip_obj_map] at hm ⊢
  have l0 := ((adjD (e.functor.obj M)).homEquiv _ _).symm_apply_apply
    ((αD (e.functor.obj P) ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj K))
      (e.functor.obj M)).hom ≫
      (TD.obj (e.functor.obj P)).map ((adjD (e.functor.obj M)).counit.app (e.functor.obj K)))
  simp only [Adjunction.homEquiv_counit, Functor.flip_obj_map] at l0
  rw [reassoc_of% l0, reassoc_of% hm]
  simp only [Category.assoc]
  rfl

/-- **The tensor–Hom diagonal of `C` is invertible as soon as the diagonal of `D` is**, at the
images of the three objects, for the adjunction on `C` transported from `D` along `e` through
`ρ : - ⊗ P ≅ e⁻¹(e(-) ⊗ e P)`; see `leftTensorHomDiagonal_transport`. -/
theorem isIso_leftTensorHomDiagonal_transport
    (adjC : ∀ P : C, TC.flip.obj P ⊣ (e.functor.op ⋙ HD ⋙
      (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse).obj (op P))
    (ρ : ∀ P : C, TC.flip.obj P ≅ e.functor ⋙ TD.flip.obj (e.functor.obj P) ⋙ e.inverse)
    (hρ : ∀ P A : C, (ρ P).hom.app A =
      e.unit.app ((TC.obj A).obj P) ≫ e.inverse.map (μ.hom.app (A, P)))
    (hadj : ∀ P : C, adjC P =
      ((e.toAdjunction.comp (adjD (e.functor.obj P))).comp e.symm.toAdjunction).ofNatIsoLeft
        (ρ P).symm)
    (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))
    (αD : ∀ A B E : D, (TD.obj ((TD.obj A).obj B)).obj E ≅ (TD.obj A).obj ((TD.obj B).obj E))
    (hassoc : ∀ A B E : C, e.functor.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (e.functor.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (e.functor.obj E) ≫
        (αD (e.functor.obj A) (e.functor.obj B) (e.functor.obj E)).hom)
    (hαD : ∀ (A : D) {B B' : D} (b : B ⟶ B') (E : D),
      (TD.map ((TD.obj A).map b)).app E ≫ (αD A B' E).hom =
        (αD A B E).hom ≫ (TD.obj A).map ((TD.map b).app E))
    (P M K : C)
    (h : IsIso (leftTensorHomDiagonal TD HD adjD αD (e.functor.obj P) (e.functor.obj M)
      (e.functor.obj K))) :
    IsIso (leftTensorHomDiagonal TC (e.functor.op ⋙ HD ⋙
      (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse) adjC αC P M K) := by
  have hφ : ∀ (M A Z : C)
      (g : A ⟶ e.inverse.obj ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj Z))),
      ((adjC M).homEquiv A Z).symm g =
        e.unit.app ((TC.obj A).obj M) ≫ e.inverse.map (μ.hom.app (A, M) ≫
          ((adjD (e.functor.obj M)).homEquiv (e.functor.obj A) (e.functor.obj Z)).symm
            (e.functor.map g ≫ e.counit.app ((HD.obj (op (e.functor.obj M))).obj
              (e.functor.obj Z)))) ≫ e.unitInv.app Z := by
    intro M A Z g
    rw [hadj M]
    exact transportAdjunction_homEquiv_symm e TC TD μ HD adjD M (ρ M) (hρ M) A Z g
  rw [leftTensorHomDiagonal_transport e TC TD μ HD adjD adjC hφ αC αD hassoc hαD P M K]
  infer_instance

end Transport

end CategoryTheory.PullbackInternalHom

end
