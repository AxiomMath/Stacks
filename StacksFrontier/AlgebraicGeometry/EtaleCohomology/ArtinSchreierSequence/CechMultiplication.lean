module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechSectionsBaseChange

/-!
# Multiplication by a function on the terms of the Zariski Čech complex of `𝐆_a`

Let `f : X ⟶ S` be a morphism of schemes, `V ⊆ X` an open and `c` a function on
`(S ×_S X) ×_X V ≅ V`. Multiplying a function `b` on an étale `S`-scheme `T` by the pullback of
`c` to `(T ×_S X) ×_X V` is a morphism of abelian sheaves `𝐆_{a,S} ⟶ f_*(ι_{V,*} 𝐆_{a,V})`.

## Main definitions

* `Stacks.ArtinSchreier.multMap`: the morphism `b ↦ b · c`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace

universe u

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens)

/-- Composing the comparison `T ×_S X ⟶ S ×_S X` with the first projection gives the
first projection followed by `t`. -/
theorem fibreMap_fst {T : Scheme.{u}} (t : T ⟶ S) :
    fibreMap f t ≫ pullback.fst (𝟙 S) f = pullback.fst t f ≫ t :=
  pullback.lift_fst _ _ _

/-- The comparison `T ×_S X ⟶ S ×_S X` commutes with the second projections to `X`. -/
theorem fibreMap_snd {T : Scheme.{u}} (t : T ⟶ S) :
    fibreMap f t ≫ pullback.snd (𝟙 S) f = pullback.snd t f :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

section General

variable {T₁ T₂ : Scheme.{u}} {t₁ : T₁ ⟶ S} {t₂ : T₂ ⟶ S} (a : T₂ ⟶ T₁) (ha : a ≫ t₁ = t₂)
  (gl : pullback t₂ f ⟶ pullback t₁ f) (hgl₁ : gl ≫ pullback.fst t₁ f = pullback.fst t₂ f ≫ a)
  (hgl₂ : gl ≫ pullback.snd t₁ f = pullback.snd t₂ f)
  (m : pullback (pullback.snd t₂ f) V.ι ⟶ pullback (pullback.snd t₁ f) V.ι)
  (hm₁ : m ≫ pullback.fst (pullback.snd t₁ f) V.ι = pullback.fst (pullback.snd t₂ f) V.ι ≫ gl)
  (hm₂ : m ≫ pullback.snd (pullback.snd t₁ f) V.ι = pullback.snd (pullback.snd t₂ f) V.ι)

include ha hgl₁ hgl₂ hm₁ hm₂ in
/-- A morphism `m : (T₂ ×_S X) ×_X V ⟶ (T₁ ×_S X) ×_X V` lying over a morphism `a : T₂ ⟶ T₁`
of `S`-schemes is compatible with the comparisons to `(S ×_S X) ×_X V`. -/
theorem comp_openFibreMap_of_comp : m ≫ openFibreMap f t₁ V = openFibreMap f t₂ V := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hm₁,
      Category.assoc]
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [fibreMap_fst, fibreMap_fst, ← Category.assoc gl, hgl₁, Category.assoc, ha]
    · simp only [Category.assoc]
      rw [fibreMap_snd, fibreMap_snd, hgl₂]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id,
      Category.comp_id, hm₂]

include hgl₁ hm₁ in
/-- A morphism `m : (T₂ ×_S X) ×_X V ⟶ (T₁ ×_S X) ×_X V` lying over `gl : T₂ ×_S X ⟶ T₁ ×_S X`,
itself lying over `a : T₂ ⟶ T₁`, commutes with the projections to `T₂` and `T₁`. -/
theorem comp_fst_fst_of_comp :
    m ≫ pullback.fst (pullback.snd t₁ f) V.ι ≫ pullback.fst t₁ f =
      (pullback.fst (pullback.snd t₂ f) V.ι ≫ pullback.fst t₂ f) ≫ a := by
  rw [← Category.assoc, hm₁, Category.assoc, hgl₁, Category.assoc]

/-- For a morphism `α : T₂ ⟶ T₁` of étale `S`-schemes, the induced map
`(T₂ ×_S X) ×_X V ⟶ (T₁ ×_S X) ×_X V` is compatible with the comparisons to `(S ×_S X) ×_X V`. -/
theorem openFibreMap_comp {T₁ T₂ : S.Etale} (α : T₂ ⟶ T₁) :
    (openPullbackFunctor X V).map ((smallEtaleBaseChange f).map α) ≫
        openFibreMap f T₁.hom V = openFibreMap f T₂.hom V :=
  comp_openFibreMap_of_comp f V α.left (MorphismProperty.Over.w α)
    ((smallEtaleBaseChange f).map α).left (smallEtaleBaseChange_map_left_fst f α)
    (smallEtaleBaseChange_w f ((smallEtaleBaseChange f).map α))
    ((openPullbackFunctor X V).map ((smallEtaleBaseChange f).map α))
    (openPullbackFunctor_map_fst X V ((smallEtaleBaseChange f).map α))
    (openPullbackFunctor_map_snd X V ((smallEtaleBaseChange f).map α))

/-- For a morphism `α : T₂ ⟶ T₁` of étale `S`-schemes, the induced map
`(T₂ ×_S X) ×_X V ⟶ (T₁ ×_S X) ×_X V` lies over `α`. -/
theorem openPullbackFunctor_map_fst_fst {T₁ T₂ : S.Etale} (α : T₂ ⟶ T₁) :
    (openPullbackFunctor X V).map ((smallEtaleBaseChange f).map α) ≫
        pullback.fst (pullback.snd T₁.hom f) V.ι ≫ pullback.fst T₁.hom f =
      (pullback.fst (pullback.snd T₂.hom f) V.ι ≫ pullback.fst T₂.hom f) ≫ α.left :=
  comp_fst_fst_of_comp f V α.left ((smallEtaleBaseChange f).map α).left
    (smallEtaleBaseChange_map_left_fst f α)
    ((openPullbackFunctor X V).map ((smallEtaleBaseChange f).map α))
    (openPullbackFunctor_map_fst X V ((smallEtaleBaseChange f).map α))

/-- Two morphisms between the additive coefficients of `Γ` agree if they agree on all functions. -/
private theorem coefficients_hom_ext {T T' : Scheme.{u}}
    {g₁ g₂ : (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).obj (op T) ⟶
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).obj (op T')}
    (h : ∀ b : Γ(T, ⊤), (g₁ (ULift.up b)).down = (g₂ (ULift.up b)).down) : g₁ = g₂ :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => ULift.ext _ _ (h b.down))

/-- Two morphisms of sheaves on the small étale site of `S` agree if they agree on all objects. -/
private theorem sheaf_hom_ext_of_app {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {φ ψ : F ⟶ G} (h : ∀ T, φ.hom.app T = ψ.hom.app T) : φ = ψ :=
  Sheaf.hom_ext (NatTrans.ext (funext h))

/-- Compatibility of `appTop` with an equation `φ ≫ ψ = χ`, evaluated at a function. -/
private theorem appTop_apply_eq_of_comp_eq {A B C : Scheme.{u}} {φ : A ⟶ B} {ψ : B ⟶ C}
    {χ : A ⟶ C} (h : φ ≫ ψ = χ) (x : Γ(C, ⊤)) :
    φ.appTop.hom (ψ.appTop.hom x) = χ.appTop.hom x := by
  subst h
  rfl

/-- Multiplication by the pullback of `c`, on the functions of an `S`-scheme `T`. -/
def multFun (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) {T : Scheme.{u}} (t : T ⟶ S)
    (b : Γ(T, ⊤)) : Γ(pullback (pullback.snd t f) V.ι, ⊤) :=
  (pullback.fst (pullback.snd t f) V.ι ≫ pullback.fst t f).appTop.hom b *
    (openFibreMap f t V).appTop.hom c

/-- On the sections over an `S`-scheme `T`, multiplication by the pullback of `c`. -/
def multMapApp (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) {T : Scheme.{u}} (t : T ⟶ S) :
    (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).obj (op T) ⟶
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).obj (op (pullback (pullback.snd t f) V.ι)) :=
  AddCommGrpCat.ofHom
    { toFun := fun b => ULift.up (multFun f V c t b.down)
      map_zero' := congrArg ULift.up
        ((congrArg (· * _) (map_zero _)).trans (zero_mul _) : multFun f V c t 0 = 0)
      map_add' := fun b b' => congrArg ULift.up
        ((congrArg (· * _) (map_add _ b.down b'.down)).trans (add_mul _ _ _) :
          multFun f V c t (b.down + b'.down) = multFun f V c t b.down + multFun f V c t b'.down) }

/-- The underlying function of `multMapApp f V c t` is `multFun f V c t`. -/
theorem multMapApp_apply (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) {T : Scheme.{u}}
    (t : T ⟶ S) (b : (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).obj (op T)) :
    (multMapApp f V c t b).down = multFun f V c t b.down :=
  rfl

include ha hgl₁ hgl₂ hm₁ hm₂ in
/-- Multiplication by `c` is natural in the `S`-scheme. -/
theorem multMapApp_naturality (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) :
    (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map a.op ≫ multMapApp f V c t₂ =
      multMapApp f V c t₁ ≫ (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map m.op := by
  refine coefficients_hom_ext fun b => ?_
  change multFun f V c t₂ (a.appTop.hom b) = m.appTop.hom (multFun f V c t₁ b)
  unfold multFun
  rw [map_mul, appTop_apply_eq_of_comp_eq (comp_fst_fst_of_comp f V a gl hgl₁ m hm₁),
    appTop_apply_eq_of_comp_eq (comp_openFibreMap_of_comp f V a ha gl hgl₁ hgl₂ m hm₁ hm₂)]
  rfl

end General

/-- **Multiplication by `c`, `𝐆_{a,S} ⟶ f_*(ι_{V,*} 𝐆_{a,V})`**: a function `b` on an étale
`S`-scheme `T` goes to the product of the pullbacks of `b` and `c` to `(T ×_S X) ×_X V`. -/
def multMap (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) :
    additiveSheaf.{u, 0} S ⟶ (etaleAbelianDirectImage.{u, 0} f).obj (openDirectImage X V) :=
  ⟨{ app T := multMapApp f V c T.unop.hom
     naturality T₁ T₂ α :=
       multMapApp_naturality f V α.unop.left (MorphismProperty.Over.w α.unop)
         ((smallEtaleBaseChange f).map α.unop).left (smallEtaleBaseChange_map_left_fst f α.unop)
         (smallEtaleBaseChange_w f ((smallEtaleBaseChange f).map α.unop))
         ((openPullbackFunctor X V).map ((smallEtaleBaseChange f).map α.unop))
         (openPullbackFunctor_map_fst X V ((smallEtaleBaseChange f).map α.unop))
         (openPullbackFunctor_map_snd X V ((smallEtaleBaseChange f).map α.unop)) c }⟩

/-- Multiplication by `c` commutes with restriction to a smaller open `V' ≤ V`. -/
theorem multMapApp_comp_restriction {V' : X.Opens} (h : V' ≤ V)
    (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) {T : Scheme.{u}} (t : T ⟶ S) :
    multMapApp f V c t ≫ (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
        (pullbackOpenMap (pullback.snd t f) h).op =
      multMapApp f V' ((pullbackOpenMap (pullback.snd (𝟙 S) f) h).appTop.hom c) t := by
  refine coefficients_hom_ext fun b => ?_
  change (pullbackOpenMap (pullback.snd t f) h).appTop.hom (multFun f V c t b) =
    multFun f V' ((pullbackOpenMap (pullback.snd (𝟙 S) f) h).appTop.hom c) t b
  unfold multFun
  rw [map_mul, sectionsRingHom_comp (pullback.snd t f) (pullback.fst t f) h b,
    appTop_apply_eq_of_comp_eq (openFibreMap_naturality f t h) c]
  rfl

/-- Multiplication by the pullback of `c` is additive in `c`. -/
theorem multMapApp_add (c c' : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) {T : Scheme.{u}}
    (t : T ⟶ S) : multMapApp f V (c + c') t = multMapApp f V c t + multMapApp f V c' t := by
  refine coefficients_hom_ext fun b => ?_
  change multFun f V (c + c') t b = multFun f V c t b + multFun f V c' t b
  unfold multFun
  rw [map_add, mul_add]

/-- Multiplication by the pullback of `0` is zero. -/
theorem multMapApp_zero {T : Scheme.{u}} (t : T ⟶ S) : multMapApp f V 0 t = 0 := by
  refine coefficients_hom_ext fun b => ?_
  change multFun f V 0 t b = 0
  unfold multFun
  rw [map_zero, mul_zero]

/-- Multiplication by the pullback of `n • c` is `n` times multiplication by that of `c`. -/
theorem multMapApp_zsmul (n : ℤ) (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) {T : Scheme.{u}}
    (t : T ⟶ S) : multMapApp f V (n • c) t = n • multMapApp f V c t := by
  refine coefficients_hom_ext fun b => ?_
  change multFun f V (n • c) t b = n • multFun f V c t b
  unfold multFun
  rw [map_zsmul, mul_smul_comm]

/-- Multiplication by `c` followed by restriction to `V' ≤ V` is multiplication by the
restriction of `c` to `V'`. -/
theorem multMap_comp_restriction {V' : X.Opens} (h : V' ≤ V)
    (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) :
    multMap f V c ≫ (etaleAbelianDirectImage.{u, 0} f).map (openDirectImageRestriction X h) =
      multMap f V' ((pullbackOpenMap (pullback.snd (𝟙 S) f) h).appTop.hom c) :=
  sheaf_hom_ext_of_app fun T => multMapApp_comp_restriction f V h c T.unop.hom

/-- `multMap f V` is additive in the function. -/
theorem multMap_add (c c' : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) :
    multMap f V (c + c') = multMap f V c + multMap f V c' :=
  sheaf_hom_ext_of_app fun T => multMapApp_add f V c c' T.unop.hom

/-- Multiplication by `0` is the zero morphism. -/
theorem multMap_zero : multMap f V 0 = 0 :=
  sheaf_hom_ext_of_app fun T => multMapApp_zero f V T.unop.hom

/-- Multiplication by `n • c` is `n` times multiplication by `c`. -/
theorem multMap_zsmul (n : ℤ) (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) :
    multMap f V (n • c) = n • multMap f V c :=
  sheaf_hom_ext_of_app fun T => multMapApp_zsmul f V n c T.unop.hom

/-- Multiplication maps, as an additive map in the function. -/
def multMapHom : (baseSectionsPresheaf f).obj (op V) →+
    (additiveSheaf.{u, 0} S ⟶ (etaleAbelianDirectImage.{u, 0} f).obj (openDirectImage X V)) where
  toFun c := multMap f V c
  map_zero' := multMap_zero f V
  map_add' c c' := multMap_add f V c c'

section Cochain

open Stacks.CategoryTheory.CechComplex

variable {ι : Type} (U : ι → X.Opens)

/-- The Čech complex of `V ↦ f_*(ι_{V,*} 𝐆_{a,V})`. -/
abbrev directImageCech : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ :=
  (cechComplexFunctor U).obj (openDirectImagePresheaf X ⋙ etaleAbelianDirectImage.{u, 0} f)

/-- The Čech complex of `V ↦ Γ((S ×_S X) ×_X V)`, over `Γ(S)`. -/
abbrev baseCech : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  (cechComplexFunctor U).obj (baseSectionsPresheaf f)

/-- **Multiplication by a Čech cochain**, `𝐆_{a,S} ⟶ Čⁿ(U, V ↦ f_*(ι_{V,*} 𝐆_{a,V}))`. -/
def cochainMult {n : ℕ} (z : (baseCech f U).X n) :
    additiveSheaf.{u, 0} S ⟶ (directImageCech f U).X n :=
  lift U _ fun x => multMap f (inter U x) (π U (baseSectionsPresheaf f) n x z)

/-- The component of `cochainMult f U z` at `x` is multiplication by the component of `z`
at `x`. -/
theorem cochainMult_comp_π {n : ℕ} (z : (baseCech f U).X n) (x : Fin (n + 1) → ι) :
    cochainMult f U z ≫ π U _ n x = multMap f (inter U x) (π U (baseSectionsPresheaf f) n x z) :=
  lift_comp_π U _ _ x

/-- **Multiplication by cochains commutes with the Čech differentials.** -/
theorem cochainMult_comp_d {n : ℕ} (z : (baseCech f U).X n) :
    cochainMult f U z ≫ (directImageCech f U).d n (n + 1) =
      cochainMult f U ((baseCech f U).d n (n + 1) z) := by
  refine hom_ext U _ fun y => ?_
  rw [Category.assoc, d_comp_π, Preadditive.comp_sum, cochainMult_comp_π]
  have hz := congrArg (fun φ => φ z) (d_comp_π U (baseSectionsPresheaf f) n y)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  refine Eq.trans ?_ (congrArg (multMapHom f (inter U y)) hz).symm
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, map_zsmul, ← Category.assoc, cochainMult_comp_π]
  exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
    (multMap_comp_restriction f _ (interMap U y i.succAbove).le _)

end Cochain

end Stacks.ArtinSchreier

end
