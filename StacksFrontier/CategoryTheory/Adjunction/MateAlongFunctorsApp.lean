module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# A mate read through functors at the four corners, one object at a time

Let `Lᵢ ⊣ Rᵢ`, `L_g ⊣ R_g` and `Lᵢ' ⊣ Rᵢ'`, `L_g' ⊣ R_g'` be two squares of adjunctions with
2-cells `θ : Rᵢ ⋙ R_f ⟶ R_f' ⋙ R_g` and `θ' : Rᵢ' ⋙ R_f'' ⟶ R_f''' ⋙ R_g'` between composites
of right adjoints, related by functors `U_A, U_B, U_C, U_D` at the four corners.  If the right
adjoints commute with the `U`s up to given morphisms, the units correspond, and so do `θ` and
`θ'`, then the image under `U_B` of the mate of `θ` at an object `K` is, up to the given
comparisons, the mate of `θ'` at `U_C K`.

Only the components actually used are taken as data, and naturality is required only of the
two comparisons where the computation passes a morphism through them; this is what makes the
statement instantiable at functors whose comparisons are identities only up to expensive
definitional unfolding.

## Main results

* `Stacks.CategoryTheory.map_mateEquiv_symm_app_comp_eq`
* `Stacks.CategoryTheory.isIso_map_mateEquiv_symm_app`
* `Stacks.CategoryTheory.isIso_map_mateEquiv_symm_app_of_comp₃`
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

variable {Am Bm Cm Dm As Bs Cs Ds : Type*} [Category Am] [Category Bm] [Category Cm]
  [Category Dm] [Category As] [Category Bs] [Category Cs] [Category Ds]
  {UA : Am ⥤ As} {UB : Bm ⥤ Bs} {UC : Cm ⥤ Cs} {UD : Dm ⥤ Ds}
  {Lmg : Am ⥤ Bm} {Rmg : Bm ⥤ Am} {Lmi : Cm ⥤ Dm} {Rmi : Dm ⥤ Cm}
  {Rmf : Cm ⥤ Am} {Rmf' : Dm ⥤ Bm}
  {Lsg : As ⥤ Bs} {Rsg : Bs ⥤ As} {Lsi : Cs ⥤ Ds} {Rsi : Ds ⥤ Cs}
  {Rsf : Cs ⥤ As} {Rsf' : Ds ⥤ Bs}

/-- A morphism followed by an identity and the image of an identity: the form in which identity
comparisons enter the hypotheses of `Stacks.CategoryTheory.map_mateEquiv_symm_app_comp_eq`. -/
theorem comp_id_comp_map_id_eq {C D : Type*} [Category C] [Category D] (F : D ⥤ C) {P : C}
    {R : D} {a b : P ⟶ F.obj R} (h : a = b) : a ≫ 𝟙 (F.obj R) ≫ F.map (𝟙 R) = b := by
  rw [Functor.map_id, Category.id_comp, Category.comp_id, h]

/-- An identity is an identity followed by the image of an identity. -/
theorem id_eq_id_comp_map_id {C D : Type*} [Category C] [Category D] (F : D ⥤ C) (R : D) :
    𝟙 (F.obj R) = 𝟙 (F.obj R) ≫ F.map (𝟙 R) := by
  rw [Functor.map_id, Category.comp_id]

/-- A composite of three components followed by an identity is an identity followed by the
component of the composite. -/
theorem comp₃_app_comp_id {C D : Type*} [Category C] [Category D] {F G H K : C ⥤ D} (a : F ⟶ G)
    (b : G ⟶ H) (c : H ⟶ K) (X : C) :
    a.app X ≫ b.app X ≫ c.app X ≫ 𝟙 (K.obj X) = 𝟙 (F.obj X) ≫ (a ≫ b ≫ c).app X := by
  simp

/-- **The mate of a 2-cell of right adjoints, read through functors at the four corners.**
If the units of the two squares and the two 2-cells correspond under the given comparisons,
then `U_B` of the mate at `K` is the mate at `U_C K`, up to those comparisons. -/
theorem map_mateEquiv_symm_app_comp_eq (ami : Lmi ⊣ Rmi) (amg : Lmg ⊣ Rmg)
    (asi : Lsi ⊣ Rsi) (asg : Lsg ⊣ Rsg)
    (θm : Rmi ⋙ Rmf ⟶ Rmf' ⋙ Rmg) (θs : Rsi ⋙ Rsf ⟶ Rsf' ⋙ Rsg)
    (ρg : Rmg ⋙ UA ⟶ UB ⋙ Rsg) (ρf : Rmf ⋙ UA ⟶ UC ⋙ Rsf) (K : Cm)
    (ρi : UC.obj (Rmi.obj (Lmi.obj K)) ⟶ Rsi.obj (UD.obj (Lmi.obj K)))
    (ρf' : UB.obj (Rmf'.obj (Lmi.obj K)) ⟶ Rsf'.obj (UD.obj (Lmi.obj K)))
    (εg : UB.obj (Lmg.obj (Rmf.obj K)) ≅ Lsg.obj (UA.obj (Rmf.obj K)))
    (εi : UD.obj (Lmi.obj K) ≅ Lsi.obj (UC.obj K))
    (hg : UA.map (amg.unit.app (Rmf.obj K)) ≫ ρg.app (Lmg.obj (Rmf.obj K)) ≫
      Rsg.map εg.hom = asg.unit.app (UA.obj (Rmf.obj K)))
    (hi : UC.map (ami.unit.app K) ≫ ρi ≫ Rsi.map εi.hom = asi.unit.app (UC.obj K))
    (hθ : UA.map (θm.app (Lmi.obj K)) ≫ ρg.app (Rmf'.obj (Lmi.obj K)) ≫ Rsg.map ρf' =
      ρf.app (Rmi.obj (Lmi.obj K)) ≫ Rsf.map ρi ≫ θs.app (UD.obj (Lmi.obj K))) :
    UB.map (((mateEquiv ami amg).symm (TwoSquare.mk _ _ _ _ θm)).app K) ≫ ρf' =
      εg.hom ≫ Lsg.map (ρf.app K) ≫
        ((mateEquiv asi asg).symm (TwoSquare.mk _ _ _ _ θs)).app (UC.obj K) ≫
          Rsf'.map εi.inv := by
  set β := ((mateEquiv ami amg).symm (TwoSquare.mk _ _ _ _ θm)).app K
  set βs := ((mateEquiv asi asg).symm (TwoSquare.mk _ _ _ _ θs)).app (UC.obj K)
  have hm : amg.unit.app (Rmf.obj K) ≫ Rmg.map β =
      Rmf.map (ami.unit.app K) ≫ θm.app (Lmi.obj K) :=
    (unit_mateEquiv_symm ami amg (TwoSquare.mk _ _ _ _ θm) K).symm
  have hs : asg.unit.app (Rsf.obj (UC.obj K)) ≫ Rsg.map βs =
      Rsf.map (asi.unit.app (UC.obj K)) ≫ θs.app (Lsi.obj (UC.obj K)) :=
    (unit_mateEquiv_symm asi asg (TwoSquare.mk _ _ _ _ θs) (UC.obj K)).symm
  have nf : UA.map (Rmf.map (ami.unit.app K)) ≫ ρf.app (Rmi.obj (Lmi.obj K)) =
      ρf.app K ≫ Rsf.map (UC.map (ami.unit.app K)) := ρf.naturality (ami.unit.app K)
  have ng : UA.map (Rmg.map β) ≫ ρg.app (Rmf'.obj (Lmi.obj K)) =
      ρg.app (Lmg.obj (Rmf.obj K)) ≫ Rsg.map (UB.map β) := ρg.naturality β
  have nθ : Rsf.map (Rsi.map εi.inv) ≫ θs.app (UD.obj (Lmi.obj K)) =
      θs.app (Lsi.obj (UC.obj K)) ≫ Rsg.map (Rsf'.map εi.inv) := θs.naturality εi.inv
  have hi' : UC.map (ami.unit.app K) ≫ ρi = asi.unit.app (UC.obj K) ≫ Rsi.map εi.inv := by
    rw [← hi]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
      Category.comp_id]
  have nu : asg.unit.app (UA.obj (Rmf.obj K)) ≫ Rsg.map (Lsg.map (ρf.app K)) =
      ρf.app K ≫ asg.unit.app (Rsf.obj (UC.obj K)) := (asg.unit.naturality (ρf.app K)).symm
  rw [← cancel_epi εg.inv, Iso.inv_hom_id_assoc]
  apply (asg.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  calc asg.unit.app (UA.obj (Rmf.obj K)) ≫ Rsg.map (εg.inv ≫ UB.map β ≫ ρf')
      = UA.map (amg.unit.app (Rmf.obj K) ≫ Rmg.map β) ≫
          ρg.app (Rmf'.obj (Lmi.obj K)) ≫ Rsg.map ρf' := by
        rw [← hg, Functor.map_comp, Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
          Iso.hom_inv_id, Functor.map_id, Category.id_comp, Functor.map_comp, ← reassoc_of% ng]
        simp only [Functor.map_comp, Category.assoc]
    _ = ρf.app K ≫ Rsf.map (UC.map (ami.unit.app K) ≫ ρi) ≫ θs.app (UD.obj (Lmi.obj K)) := by
        rw [hm, Functor.map_comp, Category.assoc, hθ, reassoc_of% nf, Functor.map_comp,
          Category.assoc]
    _ = asg.unit.app (UA.obj (Rmf.obj K)) ≫ Rsg.map (Lsg.map (ρf.app K) ≫ βs ≫
          Rsf'.map εi.inv) := by
        rw [hi', Functor.map_comp, Category.assoc, nθ, Functor.map_comp, Functor.map_comp,
          reassoc_of% nu, reassoc_of% hs]

/-- **Invertibility of a mate, read through functors at the four corners.**  In the situation of
`Stacks.CategoryTheory.map_mateEquiv_symm_app_comp_eq`, if the two comparisons it involves are
invertible and the second mate is invertible at `U_C K`, then `U_B` of the first mate at `K` is
invertible. -/
theorem isIso_map_mateEquiv_symm_app (ami : Lmi ⊣ Rmi) (amg : Lmg ⊣ Rmg)
    (asi : Lsi ⊣ Rsi) (asg : Lsg ⊣ Rsg)
    (θm : Rmi ⋙ Rmf ⟶ Rmf' ⋙ Rmg) (θs : Rsi ⋙ Rsf ⟶ Rsf' ⋙ Rsg)
    (ρg : Rmg ⋙ UA ⟶ UB ⋙ Rsg) (ρf : Rmf ⋙ UA ⟶ UC ⋙ Rsf) (K : Cm)
    (ρi : UC.obj (Rmi.obj (Lmi.obj K)) ⟶ Rsi.obj (UD.obj (Lmi.obj K)))
    (ρf' : UB.obj (Rmf'.obj (Lmi.obj K)) ⟶ Rsf'.obj (UD.obj (Lmi.obj K)))
    (εg : UB.obj (Lmg.obj (Rmf.obj K)) ≅ Lsg.obj (UA.obj (Rmf.obj K)))
    (εi : UD.obj (Lmi.obj K) ≅ Lsi.obj (UC.obj K))
    (hg : UA.map (amg.unit.app (Rmf.obj K)) ≫ ρg.app (Lmg.obj (Rmf.obj K)) ≫
      Rsg.map εg.hom = asg.unit.app (UA.obj (Rmf.obj K)))
    (hi : UC.map (ami.unit.app K) ≫ ρi ≫ Rsi.map εi.hom = asi.unit.app (UC.obj K))
    (hθ : UA.map (θm.app (Lmi.obj K)) ≫ ρg.app (Rmf'.obj (Lmi.obj K)) ≫ Rsg.map ρf' =
      ρf.app (Rmi.obj (Lmi.obj K)) ≫ Rsf.map ρi ≫ θs.app (UD.obj (Lmi.obj K)))
    [IsIso ρf'] [IsIso (ρf.app K)]
    (h : IsIso (((mateEquiv asi asg).symm (TwoSquare.mk _ _ _ _ θs)).app (UC.obj K))) :
    IsIso (UB.map (((mateEquiv ami amg).symm (TwoSquare.mk _ _ _ _ θm)).app K)) := by
  have : IsIso (UB.map (((mateEquiv ami amg).symm (TwoSquare.mk _ _ _ _ θm)).app K) ≫
      ρf') := by
    rw [map_mateEquiv_symm_app_comp_eq ami amg asi asg θm θs ρg ρf K ρi ρf' εg εi hg hi hθ]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ρf'

/-- **Invertibility of a mate read through functors at the four corners**, in the form used for
direct images of sheaves of modules against direct images of sheaves of sets: all comparisons
come in families, the 2-cell of the first square is a composite of three, and its agreement
with the 2-cell of the second square is asked componentwise, through comparisons `σ₁`, `σ₂` of
the composite right adjoints. -/
theorem isIso_map_mateEquiv_symm_app_of_comp₃ {P Q : Dm ⥤ Am} (ami : Lmi ⊣ Rmi)
    (amg : Lmg ⊣ Rmg) (asi : Lsi ⊣ Rsi) (asg : Lsg ⊣ Rsg) (a : Rmi ⋙ Rmf ⟶ P) (b : P ⟶ Q)
    (c : Q ⟶ Rmf' ⋙ Rmg) (θs : TwoSquare Rsi Rsf' Rsf Rsg)
    (ρg : Rmg ⋙ UA ⟶ UB ⋙ Rsg) (ρf : Rmf ⋙ UA ⟶ UC ⋙ Rsf)
    (ρi : Rmi ⋙ UC ⟶ UD ⋙ Rsi) (ρf' : Rmf' ⋙ UB ⟶ UD ⋙ Rsf')
    (εg : ∀ M, UB.obj (Lmg.obj M) ≅ Lsg.obj (UA.obj M))
    (εi : ∀ M, UD.obj (Lmi.obj M) ≅ Lsi.obj (UC.obj M))
    (σ₁ : ∀ L, UA.obj (Rmf.obj (Rmi.obj L)) ⟶ Rsf.obj (Rsi.obj (UD.obj L)))
    (σ₂ : ∀ L, UA.obj (Rmg.obj (Rmf'.obj L)) ⟶ Rsg.obj (Rsf'.obj (UD.obj L)))
    (hg : ∀ M, UA.map (amg.unit.app M) ≫ ρg.app (Lmg.obj M) ≫ Rsg.map (εg M).hom =
      asg.unit.app (UA.obj M))
    (hi : ∀ M, UC.map (ami.unit.app M) ≫ ρi.app (Lmi.obj M) ≫ Rsi.map (εi M).hom =
      asi.unit.app (UC.obj M))
    (hσ₁ : ∀ L, σ₁ L = ρf.app (Rmi.obj L) ≫ Rsf.map (ρi.app L))
    (hσ₂ : ∀ L, σ₂ L = ρg.app (Rmf'.obj L) ≫ Rsg.map (ρf'.app L))
    (hθ : ∀ L, UA.map (a.app L) ≫ UA.map (b.app L) ≫ UA.map (c.app L) ≫ σ₂ L =
      σ₁ L ≫ θs.app (UD.obj L))
    (hρf' : ∀ L, IsIso (ρf'.app L)) (hρf : ∀ M, IsIso (ρf.app M)) (K : Cm)
    (h : IsIso (((mateEquiv asi asg).symm θs).app (UC.obj K))) :
    IsIso (UB.map
      (((mateEquiv ami amg).symm (TwoSquare.mk _ _ _ _ (a ≫ b ≫ c))).app K)) := by
  have h₀ := hθ (Lmi.obj K)
  rw [hσ₁, hσ₂] at h₀
  have := hρf' (Lmi.obj K)
  have := hρf K
  refine isIso_map_mateEquiv_symm_app ami amg asi asg (a ≫ b ≫ c) θs ρg ρf K
    (ρi.app (Lmi.obj K)) (ρf'.app (Lmi.obj K)) (εg (Rmf.obj K)) (εi K) (hg (Rmf.obj K)) (hi K)
    ?_ h
  simpa only [NatTrans.comp_app, Functor.map_comp, Category.assoc] using h₀

end Stacks.CategoryTheory
