module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The formal half of the independence of the comparison of Tag 0ATX

The second half of the proof of [Stacks, Tag 0ATX] compares the isomorphism
`(g ∘ f)^! → f^! ∘ g^!` built from two choices of compactifications joined by a morphism of
choices. Reading every twisted inverse image, every derived pullback, every base change map and
every comparison isomorphism as a variable, what is left is the diagram chase of the source,
which is `Stacks.Duality.compositionChase` below. Its hypotheses are, in the source's notation:

* `h₁` — `γ_E = γ_A ∘ γ_F`, [Stacks, Tag 0ATR] for the row `A`, `F`;
* `h₂` — `γ_B ∘ γ_F` is the base change map of the stack of `F` over `B`, [Stacks, Tag 0ATQ];
* `h₃` — `γ_D ∘ γ_C` is the base change map of the stack of `C` over `D`, [Stacks, Tag 0ATQ];
* `h₄` — those two stacks are one square, so their base change maps agree;
* `h₅`, `h₆` — the comparisons of [Stacks, Tag 0ATX] for the twisted inverse image `f^×` are
  coherent ([Stacks, Tag 0ATY] for `f^×`).

The two squares `A` and `B` "only intersect in one point", which is the naturality of the
transformations involved; it is used freely below.

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Duality

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

/-- **The diagram chase of the second half of the proof of [Stacks, Tag 0ATX]**, with every
functor and every transformation a variable; see the module documentation for the hypotheses. The
conclusion, read at an object `K`, is that the comparison `α_E` of the compactifications of
`g ∘ f` followed by the isomorphism built from the second choice is the isomorphism built from
the first choice followed by the comparisons `α_A` of the compactifications of `f` and `α_D` of
those of `g`. -/
theorem compositionChase
    {Zc : Type u₁} {Y₁c : Type u₂} {Y₂c : Type u₃} {X₁c : Type u₄} {X₂c : Type u₅}
    {U₁c : Type u₆} {U₂c : Type u₇} {Yc : Type u₈} {Xc : Type u₉}
    [Category.{v₁} Zc] [Category.{v₂} Y₁c] [Category.{v₃} Y₂c] [Category.{v₄} X₁c]
    [Category.{v₅} X₂c] [Category.{v₆} U₁c] [Category.{v₇} U₂c] [Category.{v₈} Yc]
    [Category.{v₉} Xc]
    {B₁ : Zc ⥤ Y₁c} {B₂ : Zc ⥤ Y₂c} {Dd : Y₂c ⥤ Y₁c}
    {P₁ : Y₁c ⥤ X₁c} {P₂ : Y₂c ⥤ X₂c} {Ee : X₂c ⥤ X₁c}
    {K₁ : Zc ⥤ X₁c} {K₂ : Zc ⥤ X₂c}
    {Q₁ : Yc ⥤ U₁c} {Q₂ : Yc ⥤ U₂c} {Ee' : U₂c ⥤ U₁c}
    {IY : Yc ⥤ Yc} {IX : Xc ⥤ Xc}
    {C₁ : X₁c ⥤ Xc} {C₂ : X₂c ⥤ Xc} {F₁ : X₁c ⥤ U₁c} {F₂ : X₂c ⥤ U₂c}
    {V₁ : U₁c ⥤ Xc} {V₂ : U₂c ⥤ Xc} {I₁ : Y₁c ⥤ Yc} {I₂ : Y₂c ⥤ Yc}
    {PD EP : Y₂c ⥤ X₁c} {QI EQ : Yc ⥤ U₁c}
    (cK₁ : K₁ ≅ B₁ ⋙ P₁) (cK₂ : K₂ ≅ B₂ ⋙ P₂)
    (pc₁ : C₁ ≅ F₁ ⋙ V₁) (pc₂ : C₂ ≅ F₂ ⋙ V₂)
    (βB₁ : P₁ ⋙ F₁ ⟶ I₁ ⋙ Q₁) (βB₂ : P₂ ⋙ F₂ ⟶ I₂ ⋙ Q₂)
    (eK : K₁ ≅ K₂ ⋙ Ee) (βE : Ee ⋙ C₁ ⟶ C₂ ⋙ IX) (uX : IX ≅ 𝟭 Xc)
    (eB : B₁ ≅ B₂ ⋙ Dd) (βD : Dd ⋙ I₁ ⟶ I₂ ⋙ IY) (uY : IY ≅ 𝟭 Yc)
    (eQ : Q₁ ≅ Q₂ ⋙ Ee') (βA : Ee' ⋙ V₁ ⟶ V₂ ⋙ IX)
    (βF : Ee ⋙ F₁ ⟶ F₂ ⋙ Ee')
    (cEP : EP ≅ P₂ ⋙ Ee) (cEQ : EQ ≅ Q₂ ⋙ Ee') (cPD : PD ≅ Dd ⋙ P₁) (cQI : QI ≅ IY ⋙ Q₁)
    (γP : PD ≅ EP) (γQ : QI ≅ EQ)
    (βFB : EP ⋙ F₁ ⟶ I₂ ⋙ EQ) (βCD : PD ⋙ F₁ ⟶ I₂ ⋙ QI)
    (h₁ : ∀ M, βE.app M = pc₁.hom.app (Ee.obj M) ≫ V₁.map (βF.app M) ≫ βA.app (F₂.obj M) ≫
      IX.map (pc₂.inv.app M))
    (h₂ : ∀ N, βFB.app N = F₁.map (cEP.hom.app N) ≫ βF.app (P₂.obj N) ≫ Ee'.map (βB₂.app N) ≫
      cEQ.inv.app (I₂.obj N))
    (h₃ : ∀ N, βCD.app N = F₁.map (cPD.hom.app N) ≫ βB₁.app (Dd.obj N) ≫ Q₁.map (βD.app N) ≫
      cQI.inv.app (I₂.obj N))
    (h₄ : ∀ N, βCD.app N = F₁.map (γP.hom.app N) ≫ βFB.app N ≫ γQ.inv.app (I₂.obj N))
    (h₅ : ∀ K, eK.hom.app K ≫ Ee.map (cK₂.hom.app K) = cK₁.hom.app K ≫ P₁.map (eB.hom.app K) ≫
      cPD.inv.app (B₂.obj K) ≫ γP.hom.app (B₂.obj K) ≫ cEP.hom.app (B₂.obj K))
    (h₆ : ∀ M, eQ.hom.app M = Q₁.map (uY.inv.app M) ≫ cQI.inv.app M ≫ γQ.hom.app M ≫
      cEQ.hom.app M)
    (K : Zc) :
    (C₁.map (eK.hom.app K) ≫ βE.app (K₂.obj K) ≫ uX.hom.app (C₂.obj (K₂.obj K))) ≫
        (C₂.map (cK₂.hom.app K) ≫ pc₂.hom.app (P₂.obj (B₂.obj K)) ≫
          V₂.map (βB₂.app (B₂.obj K))) =
      (C₁.map (cK₁.hom.app K) ≫ pc₁.hom.app (P₁.obj (B₁.obj K)) ≫
          V₁.map (βB₁.app (B₁.obj K))) ≫
        (V₁.map (eQ.hom.app (I₁.obj (B₁.obj K))) ≫ βA.app (Q₂.obj (I₁.obj (B₁.obj K))) ≫
          uX.hom.app (V₂.obj (Q₂.obj (I₁.obj (B₁.obj K))))) ≫
          V₂.map (Q₂.map (I₁.map (eB.hom.app K) ≫ βD.app (B₂.obj K) ≫
            uY.hom.app (I₂.obj (B₂.obj K)))) := by
  -- the composite `βF ≫ Ee'.map βB₂` at `N`, through the stack `C` over `D`
  have key : ∀ N, βF.app (P₂.obj N) ≫ Ee'.map (βB₂.app N) =
      F₁.map (cEP.inv.app N ≫ γP.inv.app N ≫ cPD.hom.app N) ≫ βB₁.app (Dd.obj N) ≫
        Q₁.map (βD.app N ≫ uY.hom.app (I₂.obj N)) ≫ eQ.hom.app (I₂.obj N) := by
    intro N
    have e₄ := h₄ N
    rw [h₃] at e₄
    have hFB : βFB.app N = F₁.map (γP.inv.app N) ≫ F₁.map (cPD.hom.app N) ≫
        βB₁.app (Dd.obj N) ≫ Q₁.map (βD.app N) ≫ cQI.inv.app (I₂.obj N) ≫
          γQ.hom.app (I₂.obj N) := by
      rw [← cancel_epi (F₁.map (γP.hom.app N)), ← cancel_mono (γQ.inv.app (I₂.obj N))]
      simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, ← Functor.map_comp_assoc,
        Iso.hom_inv_id_app_assoc]
      exact e₄.symm
    have hF : βF.app (P₂.obj N) ≫ Ee'.map (βB₂.app N) =
        F₁.map (cEP.inv.app N) ≫ βFB.app N ≫ cEQ.hom.app (I₂.obj N) := by
      rw [h₂]
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, ← Functor.map_comp_assoc,
        Functor.map_id, Category.id_comp, Functor.comp_obj]
    rw [hF, hFB, h₆]
    simp only [Category.assoc, Functor.map_comp,
      ← Functor.map_comp_assoc Q₁ (uY.hom.app _), Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp]
  set h := I₁.map (eB.hom.app K) ≫ βD.app (B₂.obj K) ≫ uY.hom.app (I₂.obj (B₂.obj K))
  have nU := uX.hom.naturality (C₂.map (cK₂.hom.app K) ≫ pc₂.hom.app (P₂.obj (B₂.obj K)) ≫
    V₂.map (βB₂.app (B₂.obj K)))
  have nU' := uX.hom.naturality (V₂.map (Q₂.map h))
  have nP₂ := pc₂.hom.naturality (cK₂.hom.app K)
  have nA := βA.naturality (F₂.map (cK₂.hom.app K) ≫ βB₂.app (B₂.obj K))
  have nA' := βA.naturality (Q₂.map h)
  have nF := βF.naturality (cK₂.hom.app K)
  have nQ := eQ.hom.naturality h
  have nP₁ := pc₁.hom.naturality (Ee.map (cK₂.hom.app K) ≫
    (cEP.inv.app (B₂.obj K) ≫ γP.inv.app (B₂.obj K) ≫ cPD.hom.app (B₂.obj K)))
  have nP₁' := pc₁.hom.naturality (P₁.map (eB.hom.app K))
  have nB₁ := βB₁.naturality (eB.hom.app K)
  have np : ∀ {A A' : X₁c} (x : A ⟶ A'),
      pc₁.hom.app A ≫ V₁.map (F₁.map x) = C₁.map x ≫ pc₁.hom.app A' :=
    fun x => (pc₁.hom.naturality x).symm
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj] at nU nU' nP₂ nA nA' nF nQ nP₁ nP₁' nB₁
  have e₅ : eK.hom.app K ≫ Ee.map (cK₂.hom.app K) ≫ cEP.inv.app (B₂.obj K) ≫
      γP.inv.app (B₂.obj K) ≫ cPD.hom.app (B₂.obj K) = cK₁.hom.app K ≫ P₁.map (eB.hom.app K) := by
    rw [← Category.assoc, h₅]
    simp
  calc _ = C₁.map (eK.hom.app K) ≫ pc₁.hom.app (Ee.obj (K₂.obj K)) ≫
          V₁.map (βF.app (K₂.obj K)) ≫ βA.app (F₂.obj (K₂.obj K)) ≫
            IX.map (pc₂.inv.app (K₂.obj K)) ≫ IX.map (C₂.map (cK₂.hom.app K) ≫
              pc₂.hom.app (P₂.obj (B₂.obj K)) ≫ V₂.map (βB₂.app (B₂.obj K))) ≫
                uX.hom.app _ := by
        rw [Category.assoc, Category.assoc, ← nU, h₁]
        simp only [Category.assoc]
        rfl
    _ = C₁.map (eK.hom.app K) ≫ pc₁.hom.app (Ee.obj (K₂.obj K)) ≫
          V₁.map (βF.app (K₂.obj K)) ≫ V₁.map (Ee'.map (F₂.map (cK₂.hom.app K) ≫
            βB₂.app (B₂.obj K))) ≫ βA.app _ ≫ uX.hom.app _ := by
        rw [← IX.map_comp_assoc, reassoc_of% nP₂, Iso.inv_hom_id_app_assoc, ← V₂.map_comp,
          ← reassoc_of% nA]
        rfl
    _ = C₁.map (eK.hom.app K) ≫ pc₁.hom.app (Ee.obj (K₂.obj K)) ≫
          V₁.map (F₁.map (Ee.map (cK₂.hom.app K))) ≫
            V₁.map (βF.app (P₂.obj (B₂.obj K)) ≫ Ee'.map (βB₂.app (B₂.obj K))) ≫
              βA.app _ ≫ uX.hom.app _ := by
        rw [← V₁.map_comp_assoc, Ee'.map_comp, ← reassoc_of% nF, Functor.map_comp_assoc]
    _ = C₁.map (cK₁.hom.app K ≫ P₁.map (eB.hom.app K)) ≫ pc₁.hom.app _ ≫
          V₁.map (βB₁.app (Dd.obj (B₂.obj K))) ≫
            V₁.map (Q₁.map (βD.app (B₂.obj K) ≫ uY.hom.app (I₂.obj (B₂.obj K)))) ≫
              V₁.map (eQ.hom.app (I₂.obj (B₂.obj K))) ≫ βA.app _ ≫ uX.hom.app _ := by
        rw [key, ← e₅]
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% (np _), reassoc_of% (np _), reassoc_of% (np _), reassoc_of% (np _)]
        rfl
    _ = _ := by
        rw [Functor.map_comp_assoc, ← reassoc_of% (np _), ← V₁.map_comp_assoc, nB₁,
          V₁.map_comp_assoc]
        rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, ← nU',
          ← reassoc_of% nA', ← V₁.map_comp_assoc (eQ.hom.app (I₁.obj (B₁.obj K))), ← nQ]
        simp only [h, Functor.map_comp, Category.assoc]
        rfl

section Helpers

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃} {𝒟 : Type u₄} {ℰ : Type u₅} {ℱ : Type u₆}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞] [Category.{v₄} 𝒟] [Category.{v₅} ℰ]
  [Category.{v₆} ℱ]

open scoped CategoryTheory.TwoSquare

/-- Reading the row identity of [Stacks, Tag 0ATR], transported along equalities of the
horizontal edges, at an object: the shape of the hypothesis `h₁` of
`Stacks.Duality.compositionChase`. -/
theorem rowChase {Ee : 𝒜 ⥤ ℬ} {C₁ L₁ : ℬ ⥤ 𝒞} {C₂ L₂ : 𝒜 ⥤ 𝒞} {F₁ : ℬ ⥤ 𝒟} {F₂ : 𝒜 ⥤ ℰ}
    {V₁ : 𝒟 ⥤ 𝒞} {V₂ : ℰ ⥤ 𝒞} {Ee' : ℰ ⥤ 𝒟} {IX : 𝒞 ⥤ 𝒞}
    (τ₁ : C₁ ≅ L₁) (τ₂ : C₂ ≅ L₂) (ω₁ : F₁ ⋙ V₁ ≅ L₁) (ω₂ : F₂ ⋙ V₂ ≅ L₂)
    (pc₁ : C₁ ≅ F₁ ⋙ V₁) (pc₂ : C₂ ≅ F₂ ⋙ V₂) (hpc₁ : pc₁ = τ₁ ≪≫ ω₁.symm)
    (hpc₂ : pc₂ = τ₂ ≪≫ ω₂.symm)
    (βE : Ee ⋙ C₁ ⟶ C₂ ⋙ IX) (βrow : Ee ⋙ L₁ ⟶ L₂ ⋙ IX) (βF : Ee ⋙ F₁ ⟶ F₂ ⋙ Ee')
    (βA : Ee' ⋙ V₁ ⟶ V₂ ⋙ IX)
    (hE : βE = Functor.whiskerLeft Ee τ₁.hom ≫ βrow ≫ Functor.whiskerRight τ₂.inv IX)
    (hrow : βrow = (((TwoSquare.mk _ _ _ _ βF ≫ᵥ TwoSquare.mk _ _ _ _ βA).whiskerLeft
      ω₂.hom).whiskerRight ω₁.inv)) (M : 𝒜) :
    βE.app M = pc₁.hom.app (Ee.obj M) ≫ V₁.map (βF.app M) ≫ βA.app (F₂.obj M) ≫
      IX.map (pc₂.inv.app M) := by
  subst hpc₁ hpc₂ hE hrow
  simp [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

/-- Reading the stacking identity of [Stacks, Tag 0ATQ] at an object: the shape of the
hypotheses `h₂`, `h₃` of `Stacks.Duality.compositionChase`. -/
theorem stackChase {P₂ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ 𝒞} {I₂ : 𝒜 ⥤ 𝒟} {Q₂ : 𝒟 ⥤ 𝒞} {Ee : ℬ ⥤ ℰ}
    {F₁ : ℰ ⥤ ℱ} {Ee' : 𝒞 ⥤ ℱ} {EP : 𝒜 ⥤ ℰ} {EQ : 𝒟 ⥤ ℱ}
    (βB : P₂ ⋙ F₂ ⟶ I₂ ⋙ Q₂) (βF : Ee ⋙ F₁ ⟶ F₂ ⋙ Ee') (cEP : EP ≅ P₂ ⋙ Ee)
    (cEQ : EQ ≅ Q₂ ⋙ Ee') (βFB : EP ⋙ F₁ ⟶ I₂ ⋙ EQ)
    (h : βFB = ((TwoSquare.mk _ _ _ _ βB ≫ₕ TwoSquare.mk _ _ _ _ βF).whiskerTop
      cEP.hom).whiskerBottom cEQ.inv) (N : 𝒜) :
    βFB.app N = F₁.map (cEP.hom.app N) ≫ βF.app (P₂.obj N) ≫ Ee'.map (βB.app N) ≫
      cEQ.inv.app (I₂.obj N) := by
  subst h
  simp [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

/-- Reading the transport of a base change map along equalities of the vertical edges at an
object: the shape of the hypothesis `h₄` of `Stacks.Duality.compositionChase`. -/
theorem vertChase {PD EP : 𝒜 ⥤ ℬ} {F₁ : ℬ ⥤ 𝒞} {I₂ : 𝒜 ⥤ 𝒟} {QI EQ : 𝒟 ⥤ 𝒞}
    (γP : PD ≅ EP) (γQ : QI ≅ EQ) (βCD : PD ⋙ F₁ ⟶ I₂ ⋙ QI) (βFB : EP ⋙ F₁ ⟶ I₂ ⋙ EQ)
    (h : βCD = Functor.whiskerRight γP.hom F₁ ≫ βFB ≫ Functor.whiskerLeft I₂ γQ.inv) (N : 𝒜) :
    βCD.app N = F₁.map (γP.hom.app N) ≫ βFB.app N ≫ γQ.inv.app (I₂.obj N) := by
  subst h
  simp

end Helpers

section Shapes

variable {𝒲 : Type u₇} {𝒴 : Type u₁} {𝒥 : Type u₂} {𝒦 : Type u₃} {𝒳 : Type u₄}
  [Category.{v₇} 𝒲] [Category.{v₁} 𝒴] [Category.{v₂} 𝒥] [Category.{v₃} 𝒦] [Category.{v₄} 𝒳]

/-- The shape of the comparison `α_g` of [Stacks, Tag 0AA0] (`Stacks.Duality.refinementIso`): a
comparison `e` of twisted inverse images, then a base change map `β`, then the identification `u`
of the twisted inverse image of an identity with the identity functor, read along `W`. -/
noncomputable def alphaShape {A : 𝒴 ⥤ 𝒥} {A' : 𝒴 ⥤ 𝒦} {Cc : 𝒦 ⥤ 𝒥} {R : 𝒥 ⥤ 𝒳} {R' : 𝒦 ⥤ 𝒳}
    {I : 𝒳 ⥤ 𝒳}
    (W : 𝒲 ⥤ 𝒴) (e : A ≅ A' ⋙ Cc) (β : Cc ⋙ R ⟶ R' ⋙ I)
    [hβ : IsIso (Functor.whiskerLeft (W ⋙ A') β)] (u : I ≅ 𝟭 𝒳) : W ⋙ A ⋙ R ≅ W ⋙ A' ⋙ R' :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft W e) R ≪≫ Functor.associator (W ⋙ A') Cc R ≪≫
    asIso (Functor.whiskerLeft (W ⋙ A') β) ≪≫
      Functor.isoWhiskerLeft (W ⋙ A') (Functor.isoWhiskerLeft R' u ≪≫ Functor.rightUnitor R')

/-- The components of `Stacks.Duality.alphaShape`. -/
theorem alphaShape_hom_app {A : 𝒴 ⥤ 𝒥} {A' : 𝒴 ⥤ 𝒦} {Cc : 𝒦 ⥤ 𝒥} {R : 𝒥 ⥤ 𝒳} {R' : 𝒦 ⥤ 𝒳}
    {I : 𝒳 ⥤ 𝒳} (W : 𝒲 ⥤ 𝒴) (e : A ≅ A' ⋙ Cc) (β : Cc ⋙ R ⟶ R' ⋙ I)
    [hβ : IsIso (Functor.whiskerLeft (W ⋙ A') β)] (u : I ≅ 𝟭 𝒳) (K : 𝒲) :
    (alphaShape W e β u).hom.app K =
      R.map (e.hom.app (W.obj K)) ≫ β.app (A'.obj (W.obj K)) ≫
        u.hom.app (R'.obj (A'.obj (W.obj K))) := by
  simp [alphaShape]

end Shapes

section AlphaNat

variable {𝒴 : Type u₁} {𝒥 : Type u₂} {𝒦 : Type u₃} {𝒳 : Type u₄}
  [Category.{v₁} 𝒴] [Category.{v₂} 𝒥] [Category.{v₃} 𝒦] [Category.{v₄} 𝒳]

/-- The underlying transformation of `Stacks.Duality.alphaShape`, before restriction. -/
def alphaNat {A : 𝒴 ⥤ 𝒥} {A' : 𝒴 ⥤ 𝒦} {Cc : 𝒦 ⥤ 𝒥} {R : 𝒥 ⥤ 𝒳} {R' : 𝒦 ⥤ 𝒳} {I : 𝒳 ⥤ 𝒳}
    (e : A ≅ A' ⋙ Cc) (β : Cc ⋙ R ⟶ R' ⋙ I) (u : I ≅ 𝟭 𝒳) : A ⋙ R ⟶ A' ⋙ R' :=
  Functor.whiskerRight e.hom R ≫ (Functor.associator A' Cc R).hom ≫ Functor.whiskerLeft A' β ≫
    Functor.whiskerLeft A' (Functor.whiskerLeft R' u.hom ≫ (Functor.rightUnitor R').hom)

/-- The components of `Stacks.Duality.alphaNat`. -/
theorem alphaNat_app {A : 𝒴 ⥤ 𝒥} {A' : 𝒴 ⥤ 𝒦} {Cc : 𝒦 ⥤ 𝒥} {R : 𝒥 ⥤ 𝒳} {R' : 𝒦 ⥤ 𝒳}
    {I : 𝒳 ⥤ 𝒳} (e : A ≅ A' ⋙ Cc) (β : Cc ⋙ R ⟶ R' ⋙ I) (u : I ≅ 𝟭 𝒳) (K : 𝒴) :
    (alphaNat e β u).app K =
      R.map (e.hom.app K) ≫ β.app (A'.obj K) ≫ u.hom.app (R'.obj (A'.obj K)) := by
  simp [alphaNat]

variable {𝒲 : Type u₅} [Category.{v₅} 𝒲]

/-- `Stacks.Duality.alphaShape` is `Stacks.Duality.alphaNat` read along `W`. -/
theorem alphaShape_hom {A : 𝒴 ⥤ 𝒥} {A' : 𝒴 ⥤ 𝒦} {Cc : 𝒦 ⥤ 𝒥} {R : 𝒥 ⥤ 𝒳} {R' : 𝒦 ⥤ 𝒳}
    {I : 𝒳 ⥤ 𝒳} (W : 𝒲 ⥤ 𝒴) (e : A ≅ A' ⋙ Cc) (β : Cc ⋙ R ⟶ R' ⋙ I)
    [hβ : IsIso (Functor.whiskerLeft (W ⋙ A') β)] (u : I ≅ 𝟭 𝒳) :
    (alphaShape W e β u).hom = Functor.whiskerLeft W (alphaNat e β u) := by
  ext K
  simp [alphaShape, alphaNat]

end AlphaNat

section ChainIso

/-- The composite shape of `Stacks.Duality.CompositionData.compMap`, with variable data: a
comparison `α` of the first functor, then a comparison `β` of the last, then a transformation `γ`
in the middle. -/
noncomputable def chainMap {C₀ C₁ C₂ C₃ C₄ C₅ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅] {K₀ : C₀ ⥤ C₂} {B : C₀ ⥤ C₁} {P : C₁ ⥤ C₂}
    {R : C₂ ⥤ C₅} {F : C₂ ⥤ C₃} {V : C₃ ⥤ C₅} {I : C₁ ⥤ C₄} {Q : C₄ ⥤ C₃}
    (α : K₀ ⟶ B ⋙ P) (β : R ⟶ F ⋙ V) (γ : P ⋙ F ⟶ I ⋙ Q) : K₀ ⋙ R ⟶ B ⋙ I ⋙ Q ⋙ V :=
  Functor.whiskerRight α R ≫ (Functor.associator B P R).hom ≫
    Functor.whiskerLeft B (Functor.whiskerLeft P β ≫ (Functor.associator P F V).inv ≫
      Functor.whiskerRight γ V ≫ (Functor.associator I Q V).hom)

/-- The components of `Stacks.Duality.chainMap`. -/
theorem chainMap_app {C₀ C₁ C₂ C₃ C₄ C₅ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅] {K₀ : C₀ ⥤ C₂} {B : C₀ ⥤ C₁} {P : C₁ ⥤ C₂}
    {R : C₂ ⥤ C₅} {F : C₂ ⥤ C₃} {V : C₃ ⥤ C₅} {I : C₁ ⥤ C₄} {Q : C₄ ⥤ C₃}
    (α : K₀ ⟶ B ⋙ P) (β : R ⟶ F ⋙ V) (γ : P ⋙ F ⟶ I ⋙ Q) (K : C₀) :
    (chainMap α β γ).app K =
      R.map (α.app K) ≫ β.app (P.obj (B.obj K)) ≫ V.map (γ.app (B.obj K)) := by
  simp [chainMap]

/-- The composite shape `Stacks.Duality.chainMap`, read along `W`, is invertible as soon as its
middle transformation is, read along `W ⋙ B`. -/
theorem isIso_whiskerLeft_chainMap {Cw C₀ C₁ C₂ C₃ C₄ C₅ : Type*} [Category Cw] [Category C₀]
    [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₅] (W : Cw ⥤ C₀)
    {K₀ : C₀ ⥤ C₂} {B : C₀ ⥤ C₁} {P : C₁ ⥤ C₂} {R : C₂ ⥤ C₅} {F : C₂ ⥤ C₃} {V : C₃ ⥤ C₅}
    {I : C₁ ⥤ C₄} {Q : C₄ ⥤ C₃} (α : K₀ ≅ B ⋙ P) (β : R ≅ F ⋙ V) (γ : P ⋙ F ⟶ I ⋙ Q)
    [IsIso (Functor.whiskerLeft (W ⋙ B) γ)] :
    IsIso (Functor.whiskerLeft W (chainMap α.hom β.hom γ)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K => ?_
  have hγ : IsIso (γ.app (B.obj (W.obj K))) :=
    NatIso.isIso_app_of_isIso (Functor.whiskerLeft (W ⋙ B) γ) K
  simp only [Functor.whiskerLeft_app, chainMap_app]
  infer_instance

end ChainIso

section NaturalityShape

/-- The bookkeeping that turns the chase `Stacks.Duality.compositionChase`, read at every object,
into an identity of transformations, with variable data. -/
theorem naturalityShape {Zc Y₁c Y₂c X₁c X₂c U₁c U₂c Yc Xc : Type*} [Category Zc] [Category Y₁c]
    [Category Y₂c] [Category X₁c] [Category X₂c] [Category U₁c] [Category U₂c] [Category Yc]
    [Category Xc]
    {K₁ : Zc ⥤ X₁c} {K₂ : Zc ⥤ X₂c} {Ee : X₂c ⥤ X₁c} {C₁ : X₁c ⥤ Xc} {C₂ : X₂c ⥤ Xc}
    {IX : Xc ⥤ Xc} {B₁ : Zc ⥤ Y₁c} {B₂ : Zc ⥤ Y₂c} {Dd : Y₂c ⥤ Y₁c} {I₁ : Y₁c ⥤ Yc}
    {I₂ : Y₂c ⥤ Yc} {IY : Yc ⥤ Yc} {Q₁ : Yc ⥤ U₁c} {Q₂ : Yc ⥤ U₂c} {Ee' : U₂c ⥤ U₁c}
    {V₁ : U₁c ⥤ Xc} {V₂ : U₂c ⥤ Xc}
    (eK : K₁ ≅ K₂ ⋙ Ee) (βE : Ee ⋙ C₁ ⟶ C₂ ⋙ IX) (uX : IX ≅ 𝟭 Xc)
    (eB : B₁ ≅ B₂ ⋙ Dd) (βD : Dd ⋙ I₁ ⟶ I₂ ⋙ IY) (uY : IY ≅ 𝟭 Yc)
    (eQ : Q₁ ≅ Q₂ ⋙ Ee') (βA : Ee' ⋙ V₁ ⟶ V₂ ⋙ IX)
    (Γ₁ : K₁ ⋙ C₁ ⟶ B₁ ⋙ I₁ ⋙ Q₁ ⋙ V₁) (Γ₂ : K₂ ⋙ C₂ ⟶ B₂ ⋙ I₂ ⋙ Q₂ ⋙ V₂)
    (h : ∀ K, (C₁.map (eK.hom.app K) ≫ βE.app (K₂.obj K) ≫ uX.hom.app (C₂.obj (K₂.obj K))) ≫
        Γ₂.app K =
      Γ₁.app K ≫ (V₁.map (eQ.hom.app (I₁.obj (B₁.obj K))) ≫ βA.app (Q₂.obj (I₁.obj (B₁.obj K))) ≫
          uX.hom.app (V₂.obj (Q₂.obj (I₁.obj (B₁.obj K))))) ≫
        V₂.map (Q₂.map (I₁.map (eB.hom.app K) ≫ βD.app (B₂.obj K) ≫
          uY.hom.app (I₂.obj (B₂.obj K))))) :
    alphaNat eK βE uX ≫ Γ₂ =
      Γ₁ ≫ Functor.whiskerLeft (B₁ ⋙ I₁) (alphaNat eQ βA uX) ≫
        Functor.whiskerRight (alphaNat eB βD uY) (Q₂ ⋙ V₂) := by
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, alphaNat_app,
    Functor.comp_obj, Functor.comp_map]
  exact h K

end NaturalityShape

section Lift

variable {𝒵' : Type u₁} {𝒵 : Type u₂} {𝒴 : Type u₃} {𝒳 : Type u₄}
  [Category.{v₁} 𝒵'] [Category.{v₂} 𝒵] [Category.{v₃} 𝒴] [Category.{v₄} 𝒳]

/-- An isomorphism of two functors landing in a full subcategory, read in the full subcategory. -/
def liftIsoOf (P : ObjectProperty 𝒴) {F₁ F₂ : 𝒵' ⥤ 𝒴} (h₁ : ∀ K, P (F₁.obj K))
    (h₂ : ∀ K, P (F₂.obj K)) (e : F₁ ≅ F₂) : P.lift F₁ h₁ ≅ P.lift F₂ h₂ :=
  NatIso.ofComponents (fun K => P.isoMk (e.app K))
    (fun a => ObjectProperty.hom_ext _ (e.hom.naturality a))

/-- The components of `Stacks.Duality.liftIsoOf`. -/
@[simp]
theorem liftIsoOf_hom_app_hom (P : ObjectProperty 𝒴) {F₁ F₂ : 𝒵' ⥤ 𝒴} (h₁ : ∀ K, P (F₁.obj K))
    (h₂ : ∀ K, P (F₂.obj K)) (e : F₁ ≅ F₂) (K : 𝒵') :
    ((liftIsoOf P h₁ h₂ e).hom.app K).hom = e.hom.app K := rfl

/-- `Stacks.Duality.liftIsoOf` is compatible with composition. -/
theorem liftIsoOf_trans (P : ObjectProperty 𝒴) {F₁ F₂ F₃ : 𝒵' ⥤ 𝒴} (h₁ : ∀ K, P (F₁.obj K))
    (h₂ : ∀ K, P (F₂.obj K)) (h₃ : ∀ K, P (F₃.obj K)) (e : F₁ ≅ F₂) (e' : F₂ ≅ F₃) :
    liftIsoOf P h₁ h₃ (e ≪≫ e') = liftIsoOf P h₁ h₂ e ≪≫ liftIsoOf P h₂ h₃ e' := by
  ext
  rfl

/-- `Stacks.Duality.liftIsoOf` is compatible with inverses. -/
theorem liftIsoOf_symm (P : ObjectProperty 𝒴) {F₁ F₂ : 𝒵' ⥤ 𝒴} (h₁ : ∀ K, P (F₁.obj K))
    (h₂ : ∀ K, P (F₂.obj K)) (e : F₁ ≅ F₂) :
    liftIsoOf P h₂ h₁ e.symm = (liftIsoOf P h₁ h₂ e).symm := by
  ext
  rfl

/-- `Stacks.Duality.liftIsoOf` of the identity is the identity. -/
@[simp]
theorem liftIsoOf_refl (P : ObjectProperty 𝒴) {F : 𝒵' ⥤ 𝒴} (h : ∀ K, P (F.obj K)) :
    liftIsoOf P h h (Iso.refl F) = Iso.refl _ := by
  ext
  rfl

/-- `Stacks.Duality.liftIsoOf` of `e₁⁻¹ ≫ e₂`. -/
theorem liftIsoOf_symm_trans (P : ObjectProperty 𝒴) {F₁ F₂ F₃ : 𝒵' ⥤ 𝒴}
    (h₁ : ∀ K, P (F₁.obj K)) (h₂ : ∀ K, P (F₂.obj K)) (h₃ : ∀ K, P (F₃.obj K)) (e₁ : F₁ ≅ F₂)
    (e₂ : F₁ ≅ F₃) (e : F₂ ≅ F₃) (he : e₁.symm ≪≫ e₂ = e) :
    (liftIsoOf P h₁ h₂ e₁).symm ≪≫ liftIsoOf P h₁ h₃ e₂ = liftIsoOf P h₂ h₃ e := by
  subst he
  rw [liftIsoOf_trans P h₂ h₁ h₃, liftIsoOf_symm]

/-- **The composite isomorphism `f^!_A ∘ g^!_D` in transformation form**, with variable data: the
horizontal composite of the lift of an isomorphism `α_D` read along `W` with an isomorphism `α_A`
read along the inclusion of the full subcategory is the whiskered composite of the underlying
transformations. -/
theorem hcomp_liftIsoOf_hom (P : ObjectProperty 𝒴) (W : 𝒵' ⥤ 𝒵) {F₁ F₂ : 𝒵 ⥤ 𝒴}
    {H₁ H₂ : 𝒴 ⥤ 𝒳} (h₁ : ∀ K, P ((W ⋙ F₁).obj K)) (h₂ : ∀ K, P ((W ⋙ F₂).obj K))
    (αD : W ⋙ F₁ ≅ W ⋙ F₂) (αA : P.ι ⋙ H₁ ≅ P.ι ⋙ H₂) (aD : F₁ ⟶ F₂) (aA : H₁ ⟶ H₂)
    (hD : αD.hom = Functor.whiskerLeft W aD) (hA : αA.hom = Functor.whiskerLeft P.ι aA) :
    (NatIso.hcomp (liftIsoOf P h₁ h₂ αD) αA).hom =
      (Functor.whiskerLeft W (Functor.whiskerLeft F₁ aA ≫ Functor.whiskerRight aD H₂) :
        P.lift (W ⋙ F₁) h₁ ⋙ (P.ι ⋙ H₁) ⟶ P.lift (W ⋙ F₂) h₂ ⋙ (P.ι ⋙ H₂)) := by
  ext K
  have hD' := NatTrans.congr_app hD K
  have hA' := NatTrans.congr_app hA ((P.lift (W ⋙ F₁) h₁).obj K)
  simp only [Functor.whiskerLeft_app] at hD' hA'
  simp only [NatIso.hcomp, NatTrans.hcomp_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.whiskerRight_app, hA', Functor.comp_map, ObjectProperty.ι_map, liftIsoOf_hom_app_hom,
    hD']
  rfl

/-- **The naturality of the isomorphism of [Stacks, Tag 0ATX] as an identity of isomorphisms**,
with variable data: an identity of underlying transformations `hN` gives the identity of
isomorphisms out of the subcategory `W`, the second factor being read in the full subcategory
`P`. -/
theorem isoNaturalityShape (P : ObjectProperty 𝒴) (W : 𝒵' ⥤ 𝒵)
    {K₁ K₂ : 𝒵 ⥤ 𝒳} {F₁ F₂ : 𝒵 ⥤ 𝒴} {H₁ H₂ : 𝒴 ⥤ 𝒳}
    (h₁ : ∀ K, P ((W ⋙ F₁).obj K)) (h₂ : ∀ K, P ((W ⋙ F₂).obj K))
    (αE : W ⋙ K₁ ≅ W ⋙ K₂) (θ₁ : W ⋙ K₁ ≅ P.lift (W ⋙ F₁) h₁ ⋙ (P.ι ⋙ H₁))
    (θ₂ : W ⋙ K₂ ≅ P.lift (W ⋙ F₂) h₂ ⋙ (P.ι ⋙ H₂))
    (αD : W ⋙ F₁ ≅ W ⋙ F₂) (αA : P.ι ⋙ H₁ ≅ P.ι ⋙ H₂)
    (aE : K₁ ⟶ K₂) (c₁ : K₁ ⟶ F₁ ⋙ H₁) (c₂ : K₂ ⟶ F₂ ⋙ H₂) (aD : F₁ ⟶ F₂) (aA : H₁ ⟶ H₂)
    (hE : αE.hom = Functor.whiskerLeft W aE) (hθ₁ : θ₁.hom = Functor.whiskerLeft W c₁)
    (hθ₂ : θ₂.hom = Functor.whiskerLeft W c₂) (hD : αD.hom = Functor.whiskerLeft W aD)
    (hA : αA.hom = Functor.whiskerLeft P.ι aA)
    (hN : aE ≫ c₂ = c₁ ≫ Functor.whiskerLeft F₁ aA ≫ Functor.whiskerRight aD H₂) :
    αE ≪≫ θ₂ = θ₁ ≪≫ NatIso.hcomp (liftIsoOf P h₁ h₂ αD) αA := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, Iso.trans_hom, hE, hθ₁, hθ₂, hcomp_liftIsoOf_hom P W h₁ h₂ αD αA aD aA hD hA]
  simpa only [Functor.whiskerLeft_comp] using congrArg (Functor.whiskerLeft W) hN

end Lift

section Groupoid

universe w

/-- In a family of isomorphisms that is reflexive and transitive, the isomorphism between two
members is read off any third one. -/
theorem coherent_eq_symm_trans {ι : Type w} {𝒞 : Type u₁} [Category.{v₁} 𝒞] {F : ι → 𝒞}
    (e : ∀ i j, F i ≅ F j) (hrefl : ∀ i, e i i = Iso.refl _)
    (htrans : ∀ i j k, e i j ≪≫ e j k = e i k) (r i j : ι) :
    e i j = (e r i).symm ≪≫ e r j := by
  have h₂ : e i r = (e r i).symm := by
    calc e i r = (e i r ≪≫ e r i) ≪≫ (e r i).symm := by simp
      _ = (e r i).symm := by rw [htrans i r i, hrefl i, Iso.refl_trans]
  rw [← htrans i r j, h₂]

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃} [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Category.{v₃} 𝒞]

/-- **Independence from a dominating choice**, with variable data: if two isomorphisms `θ₁`, `θ₂`
are both obtained from a third `θ₃` through comparisons `aₙ`, `bₙ`, `cₙ`, then `θ₂` is `θ₁` read
through the composite comparisons. -/
theorem independenceShape {X₁ X₂ X₃ : 𝒜 ⥤ 𝒞} {G₁ G₂ G₃ : 𝒜 ⥤ ℬ} {H₁ H₂ H₃ : ℬ ⥤ 𝒞}
    (θ₁ : X₁ ≅ G₁ ⋙ H₁) (θ₂ : X₂ ≅ G₂ ⋙ H₂) (θ₃ : X₃ ≅ G₃ ⋙ H₃)
    (a₁ : X₃ ≅ X₁) (a₂ : X₃ ≅ X₂) (b₁ : G₃ ≅ G₁) (b₂ : G₃ ≅ G₂) (c₁ : H₃ ≅ H₁) (c₂ : H₃ ≅ H₂)
    (n₁ : a₁ ≪≫ θ₁ = θ₃ ≪≫ NatIso.hcomp b₁ c₁) (n₂ : a₂ ≪≫ θ₂ = θ₃ ≪≫ NatIso.hcomp b₂ c₂) :
    θ₂ = (a₁.symm ≪≫ a₂).symm ≪≫ θ₁ ≪≫ NatIso.hcomp (b₁.symm ≪≫ b₂) (c₁.symm ≪≫ c₂) := by
  have e₁ : θ₁ = a₁.symm ≪≫ θ₃ ≪≫ NatIso.hcomp b₁ c₁ := by
    rw [← n₁]
    simp
  have e₂ : θ₂ = a₂.symm ≪≫ θ₃ ≪≫ NatIso.hcomp b₂ c₂ := by
    rw [← n₂]
    simp
  rw [e₂, e₁]
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    NatIso.hcomp_hom, NatTrans.hcomp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  congr 2
  have n1 := c₁.inv.naturality (b₁.hom.app K)
  have n2 := c₂.hom.naturality (b₁.hom.app K)
  rw [reassoc_of% n1, Iso.hom_inv_id_app_assoc, reassoc_of% n2, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc]

/-- The horizontal composite with an identity on the left is a whiskering. -/
theorem hcomp_refl_left {G : 𝒜 ⥤ ℬ} {H₁ H₂ : ℬ ⥤ 𝒞} (c : H₁ ≅ H₂) :
    NatIso.hcomp (Iso.refl G) c = Functor.isoWhiskerLeft G c := by
  ext K
  simp

/-- The interchange law for horizontal composites of isomorphisms. -/
theorem hcomp_trans {G₁ G₂ G₃ : 𝒜 ⥤ ℬ} {H₁ H₂ H₃ : ℬ ⥤ 𝒞} (b : G₁ ≅ G₂) (b' : G₂ ≅ G₃)
    (c : H₁ ≅ H₂) (c' : H₂ ≅ H₃) :
    NatIso.hcomp (b ≪≫ b') (c ≪≫ c') = NatIso.hcomp b c ≪≫ NatIso.hcomp b' c' := by
  ext K
  simp only [NatIso.hcomp_hom, Iso.trans_hom, NatTrans.hcomp_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  congr 1
  rw [← Category.assoc, ← Category.assoc, ← c'.hom.naturality]

/-- The bookkeeping of the compatibility of the canonical isomorphism of [Stacks, Tag 0ATX] with
the comparisons of [Stacks, Tag 0AA0], with variable data. -/
theorem canonicalShape {Kk Kk' KD KD' : 𝒜 ⥤ 𝒞} {Gi Gi' : 𝒜 ⥤ ℬ} {HD HD' Hj Hj' : ℬ ⥤ 𝒞}
    (o₁ : Kk ≅ KD) (o₂ : Kk' ≅ KD') (oD : KD ≅ KD') (okk : Kk ≅ Kk')
    (θ : KD ≅ Gi ⋙ HD) (θ' : KD' ≅ Gi' ⋙ HD') (b : Gi ≅ Gi') (hDD' : HD ≅ HD')
    (hDj : HD ≅ Hj) (hD'j' : HD' ≅ Hj') (hjj' : Hj ≅ Hj')
    (indep : θ' = oD.symm ≪≫ θ ≪≫ NatIso.hcomp b hDD')
    (hO : okk ≪≫ o₂ = o₁ ≪≫ oD) (hI : hDD' ≪≫ hD'j' = hDj ≪≫ hjj') :
    okk ≪≫ o₂ ≪≫ θ' ≪≫ Functor.isoWhiskerLeft Gi' hD'j' =
      (o₁ ≪≫ θ ≪≫ Functor.isoWhiskerLeft Gi hDj) ≪≫ NatIso.hcomp b hjj' := by
  subst indep
  have hO' : okk ≪≫ o₂ ≪≫ oD.symm = o₁ := by
    rw [← Iso.trans_assoc, hO]
    simp
  have hI' := congrArg (fun e : HD ≅ Hj' => e.hom) hI
  simp only [Iso.trans_hom] at hI'
  ext K
  have hO'' := congrArg (fun e : Kk ≅ KD => e.hom.app K) hO'
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom] at hO''
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatIso.hcomp_hom,
    NatTrans.hcomp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% hO'']
  congr 2
  have n := hD'j'.hom.naturality (b.hom.app K)
  have hI'' := NatTrans.congr_app hI' (Gi.obj K)
  simp only [NatTrans.comp_app] at hI''
  rw [n, reassoc_of% hI'']

end Groupoid

end Stacks.Duality
