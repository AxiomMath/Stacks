module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponentTransitions
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPairEquivalence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

variable (A) in
/-- The simplicial-site situation of the small étale site of `U`. -/
abbrev situation : SimplicialSiteSituation.{u + 1} := (etaleSimplicialSite A).situation

/-- The identification of the sheaves on the component of degree `n` of `U_étale`, read as a
component of the simplicial-site situation, with the sheaves on `U_{n, spaces, étale}`. -/
def compEquiv (n : SimplexCategory) :
    Sheaf ((situation A).componentTopology n) (Type (u + 1)) ≌
      spacesEtaleSheafCat B S hS (A.left.obj (op n)) :=
  sheafEquivType n

/-- The transition comparison `f_ψ⁻¹ ⋙ E_k ≅ E_n ⋙ U(ψ)^*`, read in the situation. -/
def transInvIso {n k : SimplexCategory} (ψ : n ⟶ k) :
    ((situation A).transitionMorphism ψ).inverseImage ⋙ (compEquiv k).functor ≅
      (compEquiv n).functor ⋙ spacesEtaleInverseImage B S hS (A.left.map ψ.op) :=
  transitionInverseImageIso ψ

/-- The direct-image comparison `E_k⁻¹ ⋙ f_{ψ,*} ≅ U(ψ)_* ⋙ E_n⁻¹`, read in the situation. -/
def transPushIso {n k : SimplexCategory} (ψ : n ⟶ k) :
    (compEquiv k).inverse ⋙ ((situation A).transitionMorphism ψ).pushforward ≅
      spacesEtaleSheafPushforward B S hS (A.left.map ψ.op) ⋙ (compEquiv n).inverse :=
  transitionPushforwardIso ψ

/-- The adjunction `f_ψ⁻¹ ⊣ f_{ψ,*}` of a transition. -/
abbrev transitionAdj {m n : SimplexCategory} (ψ : m ⟶ n) :=
  ((situation A).transitionMorphism ψ).adj

/-- The adjunction of the identification of component sheaves with spaces-étale sheaves. -/
abbrev equivAdj (n : SimplexCategory) := (compEquiv (A := A) n).toAdjunction

/-- The adjunction of the spaces-étale inverse image along `U(ψ)`. -/
abbrev spacesAdj {m n : SimplexCategory} (ψ : m ⟶ n) :=
  spacesEtaleAdjunction B S hS (A.left.map ψ.op)

/-- The mate of the inverse of an isomorphism of left adjoints whose mate is invertible. -/
theorem conjugateEquiv_inv_eq {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D}
    {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁) (σ : R₁ ≅ R₂)
    (h : conjugateEquiv adj₁ adj₂ e.hom = σ.hom) : conjugateEquiv adj₂ adj₁ e.inv = σ.inv := by
  have := conjugateEquiv_comm adj₁ adj₂ (α := e.hom) (β := e.inv) e.inv_hom_id
  rw [h] at this
  rw [← cancel_epi σ.hom, this, σ.hom_inv_id]

/-- The mate of the inverse associator. -/
theorem conjugateEquiv_associator_inv {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁]
    [Category C₂] [Category C₃] {L₀₁ : C₀ ⥤ C₁} {R₁₀ : C₁ ⥤ C₀} {L₁₂ : C₁ ⥤ C₂}
    {R₂₁ : C₂ ⥤ C₁} {L₂₃ : C₂ ⥤ C₃} {R₃₂ : C₃ ⥤ C₂} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv :=
  conjugateEquiv_inv_eq _ _ (Functor.associator _ _ _) (Functor.associator _ _ _)
    (conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃)

/-- The mate of the comparison of the inverse images along two equal morphisms. -/
theorem conjugateEquiv_spacesEtaleInverseImage_eqToHom {X Y : AlgebraicSpaces B S hS}
    {f g : X ⟶ Y} (e : f = g) :
    conjugateEquiv (spacesEtaleAdjunction B S hS g) (spacesEtaleAdjunction B S hS f)
        (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) e)) =
      eqToHom (congrArg (fun k => spacesEtaleSheafPushforward B S hS k) e.symm) := by
  subst e
  simp [conjugateEquiv_id]

/-- The mate of the transition comparison `f_ψ⁻¹ ⋙ E_k ≅ E_n ⋙ U(ψ)^*` is the direct-image
comparison. -/
theorem conjugateEquiv_transInvIso_hom {n k : SimplexCategory} (ψ : n ⟶ k) :
    conjugateEquiv ((equivAdj (A := A) n).comp (spacesAdj (A := A) ψ))
        ((transitionAdj (A := A) ψ).comp (equivAdj k)) (transInvIso ψ).hom =
      (transPushIso ψ).inv :=
  conjugateEquiv_leftAdjointUniq_ofNatIsoRight _ _ (transitionPushforwardIso ψ).symm

/-- The mate of the inverse of the inverse-image compositor of the transitions is the inverse
of the direct-image compositor. -/
theorem conjugateEquiv_canonicalCompositionComparison_inv {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    conjugateEquiv (transitionAdj (A := A) (ψ ≫ φ)) ((transitionAdj ψ).comp (transitionAdj φ))
        (SimplicialSiteSituation.canonicalCompositionComparison (situation A) ψ φ).inv =
      ((situation A).pushforwardCompSymm ψ φ).inv :=
  conjugateEquiv_inv_eq _ _ _ _
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight _ _ ((situation A).pushforwardCompSymm ψ φ))

section Abstract

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*} [Category A₀] [Category A₁] [Category A₂] [Category B₀]
  [Category B₁] [Category B₂]
  {F₀₁ : A₀ ⥤ A₁} {F₁₂ : A₁ ⥤ A₂} {F₀₂ : A₀ ⥤ A₂} {R₁₀ : A₁ ⥤ A₀} {R₂₁ : A₂ ⥤ A₁}
  {R₂₀ : A₂ ⥤ A₀}
  {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂} {E₀' : B₀ ⥤ A₀} {E₁' : B₁ ⥤ A₁}
  {E₂' : B₂ ⥤ A₂}
  {G₀₁ : B₀ ⥤ B₁} {G₁₂ : B₁ ⥤ B₂} {G₀₂ : B₀ ⥤ B₂} {G₀₂' : B₀ ⥤ B₂} {Q₁₀ : B₁ ⥤ B₀}
  {Q₂₁ : B₂ ⥤ B₁} {Q₂₀ : B₂ ⥤ B₀} {Q₂₀' : B₂ ⥤ B₀}
  (a₀₁ : F₀₁ ⊣ R₁₀) (a₁₂ : F₁₂ ⊣ R₂₁) (a₀₂ : F₀₂ ⊣ R₂₀)
  (e₀ : E₀ ⊣ E₀') (e₁ : E₁ ⊣ E₁') (e₂ : E₂ ⊣ E₂')
  (b₀₁ : G₀₁ ⊣ Q₁₀) (b₁₂ : G₁₂ ⊣ Q₂₁) (b₀₂ : G₀₂ ⊣ Q₂₀) (b₀₂' : G₀₂' ⊣ Q₂₀')

/-- **Pasting of mates.** Let a triangle of left adjoints `F` on one side and `G` on the other
be compared by left adjoints `E` along three squares, all comparisons being mates of
comparisons of the right adjoints. If the right-adjoint comparisons paste, so do their mates. -/
theorem mate_paste (p : R₂₀ ⟶ R₂₁ ⋙ R₁₀) (t₀₁ : Q₁₀ ⋙ E₀' ⟶ E₁' ⋙ R₁₀)
    (t₁₂ : Q₂₁ ⋙ E₁' ⟶ E₂' ⋙ R₂₁) (t₀₂ : Q₂₀ ⋙ E₀' ⟶ E₂' ⋙ R₂₀)
    (q : Q₂₀' ⟶ Q₂₁ ⋙ Q₁₀) (r : Q₂₀ ⟶ Q₂₀')
    (h : t₀₂ ≫ Functor.whiskerLeft E₂' p =
      Functor.whiskerRight r E₀' ≫ Functor.whiskerRight q E₀' ≫
        (Functor.associator Q₂₁ Q₁₀ E₀').hom ≫ Functor.whiskerLeft Q₂₁ t₀₁ ≫
        (Functor.associator Q₂₁ E₁' R₁₀).inv ≫ Functor.whiskerRight t₁₂ R₁₀ ≫
        (Functor.associator E₂' R₂₁ R₁₀).hom) :
    Functor.whiskerRight ((conjugateEquiv a₀₂ (a₀₁.comp a₁₂)).symm p) E₂ ≫
        (conjugateEquiv (e₀.comp b₀₂) (a₀₂.comp e₂)).symm t₀₂ =
      (Functor.associator F₀₁ F₁₂ E₂).hom ≫
        Functor.whiskerLeft F₀₁ ((conjugateEquiv (e₁.comp b₁₂) (a₁₂.comp e₂)).symm t₁₂) ≫
        (Functor.associator F₀₁ E₁ G₁₂).inv ≫
        Functor.whiskerRight ((conjugateEquiv (e₀.comp b₀₁) (a₀₁.comp e₁)).symm t₀₁) G₁₂ ≫
        (Functor.associator E₀ G₀₁ G₁₂).hom ≫
        Functor.whiskerLeft E₀ ((conjugateEquiv b₀₂' (b₀₁.comp b₁₂)).symm q) ≫
        Functor.whiskerLeft E₀ ((conjugateEquiv b₀₂ b₀₂').symm r) := by
  apply (conjugateEquiv (e₀.comp b₀₂) ((a₀₁.comp a₁₂).comp e₂)).injective
  rw [← conjugateEquiv_comp _ (a₀₂.comp e₂) _, Equiv.apply_symm_apply,
    conjugateEquiv_whiskerRight, Equiv.apply_symm_apply, h]
  rw [← conjugateEquiv_comp _ (a₀₁.comp (a₁₂.comp e₂)) _,
    ← conjugateEquiv_comp _ (a₀₁.comp (e₁.comp b₁₂)) _,
    ← conjugateEquiv_comp _ ((a₀₁.comp e₁).comp b₁₂) _,
    ← conjugateEquiv_comp _ ((e₀.comp b₀₁).comp b₁₂) _,
    ← conjugateEquiv_comp _ (e₀.comp (b₀₁.comp b₁₂)) _,
    ← conjugateEquiv_comp _ (e₀.comp b₀₂') _]
  rw [conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply, conjugateEquiv_whiskerLeft,
    Equiv.apply_symm_apply, conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    Equiv.apply_symm_apply, conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft,
    Equiv.apply_symm_apply, conjugateEquiv_associator_hom]
  simp only [Category.assoc]

omit [Category A₀] [Category B₀] in
/-- **Pasting of mates, second form.** A triangle of left adjoints out of a common source,
compared with another one through left adjoints `E` on two of its vertices: if the
right-adjoint comparisons paste, so do their mates. -/
theorem mate_paste' {X₀ : Type*} [Category X₀] {c₁ : X₀ ⥤ A₁} {c₂ : X₀ ⥤ A₂}
    {c₁' : A₁ ⥤ X₀} {c₂' : A₂ ⥤ X₀} {G₁ : X₀ ⥤ B₁} {G₂ G₂' : X₀ ⥤ B₂} {Q₁ : B₁ ⥤ X₀}
    {Q₂ Q₂' : B₂ ⥤ X₀} (γ₁ : c₁ ⊣ c₁') (γ₂ : c₂ ⊣ c₂') (β₁ : G₁ ⊣ Q₁) (β₂ : G₂ ⊣ Q₂)
    (β₂' : G₂' ⊣ Q₂') (p : c₂' ⟶ R₂₁ ⋙ c₁') (s₁ : Q₁ ⟶ E₁' ⋙ c₁') (s₂ : Q₂ ⟶ E₂' ⋙ c₂')
    (t : Q₂₁ ⋙ E₁' ⟶ E₂' ⋙ R₂₁) (q : Q₂' ⟶ Q₂₁ ⋙ Q₁) (r : Q₂ ⟶ Q₂')
    (h : s₂ ≫ Functor.whiskerLeft E₂' p =
      r ≫ q ≫ Functor.whiskerLeft Q₂₁ s₁ ≫ (Functor.associator Q₂₁ E₁' c₁').inv ≫
        Functor.whiskerRight t c₁' ≫ (Functor.associator E₂' R₂₁ c₁').hom) :
    Functor.whiskerRight ((conjugateEquiv γ₂ (γ₁.comp a₁₂)).symm p) E₂ ≫
        (conjugateEquiv β₂ (γ₂.comp e₂)).symm s₂ =
      (Functor.associator c₁ F₁₂ E₂).hom ≫
        Functor.whiskerLeft c₁ ((conjugateEquiv (e₁.comp b₁₂) (a₁₂.comp e₂)).symm t) ≫
        (Functor.associator c₁ E₁ G₁₂).inv ≫
        Functor.whiskerRight ((conjugateEquiv β₁ (γ₁.comp e₁)).symm s₁) G₁₂ ≫
        (conjugateEquiv β₂' (β₁.comp b₁₂)).symm q ≫ (conjugateEquiv β₂ β₂').symm r := by
  apply (conjugateEquiv β₂ ((γ₁.comp a₁₂).comp e₂)).injective
  rw [← conjugateEquiv_comp _ (γ₂.comp e₂) _, Equiv.apply_symm_apply,
    conjugateEquiv_whiskerRight, Equiv.apply_symm_apply, h]
  rw [← conjugateEquiv_comp _ (γ₁.comp (a₁₂.comp e₂)) _,
    ← conjugateEquiv_comp _ (γ₁.comp (e₁.comp b₁₂)) _,
    ← conjugateEquiv_comp _ ((γ₁.comp e₁).comp b₁₂) _,
    ← conjugateEquiv_comp _ (β₁.comp b₁₂) _,
    ← conjugateEquiv_comp _ β₂' _]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, conjugateEquiv_whiskerRight,
    Equiv.apply_symm_apply, conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft,
    Equiv.apply_symm_apply, conjugateEquiv_associator_hom]
  simp only [Category.assoc]

end Abstract

/-! ### The site-level coherence of the transition comparisons -/

/-- Base change along equal morphisms, on the cartesian projections. -/
@[reassoc]
theorem eqToHom_comp_projection {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y} (e : f = g)
    (V : SpacesEtale B S hS Y)
    (h : (spacesBaseChange B S hS f).functor.obj V = (spacesBaseChange B S hS g).functor.obj V) :
    (eqToHom h).hom.left ≫
        (spacesBaseChange B S hS g).projection.app V =
      (spacesBaseChange B S hS f).projection.app V := by
  subst e
  simp

/-- The transitions of the components compose on the nose. -/
theorem transition_obj_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (x : EtaleComponent A l) :
    (transition φ).obj ((transition ψ).obj x) = (transition (ψ ≫ φ)).obj x :=
  (Index.push_comp (A := A) ψ φ x).symm

/-- The comparison morphism of a transition, read through the realization functors. -/
def comparison' {n k : SimplexCategory} (ψ : n ⟶ k) (x : EtaleComponent A n) :
    ((realizeFunctor k).obj ((transition ψ).obj x)).obj.left ⟶
      ((realizeFunctor n).obj x).obj.left :=
  comparison ψ x

/-- The comparison morphisms compose. -/
theorem comparison'_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (x : EtaleComponent A l) :
    ((realizeFunctor n).map (eqToHom (transition_obj_comp ψ φ x))).hom.left ≫
        comparison' (ψ ≫ φ) x =
      comparison' φ ((transition ψ).obj x) ≫ comparison' ψ x := by
  rcases x with V | ⟨m', φ', V⟩
  · exact (Category.id_comp _).trans (comparison_comp_inl ψ φ V)
  · exact (Category.id_comp _).trans (comparison_comp_inr ψ φ φ' V)

/-- Two morphisms into a base change are equal if they agree after the projection and over `X`. -/
private theorem baseChange_hom_ext {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (V : SpacesEtale B S hS Y) {W : SpacesEtale B S hS X}
    (f₁ f₂ : W ⟶ (spacesBaseChange B S hS g).functor.obj V)
    (h : f₁.hom.left ≫ (spacesBaseChange B S hS g).projection.app V =
      f₂.hom.left ≫ (spacesBaseChange B S hS g).projection.app V) : f₁ = f₂ := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  apply ((spacesBaseChange B S hS g).isPullback V).hom_ext h
  exact (Over.w (_ : _ ⟶ _)).trans (Over.w (_ : _ ⟶ _)).symm

/-- **The transition comparisons compose.** Comparing the realization of a twice transported
formal base change with an iterated base change, in two steps or in one, gives the same
isomorphism, up to the canonical identifications. -/
theorem transitionRealizeIsoApp_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (x : EtaleComponent A l) (e : A.left.map φ.op ≫ A.left.map ψ.op = A.left.map (ψ ≫ φ).op) :
    (realizeFunctor n).map (eqToHom (transition_obj_comp ψ φ x)) ≫
        (transitionRealizeIsoApp (ψ ≫ φ) x).hom =
      (transitionRealizeIsoApp φ ((transition ψ).obj x)).hom ≫
        (spacesBaseChange B S hS (A.left.map φ.op)).functor.map
          (transitionRealizeIsoApp ψ x).hom ≫
        (spacesBaseChange_comp B S hS (A.left.map φ.op) (A.left.map ψ.op)).hom.app
          ((realizeFunctor l).obj x) ≫
        eqToHom (congrArg (fun k => (spacesBaseChange B S hS k).functor.obj
          ((realizeFunctor l).obj x)) e) := by
  refine baseChange_hom_ext _ _ _ _ ?_
  · simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
    have hnat : ((spacesBaseChange B S hS (A.left.map φ.op)).functor.map
          (transitionRealizeIsoApp ψ x).hom).hom.left ≫
          (spacesBaseChange B S hS (A.left.map φ.op)).projection.app
            ((spacesBaseChange B S hS (A.left.map ψ.op)).functor.obj ((realizeFunctor l).obj x)) =
        (spacesBaseChange B S hS (A.left.map φ.op)).projection.app
            ((realizeFunctor m).obj ((transition ψ).obj x)) ≫
          (transitionRealizeIsoApp ψ x).hom.hom.left :=
      (spacesBaseChange B S hS (A.left.map φ.op)).projection.naturality _
    have hψ : (transitionRealizeIsoApp ψ x).hom.hom.left ≫
        (spacesBaseChange B S hS (A.left.map ψ.op)).projection.app ((realizeFunctor l).obj x) =
        comparison' ψ x := transitionRealizeIsoApp_hom_fst ψ x
    have hφ : (transitionRealizeIsoApp φ ((transition ψ).obj x)).hom.hom.left ≫
        (spacesBaseChange B S hS (A.left.map φ.op)).projection.app
          ((realizeFunctor m).obj ((transition ψ).obj x)) =
        comparison' φ ((transition ψ).obj x) := transitionRealizeIsoApp_hom_fst φ _
    have hψφ : (transitionRealizeIsoApp (ψ ≫ φ) x).hom.hom.left ≫
        (spacesBaseChange B S hS (A.left.map (ψ ≫ φ).op)).projection.app
          ((realizeFunctor l).obj x) =
        comparison' (ψ ≫ φ) x := transitionRealizeIsoApp_hom_fst (ψ ≫ φ) x
    rw [eqToHom_comp_projection e, spacesBaseChange_comp_projection, reassoc_of% hnat, hψ,
      reassoc_of% hφ, hψφ, comparison'_comp]

/-! ### The direct-image comparisons on sections -/

/-- On sections at `x`, the inverse of `transPushIso ψ` is restriction along the component at `x`
of `transitionRealizeIsoApp ψ`. -/
theorem transPushIso_inv_app_hom_app {n k : SimplexCategory} (ψ : n ⟶ k)
    (M : Sheaf (SpacesEtale.topology B S hS (A.left.obj (op k))) (Type (u + 1)))
    (x : (↑((situation A).component n))ᵒᵖ) :
    ((transPushIso ψ).inv.app M).hom.app x =
      M.obj.map ((transitionRealizeIsoApp ψ x.unop).hom).op :=
  rfl

/-- The sheaf `E_n⁻¹ M` acts on a morphism of the component of degree `n` as `M` acts on its
realization. -/
theorem compEquiv_inverse_obj_obj_map (n : SimplexCategory)
    (M : Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) (Type (u + 1)))
    {x y : (↑((situation A).component n))ᵒᵖ} (f : x ⟶ y) :
    ((compEquiv (A := A) n).inverse.obj M).obj.map f =
      M.obj.map ((realizeFunctor n).map f.unop).op :=
  rfl

/-- The sheaf `E_n⁻¹ M` acts on the opposite of a morphism `f` of `EtaleComponent A n` as `M` acts
on the realization of `f`. -/
theorem compEquiv_inverse_obj_obj_map' (n : SimplexCategory)
    (M : Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) (Type (u + 1)))
    {x y : EtaleComponent A n} (f : x ⟶ y) :
    ((compEquiv (A := A) n).inverse.obj M).obj.map f.op =
      M.obj.map ((realizeFunctor n).map f).op :=
  rfl

/-- On sections at `x`, the image under `E_n⁻¹` of a morphism of sheaves `f` is the component of
`f` at the realization of `x`. -/
theorem compEquiv_inverse_map_hom_app (n : SimplexCategory)
    {M N : Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) (Type (u + 1))} (f : M ⟶ N)
    (x : (↑((situation A).component n))ᵒᵖ) :
    ((compEquiv (A := A) n).inverse.map f).hom.app x =
      f.hom.app (op ((realizeFunctor n).obj x.unop)) :=
  rfl

/-- On sections at `x`, the direct image along the transition of `ψ` of a morphism of sheaves `f`
is the component of `f` at the transition of `x`. -/
theorem transition_pushforward_map_hom_app {n k : SimplexCategory} (ψ : n ⟶ k)
    {M N : Sheaf ((situation A).componentTopology k) (Type (u + 1))} (f : M ⟶ N)
    (x : (↑((situation A).component n))ᵒᵖ) :
    (((situation A).transitionMorphism ψ).pushforward.map f).hom.app x =
      f.hom.app (op ((transition ψ).obj x.unop)) :=
  rfl

/-- For equal continuous functors `F = G`, the induced morphism of sheaf pushforwards acts on
sections at `x` by the identification of `F.obj x` with `G.obj x`. -/
theorem _root_.CategoryTheory.Functor.sheafPushforwardContinuousNatTrans_eqToHom_app_hom_app
    {C D : Type*} [Category C] [Category D] {𝒜 : Type*} [Category 𝒜]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F G : C ⥤ D} (h : F = G)
    [F.IsContinuous J K] [G.IsContinuous J K] (N : Sheaf K 𝒜) (x : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousNatTrans (eqToHom h) 𝒜 J K).app N).hom.app x =
      N.obj.map (eqToHom (Functor.congr_obj h x.unop)).op := by
  subst h
  simp
  rfl

/-- On sections at `x`, the inverse of the compositor `pushforwardCompSymm ψ φ` of the situation
is the identification of the transition of `x` along `ψ ≫ φ` with the iterated transition. -/
theorem pushforwardCompSymm_inv_app_hom_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (N : Sheaf ((situation A).componentTopology n) (Type (u + 1)))
    (x : (↑((situation A).component l))ᵒᵖ) :
    (((situation A).pushforwardCompSymm ψ φ).inv.app N).hom.app x =
      N.obj.map (eqToHom (transition_obj_comp ψ φ x.unop)).op := by
  have h := (congrArg Cat.Hom.toFunctor ((etaleSimplicialSite A).underlying.map_comp ψ φ)).symm
  have : (((etaleSimplicialSite A).underlying.map ψ ≫
      (etaleSimplicialSite A).underlying.map φ)).toFunctor.IsContinuous
      ((etaleSimplicialSite A).coverage l).toGrothendieck
      ((etaleSimplicialSite A).coverage n).toGrothendieck := by
    rw [h]
    infer_instance
  exact Functor.sheafPushforwardContinuousNatTrans_eqToHom_app_hom_app
    (J := ((etaleSimplicialSite A).coverage l).toGrothendieck)
    (K := ((etaleSimplicialSite A).coverage n).toGrothendieck) h N x

/-- For equal morphisms `f = g`, the induced morphism of spaces-étale direct images acts on
sections at `V` by the identification of the base changes of `V` along `g` and along `f`. -/
theorem spacesEtaleSheafPushforward_eqToHom_app_hom_app {X Y : AlgebraicSpaces B S hS}
    {f g : X ⟶ Y} (e : f = g) (M : spacesEtaleSheafCat B S hS X)
    (V : (SpacesEtale B S hS Y)ᵒᵖ) :
    ((eqToHom (congrArg (fun k => spacesEtaleSheafPushforward B S hS k) e)).app M).hom.app V =
      M.obj.map (eqToHom (congrArg (fun k => (spacesBaseChange B S hS k).functor.obj V.unop)
        e.symm)).op := by
  subst e
  exact (M.obj.map_id _).symm

/-- `transInvIso` as the mate of `transPushIso`. -/
theorem transInvIso_hom_eq {n k : SimplexCategory} (ψ : n ⟶ k) :
    (transInvIso (A := A) ψ).hom =
      (conjugateEquiv ((equivAdj (A := A) n).comp (spacesAdj (A := A) ψ))
        ((transitionAdj (A := A) ψ).comp (equivAdj k))).symm (transPushIso ψ).inv := by
  rw [Equiv.eq_symm_apply, conjugateEquiv_transInvIso_hom]

/-- The inverse of the inverse-image compositor as a mate. -/
theorem canonicalCompositionComparison_inv_eq {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    (SimplicialSiteSituation.canonicalCompositionComparison (situation A) ψ φ).inv =
      (conjugateEquiv (transitionAdj (A := A) (ψ ≫ φ))
        ((transitionAdj ψ).comp (transitionAdj φ))).symm
        ((situation A).pushforwardCompSymm ψ φ).inv := by
  rw [Equiv.eq_symm_apply, conjugateEquiv_canonicalCompositionComparison_inv]

/-- The spaces-étale comparison along equal morphisms as a mate. -/
theorem spacesEtaleInverseImage_eqToHom_eq {X Y : AlgebraicSpaces B S hS}
    {f g : X ⟶ Y} (e : f = g) :
    eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) e) =
      (conjugateEquiv (spacesEtaleAdjunction B S hS g) (spacesEtaleAdjunction B S hS f)).symm
        (eqToHom (congrArg (fun k => spacesEtaleSheafPushforward B S hS k) e.symm)) := by
  rw [Equiv.eq_symm_apply, conjugateEquiv_spacesEtaleInverseImage_eqToHom e]

/-- Morphisms of functors between sheaf categories are equal if they agree on all sections. -/
private theorem sheaf_natTrans_ext {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))} {α β : F ⟶ G}
    (h : ∀ M x, (α.app M).hom.app x = (β.app M).hom.app x) : α = β :=
  NatTrans.ext (funext fun M => ObjectProperty.hom_ext _ (NatTrans.ext (funext (h M))))

/-- **The direct-image comparisons of the transitions compose**, against the compositors of
the situation and of the spaces-étale direct images. -/
theorem transPushIso_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (e : A.left.map φ.op ≫ A.left.map ψ.op = A.left.map (ψ ≫ φ).op) :
    (transPushIso (A := A) (ψ ≫ φ)).inv ≫
        (compEquiv n).inverse.whiskerLeft ((situation A).pushforwardCompSymm ψ φ).inv =
      Functor.whiskerRight (eqToHom (congrArg (fun k => spacesEtaleSheafPushforward B S hS k)
          e.symm)) (compEquiv l).inverse ≫
        Functor.whiskerRight (spacesEtaleSheafPushforwardComp B S hS (A.left.map φ.op)
          (A.left.map ψ.op)).hom (compEquiv l).inverse ≫
        ((spacesEtaleSheafPushforward B S hS (A.left.map φ.op)).associator
          (spacesEtaleSheafPushforward B S hS (A.left.map ψ.op)) (compEquiv l).inverse).hom ≫
        (spacesEtaleSheafPushforward B S hS (A.left.map φ.op)).whiskerLeft (transPushIso ψ).inv ≫
        ((spacesEtaleSheafPushforward B S hS (A.left.map φ.op)).associator (compEquiv m).inverse
          ((situation A).transitionMorphism ψ).pushforward).inv ≫
        Functor.whiskerRight (transPushIso φ).inv ((situation A).transitionMorphism ψ).pushforward ≫
        ((compEquiv n).inverse.associator ((situation A).transitionMorphism φ).pushforward
          ((situation A).transitionMorphism ψ).pushforward).hom := by
  refine sheaf_natTrans_ext fun M x => ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    ObjectProperty.FullSubcategory.comp_hom]
  simp only [transPushIso_inv_app_hom_app, pushforwardCompSymm_inv_app_hom_app,
    compEquiv_inverse_map_hom_app, spacesBaseChange_pushforward_comp_hom_app_hom_app,
    spacesEtaleSheafPushforward_obj_obj_map, transition_pushforward_map_hom_app]
  rw [compEquiv_inverse_obj_obj_map']
  have hq := spacesEtaleSheafPushforward_eqToHom_app_hom_app e.symm M
    (op ((realizeFunctor l).obj (unop x)))
  have key := congrArg (fun f => M.obj.map f.op) (transitionRealizeIsoApp_comp ψ φ x.unop e)
  simp only [op_comp, Functor.map_comp, Category.assoc] at key
  simp only [hq]
  exact key

/-- The transition comparisons `transInvIso` are compatible with composition: along `ψ ≫ φ`,
the comparison precomposed with the inverse of the compositor of the situation equals the
pasting of the comparisons along `ψ` and `φ` with the composition isomorphism of the
spaces-étale inverse images. -/
theorem pasteIso_bridge_natTrans {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (Functor.whiskerRight (SimplicialSiteSituation.canonicalCompositionComparison
        (situation A) ψ φ).inv (compEquiv (A := A) n).functor ≫
        (transInvIso (ψ ≫ φ)).hom :
      (((situation A).transitionMorphism ψ).inverseImage ⋙
        ((situation A).transitionMorphism φ).inverseImage) ⋙ (compEquiv n).functor ⟶ _) =
    (Functor.associator ((situation A).transitionMorphism ψ).inverseImage
        ((situation A).transitionMorphism φ).inverseImage (compEquiv n).functor).hom ≫
      Functor.whiskerLeft ((situation A).transitionMorphism ψ).inverseImage
        (transInvIso φ).hom ≫
      (Functor.associator ((situation A).transitionMorphism ψ).inverseImage
        (compEquiv m).functor (spacesEtaleInverseImage B S hS (A.left.map φ.op))).inv ≫
      Functor.whiskerRight (transInvIso ψ).hom
        (spacesEtaleInverseImage B S hS (A.left.map φ.op)) ≫
      (Functor.associator (compEquiv l).functor
        (spacesEtaleInverseImage B S hS (A.left.map ψ.op))
        (spacesEtaleInverseImage B S hS (A.left.map φ.op))).hom ≫
      Functor.whiskerLeft (compEquiv l).functor
        (spacesEtaleInverseImage_comp B S hS (A.left.map φ.op) (A.left.map ψ.op)).inv ≫
      Functor.whiskerLeft (compEquiv l).functor
        (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k)
        (by rw [op_comp, A.left.map_comp]))) := by
  have e : A.left.map φ.op ≫ A.left.map ψ.op = A.left.map (ψ ≫ φ).op := by
    rw [op_comp, A.left.map_comp]
  rw [transInvIso_hom_eq φ, transInvIso_hom_eq ψ, transInvIso_hom_eq (ψ ≫ φ),
    canonicalCompositionComparison_inv_eq, LocallyDiscrete.lComp_inv,
    spacesEtaleInverseImage_eqToHom_eq e]
  refine mate_paste (transitionAdj ψ) (transitionAdj φ) (transitionAdj (ψ ≫ φ)) (equivAdj l)
    (equivAdj m) (equivAdj n) (spacesAdj ψ) (spacesAdj φ) (spacesAdj (ψ ≫ φ))
    (spacesEtaleAdjunction B S hS (A.left.map φ.op ≫ A.left.map ψ.op)) _ _ _ _ _ _ ?_
  exact transPushIso_comp ψ φ e

end AlgebraicGeometry.Space.EtaleComponent

namespace CategoryTheory.SimplicialSite.ContinuousAugmentation

variable {C : SimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  (a : C.ContinuousAugmentation D K)

/-- In case (A), the transition comparison of the component augmentations acts on sections by
the identifications of the composites of the augmentation with the vertex and transition
functors. -/
theorem transitionPushforwardIso_inv_app_hom_app {m n : SimplexCategory} (φ : m ⟶ n)
    (N : Sheaf (C.coverage n).toGrothendieck (Type u)) (V : Dᵒᵖ) :
    ((SimplicialSiteSituation.Augmentation.transitionPushforwardIso C.situation D K a φ).inv.app
        N).hom.app V =
      N.obj.map ((eqToHom (a.compatibility n (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)
          (SimplexCategory.const (SimplexCategory.mk 0) n 0))).app V.unop).op ≫
        N.obj.map ((eqToHom (congrArg Cat.Hom.toFunctor
          (C.underlying.map_comp (SimplexCategory.const (SimplexCategory.mk 0) m 0) φ)).symm).app
            (a.functor.obj V.unop)).op :=
  rfl

/-- In case (A), the transition comparison of the component augmentations acts on sections by
the identification of two equal objects, provided the two composites of the augmentation with
the vertex and transition functors agree on the object. -/
theorem transitionPushforwardIso_inv_app_hom_app_eq_eqToHom {m n : SimplexCategory}
    (φ : m ⟶ n) (N : Sheaf (C.coverage n).toGrothendieck (Type u)) (V : Dᵒᵖ)
    (h : (C.underlying.map φ).toFunctor.obj ((C.underlying.map
        (SimplexCategory.const (SimplexCategory.mk 0) m 0)).toFunctor.obj (a.functor.obj V.unop)) =
      (C.underlying.map (SimplexCategory.const (SimplexCategory.mk 0) n 0)).toFunctor.obj
        (a.functor.obj V.unop)) :
    ((SimplicialSiteSituation.Augmentation.transitionPushforwardIso C.situation D K a φ).inv.app
        N).hom.app V =
      eqToHom (congrArg (fun X => N.obj.obj (op X)) h.symm) := by
  rw [transitionPushforwardIso_inv_app_hom_app, ← Functor.map_comp, ← op_comp, eqToHom_app,
    eqToHom_app, eqToHom_trans, eqToHom_op, eqToHom_map]

end CategoryTheory.SimplicialSite.ContinuousAugmentation

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-! ### The augmentation comparisons -/

variable (A) in
/-- The morphism of topoi `a_n : Sh(U_{n, étale}) → Sh(X_étale)` of the component of degree `n`
(Stacks 0D70, part (1)). -/
abbrev compAug (n : SimplexCategory) :=
  SimplicialSiteSituation.Augmentation.componentAugmentation (situation A) _ _
    (etaleAugmentation A) n

/-- The augmentation comparison `a_n⁻¹ ⋙ E_n ≅ a_n^*`, read in the situation. -/
def augInvIso (n : SimplexCategory) :
    (compAug A n).inverseImage ⋙ (compEquiv n).functor ≅
      spacesEtaleInverseImage B S hS (A.hom.app (op n)) :=
  componentAugmentationInverseImageIso n

/-- The augmentation comparison of direct images `E_n⁻¹ ⋙ a_{n,*} ≅ a_{n,*}`, read in the
situation. -/
def augPushIso (n : SimplexCategory) :
    (compEquiv n).inverse ⋙ (compAug A n).pushforward ≅
      spacesEtaleSheafPushforward B S hS (A.hom.app (op n)) :=
  componentAugmentationPushforwardIso n

/-- `augInvIso` as the mate of `augPushIso`. -/
theorem augInvIso_hom_eq (n : SimplexCategory) :
    (augInvIso (A := A) n).hom =
      (conjugateEquiv (spacesEtaleAdjunction B S hS (A.hom.app (op n)))
        ((compAug A n).adj.comp (equivAdj n))).symm (augPushIso n).inv := by
  rw [Equiv.eq_symm_apply]
  exact conjugateEquiv_leftAdjointUniq_ofNatIsoRight _ _ (augPushIso (A := A) n).symm

/-- The transition comparison of inverse images of the component augmentations as the mate of
the transition comparison of their direct images. -/
theorem transitionInverseImageIso_aug_hom_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    (SimplicialSiteSituation.Augmentation.transitionInverseImageIso (situation A) _ _
        (etaleAugmentation A) φ).hom =
      (conjugateEquiv (compAug A n).adj ((compAug A m).adj.comp (transitionAdj φ))).symm
        (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation A) _ _
          (etaleAugmentation A) φ).inv :=
  rfl

/-- **The transition comparison on base changes of objects étale over `X`**: comparing the
base change to `U_n` of an object étale over `X` with the iterated base change through `U_m`
is the composition isomorphism of base change. -/
theorem transitionRealizeIsoApp_baseObj {m n : SimplexCategory} (φ : m ⟶ n)
    (V : SpacesEtale B S hS A.right)
    (e : A.left.map φ.op ≫ A.hom.app (op m) = A.hom.app (op n)) :
    (transitionRealizeIsoApp φ (baseObj m V)).hom ≫
        (spacesBaseChange_comp B S hS (A.left.map φ.op) (A.hom.app (op m))).hom.app V ≫
        eqToHom (congrArg (fun k => (spacesBaseChange B S hS k).functor.obj V) e) =
      𝟙 ((realizeFunctor n).obj ((transition φ).obj (baseObj m V))) := by
  refine baseChange_hom_ext _ _ _ _ ?_
  · have h : (transitionRealizeIsoApp φ (baseObj m V)).hom.hom.left ≫
        (spacesBaseChange B S hS (A.left.map φ.op)).projection.app
          ((spacesBaseChange B S hS (A.hom.app (op m))).functor.obj V) ≫
          (spacesBaseChange B S hS (A.hom.app (op m))).projection.app V =
        (spacesBaseChange B S hS (A.hom.app (op n))).projection.app V := by
      have h₁ := transitionRealizeIsoApp_hom_fst φ (baseObj m V) =≫
        (spacesBaseChange B S hS (A.hom.app (op m))).projection.app V
      rw [Category.assoc] at h₁
      exact h₁.trans (comparison_inl_fst φ V)
    simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc,
      ObjectProperty.FullSubcategory.id_hom, Over.id_left]
    rwa [eqToHom_comp_projection e, spacesBaseChange_comp_projection]

/-- On sections at `V`, the inverse of `augPushIso n` is restriction along the component at `V`
of `augmentationRealizeIso n`. -/
theorem augPushIso_inv_app_hom_app (n : SimplexCategory)
    (M : Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) (Type (u + 1)))
    (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    ((augPushIso (A := A) n).inv.app M).hom.app V =
      M.obj.map ((augmentationRealizeIso (A := A) n).hom.app V.unop).op :=
  rfl

/-- On sections at `V`, the direct image along `a_m` of a morphism of sheaves `g` is the component
of `g` at the base change `baseObj m V`. -/
theorem compAug_pushforward_map_hom_app (m : SimplexCategory)
    {N N' : Sheaf ((situation A).componentTopology m) (Type (u + 1))} (g : N ⟶ N')
    (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    ((compAug A m).pushforward.map g).hom.app V = g.hom.app (op (baseObj m V.unop)) :=
  rfl

/-- **The augmentation comparisons on sections, at the level of the sites**: the comparison of
the transition with the augmentation, followed by the composition isomorphism of base change,
is the identity. -/
theorem augmentation_site_identity {m n : SimplexCategory} (φ : m ⟶ n)
    (V : SpacesEtale B S hS A.right)
    (e : A.left.map φ.op ≫ A.hom.app (op m) = A.hom.app (op n)) :
    (transitionRealizeIsoApp φ (baseObj m V)).hom ≫
        (spacesBaseChange B S hS (A.left.map φ.op)).functor.map
          ((augmentationRealizeIso (A := A) m).hom.app V) ≫
        (spacesBaseChange_comp B S hS (A.left.map φ.op) (A.hom.app (op m))).hom.app V ≫
        eqToHom (congrArg (fun k => (spacesBaseChange B S hS k).functor.obj V) e) =
      (augmentationRealizeIso (A := A) n).hom.app V := by
  have h₀ : (spacesBaseChange B S hS (A.left.map φ.op)).functor.map
      ((augmentationRealizeIso (A := A) m).hom.app V) = 𝟙 _ :=
    (spacesBaseChange B S hS (A.left.map φ.op)).functor.map_id _
  exact (congrArg (_ ≫ ·) ((congrArg (· ≫ _) h₀).trans (Category.id_comp _))).trans
    (transitionRealizeIsoApp_baseObj φ V e)

/-- The sections of a presheaf over a composite of four morphisms. -/
theorem map_op_comp₄ {𝒞 : Type*} [Category 𝒞] (M : 𝒞ᵒᵖ ⥤ Type (u + 1)) {X₀ X₁ X₂ X₃ X₄ : 𝒞}
    (t : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (q : X₃ ⟶ X₄) :
    M.map (t ≫ b ≫ c ≫ q).op = M.map q.op ≫ M.map c.op ≫ M.map b.op ≫ M.map t.op := by
  simp only [op_comp, Functor.map_comp, Category.assoc]

/-- **The direct-image augmentation comparisons are compatible with the transition
comparisons**, against the compositor of the spaces-étale direct images. -/
theorem augPushIso_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (e : A.left.map φ.op ≫ A.hom.app (op m) = A.hom.app (op n)) :
    (augPushIso (A := A) n).inv ≫
        (compEquiv n).inverse.whiskerLeft
          (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation A) _ _
            (etaleAugmentation A) φ).inv =
      eqToHom (congrArg (fun k => spacesEtaleSheafPushforward B S hS k) e.symm) ≫
        (spacesEtaleSheafPushforwardComp B S hS (A.left.map φ.op) (A.hom.app (op m))).hom ≫
        (spacesEtaleSheafPushforward B S hS (A.left.map φ.op)).whiskerLeft (augPushIso m).inv ≫
        ((spacesEtaleSheafPushforward B S hS (A.left.map φ.op)).associator (compEquiv m).inverse
          (compAug A m).pushforward).inv ≫
        Functor.whiskerRight (transPushIso φ).inv (compAug A m).pushforward ≫
        ((compEquiv n).inverse.associator ((situation A).transitionMorphism φ).pushforward
          (compAug A m).pushforward).hom := by
  refine sheaf_natTrans_ext fun M V => ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    ObjectProperty.FullSubcategory.comp_hom]
  rw [augPushIso_inv_app_hom_app,
    SimplicialSite.ContinuousAugmentation.transitionPushforwardIso_inv_app_hom_app_eq_eqToHom
      (etaleAugmentation A) φ ((compEquiv n).inverse.obj M) V rfl,
    spacesBaseChange_pushforward_comp_hom_app_hom_app,
    augPushIso_inv_app_hom_app, compAug_pushforward_map_hom_app, transPushIso_inv_app_hom_app]
  simp only [spacesEtaleSheafPushforward_eqToHom_app_hom_app e.symm M V]
  rw [spacesEtaleSheafPushforward_obj_obj_map]
  exact (congrArg (fun f => M.obj.map f.op) (augmentation_site_identity φ V.unop e)).symm.trans
    (map_op_comp₄ M.obj _ _ _ _)

/-- **The augmentation comparisons are compatible with the transition comparisons**: under the
identifications `E`, the comparison `f_φ⁻¹ a_m⁻¹ ≅ a_n⁻¹` of Stacks 0D70 is the spaces-étale
compositor for `a_n = a_m ∘ U(φ)`. -/
theorem augmentation_bridge_natTrans {m n : SimplexCategory} (φ : m ⟶ n)
    (e : A.left.map φ.op ≫ A.hom.app (op m) = A.hom.app (op n)) :
    Functor.whiskerRight (SimplicialSiteSituation.Augmentation.transitionInverseImageIso
        (situation A) _ _ (etaleAugmentation A) φ).hom (compEquiv n).functor ≫
        (augInvIso n).hom =
      (Functor.associator (compAug A m).inverseImage
        ((situation A).transitionMorphism φ).inverseImage (compEquiv n).functor).hom ≫
      Functor.whiskerLeft (compAug A m).inverseImage (transInvIso φ).hom ≫
      (Functor.associator (compAug A m).inverseImage (compEquiv m).functor
        (spacesEtaleInverseImage B S hS (A.left.map φ.op))).inv ≫
      Functor.whiskerRight (augInvIso m).hom (spacesEtaleInverseImage B S hS (A.left.map φ.op)) ≫
      (spacesEtaleInverseImage_comp B S hS (A.left.map φ.op) (A.hom.app (op m))).inv ≫
      eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) e) := by
  simp only [transInvIso_hom_eq φ, transitionInverseImageIso_aug_hom_eq φ, augInvIso_hom_eq n,
    augInvIso_hom_eq m, LocallyDiscrete.lComp_inv, spacesEtaleInverseImage_eqToHom_eq e]
  exact mate_paste' (transitionAdj φ) (equivAdj m) (equivAdj n) (spacesAdj φ)
    (compAug A m).adj (compAug A n).adj _ _ _ _ _ _ _ _ _ (augPushIso_comp φ e)

end AlgebraicGeometry.Space.EtaleComponent
