module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Products.Bifunctor
public import Mathlib.CategoryTheory.Yoneda

/-!
# An equivalence carrying one internal hom to another

Let `E : D₁ ≌ D₂` be an equivalence of categories, let `H₁`, `T₁` be an internal hom and a
tensor product on `D₁` carrying a tensor--hom bijection

`(A ⟶ H₁(B, C)) ≃ (T₁(A, B) ⟶ C)`,

and let `H₂`, `T₂` be the same data on `D₂`.  Suppose given an isomorphism of **bifunctors**

`E(T₁(a, b)) ≅ T₂(E a, E b)`,

with no associator or unitor compatibility asked of it.  Then `E` carries `H₁` to `H₂`:

`H₁ ⋙ E ≅ (E.op × E) ⋙ H₂`,

as an isomorphism of bifunctors.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose.SourceNatural`,
  `HomDinatural`, `TargetNatural`: the three naturality clauses of a tensor--hom bijection, at
  the *uncurried* spelling of the internal hom.
* `tensorTransportIso`: the comparison `T₂(Z, E B) ≅ E(T₁(E⁻¹ Z, B))` obtained from the
  bifunctor isomorphism and the counit of the equivalence.
* `lhsTransposeEquiv`: the transported tensor--hom bijection
  `(Z ⟶ E(H₁(B, C))) ≃ (T₂(Z, E B) ⟶ E C)`.
* `homTransportIso`: the component `E(H₁(B, C)) ≅ H₂(E B, E C)`.
* `internalHomTransportIso`: the isomorphism of bifunctors `H₁ ⋙ E ≅ (E.op × E) ⋙ H₂`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose

universe v₁ u₁ v₂ u₂

/-! ### The three naturality clauses -/

section Clauses

variable {D : Type*} [Category D] (H : Dᵒᵖ × D ⥤ D) (T : D × D ⥤ D)
  (e : ∀ A B C : D, (A ⟶ H.obj (op B, C)) ≃ (T.obj (A, B) ⟶ C))

/-- Naturality of a tensor--hom bijection in its source variable: the transpose of a morphism
precomposed with `φ` is the transpose precomposed with `T(φ, 𝟙)`. -/
def SourceNatural : Prop :=
  ∀ (A A' B C : D) (φ : A ⟶ A') (ψ : A' ⟶ H.obj (op B, C)),
    e A B C (φ ≫ ψ) = T.map (φ ×ₘ 𝟙 B) ≫ e A' B C ψ

/-- Dinaturality of a tensor--hom bijection in its internal-hom variable. -/
def HomDinatural : Prop :=
  ∀ (A B B' C : D) (φ : B' ⟶ B) (ψ : A ⟶ H.obj (op B, C)),
    e A B' C (ψ ≫ H.map (φ.op ×ₘ 𝟙 C)) = T.map (𝟙 A ×ₘ φ) ≫ e A B C ψ

/-- Naturality of a tensor--hom bijection in its target variable. -/
def TargetNatural : Prop :=
  ∀ (A B C C' : D) (φ : C ⟶ C') (ψ : A ⟶ H.obj (op B, C)),
    e A B C' (ψ ≫ H.map (𝟙 (op B) ×ₘ φ)) = e A B C ψ ≫ φ

end Clauses

/-! ### The same clauses against a curried internal hom -/

section CurriedClauses

variable {D : Type*} [Category D] (H : Dᵒᵖ ⥤ D ⥤ D) (T : D × D ⥤ D)
  (e : ∀ A B C : D, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C))

/-- `SourceNatural` against a curried internal hom. -/
def CurriedSourceNatural : Prop :=
  ∀ (A A' B C : D) (φ : A ⟶ A') (ψ : A' ⟶ (H.obj (op B)).obj C),
    e A B C (φ ≫ ψ) = T.map (φ ×ₘ 𝟙 B) ≫ e A' B C ψ

/-- `HomDinatural` against a curried internal hom. -/
def CurriedHomDinatural : Prop :=
  ∀ (A B B' C : D) (φ : B' ⟶ B) (ψ : A ⟶ (H.obj (op B)).obj C),
    e A B' C (ψ ≫ (H.map φ.op).app C) = T.map (𝟙 A ×ₘ φ) ≫ e A B C ψ

/-- `TargetNatural` against a curried internal hom. -/
def CurriedTargetNatural : Prop :=
  ∀ (A B C C' : D) (φ : C ⟶ C') (ψ : A ⟶ (H.obj (op B)).obj C),
    e A B C' (ψ ≫ (H.obj (op B)).map φ) = e A B C ψ ≫ φ

/-- The uncurrying of a bifunctor `F` sends `φ ×ₘ 𝟙 B` to `(F.map φ).app B`. -/
theorem uncurryObj_map_mkHom_id {C₁ D₁ E₁ : Type*} [Category C₁] [Category D₁] [Category E₁]
    (F : C₁ ⥤ D₁ ⥤ E₁) {A A' : C₁} (φ : A ⟶ A') (B : D₁) :
    (Functor.uncurry.obj F).map (φ ×ₘ 𝟙 B) = (F.map φ).app B := by
  simp [Functor.uncurry]

/-- The uncurrying of a bifunctor `F` sends `𝟙 A ×ₘ φ` to `(F.obj A).map φ`. -/
theorem uncurryObj_map_id_mkHom {C₁ D₁ E₁ : Type*} [Category C₁] [Category D₁] [Category E₁]
    (F : C₁ ⥤ D₁ ⥤ E₁) (A : C₁) {B B' : D₁} (φ : B ⟶ B') :
    (Functor.uncurry.obj F).map ((𝟙 A) ×ₘ φ) = (F.obj A).map φ := by
  simp [Functor.uncurry]

/-- A tensor--hom bijection natural in its source variable against a curried internal hom is so
against its uncurrying. -/
theorem sourceNatural_of_curried (h : CurriedSourceNatural H T e) :
    SourceNatural (Functor.uncurry.obj H) T e := h

/-- A tensor--hom bijection dinatural in its internal-hom variable against a curried internal hom
is so against its uncurrying. -/
theorem homDinatural_of_curried (h : CurriedHomDinatural H T e) :
    HomDinatural (Functor.uncurry.obj H) T e := by
  intro A B B' C φ ψ
  rw [uncurryObj_map_mkHom_id H φ.op C]
  exact h A B B' C φ ψ

/-- A tensor--hom bijection natural in its target variable against a curried internal hom is so
against its uncurrying. -/
theorem targetNatural_of_curried (h : CurriedTargetNatural H T e) :
    TargetNatural (Functor.uncurry.obj H) T e := by
  intro A B C C' φ ψ
  rw [uncurryObj_map_id_mkHom H (op B) φ]
  exact h A B C C' φ ψ

end CurriedClauses

/-! ### The transported bijection -/

section Transport

variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
  (E : D₁ ≌ D₂) (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (m : T₁ ⋙ E.functor ≅ E.functor.prod E.functor ⋙ T₂)

/-- The isomorphism `T₂(Z, E B) ≅ E(T₁(E⁻¹ Z, B))` given by the counit of the equivalence in the
first variable followed by the inverse of `m` at `(E⁻¹ Z, B)`. -/
def tensorTransportIso (Z : D₂) (B : D₁) :
    T₂.obj (Z, E.functor.obj B) ≅ E.functor.obj (T₁.obj (E.inverse.obj Z, B)) :=
  T₂.mapIso (Iso.prod (E.counitIso.app Z).symm (Iso.refl (E.functor.obj B))) ≪≫
    (m.app (E.inverse.obj Z, B)).symm

/-- The forward map of `tensorTransportIso` is `T₂` applied to the inverse counit paired with the
identity, followed by the inverse of `m`. -/
theorem tensorTransportIso_hom (Z : D₂) (B : D₁) :
    (tensorTransportIso E T₁ T₂ m Z B).hom =
      T₂.map (E.counitIso.inv.app Z ×ₘ 𝟙 (E.functor.obj B)) ≫
        m.inv.app (E.inverse.obj Z, B) := rfl

/-- `tensorTransportIso` is natural in both variables. -/
theorem tensorTransportIso_naturality {Z Z' : D₂} {B B' : D₁} (h : Z ⟶ Z') (φ : B ⟶ B') :
    T₂.map (h ×ₘ E.functor.map φ) ≫ (tensorTransportIso E T₁ T₂ m Z' B').hom =
      (tensorTransportIso E T₁ T₂ m Z B).hom ≫
        E.functor.map (T₁.map (E.inverse.map h ×ₘ φ)) := by
  have hm := m.inv.naturality
    (show ((E.inverse.obj Z, B) : D₁ × D₁) ⟶ (E.inverse.obj Z', B') from
      (E.inverse.map h ×ₘ φ))
  dsimp only [Functor.comp_map, Functor.prod_map] at hm
  rw [tensorTransportIso_hom, tensorTransportIso_hom, ← Category.assoc, ← T₂.map_comp]
  have hstep : (h ×ₘ E.functor.map φ) ≫
        (E.counitIso.inv.app Z' ×ₘ 𝟙 (E.functor.obj B')) =
      (E.counitIso.inv.app Z ×ₘ 𝟙 (E.functor.obj B)) ≫
        (E.functor.map (E.inverse.map h) ×ₘ E.functor.map φ) := by
    refine Prod.ext (E.counitIso.inv.naturality h) (by simp)
  rw [hstep, T₂.map_comp, Category.assoc, hm, Category.assoc]

/-- The tensor--hom bijection `(Z ⟶ E(H₁(B, C))) ≃ (T₂(Z, E B) ⟶ E C)` obtained by transporting
`e₁` along the equivalence `E` and `tensorTransportIso`. -/
def lhsTransposeEquiv (H₁ : D₁ᵒᵖ × D₁ ⥤ D₁)
    (e₁ : ∀ A B C : D₁, (A ⟶ H₁.obj (op B, C)) ≃ (T₁.obj (A, B) ⟶ C))
    (B C : D₁) (Z : D₂) :
    (Z ⟶ E.functor.obj (H₁.obj (op B, C))) ≃ (T₂.obj (Z, E.functor.obj B) ⟶ E.functor.obj C) :=
  (E.symm.toAdjunction.homEquiv Z (H₁.obj (op B, C))).symm.trans
    ((e₁ (E.inverse.obj Z) B C).trans
      (E.fullyFaithfulFunctor.homEquiv.trans
        (tensorTransportIso E T₁ T₂ m Z B).symm.homFromEquiv))

/-- The transported bijection sends `f` to `tensorTransportIso` followed by the image under `E`
of the transpose on `D₁` of the morphism `E⁻¹ Z ⟶ H₁(B, C)` corresponding to `f`. -/
theorem lhsTransposeEquiv_apply (H₁ : D₁ᵒᵖ × D₁ ⥤ D₁)
    (e₁ : ∀ A B C : D₁, (A ⟶ H₁.obj (op B, C)) ≃ (T₁.obj (A, B) ⟶ C))
    (B C : D₁) (Z : D₂) (f : Z ⟶ E.functor.obj (H₁.obj (op B, C))) :
    lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C Z f =
      (tensorTransportIso E T₁ T₂ m Z B).hom ≫
        E.functor.map (e₁ (E.inverse.obj Z) B C
          ((E.symm.toAdjunction.homEquiv Z (H₁.obj (op B, C))).symm f)) := rfl

/-- The inverse of the equivalence's hom-bijection is composition with the inverse unit. -/
theorem symm_homEquiv_apply (Y : D₁) (Z : D₂) (g : Z ⟶ E.functor.obj Y) :
    (E.symm.toAdjunction.homEquiv Z Y).symm g =
      E.inverse.map g ≫ E.unitIso.inv.app Y := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The transported bijection sends `f` to `tensorTransportIso` followed by the image under `E`
of the transpose on `D₁` of `E⁻¹ f` composed with the inverse unit. -/
theorem lhsTransposeEquiv_apply' (H₁ : D₁ᵒᵖ × D₁ ⥤ D₁)
    (e₁ : ∀ A B C : D₁, (A ⟶ H₁.obj (op B, C)) ≃ (T₁.obj (A, B) ⟶ C))
    (B C : D₁) (Z : D₂) (f : Z ⟶ E.functor.obj (H₁.obj (op B, C))) :
    lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C Z f =
      (tensorTransportIso E T₁ T₂ m Z B).hom ≫
        E.functor.map (e₁ (E.inverse.obj Z) B C
          (E.inverse.map f ≫ E.unitIso.inv.app (H₁.obj (op B, C)))) := by
  rw [lhsTransposeEquiv_apply, symm_homEquiv_apply]

/-- `lhsTransposeEquiv` is natural in its source variable. -/
theorem lhsTransposeEquiv_naturality (H₁ : D₁ᵒᵖ × D₁ ⥤ D₁)
    (e₁ : ∀ A B C : D₁, (A ⟶ H₁.obj (op B, C)) ≃ (T₁.obj (A, B) ⟶ C))
    (hn₁ : SourceNatural H₁ T₁ e₁) (B C : D₁) {Z Z' : D₂} (h : Z ⟶ Z')
    (f : Z' ⟶ E.functor.obj (H₁.obj (op B, C))) :
    lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C Z (h ≫ f) =
      T₂.map (h ×ₘ 𝟙 (E.functor.obj B)) ≫
        lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C Z' f := by
  rw [lhsTransposeEquiv_apply', lhsTransposeEquiv_apply', E.inverse.map_comp, Category.assoc,
    hn₁ _ _ _ _ (E.inverse.map h) _, E.functor.map_comp, ← Category.assoc]
  have htt := tensorTransportIso_naturality E T₁ T₂ m h (𝟙 B)
  rw [E.functor.map_id] at htt
  rw [← htt, Category.assoc]

end Transport

/-! ### The comparison of the two internal homs -/

section Comparison

variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
  (E : D₁ ≌ D₂) (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (m : T₁ ⋙ E.functor ≅ E.functor.prod E.functor ⋙ T₂)
  (H₁ : D₁ᵒᵖ × D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ H₁.obj (op B, C)) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ H₂.obj (op B, C)) ≃ (T₂.obj (A, B) ⟶ C))

/-- The morphism `E(H₁(B, C)) ⟶ H₂(E B, E C)` whose transpose under `e₂` is the image of the
identity under `lhsTransposeEquiv`. -/
def homTransportMap (B C : D₁) :
    E.functor.obj (H₁.obj (op B, C)) ⟶
      H₂.obj (op (E.functor.obj B), E.functor.obj C) :=
  (e₂ (E.functor.obj (H₁.obj (op B, C))) (E.functor.obj B) (E.functor.obj C)).symm
    (lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C (E.functor.obj (H₁.obj (op B, C))) (𝟙 _))

/-- Transposing under `e₂` the composite of `f` with `homTransportMap` gives the image of `f`
under `lhsTransposeEquiv`. -/
theorem e₂_comp_homTransportMap (hn₁ : SourceNatural H₁ T₁ e₁) (hn₂ : SourceNatural H₂ T₂ e₂)
    (B C : D₁) (Z : D₂) (f : Z ⟶ E.functor.obj (H₁.obj (op B, C))) :
    e₂ Z (E.functor.obj B) (E.functor.obj C)
        (f ≫ homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C) =
      lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C Z f := by
  rw [homTransportMap, hn₂ _ _ _ _ f _, Equiv.apply_symm_apply,
    ← lhsTransposeEquiv_naturality E T₁ T₂ m H₁ e₁ hn₁ B C f (𝟙 _), Category.comp_id]

/-- The comparison `E(H₁(B, C)) ⟶ H₂(E B, E C)` is an isomorphism. -/
theorem isIso_homTransportMap (hn₁ : SourceNatural H₁ T₁ e₁) (hn₂ : SourceNatural H₂ T₂ e₂)
    (B C : D₁) : IsIso (homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C) := by
  refine isIso_of_yoneda_map_bijective _ fun Z ↦ ?_
  have key : (fun f : Z ⟶ E.functor.obj (H₁.obj (op B, C)) ↦
      f ≫ homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C) =
      fun f ↦ (e₂ Z (E.functor.obj B) (E.functor.obj C)).symm
        (lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C Z f) := by
    funext f
    rw [← e₂_comp_homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ hn₁ hn₂ B C Z f,
      Equiv.symm_apply_apply]
  rw [key]
  exact ((lhsTransposeEquiv E T₁ T₂ m H₁ e₁ B C Z).trans
    (e₂ Z (E.functor.obj B) (E.functor.obj C)).symm).bijective

/-- The isomorphism `E(H₁(B, C)) ≅ H₂(E B, E C)` with forward map `homTransportMap`. -/
def homTransportIso (hn₁ : SourceNatural H₁ T₁ e₁) (hn₂ : SourceNatural H₂ T₂ e₂) (B C : D₁) :
    E.functor.obj (H₁.obj (op B, C)) ≅
      H₂.obj (op (E.functor.obj B), E.functor.obj C) :=
  haveI := isIso_homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ hn₁ hn₂ B C
  asIso (homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C)

/-- The forward map of `homTransportIso` is `homTransportMap`. -/
theorem homTransportIso_hom (hn₁ : SourceNatural H₁ T₁ e₁) (hn₂ : SourceNatural H₂ T₂ e₂)
    (B C : D₁) :
    (homTransportIso E T₁ T₂ m H₁ H₂ e₁ e₂ hn₁ hn₂ B C).hom =
      homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C := rfl

/-- `homTransportMap` is natural in both variables. -/
theorem homTransportMap_naturality (hn₁ : SourceNatural H₁ T₁ e₁) (hn₂ : SourceNatural H₂ T₂ e₂)
    (hd₁ : HomDinatural H₁ T₁ e₁) (hd₂ : HomDinatural H₂ T₂ e₂)
    (ht₁ : TargetNatural H₁ T₁ e₁) (ht₂ : TargetNatural H₂ T₂ e₂)
    {B B' C C' : D₁} (φ : B' ⟶ B) (ψ : C ⟶ C') :
    E.functor.map (H₁.map (((φ.op : op B ⟶ op B')) ×ₘ ψ)) ≫
        homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B' C' =
      homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C ≫
        H₂.map (((E.functor.map φ).op : op (E.functor.obj B) ⟶ op (E.functor.obj B')) ×ₘ
          E.functor.map ψ) := by
  set W := E.functor.obj (H₁.obj (op B, C))
  set A := E.inverse.obj W
  set v := E.unitIso.inv.app (H₁.obj (op B, C))
  have hsplit₁ : (((φ.op : op B ⟶ op B')) ×ₘ ψ) =
      (((φ.op : op B ⟶ op B')) ×ₘ 𝟙 C) ≫ ((𝟙 (op B')) ×ₘ ψ) := by
    exact Prod.fac' _
  have hsplit₂ :
      (((E.functor.map φ).op : op (E.functor.obj B) ⟶ op (E.functor.obj B')) ×ₘ
          E.functor.map ψ) =
        (((E.functor.map φ).op : op (E.functor.obj B) ⟶ op (E.functor.obj B')) ×ₘ
            𝟙 (E.functor.obj C)) ≫
          ((𝟙 (op (E.functor.obj B'))) ×ₘ E.functor.map ψ) := by
    exact Prod.fac' _
  have hunit : E.inverse.map (E.functor.map (H₁.map (((φ.op : op B ⟶ op B')) ×ₘ ψ))) ≫
      E.unitIso.inv.app (H₁.obj (op B', C')) =
        v ≫ H₁.map (((φ.op : op B ⟶ op B')) ×ₘ ψ) := by
    have h := E.unitIso.inv.naturality (H₁.map (((φ.op : op B ⟶ op B')) ×ₘ ψ))
    dsimp only [Functor.comp_map, Functor.id_map] at h
    exact h
  have htt : T₂.map ((𝟙 W) ×ₘ E.functor.map φ) ≫
        (tensorTransportIso E T₁ T₂ m W B).hom =
      (tensorTransportIso E T₁ T₂ m W B').hom ≫
        E.functor.map (T₁.map ((𝟙 A) ×ₘ φ)) := by
    have h := tensorTransportIso_naturality E T₁ T₂ m (𝟙 W) φ
    rw [E.inverse.map_id] at h
    exact h
  apply (e₂ W (E.functor.obj B') (E.functor.obj C')).injective
  rw [e₂_comp_homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ hn₁ hn₂ B' C' W
      (E.functor.map (H₁.map (((φ.op : op B ⟶ op B')) ×ₘ ψ))),
    lhsTransposeEquiv_apply', hunit, hsplit₁, H₁.map_comp, ← Category.assoc,
    ht₁ A B' C C' ψ (v ≫ H₁.map (((φ.op : op B ⟶ op B')) ×ₘ 𝟙 C)),
    hd₁ A B B' C φ v]
  rw [hsplit₂, H₂.map_comp, ← Category.assoc,
    ht₂ W (E.functor.obj B') (E.functor.obj C) (E.functor.obj C') (E.functor.map ψ)
      (homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C ≫
        H₂.map (((E.functor.map φ).op : op (E.functor.obj B) ⟶ op (E.functor.obj B')) ×ₘ
          𝟙 (E.functor.obj C))),
    hd₂ W (E.functor.obj B) (E.functor.obj B') (E.functor.obj C) (E.functor.map φ)
      (homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C),
    ← Category.id_comp (homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ B C),
    e₂_comp_homTransportMap E T₁ T₂ m H₁ H₂ e₁ e₂ hn₁ hn₂ B C W (𝟙 W),
    lhsTransposeEquiv_apply', E.inverse.map_id, Category.id_comp]
  simp only [E.functor.map_comp, Category.assoc]
  rw [← reassoc_of% htt]

/-- The isomorphism of bifunctors `H₁ ⋙ E ≅ (E.op × E) ⋙ H₂`: the equivalence carries the
internal hom of `D₁` to the internal hom of `D₂`. -/
def internalHomTransportIso (hn₁ : SourceNatural H₁ T₁ e₁) (hn₂ : SourceNatural H₂ T₂ e₂)
    (hd₁ : HomDinatural H₁ T₁ e₁) (hd₂ : HomDinatural H₂ T₂ e₂)
    (ht₁ : TargetNatural H₁ T₁ e₁) (ht₂ : TargetNatural H₂ T₂ e₂) :
    H₁ ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ H₂ :=
  NatIso.ofComponents
    (fun P ↦ homTransportIso E T₁ T₂ m H₁ H₂ e₁ e₂ hn₁ hn₂ P.1.unop P.2)
    (fun {_ _} g ↦
      homTransportMap_naturality E T₁ T₂ m H₁ H₂ e₁ e₂ hn₁ hn₂ hd₁ hd₂ ht₁ ht₂
        g.1.unop g.2)

end Comparison

/-! ### The comparison with the source internal hom given curried -/

section CurriedComparison

variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
  (E : D₁ ≌ D₂) (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (m : T₁ ⋙ E.functor ≅ E.functor.prod E.functor ⋙ T₂)
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ H₂.obj (op B, C)) ≃ (T₂.obj (A, B) ⟶ C))

/-- The isomorphism of bifunctors `H₁ ⋙ E ≅ (E.op × E) ⋙ H₂` of `internalHomTransportIso`, with
the internal hom `H₁` of `D₁` given in curried form and the internal hom `H₂` of `D₂` given
uncurried. -/
def internalHomTransportIsoCurried
    (hn₁ : CurriedSourceNatural H₁ T₁ e₁) (hn₂ : SourceNatural H₂ T₂ e₂)
    (hd₁ : CurriedHomDinatural H₁ T₁ e₁) (hd₂ : HomDinatural H₂ T₂ e₂)
    (ht₁ : CurriedTargetNatural H₁ T₁ e₁) (ht₂ : TargetNatural H₂ T₂ e₂) :
    Functor.uncurry.obj H₁ ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ H₂ :=
  internalHomTransportIso E T₁ T₂ m (Functor.uncurry.obj H₁) H₂ e₁ e₂
    (sourceNatural_of_curried H₁ T₁ e₁ hn₁) hn₂
    (homDinatural_of_curried H₁ T₁ e₁ hd₁) hd₂
    (targetNatural_of_curried H₁ T₁ e₁ ht₁) ht₂

end CurriedComparison

end Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose

end
