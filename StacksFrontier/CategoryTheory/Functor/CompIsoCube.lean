module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom

/-!
# Pasting comparisons of a pseudofunctor-like family along a cube

Let `𝒞` be a category, `GA` a family of categories indexed by the objects of `𝒞`, and
`P f : GA B ⥤ GA A` a functor for every morphism `f : A ⟶ B` — an inverse image.  Suppose given,
for every morphism `t` equal to a composite `a ≫ b`, a comparison `D a b t : P t ≅ P b ⋙ P a`,
associative in the evident sense (`CategoryTheory.CompIsoCube.IsAssoc`).

For a commutative square `k = p ≫ i = iU ≫ φ` and an isomorphism `Ψ : P φ R ≅ R_U`, the
comparisons give an isomorphism

`CategoryTheory.CompIsoCube.squareIso : P p (P i R) ≅ P iU R_U`,

and this file proves that these isomorphisms **compose along a cube**: pasting the square of `U`
over `X` with the square of `U'` over `U` gives the square of `U'` over `X`, provided the three
isomorphisms `Ψ` are compatible.

## Main definitions

* `CategoryTheory.CompIsoCube.IsAssoc`: associativity of the comparisons.
* `CategoryTheory.CompIsoCube.squareIso`: the isomorphism attached to a commutative square.

## Main results

* `CategoryTheory.CompIsoCube.assoc_app`: associativity at an object.
* `CategoryTheory.CompIsoCube.squareIso_comp`: the pasting law for the isomorphisms attached to
  squares.
* `CategoryTheory.CompIsoCube.conj_comp`: the pasting law is preserved by conjugation.
* `CategoryTheory.CompIsoCube.inv_comp_map_comp_app_comp` and
  `CategoryTheory.CompIsoCube.map_eqToHom_comp_eqToHom`: two cancellations, for a composite
  through a natural transformation and for transports along equalities of objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.CompIsoCube

universe w w' v u

variable {𝒞 : Type u} [Category.{v} 𝒞] {GA : 𝒞 → Type w} [∀ A, Category.{w'} (GA A)]
  (P : ∀ {A B : 𝒞}, (A ⟶ B) → (GA B ⥤ GA A))
  (D : ∀ {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (t : A ⟶ C), t = a ≫ b → (P t ≅ P b ⋙ P a))

/-- **Associativity of the comparisons.**  For `a : W ⟶ X`, `b : X ⟶ Y`, `c : Y ⟶ Z` and
morphisms `ab`, `bc`, `t` equal to `a ≫ b`, `b ≫ c` and to both `a ≫ bc` and `ab ≫ c`, the two
ways of comparing `P t` with `P c ⋙ P b ⋙ P a` agree. -/
def IsAssoc : Prop :=
  ∀ {W X Y Z : 𝒞} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (ab : W ⟶ Y) (bc : X ⟶ Z) (t : W ⟶ Z)
    (hab : ab = a ≫ b) (hbc : bc = b ≫ c) (h₁ : t = a ≫ bc) (h₂ : t = ab ≫ c),
    isoWhiskerLeft (P c) (D a b ab hab).symm ≪≫ (D ab c t h₂).symm =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (D b c bc hbc).symm (P a) ≪≫
        (D a bc t h₁).symm

variable {P D}

/-- Associativity of the comparisons at an object. -/
theorem assoc_app (hD : IsAssoc P D) {W X Y Z : 𝒞} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (t : W ⟶ Z) (hab : ab = a ≫ b) (hbc : bc = b ≫ c)
    (h₁ : t = a ≫ bc) (h₂ : t = ab ≫ c) (R : GA Z) :
    (D a bc t h₁).hom.app R ≫ (P a).map ((D b c bc hbc).hom.app R) =
      (D ab c t h₂).hom.app R ≫ (D a b ab hab).hom.app ((P c).obj R) := by
  have e := congrArg (fun i => i.inv.app R) (hD a b c ab bc t hab hbc h₁ h₂)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, associator_hom_app,
    Category.comp_id, Functor.comp_obj] at e
  exact e.symm

variable (P D)

/-- **The isomorphism attached to a commutative square.**  For `k = p ≫ i = iU ≫ φ` and
`Ψ : P φ R ≅ R_U`, the composite `P p (P i R) ≅ P k R ≅ P iU (P φ R) ≅ P iU R_U`. -/
def squareIso {Z X U ZU : 𝒞} (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X) (k : ZU ⟶ X)
    (h₁ : k = p ≫ i) (h₂ : k = iU ≫ φ) {R : GA X} {RU : GA U} (Ψ : (P φ).obj R ≅ RU) :
    (P p).obj ((P i).obj R) ≅ (P iU).obj RU :=
  ((D p i k h₁).app R).symm ≪≫ (D iU φ k h₂).app R ≪≫ (P iU).mapIso Ψ

variable {P D}

/-- **The pasting law for the isomorphisms attached to squares.**  Let `k = p ≫ i = iU ≫ φ` be a
square over `X`, let `ψ : U' ⟶ U` and let `kψ = q ≫ iU = iU' ≫ ψ` be a square over `U`, with the
composite square `k' = p' ≫ i = iU' ≫ φ'` where `p' = q ≫ p` and `φ' = ψ ≫ φ`.  If the
isomorphism `Ψ' : P φ' R ≅ R_{U'}` is the comparison `P φ' ≅ P ψ ⋙ P φ` followed by `P ψ Ψ` and
`Ψψ : P ψ R_U ≅ R_{U'}`, then the isomorphism of the composite square is the comparison
`P p' ≅ P q ⋙ P p` followed by `P q` of the isomorphism of the square over `X` and the
isomorphism of the square over `U`. -/
theorem squareIso_comp (hD : IsAssoc P D) {Z X U U' ZU ZU' : 𝒞} (p : ZU ⟶ Z) (iU : ZU ⟶ U)
    (i : Z ⟶ X) (φ : U ⟶ X) (k : ZU ⟶ X) (h₁ : k = p ≫ i) (h₂ : k = iU ≫ φ) (q : ZU' ⟶ ZU)
    (iU' : ZU' ⟶ U') (ψ : U' ⟶ U) (kψ : ZU' ⟶ U) (hψ₁ : kψ = q ≫ iU) (hψ₂ : kψ = iU' ≫ ψ)
    (p' : ZU' ⟶ Z) (hp' : p' = q ≫ p) (φ' : U' ⟶ X) (hφ' : φ' = ψ ≫ φ) (k' : ZU' ⟶ X)
    (h'₁ : k' = p' ≫ i) (h'₂ : k' = iU' ≫ φ') {R : GA X} {RU : GA U} {RU' : GA U'}
    (Ψ : (P φ).obj R ≅ RU) (Ψψ : (P ψ).obj RU ≅ RU') (Ψ' : (P φ').obj R ≅ RU')
    (hΨ : (D ψ φ φ' hφ').hom.app R ≫ (P ψ).map Ψ.hom ≫ Ψψ.hom = Ψ'.hom) :
    squareIso P D p' iU' i φ' k' h'₁ h'₂ Ψ' =
      (D q p p' hp').app ((P i).obj R) ≪≫ (P q).mapIso (squareIso P D p iU i φ k h₁ h₂ Ψ) ≪≫
        squareIso P D q iU' iU ψ kψ hψ₁ hψ₂ Ψψ := by
  have hk₁ : k' = q ≫ k := by rw [h'₁, hp', h₁, Category.assoc]
  have hk₂ : k' = kψ ≫ φ := by rw [hk₁, h₂, hψ₁, Category.assoc]
  have N₁ := (D q iU kψ hψ₁).inv.naturality Ψ.hom
  have N₂ := (D iU' ψ kψ hψ₂).hom.naturality Ψ.hom
  simp only [Functor.comp_map, Functor.comp_obj] at N₁ N₂
  have I₁ : (D q p p' hp').hom.app ((P i).obj R) ≫ (P q).map ((D p i k h₁).inv.app R) =
      (D p' i k' h'₁).inv.app R ≫ (D q k k' hk₁).hom.app R := by
    rw [← cancel_epi ((D p' i k' h'₁).hom.app R), ← Category.assoc,
      ← assoc_app hD q p i p' k k' hp' h₁ hk₁ h'₁ R, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    simp
  have I₂ : (D q k k' hk₁).hom.app R ≫ (P q).map ((D iU φ k h₂).hom.app R) ≫
      (D q iU kψ hψ₁).inv.app ((P φ).obj R) = (D kψ φ k' hk₂).hom.app R := by
    rw [← Category.assoc, assoc_app hD q iU φ kψ k k' hψ₁ h₂ hk₁ hk₂ R, Category.assoc,
      Iso.hom_inv_id_app]
    simp
  have I₃ := (assoc_app hD iU' ψ φ kψ φ' k' hψ₂ hφ' h'₂ hk₂ R).symm
  ext
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% N₁, reassoc_of% N₂, reassoc_of% I₁, reassoc_of% I₂, reassoc_of% I₃, ← hΨ,
    Functor.map_comp, Functor.map_comp]

/-- **The pasting law survives conjugation.**  If three isomorphisms `α`, `α_ψ`, `α'` of the shape
of `CategoryTheory.CompIsoCube.squareIso` satisfy the pasting law, then so do their conjugates by
isomorphisms `κ : C' ≅ C` of the source on `Z` and `κ_U`, `κ_{U'}` of the targets on `Z_U` and
`Z_{U'}`. -/
theorem conj_comp {Z ZU ZU' : 𝒞} {C : GA Z} {C' : GA Z} {CU CU' : GA ZU} {CV CV' : GA ZU'}
    (p : ZU ⟶ Z) (q : ZU' ⟶ ZU) (p' : ZU' ⟶ Z) (hp' : p' = q ≫ p)
    (α : (P p).obj C ≅ CU) (αψ : (P q).obj CU ≅ CV) (α' : (P p').obj C ≅ CV)
    (h : α' = (D q p p' hp').app C ≪≫ (P q).mapIso α ≪≫ αψ)
    (κ : C' ≅ C) (κU : CU ≅ CU') (κV : CV ≅ CV') :
    (P p').mapIso κ ≪≫ α' ≪≫ κV =
      (D q p p' hp').app C' ≪≫ (P q).mapIso ((P p).mapIso κ ≪≫ α ≪≫ κU) ≪≫
        ((P q).mapIso κU.symm ≪≫ αψ ≪≫ κV) := by
  subst h
  ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
    Iso.symm_hom]
  have N := (D q p p' hp').hom.naturality κ.hom
  simp only [Functor.comp_map] at N
  rw [reassoc_of% N, ← Functor.map_comp_assoc (P q) κU.hom κU.inv, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]

/-! ### Two cancellations -/

/-- A cancellation in a composite of an isomorphism, the image of a composite under `F`, a
component of `θ : F ⟶ G` and a further morphism: if `i ≫ L'` factors as `θ ≫ G x ≫ c` and
`G y ≫ e` factors as `c ≫ e'`, then `i⁻¹ ≫ F (x ≫ y) ≫ θ ≫ e = L' ≫ e'`. -/
theorem inv_comp_map_comp_app_comp {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (θ : F ⟶ G) {M₀ M₁ M₂ : C} (x : M₀ ⟶ M₁) (y : M₁ ⟶ M₂) {P Q K : D} (i : F.obj M₀ ≅ P)
    (L' : P ⟶ Q) (c : G.obj M₁ ⟶ Q) (e : G.obj M₂ ⟶ K) (e' : Q ⟶ K)
    (key : i.hom ≫ L' = θ.app M₀ ≫ G.map x ≫ c) (hyc : G.map y ≫ e = c ≫ e') :
    i.inv ≫ F.map (x ≫ y) ≫ θ.app M₂ ≫ e = L' ≫ e' := by
  rw [← cancel_epi i.hom, Iso.hom_inv_id_assoc, ← Category.assoc i.hom, key, Category.assoc,
    Category.assoc, ← hyc, Functor.map_comp, Category.assoc, θ.naturality_assoc,
    θ.naturality_assoc]

/-- The image of a transport along an equality of objects, followed by a transport, is a
transport. -/
theorem map_eqToHom_comp_eqToHom {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A A' : C} {K : D} (h₁ : A = A') (h₂ : G.obj A' = K) (h₃ : G.obj A = K) :
    G.map (eqToHom h₁) ≫ eqToHom h₂ = 𝟙 _ ≫ eqToHom h₃ := by
  subst h₁ h₂
  simp

end CategoryTheory.CompIsoCube

end
