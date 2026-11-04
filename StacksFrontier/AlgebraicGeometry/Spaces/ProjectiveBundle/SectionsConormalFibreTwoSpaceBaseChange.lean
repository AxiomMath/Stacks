module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceCompObj

/-!
# Coherences of Stacks 03LU for the comparison of fibres of `𝐏(ℰ)` and `𝐏(g^*ℰ)`

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points
and `h : T' ⟶ T` with `v ≫ g = u ∘ h`.  The comparison of the fibres of `𝐏(g^*ℰ)` over `v` and
of `𝐏(ℰ)` over `u` with the base-change morphism of projective bundles of Tag 01O3 along
`AlgebraicGeometry.Space.pointZariskiModuleTwoSpaceIso` rests on a cocycle of the comparisons of
inverse images of Stacks 03LU along `f' : Z ⟶ T'`, `v`, `g` and along `f'`, `h`, `u`.  This file
proves the two halves of that cocycle for arbitrary morphisms of algebraic spaces, with every
change of spelling of a composite carried by an explicit identification, so that they can be
instantiated without comparing two spellings of a morphism.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_twoSpace_comp`: the two-space half.
* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_map_eqToHom_comp`: the one-space half.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- Two identifications followed by the same morphism agree. -/
theorem CategoryTheory.eqToHom_comp_congr {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞} (p q : A = B)
    (f : B ⟶ C) : eqToHom p ≫ f = eqToHom q ≫ f :=
  rfl

/-- Two composable identifications followed by a morphism are one identification. -/
theorem CategoryTheory.eqToHom_comp_eqToHom_comp_congr {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}
    (p : A = B) (p' : B = C) (q : A = C) (f : C ⟶ D) :
    eqToHom p ≫ eqToHom p' ≫ f = eqToHom q ≫ f := by
  rw [eqToHom_trans_assoc]

/-- Three composable identifications followed by a morphism are one identification. -/
theorem CategoryTheory.eqToHom_comp_eqToHom_comp_eqToHom_comp_congr {𝒞 : Type*} [Category 𝒞]
    {A B C D F : 𝒞} (p : A = B) (p' : B = C) (p'' : C = D) (q : A = D) (f : D ⟶ F) :
    eqToHom p ≫ eqToHom p' ≫ eqToHom p'' ≫ f = eqToHom q ≫ f := by
  rw [eqToHom_trans_assoc, eqToHom_trans_assoc]

/-- Four composable identifications followed by a morphism are one identification. -/
theorem CategoryTheory.eqToHom_comp_eqToHom_comp_eqToHom_comp_eqToHom_comp_congr {𝒞 : Type*}
    [Category 𝒞] {A B C D F G : 𝒞} (p : A = B) (p' : B = C) (p'' : C = D) (p''' : D = F)
    (q : A = F) (f : F ⟶ G) :
    eqToHom p ≫ eqToHom p' ≫ eqToHom p'' ≫ eqToHom p''' ≫ f = eqToHom q ≫ f := by
  rw [eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_trans_assoc]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section TwoSpaceCocycle

/-- The comparison `a^* d^* ≅ (a ≫ d)^*` followed by the identification along `d = d'`. -/
theorem modulePullbackCompIso_inv_app_map_eqToHom_app {W Y X₀ : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) {d d' : Y ⟶ X₀} (hd : d = d') (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompIso B S hS a d).inv.app M ≫
        (modulePullback B S hS a).map ((eqToHom (congrArg (modulePullback B S hS) hd)).app M) =
      eqToHom (show (modulePullback B S hS (a ≫ d)).obj M = (modulePullback B S hS (a ≫ d')).obj M
        by rw [hd]) ≫ (modulePullbackCompIso B S hS a d').inv.app M := by
  subst hd
  simp

/-- The comparisons `a^*(b ≫ c)^* ≅ (a ≫ b ≫ c)^*` and `a^* b^* c^* ≅ ((a ≫ b) ≫ c)^*` of
Stacks 03LU. -/
theorem modulePullbackCompIso_inv_app_map_inv_app_hom_app {W Y Y₂ X₀ : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) (b : Y ⟶ Y₂) (c : Y₂ ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompIso B S hS a (b ≫ c)).inv.app M ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).inv.app M) ≫
        (modulePullbackCompIso B S hS a b).hom.app ((modulePullback B S hS c).obj M) =
      eqToHom (show (modulePullback B S hS (a ≫ (b ≫ c))).obj M =
          (modulePullback B S hS ((a ≫ b) ≫ c)).obj M by rw [Category.assoc]) ≫
        (modulePullbackCompIso B S hS (a ≫ b) c).inv.app M := by
  rw [← reassoc_of% (modulePullbackCompIso_assoc_inv_app B S hS a b c M), Iso.inv_hom_id_app,
    Category.comp_id]
  simp

/-- The comparison `a^* d^* ≅ (a ≫ d)^*` followed by an identification of inverse images along
equal morphisms `d = d'`, at a module. -/
theorem modulePullbackCompIso_inv_app_map_eqToHom {W Y X₀ : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) {d d' : Y ⟶ X₀} (hd : d = d') (M : Modules.{u, u} B S hS X₀.1 X₀.2)
    (p : (modulePullback B S hS d).obj M = (modulePullback B S hS d').obj M) :
    (modulePullbackCompIso B S hS a d).inv.app M ≫ (modulePullback B S hS a).map (eqToHom p) =
      eqToHom (show (modulePullback B S hS (a ≫ d)).obj M = (modulePullback B S hS (a ≫ d')).obj M
        by rw [hd]) ≫ (modulePullbackCompIso B S hS a d').inv.app M := by
  subst hd
  simp

/-- **The one-space coherence of Stacks 03LU behind `pointTwoSpaceCompIso_hom_comp`**, for
morphisms of algebraic spaces, with every change of spelling carried by an identification: the
comparison along `a` and `d`, the identification `d^* = (b' ≫ c')^*` and the comparisons along
`b'`, `c'` and along `a`, `b'` give the comparison along `a ≫ b'` and `c'`. -/
theorem modulePullbackCompIso_inv_app_map_eqToHom_comp {W Y Y₂ X₀ : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) (b' : Y ⟶ Y₂) (c' : Y₂ ⟶ X₀) {d : Y ⟶ X₀} (hd : d = b' ≫ c') {z : W ⟶ X₀}
    (M : Modules.{u, u} B S hS X₀.1 X₀.2)
    (p₂ : (modulePullback B S hS d).obj M = (modulePullback B S hS (b' ≫ c')).obj M)
    (p₅ : (modulePullback B S hS z).obj M = (modulePullback B S hS (a ≫ d)).obj M)
    (p₆ : (modulePullback B S hS z).obj M = (modulePullback B S hS ((a ≫ b') ≫ c')).obj M) :
    eqToHom p₅ ≫ (modulePullbackCompIso B S hS a d).inv.app M ≫
        (modulePullback B S hS a).map (eqToHom p₂) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b' c').inv.app M) ≫
        (modulePullbackCompIso B S hS a b').hom.app ((modulePullback B S hS c').obj M) =
      eqToHom p₆ ≫ (modulePullbackCompIso B S hS (a ≫ b') c').inv.app M := by
  rw [reassoc_of% (modulePullbackCompIso_inv_app_map_eqToHom a hd M p₂),
    modulePullbackCompIso_inv_app_map_inv_app_hom_app a b' c' M]
  exact CategoryTheory.eqToHom_comp_eqToHom_comp_eqToHom_comp_congr _ _ _ _ _

/-- **The two-space coherence of Stacks 03LU behind `pointTwoSpaceCompIso_hom_comp`**, for
morphisms of algebraic spaces, with every change of spelling carried by an identification: a
morphism `φ` given as an identification followed by the comparison along `x = a ≫ b` and `c`,
then the comparisons along `a`, `b` and along `b`, `c` and the identification along
`b ≫ c = d`, is the comparison along `a` and `d`. -/
theorem modulePullbackCompIso_inv_app_twoSpace_comp {W Y X₁ X₀ : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) (b : Y ⟶ X₁) (c : X₁ ⟶ X₀) {d : Y ⟶ X₀} (hd : b ≫ c = d) {x : W ⟶ X₁}
    (hx : x = a ≫ b) {z : W ⟶ X₀} (M : Modules.{u, u} B S hS X₀.1 X₀.2)
    (P : (modulePullback B S hS z).obj M = (modulePullback B S hS (x ≫ c)).obj M)
    (ψ : (modulePullback B S hS (x ≫ c)).obj M ⟶
      (modulePullback B S hS x).obj ((modulePullback B S hS c).obj M))
    (hψ : ψ = (modulePullbackCompIso B S hS x c).inv.app M)
    (φ : (modulePullback B S hS z).obj M ⟶
      (modulePullback B S hS x).obj ((modulePullback B S hS c).obj M))
    (hφ : φ = (eqToIso P).hom ≫ ψ)
    (p₁ : (modulePullback B S hS x).obj ((modulePullback B S hS c).obj M) =
      (modulePullback B S hS (a ≫ b)).obj ((modulePullback B S hS c).obj M))
    (p₅ : (modulePullback B S hS z).obj M = (modulePullback B S hS (a ≫ d)).obj M) :
    φ ≫ eqToHom p₁ ≫ (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M) ≫
        (modulePullback B S hS a).map ((eqToHom (congrArg (modulePullback B S hS) hd)).app M) =
      eqToHom p₅ ≫ (modulePullbackCompIso B S hS a d).inv.app M := by
  rw [hφ, hψ, modulePullbackCompIso_inv_app_of_eq hx c M, eqToIso.hom]
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc _ p₁, eqToHom_refl, Category.id_comp,
    reassoc_of% (modulePullbackCompIso_inv_app_inv_app_map_hom_app_eqToHom a b c M),
    modulePullbackCompIso_inv_app_map_eqToHom_app a hd M]
  exact CategoryTheory.eqToHom_comp_eqToHom_comp_eqToHom_comp_eqToHom_comp_congr _ _ _ _ _ _

/-- `modulePullbackCompIso_inv_app_twoSpace_comp` with the first factor the identification
`z^* = (x ≫ c)^*` followed by the comparison `(x ≫ c)^* M ≅ x^* c^* M`. -/
theorem modulePullbackCompObjIso_twoSpace_comp {W Y X₁ X₀ : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) (b : Y ⟶ X₁) (c : X₁ ⟶ X₀) {d : Y ⟶ X₀} (hd : b ≫ c = d) {x : W ⟶ X₁}
    (hx : x = a ≫ b) {z : W ⟶ X₀} (M : Modules.{u, u} B S hS X₀.1 X₀.2)
    (P : (modulePullback B S hS z).obj M = (modulePullback B S hS (x ≫ c)).obj M)
    (p₁ : (modulePullback B S hS x).obj ((modulePullback B S hS c).obj M) =
      (modulePullback B S hS (a ≫ b)).obj ((modulePullback B S hS c).obj M))
    (p₅ : (modulePullback B S hS z).obj M = (modulePullback B S hS (a ≫ d)).obj M) :
    (eqToIso P ≪≫ modulePullbackCompObjIso x c M).hom ≫ eqToHom p₁ ≫
        (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M) ≫
        (modulePullback B S hS a).map ((eqToHom (congrArg (modulePullback B S hS) hd)).app M) =
      eqToHom p₅ ≫ (modulePullbackCompIso B S hS a d).inv.app M :=
  modulePullbackCompIso_inv_app_twoSpace_comp a b c hd hx M P _
    (modulePullbackCompObjIso_hom x c M) _ (Iso.trans_hom _ _) p₁ p₅

end TwoSpaceCocycle

end AlgebraicGeometry.Space

end
