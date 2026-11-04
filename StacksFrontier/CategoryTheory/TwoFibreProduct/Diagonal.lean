module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The 2-fibre product along a diagonal (Stacks 02XE)

Let `S`, `C₁`, `C₂` be categories and `G₁ : C₁ ⥤ S`, `G₂ : C₂ ⥤ S` functors. Alongside the
2-fibre product `C₁ ×_S C₂` of Example 003R — Mathlib's
`CategoryTheory.Limits.CategoricalPullback G₁ G₂` — one may form the 2-fibre product of the
cospan `G₁ × G₂ : C₁ × C₂ ⥤ S × S` and the diagonal `Δ : S ⥤ S × S`. This file constructs the
canonical equivalence
`CategoricalPullback (G₁.prod G₂) (Functor.diag S) ≌ CategoricalPullback G₁ G₂`.

The comparison functor sends an object `((X₁, X₂), Y, φ)`, where
`φ : (G₁ X₁, G₂ X₂) ≅ (Y, Y)` has components `φ = (φ₁, φ₂)`, to `(X₁, X₂, φ₁ ≪≫ φ₂⁻¹)`, and acts
as the identity on the underlying pair of component morphisms; the quasi-inverse sends
`(X₁, X₂, ψ)` to `((X₁, X₂), G₂ X₂, (ψ, 𝟙))`.

A strict isomorphism of categories does *not* hold: the round trip through the quasi-inverse
replaces the middle `S`-component `Y` by `G₂ X₂`, and the two are related only by the
isomorphism `φ₂`. So the unit of the equivalence is the isomorphism with `C₁ × C₂`-component the
identity and `S`-component `φ₂`, while the counit is an identity. Since taking the middle
category to be the explicit model of Example 003R is exactly what the source proof does ("we may
assume that `C₃` is the category ..."), stating the result for that model is faithful.
-/

@[expose] public section


universe v_S v₁ v₂ u_S u₁ u₂

namespace CategoryTheory.Limits.CategoricalPullback

variable {S : Type u_S} [Category.{v_S} S]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]

/-- The componentwise commutativity condition needed for `prodDiagFunctor` to be well defined on
morphisms: the comparison isomorphism `φ₁ ≪≫ φ₂⁻¹` is natural. -/
private lemma prodDiagAux {a b c a' b' c' : S}
    (φx₁ : a ≅ b) (φx₂ : c ≅ b) (φy₁ : a' ≅ b') (φy₂ : c' ≅ b')
    (G1 : a ⟶ a') (G2 : c ⟶ c') (fs : b ⟶ b')
    (hw1 : G1 ≫ φy₁.hom = φx₁.hom ≫ fs)
    (hw2 : G2 ≫ φy₂.hom = φx₂.hom ≫ fs) :
    G1 ≫ φy₁.hom ≫ φy₂.inv = (φx₁.hom ≫ φx₂.inv) ≫ G2 := by
  have key : fs ≫ φy₂.inv = φx₂.inv ≫ G2 := by
    rw [Iso.comp_inv_eq, Category.assoc, hw2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc G1, hw1, Category.assoc, key, Category.assoc]

/-- **Stacks 02XE.** The canonical comparison functor
`CategoricalPullback (G₁.prod G₂) (Functor.diag S) ⥤ CategoricalPullback G₁ G₂`. On objects it
sends `((X₁, X₂), Y, φ)` to `(X₁, X₂, φ₁ ≪≫ φ₂⁻¹)`, where `φ = (φ₁, φ₂)`; on morphisms it acts as
the identity on the underlying pair of component morphisms. -/
@[stacks 02XE]
def prodDiagFunctor (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S) :
    CategoricalPullback (G₁.prod G₂) (Functor.diag S) ⥤ CategoricalPullback G₁ G₂ where
  obj x := ⟨x.fst.1, x.fst.2,
    ((CategoryTheory.Prod.fst S S).mapIso x.iso) ≪≫
      ((CategoryTheory.Prod.snd S S).mapIso x.iso).symm⟩
  map {x y} f := ⟨f.fst.1, f.fst.2, by
    have hw := f.w
    have hw1 : G₁.map f.fst.1 ≫ y.iso.hom.1 = x.iso.hom.1 ≫ f.snd := by
      have := congrArg (·.1) hw
      simpa only [prod_comp_fst, prod_comp_snd, Functor.diag_map, Functor.prod] using this
    have hw2 : G₂.map f.fst.2 ≫ y.iso.hom.2 = x.iso.hom.2 ≫ f.snd := by
      have := congrArg (·.2) hw
      simpa only [prod_comp_fst, prod_comp_snd, Functor.diag_map, Functor.prod] using this
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      CategoryTheory.Prod.fst_map, CategoryTheory.Prod.snd_map] using
      prodDiagAux ((CategoryTheory.Prod.fst S S).mapIso x.iso)
        ((CategoryTheory.Prod.snd S S).mapIso x.iso)
        ((CategoryTheory.Prod.fst S S).mapIso y.iso)
        ((CategoryTheory.Prod.snd S S).mapIso y.iso)
        (G₁.map f.fst.1) (G₂.map f.fst.2) f.snd hw1 hw2⟩
  map_id x := by apply CategoricalPullback.Hom.ext <;> simp
  map_comp f g := by apply CategoricalPullback.Hom.ext <;> simp

/-- The quasi-inverse to `prodDiagFunctor`: on objects it sends `(X₁, X₂, ψ)` to
`((X₁, X₂), G₂ X₂, (ψ, 𝟙))`, and a morphism `(f₁, f₂)` to `((f₁, f₂), G₂ f₂)`. -/
def prodDiagInverse (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S) :
    CategoricalPullback G₁ G₂ ⥤ CategoricalPullback (G₁.prod G₂) (Functor.diag S) where
  obj z := ⟨(z.fst, z.snd), G₂.obj z.snd, z.iso.prod (Iso.refl (G₂.obj z.snd))⟩
  map {x y} f := ⟨((f.fst, f.snd) : (x.fst, x.snd) ⟶ (y.fst, y.snd)), G₂.map f.snd, by
    have hw := f.w
    apply Prod.ext
    · simpa only [prod_comp_fst, Functor.diag_map, Functor.prod, Iso.prod_hom, prod_Hom] using hw
    · simp [Functor.prod, Functor.diag, Iso.prod_hom]⟩
  map_id z := by apply CategoricalPullback.Hom.ext <;> simp
  map_comp f g := by apply CategoricalPullback.Hom.ext <;> simp

/-- The unit of the equivalence, `𝟭 ≅ prodDiagFunctor ⋙ prodDiagInverse`. At an object
`x = ((X₁, X₂), Y, φ)` it is the identity on the `C₁ × C₂`-component and `φ₂ : G₂ X₂ ≅ Y` on the
middle `S`-component. -/
def prodDiagUnitIso (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S) :
    𝟭 (CategoricalPullback (G₁.prod G₂) (Functor.diag S)) ≅
      prodDiagFunctor G₁ G₂ ⋙ prodDiagInverse G₁ G₂ :=
  NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (Iso.refl _)
      (((CategoryTheory.Prod.snd S S).mapIso x.iso).symm)
      (by
        have h2 : x.iso.hom.2 ≫ x.iso.inv.2 = 𝟙 (G₂.obj x.fst.2) := by
          have := congrArg (·.2) x.iso.hom_inv_id
          simp only [prod_comp_snd, prod_id_snd] at this
          exact this
        apply Prod.ext
        · simp [prodDiagFunctor, prodDiagInverse, Functor.prod, Functor.diag, Iso.prod_hom]
        · simp [prodDiagFunctor, prodDiagInverse, Functor.prod, Functor.diag, Iso.prod_hom, h2]))
    (by
      intro x y f
      apply CategoricalPullback.Hom.ext
      · simp [prodDiagFunctor, prodDiagInverse]
      · have hw := f.w
        have hw2 : G₂.map f.fst.2 ≫ y.iso.hom.2 = x.iso.hom.2 ≫ f.snd := by
          have := congrArg (·.2) hw
          simpa only [prod_comp_fst, prod_comp_snd, Functor.diag_map, Functor.prod] using this
        have hyinv : y.iso.hom.2 ≫ y.iso.inv.2 = 𝟙 (G₂.obj y.fst.2) := by
          have := congrArg (·.2) y.iso.hom_inv_id
          simp only [prod_comp_snd, prod_id_snd] at this
          exact this
        have hxinv : x.iso.inv.2 ≫ x.iso.hom.2 = 𝟙 x.snd := by
          have := congrArg (·.2) x.iso.inv_hom_id
          simp only [prod_comp_snd, prod_id_snd] at this
          exact this
        simp only [prodDiagFunctor, prodDiagInverse, Functor.comp_obj, Functor.comp_map,
          Functor.id_map, CategoricalPullback.comp_snd, CategoricalPullback.mkIso,
          Iso.symm_hom, Functor.mapIso_inv, CategoryTheory.Prod.snd_map]
        calc f.snd ≫ y.iso.inv.2
            = (x.iso.inv.2 ≫ x.iso.hom.2) ≫ f.snd ≫ y.iso.inv.2 := by
                rw [hxinv]; simp
          _ = x.iso.inv.2 ≫ (x.iso.hom.2 ≫ f.snd) ≫ y.iso.inv.2 := by
                simp
          _ = x.iso.inv.2 ≫ (G₂.map f.fst.2 ≫ y.iso.hom.2) ≫ y.iso.inv.2 := by rw [hw2]
          _ = x.iso.inv.2 ≫ G₂.map f.fst.2 := by
                simp [hyinv])

/-- The counit of the equivalence, `prodDiagInverse ⋙ prodDiagFunctor ≅ 𝟭`. This round trip is
the identity on objects on the nose, so the counit is the identity transformation. -/
def prodDiagCounitIso (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S) :
    prodDiagInverse G₁ G₂ ⋙ prodDiagFunctor G₁ G₂ ≅
      𝟭 (CategoricalPullback G₁ G₂) :=
  NatIso.ofComponents
    (fun _ => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
      (by simp [prodDiagFunctor, prodDiagInverse]))
    (by intro x y f; apply CategoricalPullback.Hom.ext <;>
      simp [prodDiagFunctor, prodDiagInverse])

/-- The triangle identity making `prodDiagFunctor`, `prodDiagInverse`, `prodDiagUnitIso` and
`prodDiagCounitIso` a half-adjoint equivalence. -/
theorem prodDiagTriangle (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S)
    (X : CategoricalPullback (G₁.prod G₂) (Functor.diag S)) :
    (prodDiagCounitIso G₁ G₂).inv.app ((prodDiagFunctor G₁ G₂).obj X) ≫
        (prodDiagFunctor G₁ G₂).map ((prodDiagUnitIso G₁ G₂).inv.app X) =
      𝟙 ((prodDiagFunctor G₁ G₂).obj X) := by
  apply CategoricalPullback.Hom.ext <;>
    simp [prodDiagFunctor, prodDiagInverse, prodDiagCounitIso, prodDiagUnitIso,
      CategoricalPullback.mkIso, NatIso.ofComponents]

/-- **Stacks 02XE.** The canonical comparison functor `prodDiagFunctor` is an equivalence of
categories: the 2-fibre product of `G₁ × G₂ : C₁ × C₂ ⥤ S × S` and the diagonal `Δ : S ⥤ S × S`
is canonically equivalent to `C₁ ×_S C₂`. -/
@[stacks 02XE]
theorem isEquivalence_prodDiagFunctor (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S) :
    (prodDiagFunctor G₁ G₂).IsEquivalence :=
  (Equivalence.mk'' (prodDiagFunctor G₁ G₂) (prodDiagInverse G₁ G₂)
    (prodDiagUnitIso G₁ G₂) (prodDiagCounitIso G₁ G₂)
    (prodDiagTriangle G₁ G₂)).isEquivalence_functor

/-- **Stacks 02XE.** The canonical equivalence of categories
`CategoricalPullback (G₁.prod G₂) (Functor.diag S) ≌ CategoricalPullback G₁ G₂`, induced by
`prodDiagFunctor`. -/
@[stacks 02XE]
noncomputable def prodDiagEquiv (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S) :
    CategoricalPullback (G₁.prod G₂) (Functor.diag S) ≌ CategoricalPullback G₁ G₂ :=
  have : (prodDiagFunctor G₁ G₂).IsEquivalence := isEquivalence_prodDiagFunctor G₁ G₂
  (prodDiagFunctor G₁ G₂).asEquivalence

section Components

variable (G₁ : C₁ ⥤ S) (G₂ : C₂ ⥤ S)

/-- The first component of `prodDiagFunctor` at `((X₁, X₂), Y, φ)` is `X₁`. -/
@[simp] lemma prodDiagFunctor_obj_fst
    (x : CategoricalPullback (G₁.prod G₂) (Functor.diag S)) :
    ((prodDiagFunctor G₁ G₂).obj x).fst = x.fst.1 := rfl

/-- The second component of `prodDiagFunctor` at `((X₁, X₂), Y, φ)` is `X₂`. -/
@[simp] lemma prodDiagFunctor_obj_snd
    (x : CategoricalPullback (G₁.prod G₂) (Functor.diag S)) :
    ((prodDiagFunctor G₁ G₂).obj x).snd = x.fst.2 := rfl

/-- The structural isomorphism produced by `prodDiagFunctor` is `φ₁ ≪≫ φ₂⁻¹`. -/
@[simp] lemma prodDiagFunctor_obj_iso
    (x : CategoricalPullback (G₁.prod G₂) (Functor.diag S)) :
    ((prodDiagFunctor G₁ G₂).obj x).iso =
      ((CategoryTheory.Prod.fst S S).mapIso x.iso) ≪≫
        ((CategoryTheory.Prod.snd S S).mapIso x.iso).symm := rfl

/-- The `C₁ × C₂`-component of `prodDiagInverse` at `(X₁, X₂, ψ)` is `(X₁, X₂)`. -/
@[simp] lemma prodDiagInverse_obj_fst (z : CategoricalPullback G₁ G₂) :
    ((prodDiagInverse G₁ G₂).obj z).fst = (z.fst, z.snd) := rfl

/-- The `S`-component of `prodDiagInverse` at `(X₁, X₂, ψ)` is `G₂ X₂`. -/
@[simp] lemma prodDiagInverse_obj_snd (z : CategoricalPullback G₁ G₂) :
    ((prodDiagInverse G₁ G₂).obj z).snd = G₂.obj z.snd := rfl

/-- The structural isomorphism produced by `prodDiagInverse` is `(ψ, 𝟙)`. -/
@[simp] lemma prodDiagInverse_obj_iso (z : CategoricalPullback G₁ G₂) :
    ((prodDiagInverse G₁ G₂).obj z).iso = z.iso.prod (Iso.refl (G₂.obj z.snd)) := rfl

end Components

end CategoryTheory.Limits.CategoricalPullback
