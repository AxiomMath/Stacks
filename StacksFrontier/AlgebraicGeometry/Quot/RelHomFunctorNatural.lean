module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFunctorTransport

/-!
# Morphisms of relative Hom functors

Let `P` be a coherent pullback pseudofunctor datum on a category `A`.  This file produces
morphisms between the relative Hom functors `i ↦ Hom((κ i)^*M, (κ i)^*N)` of
`CategoryTheory.PullbackData.relHomFunctor` in two ways.

* From a family of maps `Θ_q : Hom(q^*M, q^*N) ⟶ Hom(q^*M', q^*N')`, one for every morphism `q`
  into `a₀`, compatible with conjugation along the comparison triangles: this gives a morphism
  of relative Hom functors at every cone over `a₀`.  Composition with the inverse images of fixed
  morphisms `M' ⟶ M` and `N ⟶ N'` is such a family.
* From a morphism `φ : π₁ ⟶ π₂` of the diagrams of two cones over `a₀`, compatible with the legs:
  conjugation by the comparisons `(κ₁ i)^* ≅ (κ₂ i)^* ⋙ (φ i)^*`.

## Main definitions

* `CategoryTheory.PullbackData.IsTriangleNatural`: the compatibility of a family `Θ` with the
  comparison triangles.
* `CategoryTheory.PullbackData.relHomNatTrans`: the morphism of relative Hom functors of such a
  family.
* `CategoryTheory.PullbackData.relHomFunctorConeMap`: the morphism along a morphism of cones.

## Main results

* `CategoryTheory.Functor.conjHom_map_comp_comp`: conjugation commutes with composition with the
  images of fixed morphisms.
* `CategoryTheory.PullbackData.isTriangleNatural_comp`: composition with the inverse images of
  fixed morphisms is compatible with the comparison triangles.
-/

@[expose] public noncomputable section

namespace CategoryTheory

/-- Conjugation by a comparison commutes with composition with the images of fixed morphisms. -/
theorem Functor.conjHom_map_comp_comp {C D₁ D₂ : Type*} [Category* C] [Category* D₁]
    [Category* D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L)
    {M' M N N' : C} (u : M' ⟶ M) (v : N ⟶ N') (α : P₁.obj M ⟶ P₁.obj N) :
    Functor.conjHom e (P₁.map u ≫ α ≫ P₁.map v) = P₂.map u ≫ Functor.conjHom e α ≫ P₂.map v := by
  simp only [Functor.conjHom, Functor.map_comp, Category.assoc]
  have h₁ := e.hom.naturality u
  have h₂ := e.inv.naturality v
  simp only [Functor.comp_map] at h₁ h₂
  rw [← h₂, ← reassoc_of% h₁]

namespace PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D)

/-- **A family of maps of Hom sets compatible with the comparison triangles.**  For each morphism
`q : b ⟶ a₀` a map `Θ q : Hom(q^*M, q^*N) ⟶ Hom(q^*M', q^*N')`, such that for every
`h : a ⟶ b` and `h ≫ q = k`, `Θ k` of the conjugate along the comparison
`k^* ≅ q^* ⋙ h^*` is the conjugate of `Θ q`. -/
def IsTriangleNatural {a₀ : A} {M N M' N' : D a₀}
    (Θ : ∀ {b : A} (q : b ⟶ a₀), ((P.pull q).obj M ⟶ (P.pull q).obj N) →
      ((P.pull q).obj M' ⟶ (P.pull q).obj N')) : Prop :=
  ∀ {a b : A} (h : a ⟶ b) (q : b ⟶ a₀) (k : a ⟶ a₀) (hk : h ≫ q = k)
    (α : (P.pull q).obj M ⟶ (P.pull q).obj N),
    Θ k (Functor.conjHom (P.triangle hk) α) = Functor.conjHom (P.triangle hk) (Θ q α)

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- **The morphism of relative Hom functors of a family compatible with the comparison
triangles.** -/
def relHomNatTrans (hP : P.IsCoherent) (κ : ConeTo π a₀) {M N M' N' : D a₀}
    (Θ : ∀ {b : A} (q : b ⟶ a₀), ((P.pull q).obj M ⟶ (P.pull q).obj N) →
      ((P.pull q).obj M' ⟶ (P.pull q).obj N'))
    (hΘ : P.IsTriangleNatural Θ) :
    P.relHomFunctor hP κ M N ⟶ P.relHomFunctor hP κ M' N' where
  app i := TypeCat.ofHom fun α => Θ (κ.leg i.unop) α
  naturality {i j} g := by
    ext α
    exact hΘ (π.map g.unop) (κ.leg i.unop) (κ.leg j.unop) (κ.w g.unop) α

/-- The component of `relHomNatTrans` at `i` sends `α` to `Θ (κ.leg i) α`. -/
theorem relHomNatTrans_app (hP : P.IsCoherent) (κ : ConeTo π a₀) {M N M' N' : D a₀}
    (Θ : ∀ {b : A} (q : b ⟶ a₀), ((P.pull q).obj M ⟶ (P.pull q).obj N) →
      ((P.pull q).obj M' ⟶ (P.pull q).obj N'))
    (hΘ : P.IsTriangleNatural Θ) (i : I) (α : P.relHomObj κ M N i) :
    (P.relHomNatTrans hP κ Θ hΘ).app (Opposite.op i) α = Θ (κ.leg i) α :=
  rfl

/-- Composition with the inverse images of fixed morphisms `u : M' ⟶ M` and `v : N ⟶ N'` is
compatible with the comparison triangles. -/
theorem isTriangleNatural_comp {M' M N N' : D a₀} (u : M' ⟶ M) (v : N ⟶ N') :
    P.IsTriangleNatural (M := M) (N := N) (M' := M') (N' := N')
      (fun q α => (P.pull q).map u ≫ α ≫ (P.pull q).map v) :=
  fun _ _ _ hk α => (Functor.conjHom_map_comp_comp (P.triangle hk) u v α).symm

/-- **The morphism of relative Hom functors along a morphism of cones.**  For cones `κ₁` from
`π₁` and `κ₂` from `π₂` to `a₀` and a natural transformation `φ : π₁ ⟶ π₂` compatible with the
legs, conjugation by the comparisons `(κ₁ i)^* ≅ (κ₂ i)^* ⋙ (φ i)^*`. -/
def relHomFunctorConeMap (hP : P.IsCoherent) {π₁ π₂ : I ⥤ A} (κ₁ : ConeTo π₁ a₀) (κ₂ : ConeTo π₂ a₀)
    (φ : π₁ ⟶ π₂) (hφ : ∀ i, φ.app i ≫ κ₂.leg i = κ₁.leg i) (M N : D a₀) :
    P.relHomFunctor hP κ₂ M N ⟶ P.relHomFunctor hP κ₁ M N where
  app i := TypeCat.ofHom fun β => Functor.conjHom (P.triangle (hφ i.unop)) β
  naturality {i j} g := by
    ext β
    have hnat : φ.app j.unop ≫ π₂.map g.unop = π₁.map g.unop ≫ φ.app i.unop :=
      (φ.naturality g.unop).symm
    have hkr : (π₁.map g.unop ≫ φ.app i.unop) ≫ κ₂.leg i.unop = κ₁.leg j.unop := by
      rw [Category.assoc, hφ, κ₁.w]
    change Functor.conjHom (P.triangle (hφ j.unop)) (Functor.conjHom (P.triangle (κ₂.w g.unop)) β) =
      Functor.conjHom (P.triangle (κ₁.w g.unop)) (Functor.conjHom (P.triangle (hφ i.unop)) β)
    exact (P.conjHom_triangle_comp hP hnat (κ₂.w g.unop) (hφ j.unop) hkr β).trans
      (P.conjHom_triangle_comp hP rfl (hφ i.unop) (κ₁.w g.unop) hkr β).symm

/-- The component of `relHomFunctorConeMap` at `i` is conjugation by the comparison
`(κ₁ i)^* ≅ (κ₂ i)^* ⋙ (φ i)^*`. -/
theorem relHomFunctorConeMap_app (hP : P.IsCoherent) {π₁ π₂ : I ⥤ A} (κ₁ : ConeTo π₁ a₀)
    (κ₂ : ConeTo π₂ a₀) (φ : π₁ ⟶ π₂) (hφ : ∀ i, φ.app i ≫ κ₂.leg i = κ₁.leg i) (M N : D a₀)
    (i : I) (β : P.relHomObj κ₂ M N i) :
    (P.relHomFunctorConeMap hP κ₁ κ₂ φ hφ M N).app (Opposite.op i) β =
      Functor.conjHom (P.triangle (hφ i)) β :=
  rfl

end PullbackData

end CategoryTheory
