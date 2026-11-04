module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeKernelFunctor

/-!
# Changing the cone of test objects of a relative Hom functor

Let `P` be a coherent pullback pseudofunctor datum on a category `A`.  Its relative Hom functor
`CategoryTheory.PullbackData.relHomFunctor` sends a test object `i` of a cone `κ` over `a₀` to the
morphisms `(κ i)^*M ⟶ (κ i)^*N`.  This file records two ways of changing the cone, each as a
morphism of relative Hom functors, so that naturality in the test object is part of the
construction:

* along a **morphism of cones over the same object**, a family `mᵢ : π' i ⟶ π i` compatible with
  the legs, a morphism `α : (κ i)^*M ⟶ (κ i)^*N` is pulled back along `mᵢ`
  (`CategoryTheory.PullbackData.relHomConeMap`);
* along a **morphism `k : a₁ ⟶ a₀` of the objects the cones lie over**, the relative Hom functor of
  `k^*M` and `k^*N` over a cone over `a₁` is the relative Hom functor of `M` and `N` over its
  composite with `k` (`CategoryTheory.PullbackData.relHomPrecompIso`).

## Main definitions

* `CategoryTheory.PullbackData.relHomConeMap`: pullback along a morphism of cones.
* `CategoryTheory.PullbackData.relHomPrecompIso`: transport along a change of the base object.
* `CategoryTheory.PullbackData.relHomBimap`: functoriality of the relative Hom functor in its two
  objects.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D) {I : Type*} [Category* I]

/-- Conjugation by the comparison of a triangle only depends on the composite through the
morphisms, not on the way the first factor is spelled. -/
theorem conjHom_triangle_congr {a b c : A} {f f' : a ⟶ b} (hf : f = f') {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (hk' : f' ≫ g = k) {M N : D c}
    (α : (P.pull g).obj M ⟶ (P.pull g).obj N) :
    Functor.conjHom (P.triangle hk) α = Functor.conjHom (P.triangle hk') α := by
  subst hf
  rfl

/-- Conjugating twice along the comparisons of two triangles is conjugating once along the
comparison of the composite triangle.  This is the associativity coherence of the datum. -/
theorem conjHom_triangle_triangle (hP : P.IsCoherent) {a b c d : A} {f : a ⟶ b} {g : b ⟶ c}
    {p : c ⟶ d} {q : b ⟶ d} {r : a ⟶ d} (hq : g ≫ p = q) (hr : f ≫ q = r)
    (hkr : (f ≫ g) ≫ p = r) {M N : D d} (α : (P.pull p).obj M ⟶ (P.pull p).obj N) :
    Functor.conjHom (P.triangle hr) (Functor.conjHom (P.triangle hq) α) =
      Functor.conjHom (P.triangle hkr) α :=
  (Functor.conjHom_comp (P.triangle hq) (P.triangle hr) (P.triangle hkr)
    (P.triangle (f := f) (g := g) rfl) (hP.triangle_comp' rfl hq hr hkr) α).symm

variable {π π' : I ⥤ A} {a₀ : A}

/-- **Pullback along a morphism of cones over the same object.**  A natural family
`mᵢ : π' i ⟶ π i` compatible with the legs of two cones `κ'` and `κ` over `a₀` carries a
morphism `α : (κ i)^*M ⟶ (κ i)^*N` to its inverse image along `mᵢ`, read through the comparison
of `mᵢ ≫ κ i = κ' i`.  This is natural in the test object `i`. -/
def relHomConeMap (hP : P.IsCoherent) (κ : ConeTo π a₀) (κ' : ConeTo π' a₀) (m : π' ⟶ π)
    (hm : ∀ i, m.app i ≫ κ.leg i = κ'.leg i) (M N : D a₀) :
    P.relHomFunctor hP κ M N ⟶ P.relHomFunctor hP κ' M N where
  app i := ↾fun α => Functor.conjHom (P.triangle (hm i.unop)) α
  naturality {i j} g := by
    refine ConcreteCategory.hom_ext _ _ fun (α : P.relHomObj κ M N i.unop) => ?_
    change Functor.conjHom (P.triangle (hm j.unop)) (P.relHomMap κ M N g.unop α) =
      P.relHomMap κ' M N g.unop (Functor.conjHom (P.triangle (hm i.unop)) α)
    have h1 : (π'.map g.unop ≫ m.app i.unop) ≫ κ.leg i.unop = κ'.leg j.unop := by
      rw [Category.assoc, hm, κ'.w]
    have h2 : (m.app j.unop ≫ π.map g.unop) ≫ κ.leg i.unop = κ'.leg j.unop := by
      rw [Category.assoc, κ.w, hm]
    exact (P.conjHom_triangle_triangle hP (κ.w g.unop) (hm j.unop) h2 α).trans
      ((P.conjHom_triangle_congr (m.naturality g.unop).symm h2 h1 α).trans
        (P.conjHom_triangle_triangle hP (hm i.unop) (κ'.w g.unop) h1 α).symm)

/-- The component of `CategoryTheory.PullbackData.relHomConeMap`. -/
theorem relHomConeMap_app (hP : P.IsCoherent) (κ : ConeTo π a₀) (κ' : ConeTo π' a₀)
    (m : π' ⟶ π) (hm : ∀ i, m.app i ≫ κ.leg i = κ'.leg i) (M N : D a₀) (i : I)
    (α : P.relHomObj κ M N i) :
    (P.relHomConeMap hP κ κ' m hm M N).app (Opposite.op i) α =
      Functor.conjHom (P.triangle (hm i)) α :=
  rfl

section Precomp

variable {I₁ : Type*} [Category* I₁] {a₁ : A}

/-- **Transport along a change of the base object.**  If `Φ : I₁ ⥤ I` carries a cone `κ₁` over
`a₁` to the cone `κ` over `a₀` along `k : a₁ ⟶ a₀`, the relative Hom functor of `k^*M` and `k^*N`
over `κ₁` is the relative Hom functor of `M` and `N` over `κ`, restricted along `Φ`. -/
def relHomPrecompIso (hP : P.IsCoherent) (κ : ConeTo π a₀) (Φ : I₁ ⥤ I) (k : a₁ ⟶ a₀)
    (κ₁ : ConeTo (Φ ⋙ π) a₁) (hκ : ∀ i, κ₁.leg i ≫ k = κ.leg (Φ.obj i)) (M N : D a₀) :
    P.relHomFunctor hP κ₁ ((P.pull k).obj M) ((P.pull k).obj N) ≅
      Φ.op ⋙ P.relHomFunctor hP κ M N :=
  NatIso.ofComponents
    (fun i =>
      { hom := ↾fun α => Functor.transportHom (P.triangle (hκ i.unop)) α
        inv := ↾fun α => Functor.transportHom (P.triangle (hκ i.unop)).symm α
        hom_inv_id := ConcreteCategory.hom_ext _ _ fun α =>
          (Functor.transportHomEquiv (P.triangle (hκ i.unop)) _ _).left_inv α
        inv_hom_id := ConcreteCategory.hom_ext _ _ fun α =>
          (Functor.transportHomEquiv (P.triangle (hκ i.unop)) _ _).right_inv α })
    (fun {_ _} g => ConcreteCategory.hom_ext _ _ fun α =>
      P.transportHom_relHomMap hP κ Φ k κ₁ hκ M N g.unop α)

/-- The component of `CategoryTheory.PullbackData.relHomPrecompIso`. -/
theorem relHomPrecompIso_hom_app (hP : P.IsCoherent) (κ : ConeTo π a₀) (Φ : I₁ ⥤ I)
    (k : a₁ ⟶ a₀) (κ₁ : ConeTo (Φ ⋙ π) a₁) (hκ : ∀ i, κ₁.leg i ≫ k = κ.leg (Φ.obj i))
    (M N : D a₀) (i : I₁) (α : P.relHomObj κ₁ ((P.pull k).obj M) ((P.pull k).obj N) i) :
    (P.relHomPrecompIso hP κ Φ k κ₁ hκ M N).hom.app (Opposite.op i) α =
      Functor.transportHom (P.triangle (hκ i)) α :=
  rfl

end Precomp

/-- **Functoriality of the relative Hom functor in its two objects**: morphisms `a : M' ⟶ M` and
`b : N ⟶ N'` act on `α : (κ i)^*M ⟶ (κ i)^*N` by pre- and postcomposition with their inverse
images, naturally in the test object. -/
def relHomBimap (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M' N N' : D a₀} (a : M' ⟶ M)
    (b : N ⟶ N') : P.relHomFunctor hP κ M N ⟶ P.relHomFunctor hP κ M' N' where
  app i := ↾fun α => (P.pull (κ.leg i.unop)).map a ≫ α ≫ (P.pull (κ.leg i.unop)).map b
  naturality {i j} g := by
    refine ConcreteCategory.hom_ext _ _ fun (α : P.relHomObj κ M N i.unop) => ?_
    change (P.pull (κ.leg j.unop)).map a ≫ P.relHomMap κ M N g.unop α ≫
        (P.pull (κ.leg j.unop)).map b =
      P.relHomMap κ M' N' g.unop
        ((P.pull (κ.leg i.unop)).map a ≫ α ≫ (P.pull (κ.leg i.unop)).map b)
    symm
    rw [P.relHomMap_comp_map κ M b g.unop α, P.map_comp_relHomMap κ a N' g.unop]

/-- The component of `CategoryTheory.PullbackData.relHomBimap`. -/
theorem relHomBimap_app (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M' N N' : D a₀}
    (a : M' ⟶ M) (b : N ⟶ N') (i : I) (α : P.relHomObj κ M N i) :
    (P.relHomBimap hP κ a b).app (Opposite.op i) α =
      (P.pull (κ.leg i)).map a ≫ α ≫ (P.pull (κ.leg i)).map b :=
  rfl

end CategoryTheory.PullbackData

end
