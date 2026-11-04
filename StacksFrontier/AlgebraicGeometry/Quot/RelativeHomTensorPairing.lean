module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomConeChange
public import StacksFrontier.CategoryTheory.Functor.ConjugateHomTensorPairing

/-!
# The tensor pairing on relative Hom functors

Let `P` be a pullback pseudofunctor datum whose fibres carry tensor bifunctors, with comparisons
`μ_f : f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` compatible with the composition comparisons of `P`.  For
objects `O, Π, R, G` over `a₀` with `ℓ : Π ⟶ O ⊗ Π` and `ev : R ⊗ Π ⟶ G`, a morphism
`α : (κ i)^*O ⟶ (κ i)^*R` over a test object `i` gives the tensor pairing
`(κ i)^*Π ⟶ (κ i)^*G`, and this is natural in the test object: a morphism
`relHom(κ, O, R) ⟶ relHom(κ, Π, G)` of relative Hom functors.

## Main definitions

* `CategoryTheory.PullbackData.TensorCompatibility`: comparisons of the inverse images with the
  tensor products, compatible with composition.
* `CategoryTheory.PullbackData.relHomTensorPairing`: the tensor pairing as a morphism of relative
  Hom functors.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D) (T : ∀ a, D a ⥤ D a ⥤ D a)

/-- Compatibility of a pullback datum with tensor products: comparisons
`μ_f : f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`, natural in the first factor, and compatible with the
composition comparison `(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
structure TensorCompatibility where
  /-- The comparison of the inverse image of a tensor product with the tensor product of the
  inverse images. -/
  μ : ∀ {a b : A} (f : a ⟶ b) (M N : D b),
    (P.pull f).obj (((T b).obj M).obj N) ≅ ((T a).obj ((P.pull f).obj M)).obj ((P.pull f).obj N)
  /-- The comparison is natural in the first factor. -/
  μ_naturality : ∀ {a b : A} (f : a ⟶ b) {M M' : D b} (u : M ⟶ M') (N : D b),
    (P.pull f).map (((T b).map u).app N) ≫ (μ f M' N).hom =
      (μ f M N).hom ≫ ((T a).map ((P.pull f).map u)).app ((P.pull f).obj N)
  /-- The comparison is compatible with composition. -/
  μ_comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (M N : D c),
    (μ (f ≫ g) M N).hom ≫ ((T a).map ((P.compIso f g).hom.app M)).app ((P.pull (f ≫ g)).obj N) ≫
        ((T a).obj ((P.pull g ⋙ P.pull f).obj M)).map ((P.compIso f g).hom.app N) =
      (P.compIso f g).hom.app (((T c).obj M).obj N) ≫ (P.pull f).map (μ g M N).hom ≫
        (μ f ((P.pull g).obj M) ((P.pull g).obj N)).hom

variable {P T} (τ : TensorCompatibility P T)

/-- The compatibility with composition, along the comparison of a triangle. -/
theorem TensorCompatibility.μ_triangle {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (M N : D c) :
    (τ.μ k M N).hom ≫ ((T a).map ((P.triangle hk).hom.app M)).app ((P.pull k).obj N) ≫
        ((T a).obj ((P.pull g ⋙ P.pull f).obj M)).map ((P.triangle hk).hom.app N) =
      (P.triangle hk).hom.app (((T c).obj M).obj N) ≫ (P.pull f).map (τ.μ g M N).hom ≫
        (τ.μ f ((P.pull g).obj M) ((P.pull g).obj N)).hom := by
  subst hk
  rw [triangle_rfl]
  exact τ.μ_comp f g M N

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- The tensor pairing on relative Hom functors.  For `ℓ : Π ⟶ O ⊗ Π` and `ev : R ⊗ Π ⟶ G`, a
morphism `α : (κ i)^*O ⟶ (κ i)^*R` goes to the composite
`(κ i)^*Π ⟶ (κ i)^*(O ⊗ Π) ≅ (κ i)^*O ⊗ (κ i)^*Π ⟶ (κ i)^*R ⊗ (κ i)^*Π` followed by
`(κ i)^*R ⊗ (κ i)^*Π ≅ (κ i)^*(R ⊗ Π) ⟶ (κ i)^*G`, naturally in the test object. -/
def relHomTensorPairing (hP : P.IsCoherent) (κ : ConeTo π a₀) {O Pm R G : D a₀}
    (ℓ : Pm ⟶ ((T a₀).obj O).obj Pm) (ev : ((T a₀).obj R).obj Pm ⟶ G) :
    P.relHomFunctor hP κ O R ⟶ P.relHomFunctor hP κ Pm G where
  app i := ↾fun α => Functor.tensorPairing (T a₀) (P.pull (κ.leg i.unop)) (T (π.obj i.unop))
    (τ.μ (κ.leg i.unop)) ℓ ev α
  naturality {i j} g := ConcreteCategory.hom_ext _ _ fun (α : P.relHomObj κ O R i.unop) =>
    Functor.tensorPairing_conjHom (T a₀) (T (π.obj i.unop)) (T (π.obj j.unop))
      (P.triangle (κ.w g.unop)) (τ.μ (κ.leg i.unop)) (τ.μ (κ.leg j.unop))
      (τ.μ (π.map g.unop)) (fun u B => τ.μ_naturality (π.map g.unop) u B)
      (fun M N => τ.μ_triangle (κ.w g.unop) M N) ℓ ev α

/-- The component of `CategoryTheory.PullbackData.relHomTensorPairing` at a test object `i` is
the tensor pairing along `κ.leg i`. -/
theorem relHomTensorPairing_app (hP : P.IsCoherent) (κ : ConeTo π a₀) {O Pm R G : D a₀}
    (ℓ : Pm ⟶ ((T a₀).obj O).obj Pm) (ev : ((T a₀).obj R).obj Pm ⟶ G) (i : I)
    (α : P.relHomObj κ O R i) :
    (relHomTensorPairing τ hP κ ℓ ev).app (Opposite.op i) α =
      Functor.tensorPairing (T a₀) (P.pull (κ.leg i)) (T (π.obj i)) (τ.μ (κ.leg i)) ℓ ev α :=
  rfl

end CategoryTheory.PullbackData

end
