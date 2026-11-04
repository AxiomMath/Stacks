module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import StacksFrontier.Algebra.Homology.CupProductBoundary

/-!
# The cup-product sign rule with the representatives identified as boundaries

Given a short exact sequence `S` of cochain complexes in an abelian category, a cocycle `x₃` of
`S.X₃` in degree `n`, a lift `x₂` of `x₃` along `S.g`, and a cochain `x₁` of `S.X₁` in degree
`n + 1` whose image along `S.f` is `d(x₂)`, the class of `x₁` is the image of the class of `x₃`
under the connecting morphism `∂`. With this, the cup-product sign rule
`Stacks.CupProduct.gamma_cup_boundary_homologyClass` is stated with its two cochain
representatives identified as the boundaries `∂a₃` and `∂b₁`.

## Main results

* `Stacks.CupProduct.mono_f_f`: a short exact sequence of complexes is degreewise monomorphic
  in its first map.
* `Stacks.CupProduct.liftCycles_homologyπ_eq_δ`: the class of `x₁` in `H^{n+1}` is `∂` of the
  class of `x₃` in `H^n`.
* `Stacks.CupProduct.liftCycles_homologyπ_eq_of_lift`: the class of `x₁` does not depend on the
  chosen lift `x₂`, nor on the chosen `x₁` over it.
* `Stacks.CupProduct.gamma_cup_boundary_delta`: the sign rule
  `[γ₁(α₁ ∪ b₁)] = (-1)^{n+1} [γ₃(a₃ ∪ β₃)]` with `α₁` and `β₃` representatives of `∂a₃` and
  `∂b₁`.

## Implementation notes

The lifts `x₂` of `x₃` along `S.g` are data: the test object `P` is arbitrary, and with no
projectivity assumption on `P` a lift of a `P`-valued cochain need not exist.

## References

* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe v₁ v₂ v u₁ u₂ u

namespace Stacks.CupProduct

/-- A short exact sequence of complexes is degreewise monomorphic in its first map. -/
theorem mono_f_f {C : Type u₁} [Category.{v₁} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (k : ι) :
    Mono (S.f.f k) :=
  (hS.map_of_exact (HomologicalComplex.eval C c k)).mono_f

section Delta

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {S : ShortComplex (CochainComplex C ℤ)}

/-- Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of cochain complexes, let `x₃` be
a `P`-valued cocycle of `S.X₃` in degree `n`, let `x₂` be a cochain of `S.X₂` lifting it, and let
`x₁` be a cochain of `S.X₁` in degree `n + 1` whose image in `S.X₂` is `d(x₂)`. Then `x₁` is a
cocycle and its class in `H^{n+1}(S.X₁)` is the image of the class of `x₃` under the connecting
morphism `∂ : H^n(S.X₃) ⟶ H^{n+1}(S.X₁)`. -/
theorem liftCycles_homologyπ_eq_δ (hS : S.ShortExact) {P : C} (n : ℤ)
    (x₃ : P ⟶ S.X₃.X n) (hx₃ : x₃ ≫ S.X₃.d n (n + 1) = 0)
    (x₂ : P ⟶ S.X₂.X n) (hx₂ : x₂ ≫ S.g.f n = x₃)
    (x₁ : P ⟶ S.X₁.X (n + 1)) (hx₁ : x₁ ≫ S.f.f (n + 1) = x₂ ≫ S.X₂.d n (n + 1)) :
    S.X₁.liftCycles x₁ (n + 1 + 1) (CochainComplex.next ℤ (n + 1))
          (by
            have := mono_f_f hS (n + 1 + 1)
            exact comp_d_eq_zero_of_comp_eq_comp_d S.f n x₂ x₁ hx₁) ≫
        S.X₁.homologyπ (n + 1) =
      (S.X₃.liftCycles x₃ (n + 1) (CochainComplex.next ℤ n) hx₃ ≫ S.X₃.homologyπ n) ≫
        hS.δ n (n + 1) rfl := by
  rw [Category.assoc]
  exact (hS.δ_eq n (n + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ (n + 1 + 1)
    (CochainComplex.next ℤ (n + 1))).symm

/-- The class of a representative of `∂x₃` does not depend on the choice of the lift `x₂` of `x₃`
or of the cochain `x₁` over `d(x₂)`. -/
theorem liftCycles_homologyπ_eq_of_lift (hS : S.ShortExact) {P : C} (n : ℤ)
    (x₃ : P ⟶ S.X₃.X n) (hx₃ : x₃ ≫ S.X₃.d n (n + 1) = 0)
    (x₂ x₂' : P ⟶ S.X₂.X n) (hx₂ : x₂ ≫ S.g.f n = x₃) (hx₂' : x₂' ≫ S.g.f n = x₃)
    (x₁ : P ⟶ S.X₁.X (n + 1)) (hx₁ : x₁ ≫ S.f.f (n + 1) = x₂ ≫ S.X₂.d n (n + 1))
    (x₁' : P ⟶ S.X₁.X (n + 1)) (hx₁' : x₁' ≫ S.f.f (n + 1) = x₂' ≫ S.X₂.d n (n + 1)) :
    S.X₁.liftCycles x₁ (n + 1 + 1) (CochainComplex.next ℤ (n + 1))
          (by
            have := mono_f_f hS (n + 1 + 1)
            exact comp_d_eq_zero_of_comp_eq_comp_d S.f n x₂ x₁ hx₁) ≫
        S.X₁.homologyπ (n + 1) =
      S.X₁.liftCycles x₁' (n + 1 + 1) (CochainComplex.next ℤ (n + 1))
          (by
            have := mono_f_f hS (n + 1 + 1)
            exact comp_d_eq_zero_of_comp_eq_comp_d S.f n x₂' x₁' hx₁') ≫
        S.X₁.homologyπ (n + 1) :=
  (liftCycles_homologyπ_eq_δ hS n x₃ hx₃ x₂ hx₂ x₁ hx₁).trans
    (liftCycles_homologyπ_eq_δ hS n x₃ hx₃ x₂' hx₂' x₁' hx₁').symm

end Delta

section Main

variable {A : Type u₁} {B : Type u₂} {D : Type u}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v} D]
  [Abelian A] [Abelian B] [Preadditive D]
  (Φ : A ⥤ B ⥤ D) [Φ.PreservesZeroMorphisms] [∀ X, (Φ.obj X).PreservesZeroMorphisms]
  {S : ShortComplex (CochainComplex A ℤ)} {T : ShortComplex (CochainComplex B ℤ)}
  {H : CochainComplex D ℤ}
  [HomologicalComplex.HasMapBifunctor S.X₁ T.X₃ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₁ T.X₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₂ T.X₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₂ T.X₁ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₃ T.X₁ Φ (up ℤ)]

/-- For short exact sequences `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of complexes of `A` and
`0 ⟶ G₃ ⟶ G₂ ⟶ G₁ ⟶ 0` of complexes of `B`, pairings `γᵢ : Tot(Φ(Fᵢ, Gᵢ)) ⟶ H` making the two
squares commute, a cocycle `a₃` of `F₃` in degree `n` and a cocycle `b₁` of `G₁` in degree `m`,
lifts `α₂` of `a₃` and `β₂` of `b₁`, and cochains `α₁`, `β₃` over `d(α₂)`, `d(β₂)`,

`[γ₁(α₁ ∪ b₁)] = (-1)^{n+1} [γ₃(a₃ ∪ β₃)]`  in  `H^{n+m+1}(H)`,

where `α₁` represents `∂a₃` and `β₃` represents `∂b₁` by
`Stacks.CupProduct.liftCycles_homologyπ_eq_δ`. -/
theorem gamma_cup_boundary_delta (hS : S.ShortExact) (hT : T.ShortExact) {P : A} {Q : B}
    (γ₁ : HomologicalComplex.mapBifunctor S.X₁ T.X₃ Φ (up ℤ) ⟶ H)
    (γ₂ : HomologicalComplex.mapBifunctor S.X₂ T.X₂ Φ (up ℤ) ⟶ H)
    (γ₃ : HomologicalComplex.mapBifunctor S.X₃ T.X₁ Φ (up ℤ) ⟶ H)
    (h₁ : HomologicalComplex.mapBifunctorMap (𝟙 S.X₁) T.g Φ (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap S.f (𝟙 T.X₂) Φ (up ℤ) ≫ γ₂)
    (h₂ : HomologicalComplex.mapBifunctorMap (𝟙 S.X₂) T.f Φ (up ℤ) ≫ γ₂ =
      HomologicalComplex.mapBifunctorMap S.g (𝟙 T.X₁) Φ (up ℤ) ≫ γ₃)
    (n m : ℤ) [H.HasHomology (n + m + 1)]
    (a₃ : P ⟶ S.X₃.X n) (ha₃ : a₃ ≫ S.X₃.d n (n + 1) = 0)
    (b₁ : Q ⟶ T.X₃.X m) (hb₁ : b₁ ≫ T.X₃.d m (m + 1) = 0)
    (α₂ : P ⟶ S.X₂.X n) (hα₂ : α₂ ≫ S.g.f n = a₃)
    (β₂ : Q ⟶ T.X₂.X m) (hβ₂ : β₂ ≫ T.g.f m = b₁)
    (α₁ : P ⟶ S.X₁.X (n + 1)) (hα₁ : α₁ ≫ S.f.f (n + 1) = α₂ ≫ S.X₂.d n (n + 1))
    (β₃ : Q ⟶ T.X₁.X (m + 1)) (hβ₃ : β₃ ≫ T.f.f (m + 1) = β₂ ≫ T.X₂.d m (m + 1)) :
    H.liftCycles (cupPair Φ S.X₁ T.X₃ (n + 1) m (n + m + 1) (by omega) α₁ b₁ ≫
            γ₁.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1))
          (by
            refine cupPair_comp_gamma_comp_d_eq_zero Φ _ _ γ₁ _ _ _ _ _ _ ?_ hb₁
            have := mono_f_f hS (n + 1 + 1)
            exact comp_d_eq_zero_of_comp_eq_comp_d S.f n α₂ α₁ hα₁) ≫
        H.homologyπ (n + m + 1) =
      ((n + 1).negOnePow : ℤ) •
        (H.liftCycles (cupPair Φ S.X₃ T.X₁ n (m + 1) (n + m + 1) (by omega) a₃ β₃ ≫
              γ₃.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1))
            (by
              refine cupPair_comp_gamma_comp_d_eq_zero Φ _ _ γ₃ _ _ _ _ _ _ ha₃ ?_
              have := mono_f_f hT (m + 1 + 1)
              exact comp_d_eq_zero_of_comp_eq_comp_d T.f m β₂ β₃ hβ₃) ≫
          H.homologyπ (n + m + 1)) := by
  subst hα₂ hβ₂
  exact gamma_cup_boundary_homologyClass Φ S.f S.g T.f T.g γ₁ γ₂ γ₃ h₁ h₂ n m α₂ β₂ α₁ hα₁
    β₃ hβ₃ _ _

end Main

end Stacks.CupProduct

end
