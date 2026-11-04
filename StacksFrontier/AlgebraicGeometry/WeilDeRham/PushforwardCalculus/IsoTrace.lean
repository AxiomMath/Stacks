module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilCohomologyTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.PushforwardCalculus.Chow
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PoincareDualityWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SecondAdamsChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullbackComp
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupPushforwardOne
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.Product

/-!
# Fundamental classes along an isomorphism

For an isomorphism `e : X ≅ X'` of nonempty equidimensional smooth projective schemes over `k`,
the proper pushforward along `e` carries the fundamental class `[X]` in `CH^0(X)` to `[X']`, and
the product of two isomorphisms of smooth projective schemes is an isomorphism of the products.

## Main definitions

* `Stacks.WeilDeRham.prodIso`: the product of two isomorphisms of smooth projective schemes,
  built from the product of morphisms `Stacks.WeilCohomology.SmoothProjectiveScheme.prodMap`.

## Main results

* `Stacks.WeilDeRham.chowCodimPushforward_chowCodimFundamental_of_isIso`: `e_*[X] = [X']`.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open Stacks.Chow Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u w

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k]

/-! ### Products of morphisms -/

section Prod

variable {X Y X' Y' : (SmoothProjectiveScheme k).FullSubcategory}

/-- **The product of two isomorphisms** of smooth projective schemes over `k`. -/
@[simps]
def prodIso (e : X ≅ X') (e' : Y ≅ Y') : prod X Y ≅ prod X' Y' where
  hom := prodMap e.hom e'.hom
  inv := prodMap e.inv e'.inv
  hom_inv_id := by rw [prodMap_comp, e.hom_inv_id, e'.hom_inv_id, prodMap_id]
  inv_hom_id := by rw [prodMap_comp, e.inv_hom_id, e'.inv_hom_id, prodMap_id]

end Prod

/-! ### Fundamental classes and the class of the diagonal -/

section Fundamental

/-- The fundamental class `[X] ∈ CH^0(X)` is the codimension-`0` part of the fundamental classes
`[X]_n ∈ CH_n(X)`, for `X` smooth over `k`: `[X]_n` restricts to `[X_d]_n` on each part. -/
theorem chowCodimFundamental_eq_chowCodimPart {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] :
    chowCodimFundamental k sX =
      chowCodimPart k sX (fun n ↦ fundamentalChowClass (fieldChowSituation k) sX n) 0 := by
  funext d
  exact (chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion _ sX (partBase sX d)
    (dimPart sX d).ι rfl _).symm

/-- On `X` equidimensional of dimension `d`, the class in dimension `n` of `[X] ∈ CH^0(X)` is
`[X]_n`. -/
theorem chowCodimTotal_chowCodimFundamental {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] {d : ℕ} (hX : RelativeDimension sX d)
    (n : ℤ) :
    chowCodimTotal k sX 0 n (chowCodimFundamental k sX) =
      fundamentalChowClass (fieldChowSituation k) sX n := by
  by_cases hn : n = (d : ℤ) - (0 : ℕ)
  · rw [chowCodimFundamental_eq_chowCodimPart]
    exact chowCodimTotal_chowCodimPart k sX hX 0 hn.symm _
  · rw [chowCodimTotal_eq_zero_of_ne k sX hX 0 hn,
      Stacks.Chow.fundamentalChowClass_eq_zero_of_relativeDimension k sX hX (by simpa using hn)]

variable {X X' : (SmoothProjectiveScheme k).FullSubcategory}

/-- **`e_*[X] = [X']`** in `CH^0(X')`, for an isomorphism `e : X ≅ X'` of smooth projective
schemes equidimensional of dimension `d`. -/
theorem chowCodimPushforward_chowCodimFundamental_of_isIso (e : X ≅ X') {d : ℕ}
    (hd : RelativeDimension X.obj.hom d) :
    chowCodimPushforward k X.obj.hom X'.obj.hom ((toScheme k).map e.hom) (w e.hom) 0 0
        (chowCodimFundamental k X.obj.hom) =
      chowCodimFundamental k X'.obj.hom := by
  rw [chowCodimFundamental_eq_chowCodimPart X'.obj.hom]
  unfold chowCodimPushforward
  congr 1
  funext n
  rw [chowCodimTotal_chowCodimFundamental X.obj.hom hd n]
  have : IsIso ((toScheme k).map e.hom) := Functor.map_isIso _ _
  have h := chowPushforwardOfIso_fundamentalChowClass (fieldChowSituation k) X.obj.hom X'.obj.hom
    ((toScheme k).map e.hom) (w e.hom) n
  exact h

end Fundamental

/-! ### Pullback along an isomorphism -/

section Graded

variable {F : Type w} [Field F] {𝔇 : FirstChernClassData k F}

end Graded

/-! ### The normalisation of (A6) along an isomorphism -/

section Normalization

variable {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA5 : 𝔇.KunnethAxiom)
  {X X' : (SmoothProjectiveScheme k).FullSubcategory}

variable (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom)
  (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass) (hA7 : 𝔇.BlowupAxiom)

end Normalization

end Stacks.WeilDeRham

end
