module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent

/-!
# Associativity of the exterior product on `CH_*`

Let `k` be a field and let `X`, `Y`, `Z` be schemes locally of finite type over `k`. The exterior
product `CH_n(X) ⊗ CH_m(Y) ⟶ CH_{n+m}(X ×_k Y)` of Stacks 0FBV extends additively to the total
Chow groups `CH_*(X) = ⨁_n CH_n(X)`, giving a biadditive map

  `CH_*(X) × CH_*(Y) ⟶ CH_*(X ×_k Y)`,

which is `Stacks.Chow.totalChowExteriorProduct`. Stacks 0FBZ says that it is associative:
for `α ∈ CH_*(X)`, `β ∈ CH_*(Y)`, `γ ∈ CH_*(Z)`,

  `(α × β) × γ = α × (β × γ)` in `CH_*(X ×_k Y ×_k Z)`,

where the left-hand side, which lives on `(X ×_k Y) ×_k Z`, is carried to `X ×_k (Y ×_k Z)` by
pushforward along the associator `Stacks.Chow.tripleProductAssoc` of the fibre product.

In each degree this is `Stacks.Chow.chowExteriorProduct_assoc`, whose hypothesis that flat
pullback preserves rational equivalence (Stacks 02S1) is discharged by
`Stacks.Chow.flatPullbackDescends`; the statement on `CH_*` follows by additivity in each of the
three variables.

## Main definitions

* `Stacks.Chow.totalChowExteriorProduct` — the exterior product on total Chow groups.
* `Stacks.Chow.totalChowPushforwardOfIso` — pushforward of total Chow groups along an
  isomorphism over the base.

## Main results

* `Stacks.Chow.chowExteriorProduct_assoc_of_field` — associativity in fixed degrees.
* `Stacks.Chow.totalChowExteriorProduct_assoc` — Tag 0FBZ.

## References

* [Stacks Project, Tag 0FBZ](https://stacks.math.columbia.edu/tag/0FBZ)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The dimension function of `Stacks.Chow.fieldChowSituation` vanishes at the closed point, which
is the hypothesis on the base under which `Stacks.Chow.chowExteriorProduct` is defined. -/
theorem dimensionFunction_eq_zero_of_isClosed (k : Type u) [Field k] :
    ∀ s : (fieldChowSituation k).S, IsClosed ({s} : Set (fieldChowSituation k).S) →
      (fieldChowSituation k).dimensionFunction s = 0 :=
  fun s _ ↦ fieldChowSituation_dimensionFunction k s

/-- Associativity of the exterior product on Chow groups over a field, in fixed degrees
`n`, `m`, `l`: for `a ∈ CH_n(X)`, `b ∈ CH_m(Y)`, `c ∈ CH_l(Z)` the class `(a × b) × c`, pushed
forward along the associator and read in degree `n + (m + l)`, is `a × (b × c)`. -/
theorem chowExteriorProduct_assoc_of_field (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (h : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType h] (n m l : ℤ)
    (a : chowGroup (fieldChowSituation k) f n)
    (b : chowGroup (fieldChowSituation k) g m)
    (c : chowGroup (fieldChowSituation k) h l) :
    chowGroupDegreeEquiv (fieldChowSituation k)
        (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (add_assoc n m l)
        (chowPushforwardOfIso (fieldChowSituation k)
          (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
          (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleProductAssoc f g h).hom
          (tripleProductAssoc_hom_comp_base f g h) (n + m + l)
          (chowExteriorProduct (fieldChowSituation k) (dimensionFunction_eq_zero_of_isClosed k)
            (pullback.fst f g ≫ f) h (n + m) l
            (TensorProduct.tmul ℤ
              (chowExteriorProduct (fieldChowSituation k) (dimensionFunction_eq_zero_of_isClosed k)
                f g n m (TensorProduct.tmul ℤ a b)) c))) =
      chowExteriorProduct (fieldChowSituation k) (dimensionFunction_eq_zero_of_isClosed k) f
        (pullback.fst g h ≫ g) n (m + l)
        (TensorProduct.tmul ℤ a
          (chowExteriorProduct (fieldChowSituation k) (dimensionFunction_eq_zero_of_isClosed k)
            g h m l (TensorProduct.tmul ℤ b c))) :=
  chowExteriorProduct_assoc k (flatPullbackDescends _) f g h n m l a b c

section Total

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)

/-- The exterior product on total Chow groups, `CH_*(X) × CH_*(Y) ⟶ CH_*(X ×_S Y)`: the
additive extension of the exterior products `CH_n(X) ⊗ CH_m(Y) ⟶ CH_{n+m}(X ×_S Y)` of
Stacks 0FBV. -/
def totalChowExteriorProduct {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (g : Y ⟶ C.S) [LocallyOfFiniteType g] :
    (DirectSum ℤ fun n : ℤ ↦ chowGroup C f n) →ₗ[ℤ] (DirectSum ℤ fun m : ℤ ↦ chowGroup C g m) →ₗ[ℤ]
      DirectSum ℤ fun d : ℤ ↦ chowGroup C (pullback.fst f g ≫ f) d :=
  DirectSum.toModule ℤ ℤ _ fun n ↦ LinearMap.flip <|
    DirectSum.toModule ℤ ℤ _ fun m ↦ LinearMap.flip <|
      (TensorProduct.mk ℤ (chowGroup C f n) (chowGroup C g m)).compr₂
        (DirectSum.lof ℤ ℤ (fun d : ℤ ↦ chowGroup C (pullback.fst f g ≫ f) d) (n + m) ∘ₗ
          (chowExteriorProduct C hδ f g n m).toIntLinearMap)

/-- On homogeneous classes the total exterior product is the exterior product of Stacks 0FBV,
placed in degree `n + m`. -/
@[simp]
theorem totalChowExteriorProduct_lof_lof {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ) (a : chowGroup C f n)
    (b : chowGroup C g m) :
    totalChowExteriorProduct C hδ f g (DirectSum.lof ℤ ℤ _ n a) (DirectSum.lof ℤ ℤ _ m b) =
      DirectSum.lof ℤ ℤ (fun d : ℤ ↦ chowGroup C (pullback.fst f g ≫ f) d) (n + m)
        (chowExteriorProduct C hδ f g n m (TensorProduct.tmul ℤ a b)) := by
  simp only [totalChowExteriorProduct, DirectSum.toModule_lof, LinearMap.flip_apply,
    LinearMap.compr₂_apply, TensorProduct.mk_apply]
  rfl

/-- Pushforward of total Chow groups along an isomorphism over the base, degree by degree. -/
def totalChowPushforwardOfIso {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ⟶ B) [IsIso e] (he : e ≫ sB = sA) :
    (DirectSum ℤ fun d : ℤ ↦ chowGroup C sA d) →ₗ[ℤ] DirectSum ℤ fun d : ℤ ↦ chowGroup C sB d :=
  DirectSum.toModule ℤ ℤ _ fun d ↦
    DirectSum.lof ℤ ℤ (fun d : ℤ ↦ chowGroup C sB d) d ∘ₗ
      (chowPushforwardOfIso C sA sB e he d).toIntLinearMap

omit [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S] in
/-- On a homogeneous class, total pushforward along an isomorphism is the pushforward of
`Stacks.Chow.chowPushforwardOfIso` in the same degree. -/
@[simp]
theorem totalChowPushforwardOfIso_lof {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ⟶ B) [IsIso e] (he : e ≫ sB = sA) (d : ℤ)
    (a : chowGroup C sA d) :
    totalChowPushforwardOfIso C sA sB e he (DirectSum.lof ℤ ℤ _ d a) =
      DirectSum.lof ℤ ℤ (fun d : ℤ ↦ chowGroup C sB d) d
        (chowPushforwardOfIso C sA sB e he d a) := by
  simp [totalChowPushforwardOfIso, DirectSum.toModule_lof]

end Total

/-- Reading a class in an equal degree does not change its image in the total Chow group. -/
theorem lof_chowGroupDegreeEquiv (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {d e : ℤ} (hde : d = e) (a : chowGroup C sX d) :
    DirectSum.lof ℤ ℤ (fun j : ℤ ↦ chowGroup C sX j) e (chowGroupDegreeEquiv C sX hde a) =
      DirectSum.lof ℤ ℤ (fun j : ℤ ↦ chowGroup C sX j) d a := by
  subst hde
  rfl

/-- **Stacks 0FBZ.** Exterior product is associative. Let `k` be a field, let `X`, `Y`, `Z` be
schemes locally of finite type over `k`, and let `α ∈ CH_*(X)`, `β ∈ CH_*(Y)`, `γ ∈ CH_*(Z)`.
Then `(α × β) × γ = α × (β × γ)` in `CH_*(X ×_k Y ×_k Z)`, the left-hand side being carried
from `(X ×_k Y) ×_k Z` to `X ×_k (Y ×_k Z)` by pushforward along the associator of the fibre
product. -/
@[stacks 0FBZ]
theorem totalChowExteriorProduct_assoc (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (h : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType h]
    (α : DirectSum ℤ fun n : ℤ ↦ chowGroup (fieldChowSituation k) f n)
    (β : DirectSum ℤ fun m : ℤ ↦ chowGroup (fieldChowSituation k) g m)
    (γ : DirectSum ℤ fun l : ℤ ↦ chowGroup (fieldChowSituation k) h l) :
    totalChowPushforwardOfIso (fieldChowSituation k)
        (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
        (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleProductAssoc f g h).hom
        (tripleProductAssoc_hom_comp_base f g h)
        (totalChowExteriorProduct (fieldChowSituation k) (dimensionFunction_eq_zero_of_isClosed k)
          (pullback.fst f g ≫ f) h
          (totalChowExteriorProduct (fieldChowSituation k)
            (dimensionFunction_eq_zero_of_isClosed k) f g α β) γ) =
      totalChowExteriorProduct (fieldChowSituation k) (dimensionFunction_eq_zero_of_isClosed k) f
        (pullback.fst g h ≫ g) α
        (totalChowExteriorProduct (fieldChowSituation k)
          (dimensionFunction_eq_zero_of_isClosed k) g h β γ) := by
  induction α using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | of n a =>
    induction β using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | of m b =>
      induction γ using DirectSum.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | of l c =>
        simp only [← DirectSum.lof_eq_of ℤ, totalChowExteriorProduct_lof_lof,
          totalChowPushforwardOfIso_lof]
        rw [← chowExteriorProduct_assoc_of_field k f g h n m l a b c, lof_chowGroupDegreeEquiv]

end Stacks.Chow

end
