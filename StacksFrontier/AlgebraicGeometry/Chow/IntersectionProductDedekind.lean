module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRule
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalThroughBase
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.RespectsRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariantIdentification
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindCapCommute
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductRegularImmersion

/-!
# Intersection products over a Dedekind base

Let `(S, δ)` be as in Stacks section 42.63: `S` is locally the spectrum of a Dedekind domain,
`δ = 0` at the closed points and `δ = 1` elsewhere. Let `X` be a scheme over `S` whose diagonal
`Δ : X ⟶ X ×_S X` carries a bivariant class `Δ^!` (for `X` smooth over `S` this is the Gysin
class of Stacks section 42.59), and let `Y ⟶ X`, `Z ⟶ X` be locally of finite type. Stacks
section 42.64 forms the composite

  `CH_n(Y) ⊗_ℤ CH_m(Z) ⟶ CH_{n+m-1}(Y ×_S Z) ⟶ CH_{n+m-1-d}(Y ×_X Z)`,

the first arrow being the exterior product of Stacks 0FC4 and the second the Gysin map of the
diagonal, applied through the identification `Y ×_X Z = (Y ×_S Z) ×_{X ×_S X, Δ} X`. The product
is written `α · β = Δ^!(α × β)`.

**Stacks 0FCB** says that for `X` smooth over `S` and equidimensional of dimension `d` the map
`A^p(X) ⟶ CH_{d-p}(X)`, `c ↦ c ∩ [X]_d`, is an isomorphism, and that it carries composition of
bivariant classes to this product. Its proof factors the map as `c ↦ c ∘ g^*` (Stacks 0FBT)
followed by `c' ↦ c' ∩ [S]_1` (Stacks 0FC5), and reads off from the inverse of the second arrow
that the class `c_α` with `c_α ∩ [S]_1 = α` acts by `β ↦ α × β`; the inverse of the first arrow
then sends `c_α` to the class `β ↦ Δ^!(α × β) = α · β`. This file carries out that computation:
for `c ∈ A^p(X)` it proves `c ∩ β = Θ(c) · β` with `Θ(c) = c ∩ [X]_{e+1}`, and deduces the
second clause `Θ(a · b) = Θ(a) · Θ(b)`.

## Main definitions

* `Stacks.Chow.IsDedekindChowBase.intersectionProduct` — the product
  `CH_n(Y) ⊗_ℤ CH_m(Z) ⟶ CH_{n+m-1-d}(Y ×_X Z)` of Stacks section 42.64, formed with a class `c`
  of the diagonal of degree `d`.
* `Stacks.Chow.IsDedekindChowBase.intersectionProductBilin` — the same product as a `ℤ`-bilinear
  map.

## Main results

* `Stacks.Chow.IsDedekindChowBase.intersectionProduct_apply` — the defining formula
  `α · β = Δ^!(α × β)`.
* `Stacks.Chow.IsDedekindChowBase.cap_id_eq_intersectionProduct`,
  `Stacks.Chow.IsDedekindChowBase.chowCohomologyCap_eq_intersectionProduct` — the action of
  `c ∈ A^p(X)` on `CH_n(X)` is the intersection product with `Θ(c)`: `c ∩ β = Θ(c) · β`.
* `Stacks.Chow.IsDedekindChowBase.chowCohomologyCapFundamentalClass_mulId` — the second clause of
  Stacks 0FCB: `Θ(a · b) = Θ(a) · Θ(b)`.

## Implementation notes

### The product

The product is defined for `Y` and `Z` arbitrary schemes locally of finite type over `X` and for
an arbitrary bivariant class `c ∈ A^d(X ⟶ X ×_S X)`; nothing about `X` is assumed. This is the
shape of `Stacks.Chow.intersectionProduct` over a field, with the exterior product of that
definition replaced by `Stacks.Chow.IsDedekindChowBase.exteriorProductChow`, which lowers the
degree by one: the product lands in degree `n + m - 1 - d`. For `X` smooth of relative dimension
`e` over `S`, equidimensional of dimension `e + 1`, the degree of `Δ^!` is `e`, and
`n + m - 1 - e = n + m - (e + 1)` is the degree of the source.

### The composition clause

As in `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalProduct`, the class of
the diagonal is a class `D` in the presentation of `Stacks.Chow.smoothShiftBackward`, and two of
its properties are hypotheses: `D` commutes with every bivariant class over `X ×_S X`
(Stacks 0FBP) and `D ∘ pr₂^* = 1` (Stacks 0FBS). What is assumed of `X` is that it is flat of
relative dimension `e` over `S`, which is what the flat pullback class `g^*` needs, and the degree
of the fundamental class is `e + 1`.

The proof over a field uses that every class towards the point caps as the exterior product with
its value (Stacks 0FBW). Its analogue here is the description of the inverse of the map of
Stacks 0FC5 in its proof: a class `c' ∈ A^q(X ⟶ S)` caps as the exterior product with
`c' ∩ [S]_1 ∈ CH_{1-q}(X)`, in the sense of `Stacks.Chow.IsExteriorProductOverBase`. It is a
hypothesis of the statements below, read at the one degree `q = p - e` at which the proof uses
it. As stated, Stacks 0FCB also admits a base with a zero-dimensional component; there the
exterior product of section 42.63 vanishes identically and the second clause fails, so the
statement this hypothesis is discharged by holds under
`Stacks.Chow.HasNoZeroDimensionalComponent`, and that restriction is part of the correct
statement.

### The order of the product

The product `a · b` of `A^*(X)` is `Stacks.Chow.BivariantClass.mulId`, whose action is
`a ∩ (b ∩ -)`, and it is carried to `Θ(a) · Θ(b)` with `Θ(a)` in the first slot of the exterior
product, as in the proof of the source, which forms `c_α ∩ β = α × β`.

## References

* [Stacks Project, Section 42.64 (Tag 0FC9)](https://stacks.math.columbia.edu/tag/0FC9)
* [Stacks Project, Tag 0FCB](https://stacks.math.columbia.edu/tag/0FCB)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Exterior products over a Dedekind base of heterogeneously equal classes -/

/-- The exterior product `x × y` over a Dedekind base depends on the class `x` only up to
heterogeneous equality: the structure morphism of the first factor and the degree of `x` may be
replaced by equal ones. -/
theorem exteriorProductDedekindChow_heq_of_heq (C : ChowSituation.{u}) {A T : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hA : sA = sA')
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {n n' : ℤ} (hn : n = n') (m : ℤ)
    (hfac : ExteriorProductFactorsThroughRationalEquivalence C sA sT n m)
    (hfac' : ExteriorProductFactorsThroughRationalEquivalence C sA' sT n' m)
    (x : chowGroup C sA n) (x' : chowGroup C sA' n') (hx : x ≍ x') (y : chowGroup C sT m) :
    exteriorProductDedekindChow C sA sT n m hfac x y ≍
      exteriorProductDedekindChow C sA' sT n' m hfac' x' y := by
  subst hA hn
  obtain rfl := eq_of_heq hx
  rfl

namespace IsDedekindChowBase

/-! ### The intersection product of section 42.64 -/

section Product

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) (G : GysinSystem C)
  {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b] (d : ℤ)
  (c : BivariantClass C G sX (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d)
  (n m : ℤ)

/-- **Stacks section 42.64.** The intersection product over a Dedekind base,

  `· : CH_n(Y) ⊗_ℤ CH_m(Z) ⟶ CH_{n+m-1-d}(Y ×_X Z)`,   `α ⊗ β ↦ Δ^!(α × β)`,

for `Y` and `Z` locally of finite type over a scheme `X` whose diagonal carries the bivariant
class `c ∈ A^d(X ⟶ X ×_S X)`. The exterior product is that of Stacks 0FC4,
`Stacks.Chow.IsDedekindChowBase.exteriorProductChow`, landing on `Y ×_S Z` in degree
`n + m - 1`; the cap product with `c` lands on `(Y ×_S Z) ×_{X ×_S X} X`, and the value is pushed
forward along its identification with `Y ×_X Z`. -/
def intersectionProduct :
    TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m) →+
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - 1 - d) :=
  (properChowPushforward C
      (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX)
      (pullback.fst a b ≫ (a ≫ sX)) (pullbackDiagonalMapIdIso a b sX).hom
      (pullbackDiagonalMapIdIso_hom_comp_structure C sX a b) (n + m - 1 - d)
      (properPushforwardDescends C _ _ _ _ _)).comp
    ((c.cap (exteriorToSelfProduct C sX a b) (n + m - 1)).comp
      (((chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sX a b).symm
          (n + m - 1)).toAddMonoidHom).comp
        (hS.exteriorProductChow (a ≫ sX) (b ≫ sX) n m)))

/-- The defining formula of the intersection product over a Dedekind base: it is the Gysin
pullback of the exterior product along the diagonal, carried to `Y ×_X Z`. -/
theorem intersectionProduct_apply
    (t : TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m)) :
    hS.intersectionProduct G sX a b d c n m t =
      properChowPushforward C
        (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX)
        (pullback.fst a b ≫ (a ≫ sX)) (pullbackDiagonalMapIdIso a b sX).hom
        (pullbackDiagonalMapIdIso_hom_comp_structure C sX a b) (n + m - 1 - d)
        (properPushforwardDescends C _ _ _ _ _)
        (c.cap (exteriorToSelfProduct C sX a b) (n + m - 1)
          (chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sX a b).symm
            (n + m - 1) (hS.exteriorProductChow (a ≫ sX) (b ≫ sX) n m t))) :=
  rfl

/-- The intersection product over a Dedekind base as a `ℤ`-bilinear map
`CH_n(Y) → CH_m(Z) → CH_{n+m-1-d}(Y ×_X Z)`. -/
def intersectionProductBilin :
    chowGroup C (a ≫ sX) n →ₗ[ℤ] chowGroup C (b ≫ sX) m →ₗ[ℤ]
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - 1 - d) :=
  TensorProduct.curry (hS.intersectionProduct G sX a b d c n m).toIntLinearMap

/-- The bilinear form of the product agrees with the product on a pure tensor. -/
theorem intersectionProductBilin_apply
    (α : chowGroup C (a ≫ sX) n) (β : chowGroup C (b ≫ sX) m) :
    hS.intersectionProductBilin G sX a b d c n m α β =
      hS.intersectionProduct G sX a b d c n m (α ⊗ₜ[ℤ] β) :=
  rfl

end Product

/-! ### The action of `A^*(X)` on `CH_*(X)` is the intersection product -/

section Action

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) {X : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX] (e : ℕ)
  (he : AlgebraicGeometry.RelativeDimension sX e)
  (D : BivariantClass C (gysinSystemOfInvertible C)
    (pullback.diagonal sX ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX)
    (pullback.diagonal sX) rfl e)

/-- **The cap product of `A^p(X)` is the intersection product with the value on `[X]_{e+1}`, on
`X ×_X X`.** Let `X` be flat of relative dimension `e` over a base as in section 42.63, let
`D ∈ A^e(X ⟶ X ×_S X)` be a class of the diagonal which commutes with every bivariant class over
`X ×_S X` and satisfies `D ∘ pr₂^* = 1`, and suppose every `c' ∈ A^{p-e}(X ⟶ S)` caps as the
exterior product with `c' ∩ [S]_1` (`hrep`). Then for `c ∈ A^p(X)` and `β ∈ CH_n(X)`

  `c ∩ β = (c ∩ [X]_{e+1}) · β`,

the intersection product of section 42.64 formed with `Δ^! = D`, both sides read on `X ×_X X`.

By Stacks 0FBT `c` is `res(D) ∘ res(c ∘ g^*)`
(`Stacks.Chow.smoothShiftBackward_smoothShiftForward`), and `c ∘ g^*` caps as the exterior
product with its value `c ∩ [X]_{e+1}` on `[S]_1`
(`Stacks.Chow.chowCohomologyCapFundamentalClass_eq_bivariantCapBaseFundamentalClass` and
`hrep`), so `c ∩ β = D ∩ ((c ∩ [X]_{e+1}) × β)`, which is the intersection product. -/
theorem cap_id_eq_intersectionProduct
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback sX sX) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass C (gysinSystemOfInvertible C)
        (f₂ ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX) f₂ rfl p₂),
      BivariantCommute C (gysinSystemOfInvertible C)
        (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) f₂ e p₂ D c₂)
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd sX sX)
      (smoothShift_pullback_snd_comp_structureMorphism C sX
        (𝟙 C.S) sX (Category.comp_id sX)) (pullback.diagonal_snd sX)
      (relativeDimension_pullback_snd sX sX e he))
    (p : ℤ)
    (hrep : ∀ c' : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX
        (Category.comp_id sX) (p + -(e : ℤ)),
      IsExteriorProductOverBase C (gysinSystemOfInvertible C) sX (1 - (p + -(e : ℤ)))
        (p + -(e : ℤ))
        (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX (p + -(e : ℤ)) c')
        c')
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (n : ℤ) (β : chowGroup C (𝟙 X ≫ sX) n) :
    c.cap (𝟙 X) n β =
      chowGroupDegreeEquiv C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX)
        (by ring : ((e : ℤ) + 1 - p) + n - 1 - e = n - p)
        (chowGroupCongr C (by rw [Category.id_comp]) _
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX (𝟙 X) (𝟙 X) e
            (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure C sX) rfl e D)
            ((e : ℤ) + 1 - p) n
            (chowGroupCongr C (Category.id_comp sX).symm ((e : ℤ) + 1 - p)
              (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p c)
              ⊗ₜ[ℤ] β))) := by
  have hback := smoothShiftBackward_smoothShiftForward C sX sX
    (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX) (Category.comp_id sX) e he p D
    hcomm hD₂ c
  have H1 := smoothShiftBackward_cap C sX sX (𝟙 C.S)
    (𝟙 X) sX (Category.id_comp sX) (Category.comp_id sX) e p D
    (smoothShiftForward C sX sX (𝟙 C.S) (𝟙 X) sX
      (Category.id_comp sX) (Category.comp_id sX) e he p c) (𝟙 X) n β
    (smoothShiftCapIso (𝟙 X) sX (𝟙 X)).hom (by simp) (by simp)
    (by simp [smoothShift_diagonal_testMap_fst_eq_fst_assoc])
  rw [hback] at H1
  refine eq_of_heq (H1.trans ?_)
  refine HEq.trans ?_ ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _)).symm
  refine HEq.trans ?_ (heq_of_eq (hS.intersectionProduct_apply _ sX (𝟙 X) (𝟙 X) _ _ _ _ _).symm)
  rw [properChowPushforward_eq_chowPushforwardOfIso]
  have hΞ : (smoothShiftCapIso (𝟙 X) sX (𝟙 X)).hom =
      (pullbackDiagonalMapIdIso (𝟙 X) (𝟙 X) sX).hom := by
    ext <;> simp
  rw [chowPushforwardOfIso_congr_apply _ _ _ _ _ hΞ _ (by
    simp [← hΞ, smoothShift_diagonal_testMap_fst_eq_fst_assoc])]
  refine chowPushforwardOfIso_heq _ _ _
    (by rw [pullback.diagonal_fst_assoc]) (by rw [Category.id_comp])
    (by ring) ?_
  refine (D.cap_heq_congr _ (by ring) _ _ ?_).trans
    (bivariantClassCongrBase_cap C (gysinSystemOfInvertible C) (pullback.diagonal sX)
      (diagonal_comp_selfProductStructure C sX) rfl e D _ _ _ _ HEq.rfl).symm
  refine (chowGroupCongr_heq _ _ _ _).trans (HEq.trans ?_ (chowGroupCongr_heq _ _ _ _).symm)
  -- the class `c ∘ g^*` towards the base caps as the exterior product with `c ∩ [X]_{e+1}`
  have hcap := hrep (compStructureFlatPullbackClass C sX e he p c) (𝟙 X ≫ sX) n
    (hS.exteriorProductFactorsThroughRationalEquivalence sX (𝟙 X ≫ sX) _ n) β
  have hΘ := chowCohomologyCapFundamentalClass_eq_bivariantCapBaseFundamentalClass C sX e he p
    (hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)) c
  have heval : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX (p + -(e : ℤ))
      (compStructureFlatPullbackClass C sX e he p c) ≍
      chowGroupCongr C (Category.id_comp sX).symm ((e : ℤ) + 1 - p)
        (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p c) := by
    rw [hΘ]
    exact ((chowGroupCongr_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _)).symm
  refine (BivariantClass.congrHom_cap_heq (Category.id_comp sX) (Category.comp_id sX)
    (smoothShiftForward C sX sX (𝟙 C.S) (𝟙 X) sX
      (Category.id_comp sX) (Category.comp_id sX) e he p c) (𝟙 X ≫ sX) n _).symm.trans ?_
  refine hcap.trans ?_
  exact exteriorProductDedekindChow_heq_of_heq C (Category.id_comp sX).symm _ (by ring) n _ _
    _ _ heval β

/-- **The action of `A^p(X)` on `CH_*(X)` is the intersection product with the value on
`[X]_{e+1}`.** Under the hypotheses of
`Stacks.Chow.IsDedekindChowBase.cap_id_eq_intersectionProduct`, for `c ∈ A^p(X)` and
`β ∈ CH_n(X)`

  `c ∩ β = (c ∩ [X]_{e+1}) · β`   in   `CH_{n-p}(X)`,

the intersection product of section 42.64 being formed with `Δ^! = D` and read on `X` through
the collapse of `X ×_X X`, and the degrees `((e + 1) - p) + n - 1 - e` and `n - p` being
matched. -/
theorem chowCohomologyCap_eq_intersectionProduct
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback sX sX) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass C (gysinSystemOfInvertible C)
        (f₂ ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX) f₂ rfl p₂),
      BivariantCommute C (gysinSystemOfInvertible C)
        (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) f₂ e p₂ D c₂)
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd sX sX)
      (smoothShift_pullback_snd_comp_structureMorphism C sX
        (𝟙 C.S) sX (Category.comp_id sX)) (pullback.diagonal_snd sX)
      (relativeDimension_pullback_snd sX sX e he))
    (p : ℤ)
    (hrep : ∀ c' : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX
        (Category.comp_id sX) (p + -(e : ℤ)),
      IsExteriorProductOverBase C (gysinSystemOfInvertible C) sX (1 - (p + -(e : ℤ)))
        (p + -(e : ℤ))
        (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX (p + -(e : ℤ)) c')
        c')
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (n : ℤ) (β : chowGroup C sX n) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX p c n β =
      chowGroupDegreeEquiv C sX (by ring : ((e : ℤ) + 1 - p) + n - 1 - e = n - p)
        (chowGroupSelfProductUnitCollapse C sX (((e : ℤ) + 1 - p) + n - 1 - e)
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX (𝟙 X) (𝟙 X) e
            (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure C sX) rfl e D)
            ((e : ℤ) + 1 - p) n
            (chowGroupCongr C (Category.id_comp sX).symm ((e : ℤ) + 1 - p)
              (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p c)
              ⊗ₜ[ℤ] chowGroupCongr C (Category.id_comp sX).symm n β))) := by
  simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
  rw [hS.cap_id_eq_intersectionProduct sX e he D hcomm hD₂ p hrep c n]
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  rw [chowGroupSelfProductUnitCollapse, chowGroupEquivOfIso_apply]
  exact chowPushforwardOfIso_heq _ _ _ (by rw [Category.id_comp]) rfl (by ring)
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _))

/-- **Stacks 0FCB, second clause: composition of bivariant classes is the intersection
product.** Let `X` be flat of relative dimension `e` over a base as in section 42.63, let
`D ∈ A^e(X ⟶ X ×_S X)` be a class of the diagonal which commutes with every bivariant class over
`X ×_S X` and satisfies `D ∘ pr₂^* = 1`, and suppose every `c' ∈ A^{p-e}(X ⟶ S)` caps as the
exterior product with `c' ∩ [S]_1` (`hrep`). Then the map `Θ : A^p(X) ⟶ CH_{(e+1)-p}(X)`,
`c ↦ c ∩ [X]_{e+1}`, carries the product `a · b` of `A^*(X)` (the composite of Stacks 0B75, whose
action is `a ∩ (b ∩ -)`) to the intersection product of section 42.64 formed with `Δ^! = D`:

  `Θ(a · b) = Θ(a) · Θ(b)`   in   `CH_{(e+1)-(p+q)}(X)`.

Indeed `Θ(a · b) = a ∩ (b ∩ [X]_{e+1}) = a ∩ Θ(b)`, which is `Θ(a) · Θ(b)` by
`Stacks.Chow.IsDedekindChowBase.chowCohomologyCap_eq_intersectionProduct`. Only the degree `p`
of `a` enters `hrep`. -/
theorem chowCohomologyCapFundamentalClass_mulId
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback sX sX) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass C (gysinSystemOfInvertible C)
        (f₂ ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX) f₂ rfl p₂),
      BivariantCommute C (gysinSystemOfInvertible C)
        (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) f₂ e p₂ D c₂)
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd sX sX)
      (smoothShift_pullback_snd_comp_structureMorphism C sX
        (𝟙 C.S) sX (Category.comp_id sX)) (pullback.diagonal_snd sX)
      (relativeDimension_pullback_snd sX sX e he))
    (p q : ℤ)
    (hrep : ∀ c' : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX
        (Category.comp_id sX) (p + -(e : ℤ)),
      IsExteriorProductOverBase C (gysinSystemOfInvertible C) sX (1 - (p + -(e : ℤ)))
        (p + -(e : ℤ))
        (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX (p + -(e : ℤ)) c')
        c')
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) (p + q)
        (a.mulId C sX b) =
      chowGroupDegreeEquiv C sX
        (by ring : ((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e = (e + 1) - (p + q))
        (chowGroupSelfProductUnitCollapse C sX (((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e)
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX (𝟙 X) (𝟙 X) e
            (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure C sX) rfl e D)
            ((e : ℤ) + 1 - p) ((e : ℤ) + 1 - q)
            (chowGroupCongr C (Category.id_comp sX).symm ((e : ℤ) + 1 - p)
              (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p a)
              ⊗ₜ[ℤ] chowGroupCongr C (Category.id_comp sX).symm ((e : ℤ) + 1 - q)
                (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) q
                  b)))) := by
  have h1 := hS.chowCohomologyCap_eq_intersectionProduct sX e he D hcomm hD₂ p hrep a
    ((e : ℤ) + 1 - q)
    (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) q b)
  refine eq_of_heq (HEq.trans ?_ (((heq_of_eq h1).trans (chowGroupDegreeEquiv_heq _ _ _ _)).trans
    (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  rw [← chowCohomologyCap_fundamentalChowClass, ← chowCohomologyCap_fundamentalChowClass]
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem _ _ sX (p + q) _ (e + 1) _).trans ?_
  refine (BivariantClass.idRule_mulId _ sX a b (𝟙 X) (e + 1) _).trans ?_
  refine HEq.trans ?_ (chowCohomologyCap_heq_idRule_ofGysinSystem _ _ sX p a _ _).symm
  refine IdentityCapRule.heq_congr _ sX _ rfl (by ring) ?_
  exact ((chowCohomologyCap_heq_idRule_ofGysinSystem _ _ sX q b (e + 1) _).symm.trans
    (chowGroupCongr_heq _ _ _ _).symm)

end Action

end IsDedekindChowBase

end Stacks.Chow

end
