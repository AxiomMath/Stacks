module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Homology.KunnethDegreeZero
public import StacksFrontier.Homology.Tor.ProductNaturality

/-!
# Morphisms out of the unit of a derived tensor product are spanned by box products

Let `k` be a field and let `K` and `L` be objects of `D(k)` whose cohomology vanishes in
negative degrees. This file proves that the **box products**

`u ⊠ v : k[0] ≅ k[0] ⊗^𝐋_k k[0] ⟶ K ⊗^𝐋_k L`

of morphisms `u : k[0] ⟶ K` and `v : k[0] ⟶ L` span `Hom_{D(k)}(k[0], K ⊗^𝐋_k L)` as a
`k`-module, and indeed that every morphism out of the unit into `K ⊗^𝐋_k L` is a finite **sum** of
box products, with no coefficients. The box product is formed from the right unitor of the derived
tensor product and its functoriality in the two variables, so this is a statement about the
derived tensor product itself.

## The route

The input is the degree-zero Künneth comparison of
`CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero`: over a field, and exactly under
the vanishing of the cohomology of both arguments in negative degrees, the cohomology product of
[Stacks, Tag 068H]

`H⁰(K) ⊗_k H⁰(L) ⟶ H⁰(K ⊗^𝐋_k L)`

is an isomorphism. A surjection out of a tensor product has its target spanned by the images of
the pure tensors (`CochainComplex.Kunneth.span_tmul_image_eq_top`), so `H⁰(K ⊗^𝐋_k L)` is spanned
by the cohomology products of pure tensors: that is
`CochainComplex.Kunneth.span_cohomologyTensorProduct_tmul_eq_top`, the spanning statement at the
level of cohomology modules.

Passing from there to morphisms out of the unit uses two further inputs.

* `DerivedCategory.homologyFromSingleLinearEquiv` — a projective object corepresents cohomology
  on the whole unbounded derived category. At the projective object `k` this is a `k`-linear
  isomorphism `Hom_{D(k)}(k[0], X) ≅ H⁰(X)`, natural in `X`, recorded here as
  `CochainComplex.Kunneth.homologyFromUnitLinearEquiv`.
* `RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective` — the cohomology
  product is natural at a source represented by a K-projective, K-flat complex. The unit complex
  `k[0]` is a single complex of a free module, so it is K-projective
  (`CochainComplex.Kunneth.isKProjective_unitComplex`), and over a field every complex is K-flat
  (`CochainComplex.Kunneth.kFlat_of_field`). The naturality square is therefore available at
  `K = L = k[0]`, which is the only instance of it this argument needs.

Reading that naturality square at the canonical class of `H⁰(k[0])`
(`CochainComplex.Kunneth.unitClass`) turns the cohomology product of the classes of `u` and `v`
into the class of the box product `u ⊠ v`, up to the single scalar relating the class of the
inverse right unitor of `k[0] ⊗^𝐋_k k[0]` to the cohomology product of the canonical class with
itself. That is
`CochainComplex.Kunneth.cohomologyTensorProduct_tmul_eq_smul_unitBox`. The scalar exists because
the morphisms out of the unit of `k[0] ⊗^𝐋_k k[0]` are spanned by the inverse right unitor
(`CochainComplex.Kunneth.span_unitorInv_eq_top`), and it is nonzero because the cohomology product
is injective at the unit and the pure tensor of the canonical class with itself is nonzero
(`CochainComplex.Kunneth.unitClass_tmul_ne_zero`). It is never evaluated.

## Main results

* `CochainComplex.Kunneth.span_tmul_image_eq_top` — a surjective linear map out of a tensor
  product has its target spanned by the images of the pure tensors.
* `CochainComplex.Kunneth.span_cohomologyTensorProduct_tmul_eq_top` — over a field, and under the
  vanishing of the cohomology of `K` and `L` in negative degrees, `H⁰(K ⊗^𝐋_k L)` is spanned by
  the cohomology products of [Stacks, Tag 068H] of pure tensors.
* `CochainComplex.Kunneth.homologyFromUnitLinearEquiv` — the corepresentation
  `Hom_{D(k)}(k[0], X) ≅ H⁰(X)` at the unit of the derived tensor product.
* `CochainComplex.Kunneth.unitBox` — the box product of two morphisms out of the unit.
* `CochainComplex.Kunneth.span_unitBox_eq_top` — **the spanning statement**: the box products
  span `Hom_{D(k)}(k[0], K ⊗^𝐋_k L)`.
* `CochainComplex.Kunneth.unitBox_smul_left` — the box product is `k`-homogeneous in its first
  variable.
* `CochainComplex.Kunneth.exists_sum_unitBox` — the spanning statement on elements: every
  morphism `k[0] ⟶ K ⊗^𝐋_k L` is a finite sum of box products.

## Implementation notes

*What the statement needs, and what it does not.* The hypotheses are exactly those of the
degree-zero Künneth comparison: `k` is a field, and the cohomology of `K` and of `L` vanishes in
negative degrees. No boundedness above, no finite-dimensionality of the cohomology modules and no
perfectness is used anywhere, and none would strengthen the conclusion. Over a field every module
is flat, so the Künneth decomposition carries no `Tor` corrections; and vanishing below degree
zero is what collapses `⨁_{i + j = 0} Hⁱ(K) ⊗ Hʲ(L)` to its single summand `H⁰(K) ⊗ H⁰(L)`,
because `i + j = 0` with `i, j ≥ 0` forces `i = j = 0`. A hypothesis bounding the complexes above
would be inert here: the degree-zero statement cannot see it.

*Why the scalar of `CochainComplex.Kunneth.cohomologyTensorProduct_tmul_eq_smul_unitBox` is left
unevaluated.* Evaluating it would mean comparing the cohomology product of [Stacks, Tag 068H] at
`k[0] ⊗ k[0]` with the right unitor of the derived tensor product through
`CochainComplex.DerivedTensor.DerivedTensorProduct.rightUnitor_comparison`, a normalisation no
statement here requires. Only that the scalar is nonzero is used, and only in one place: it is
what cancels in `CochainComplex.Kunneth.unitBox_smul_left`, which is how the coefficients of
`CochainComplex.Kunneth.span_unitBox_eq_top` are absorbed into the first factors to give the
coefficient-free sums of `CochainComplex.Kunneth.exists_sum_unitBox`. The spanning statement
itself does not need even that: a scalar multiple of a spanning family spans.

*Why the homogeneity of the box product has to be derived.* `CochainComplex.Kunneth.unitBox` is
visibly additive in each variable, but its `k`-homogeneity is not visible: it would follow at once
from the `k`-linearity of
`CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor` in each variable, and the
`CochainComplex.DerivedTensor.DerivedTensorProduct` structure does not carry that — it asks for
exactness, hence additivity, and not for linearity over the base. So
`CochainComplex.Kunneth.unitBox_smul_left` goes the long way round, through the cohomology
product, which is `k`-bilinear by construction.

*Where the box product comes from.* `CochainComplex.Kunneth.unitBox` is built from
`CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso` and the functoriality of
`CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor` in its two variables. It is
therefore the box product of the derived tensor product, not a transport of the cohomology
product along the corepresentation, and that is what makes
`CochainComplex.Kunneth.span_unitBox_eq_top` a statement about `D(k)` rather than a restatement of
`CochainComplex.Kunneth.span_cohomologyTensorProduct_tmul_eq_top`.

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CochainComplex.DerivedTensor RingTheory.TorProducts

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CochainComplex.Kunneth

/-! ### Transporting a spanning set along a surjection -/

/-- **A spanning set carried into the span of `t` by a surjection makes `t` span.** This is the
one transport step every spanning statement below is assembled from. -/
theorem span_eq_top_of_surjective {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) {s : Set M}
    (hs : Submodule.span R s = ⊤) {t : Set N}
    (hst : ∀ x ∈ s, f x ∈ Submodule.span R t) :
    Submodule.span R t = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hle : Submodule.span R s ≤ (Submodule.span R t).comap f := by
    rw [Submodule.span_le]
    exact hst
  exact hle (hs ▸ Submodule.mem_top)

/-- **A surjection out of a tensor product has its target spanned by the images of the pure
tensors.** This is the elementary step that turns an isomorphism whose source is a tensor product
into a spanning statement about its target: the source is spanned by its pure tensors, and
spanning is carried along a surjection. -/
theorem span_tmul_image_eq_top {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    (f : TensorProduct R M N →ₗ[R] P) (hf : Function.Surjective f) :
    Submodule.span R {z : P | ∃ (a : M) (b : N), z = f (a ⊗ₜ[R] b)} = ⊤ := by
  refine span_eq_top_of_surjective f hf (TensorProduct.span_tmul_eq_top R M N) ?_
  rintro x ⟨a, b, rfl⟩
  exact Submodule.subset_span ⟨a, b, rfl⟩

/-- A surjective linear map carries a spanning singleton to a spanning singleton. -/
private theorem span_singleton_image_eq_top {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) {x : M} (hx : Submodule.span R {x} = ⊤) :
    Submodule.span R {f x} = ⊤ := by
  rw [← Set.image_singleton, ← Submodule.map_span, hx, Submodule.map_top,
    LinearMap.range_eq_top.2 hf]

variable {k : Type u} [Field k]

/-! ### The degree-zero Künneth comparison, read as a spanning statement -/

/-- **Over a field the degree-zero cohomology of a derived tensor product is spanned by the
cohomology products of pure tensors.** For `K` and `L` in `D(k)` whose cohomology vanishes in
negative degrees, every element of `H⁰(K ⊗^𝐋_k L)` is a `k`-linear combination of values of the
cohomology product of [Stacks, Tag 068H] on pure tensors `a ⊗ b` with `a ∈ H⁰(K)` and
`b ∈ H⁰(L)`.

This is the spanning consequence of
`CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero`: unlike an abstract isomorphism of
the two cohomology modules it says which elements of the target are hit. -/
theorem span_cohomologyTensorProduct_tmul_eq_top (K L : DObj k)
    (hK : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj K))
    (hL : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj L)) :
    Submodule.span k
        {z : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
            (((canonicalDerivedTensorProductFunctor k).obj K).obj L) |
          ∃ (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj K)
            (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj L),
            z = (cohomologyTensorProduct K L 0 0).map.hom (a ⊗ₜ[k] b)} = ⊤ :=
  have := isIso_cohomologyTensorProduct_map_zero K L hK hL
  span_tmul_image_eq_top _
    ((ConcreteCategory.isIso_iff_bijective (cohomologyTensorProduct K L 0 0).map).1
      inferInstance).2

/-! ### The unit of the derived tensor product corepresents degree-zero cohomology -/

/-- **Degree-zero cohomology of `D(k)` is corepresented by the unit `k[0]` of the derived tensor
product, `k`-linearly.** This is `DerivedCategory.homologyFromSingleLinearEquiv` at the
projective object `k`, composed with the evaluation `Hom_k(k, M) ≅ M`. There is no hypothesis on
`X`. -/
def homologyFromUnitLinearEquiv (X : DObj k) :
    ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ X) ≃ₗ[k]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj X) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of k k) X 0 k).trans
    ((ModuleCat.homLinearEquiv (S := k)).trans (LinearMap.ringLmapEquivSelf k k _))

/-- `CochainComplex.Kunneth.homologyFromUnitLinearEquiv` is natural in its argument: the class of
a composite is the class of the first factor pushed along the second. -/
theorem homologyFromUnitLinearEquiv_comp {X Y : DObj k}
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ X)
    (g : X ⟶ Y) :
    homologyFromUnitLinearEquiv Y (f ≫ g) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map g).hom
        (homologyFromUnitLinearEquiv X f) := by
  change ((DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of k k) Y 0 k)
      (f ≫ g)).hom (1 : k) = _
  rw [DerivedCategory.homologyFromSingleLinearEquiv_comp]
  rfl

/-- The canonical class of `H⁰(k[0])`: the cohomology class of the identity of the unit. -/
def unitClass (k : Type u) [Field k] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) :=
  homologyFromUnitLinearEquiv _ (𝟙 _)

/-- The class of a morphism out of the unit is the canonical class of `H⁰(k[0])` pushed along
it. -/
theorem homologyFromUnitLinearEquiv_apply_eq {X : DObj k}
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ X) :
    homologyFromUnitLinearEquiv X f =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map f).hom (unitClass k) := by
  rw [unitClass, ← homologyFromUnitLinearEquiv_comp, Category.id_comp]

/-- The canonical class of `H⁰(k[0])` is the image of `1` under the canonical identification of
`H⁰(k[0])` with `k`. -/
theorem unitClass_eq (k : Type u) [Field k] :
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} k) 0).inv.app (ModuleCat.of k k)).hom (1 : k) = unitClass k := by
  change _ = ((DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of k k)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) 0 k)
      (𝟙 _)).hom (1 : k)
  rw [DerivedCategory.homologyFromSingleLinearEquiv_apply, CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Functor.comp_obj, Category.comp_id]

/-- The canonical identification of `H⁰(k[0])` with `k` carries the canonical class to `1`. -/
theorem singleFunctorCompHomologyFunctorIso_hom_unitClass (k : Type u) [Field k] :
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} k) 0).hom.app (ModuleCat.of k k)).hom (unitClass k) = (1 : k) := by
  rw [← unitClass_eq]
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ (1 : k))
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} k) 0).inv_hom_id_app (ModuleCat.of k k))
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id,
    LinearMap.id_coe, id_eq] using h

/-- **The pure tensor of the canonical class with itself is nonzero.** `H⁰(k[0])` is `k`, so the
two-fold tensor power is `k` again with the pure tensor of the canonical class corresponding to
`1`. -/
theorem unitClass_tmul_ne_zero (k : Type u) [Field k] :
    (unitClass k ⊗ₜ[k] unitClass k) ≠ 0 := by
  intro hzero
  have h1 : (TensorProduct.lid k k)
      (TensorProduct.map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} k) 0).hom.app (ModuleCat.of k k)).hom
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} k) 0).hom.app (ModuleCat.of k k)).hom
        (unitClass k ⊗ₜ[k] unitClass k)) = (1 : k) := by
    rw [TensorProduct.map_tmul, singleFunctorCompHomologyFunctorIso_hom_unitClass,
      TensorProduct.lid_tmul, smul_eq_mul, mul_one]
  rw [hzero, map_zero, map_zero] at h1
  exact one_ne_zero h1.symm

/-- **The canonical class spans `H⁰(k[0])`.** The degree-zero cohomology of the unit is `k`, with
the canonical class corresponding to `1`. -/
theorem span_unitClass_eq_top : Submodule.span k {unitClass k} = ⊤ := by
  have := span_singleton_image_eq_top
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} k) 0).inv.app (ModuleCat.of k k)).hom
    ((ConcreteCategory.isIso_iff_bijective
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} k) 0).inv.app (ModuleCat.of k k))).1 inferInstance).2
    (x := (1 : k))
    (Submodule.eq_top_iff'.2 fun x => Submodule.mem_span_singleton.2 ⟨x, by simp⟩)
  rwa [unitClass_eq] at this

/-! ### The box product of two morphisms out of the unit -/

/-- **The box product of two morphisms out of the unit of the derived tensor product.** For
`u : k[0] ⟶ K` and `v : k[0] ⟶ L` this is the composite

`k[0] ≅ k[0] ⊗^𝐋_k k[0] ⟶ K ⊗^𝐋_k k[0] ⟶ K ⊗^𝐋_k L`

of the inverse right unitor of the derived tensor product with `u` tensored on the left and `v`
tensored on the right. It is built from the derived tensor product itself, not from the cohomology
product of [Stacks, Tag 068H]. -/
def unitBox {K L : DObj k}
    (u : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ K)
    (v : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ L) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶
      ((canonicalDerivedTensorProductFunctor k).obj K).obj L :=
  (derivedTensorProductRightUnitorIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))).inv ≫
    ((canonicalDerivedTensorProductFunctor k).map u).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) ≫
      ((canonicalDerivedTensorProductFunctor k).obj K).map v

/-- The class of a box product is the class of the inverse right unitor pushed along the two
tensored morphisms. -/
theorem homologyFromUnitLinearEquiv_unitBox {K L : DObj k}
    (u : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ K)
    (v : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ L) :
    homologyFromUnitLinearEquiv _ (unitBox u v) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          (((canonicalDerivedTensorProductFunctor k).map u).app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) ≫
            ((canonicalDerivedTensorProductFunctor k).obj K).map v)).hom
        (homologyFromUnitLinearEquiv _
          (derivedTensorProductRightUnitorIso
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
              (ModuleCat.of k k))).inv) :=
  homologyFromUnitLinearEquiv_comp _ _

/-- The unit complex `k[0]` is K-projective: it is a single complex of a free module. -/
theorem isKProjective_unitComplex (k : Type u) [Field k] :
    ((CochainComplex.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

/-- **The morphisms out of the unit into `k[0] ⊗^𝐋_k k[0]` are spanned by the inverse right
unitor.** This is what makes the scalar of
`CochainComplex.Kunneth.cohomologyTensorProduct_tmul_eq_smul_unitBox` invisible to a spanning
conclusion. -/
theorem span_unitorInv_eq_top :
    Submodule.span k
        {(derivedTensorProductRightUnitorIso
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
              (ModuleCat.of k k))).inv} = ⊤ := by
  -- The identity spans the endomorphisms of the unit, because its class spans `H⁰(k[0])`.
  have hone : Submodule.span k
      {(𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) :
        (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶
          (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))} = ⊤ := by
    have := span_singleton_image_eq_top
      (homologyFromUnitLinearEquiv
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
          (ModuleCat.of k k))).symm.toLinearMap
      (LinearEquiv.surjective _) span_unitClass_eq_top
    rwa [LinearEquiv.coe_coe, unitClass, LinearEquiv.symm_apply_apply] at this
  -- Postcomposing with the inverse right unitor is a surjective linear map.
  have := span_singleton_image_eq_top
    (Linear.rightComp k
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      (derivedTensorProductRightUnitorIso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))).inv)
    (fun f => ⟨f ≫ (derivedTensorProductRightUnitorIso _).hom, by
      change (f ≫ (derivedTensorProductRightUnitorIso _).hom) ≫
        (derivedTensorProductRightUnitorIso _).inv = f
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩)
    hone
  rwa [Linear.rightComp_apply, Category.id_comp] at this

/-- **The cohomology product of [Stacks, Tag 068H] on a pure tensor is the class of a box
product, up to one scalar.** The scalar relates the class of the inverse right unitor of
`k[0] ⊗^𝐋_k k[0]` to the cohomology product of the canonical class of `H⁰(k[0])` with itself; it
does not depend on `u` or `v`.

The proof is the naturality square of
`RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective`, available at the
unit because `k[0]` is K-projective (`CochainComplex.Kunneth.isKProjective_unitComplex`) and
K-flat (`CochainComplex.Kunneth.kFlat_of_field`), read at the canonical class. -/
theorem cohomologyTensorProduct_tmul_eq_smul_unitBox (K L : DObj k) :
    ∃ c : k, c ≠ 0 ∧ ∀ (u : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
            (ModuleCat.of k k) ⟶ K)
        (v : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
            (ModuleCat.of k k) ⟶ L),
      (cohomologyTensorProduct K L 0 0).map.hom
          (homologyFromUnitLinearEquiv K u ⊗ₜ[k] homologyFromUnitLinearEquiv L v) =
        c • homologyFromUnitLinearEquiv _ (unitBox u v) := by
  -- The cohomology product of the canonical class with itself is a multiple of the class of the
  -- inverse right unitor, because that class spans.
  have hspan : Submodule.span k
      {homologyFromUnitLinearEquiv
        (((canonicalDerivedTensorProductFunctor k).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)))
        (derivedTensorProductRightUnitorIso
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
            (ModuleCat.of k k))).inv} = ⊤ := by
    exact span_singleton_image_eq_top
      (homologyFromUnitLinearEquiv
        (((canonicalDerivedTensorProductFunctor k).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
            (ModuleCat.of k k)))).toLinearMap
      (LinearEquiv.surjective _) span_unitorInv_eq_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hspan ▸ Submodule.mem_top (x := (cohomologyTensorProduct
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      0 0).map.hom (unitClass k ⊗ₜ[k] unitClass k)))
  -- The scalar is nonzero: the cohomology product at the unit is injective and the pure tensor
  -- of the canonical class with itself is nonzero.
  have hinj : Function.Injective (cohomologyTensorProduct
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      0 0).map.hom :=
    have := isIso_cohomologyTensorProduct_map_zero
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      (fun i hi => DerivedCategory.isZero_of_isGE _ 0 i hi)
      (fun i hi => DerivedCategory.isZero_of_isGE _ 0 i hi)
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    refine unitClass_tmul_ne_zero k (hinj ?_)
    rw [← hc, map_zero]
  refine ⟨c, hcne, fun u v => ?_⟩
  have hkproj := isKProjective_unitComplex k
  -- The naturality square at the unit, with the degree written `0` rather than `0 + 0`.
  have hnat : ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map u ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map v) ≫
        (cohomologyTensorProduct K L 0 0).map =
      (cohomologyTensorProduct
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
          0 0).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          (((canonicalDerivedTensorProductFunctor k).map u).app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) ≫
            ((canonicalDerivedTensorProductFunctor k).obj K).map v) :=
    cohomologyTensorProduct_naturality_of_isKProjective
      ((CochainComplex.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      ((CochainComplex.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      (kFlat_of_field _) (kFlat_of_field _) u v 0 0
  have hel : (cohomologyTensorProduct K L 0 0).map.hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map u).hom (unitClass k) ⊗ₜ[k]
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map v).hom (unitClass k)) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          (((canonicalDerivedTensorProductFunctor k).map u).app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) ≫
            ((canonicalDerivedTensorProductFunctor k).obj K).map v)).hom
        ((cohomologyTensorProduct
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
            0 0).map.hom (unitClass k ⊗ₜ[k] unitClass k)) := by
    have h := congrArg
      (fun φ => ModuleCat.Hom.hom φ (unitClass k ⊗ₜ[k] unitClass k)) hnat
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul] using h
  rw [homologyFromUnitLinearEquiv_apply_eq u, homologyFromUnitLinearEquiv_apply_eq v, hel, ← hc,
    map_smul, homologyFromUnitLinearEquiv_unitBox]

/-! ### The spanning statement -/

/-- **Morphisms out of the unit into a derived tensor product over a field are spanned by box
products.** For `k` a field and `K`, `L` objects of `D(k)` whose cohomology vanishes in negative
degrees, the `k`-module `Hom_{D(k)}(k[0], K ⊗^𝐋_k L)` is spanned by the box products
`CochainComplex.Kunneth.unitBox u v` with `u : k[0] ⟶ K` and `v : k[0] ⟶ L`.

This is the conclusion the degree-zero Künneth comparison is for: an isomorphism of the two
cohomology modules says only that every morphism is hit by some element of the source, whereas
this says that every morphism is a `k`-linear combination of box products. -/
theorem span_unitBox_eq_top (K L : DObj k)
    (hK : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj K))
    (hL : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj L)) :
    Submodule.span k
        {f : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶
            ((canonicalDerivedTensorProductFunctor k).obj K).obj L |
          ∃ u v, f = unitBox u v} = ⊤ := by
  obtain ⟨c, -, hc⟩ := cohomologyTensorProduct_tmul_eq_smul_unitBox K L
  refine span_eq_top_of_surjective
    ((homologyFromUnitLinearEquiv
      (((canonicalDerivedTensorProductFunctor k).obj K).obj L)).symm.toLinearMap)
    (LinearEquiv.surjective _)
    (span_cohomologyTensorProduct_tmul_eq_top K L hK hL) ?_
  rintro x ⟨a, b, rfl⟩
  obtain ⟨u, hu⟩ := (homologyFromUnitLinearEquiv K).surjective a
  obtain ⟨v, hv⟩ := (homologyFromUnitLinearEquiv L).surjective b
  rw [LinearEquiv.coe_coe, ← hu, ← hv, hc u v, LinearEquiv.map_smul,
    LinearEquiv.symm_apply_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, v, rfl⟩)

/-- **The box product is `k`-homogeneous in its first variable.** This does not come from any
linearity of the derived tensor product over `k` — the
`CochainComplex.DerivedTensor.DerivedTensorProduct` structure asks only for exactness — but from
`CochainComplex.Kunneth.cohomologyTensorProduct_tmul_eq_smul_unitBox` with its nonzero scalar
cancelled, the cohomology product being `k`-bilinear and the corepresentation `k`-linear. -/
theorem unitBox_smul_left {K L : DObj k} (a : k)
    (u : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ K)
    (v : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶ L) :
    unitBox (a • u) v = a • unitBox u v := by
  obtain ⟨c, hcne, hc⟩ := cohomologyTensorProduct_tmul_eq_smul_unitBox K L
  refine (homologyFromUnitLinearEquiv
    (((canonicalDerivedTensorProductFunctor k).obj K).obj L)).injective ?_
  refine smul_right_injective _ hcne ?_
  change c • homologyFromUnitLinearEquiv _ (unitBox (a • u) v) =
    c • homologyFromUnitLinearEquiv _ (a • unitBox u v)
  rw [← hc (a • u) v, LinearEquiv.map_smul, ← TensorProduct.smul_tmul', map_smul, hc u v,
    LinearEquiv.map_smul, smul_comm]

/-- **Every morphism out of the unit into a derived tensor product over a field is a finite sum
of box products.** The element-level form of
`CochainComplex.Kunneth.span_unitBox_eq_top`: the coefficients of the linear combination are
absorbed into the first factors by
`CochainComplex.Kunneth.unitBox_smul_left`, so no scalars survive. -/
theorem exists_sum_unitBox (K L : DObj k)
    (hK : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj K))
    (hL : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj L))
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) ⟶
      ((canonicalDerivedTensorProductFunctor k).obj K).obj L) :
    ∃ (n : ℕ)
      (u : Fin n → ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
        (ModuleCat.of k k) ⟶ K))
      (v : Fin n → ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
        (ModuleCat.of k k) ⟶ L)),
      f = ∑ i, unitBox (u i) (v i) := by
  classical
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1
    ((span_unitBox_eq_top K L hK hL) ▸ Submodule.mem_top (x := f))
  choose u v huv using fun i : Fin n => (g i).2
  refine ⟨n, fun i => c i • u i, v, ?_⟩
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => by rw [unitBox_smul_left, huv i]

end CochainComplex.Kunneth

end
