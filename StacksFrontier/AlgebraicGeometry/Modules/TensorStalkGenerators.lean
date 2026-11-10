module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk

/-!
# Generators of the stalk of a tensor product of modules on a scheme

Let `X` be a scheme and let `L`, `N` be sheaves of `𝒪_X`-modules. Tag 01CB identifies the stalk
of `L ⊗_{𝒪_X} N` at a point `x` with `L_x ⊗_{𝒪_{X,x}} N_x`, so a pair of elements of `L_x` and
`N_x` has a product in `(L ⊗ N)_x`. This file records the three properties of that product which
the order of vanishing of a meromorphic section is computed from: it is the germ of the pure
tensor of two sections, it commutes with specialization, and the product of two generators of
`L_x` and `N_x` generates `(L ⊗ N)_x` — as a generating set, and as a basis when both factors
are bases.

The two underlying statements of linear algebra are proved first, for a module over a
commutative ring: the span of a pure tensor of two generators is everything, and multiplication
by a pure tensor of two bases of rank-one free modules is bijective.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorObj`: the tensor product `L ⊗_{𝒪_X} N`, read as an
  `𝒪_X`-module in the sense of `AlgebraicGeometry.Scheme.Modules`.
* `AlgebraicGeometry.tensorStalkEquiv`: Tag 01CB for that spelling of the tensor product,
  `(L ⊗_{𝒪_X} N)_x ≅ L_x ⊗_{𝒪_{X,x}} N_x`.
* `AlgebraicGeometry.tensorStalkTmul`: the product in `(L ⊗_{𝒪_X} N)_x` of an element of `L_x`
  and an element of `N_x`.

## Main results

* `TensorProduct.bijective_smul_tmul` and `Submodule.span_singleton_tmul_eq_top`: the two
  statements of linear algebra.
* `AlgebraicGeometry.tensorStalkTmul_germ`: the product of the germs of two sections over `U` is
  the germ of the image of their pure tensor.
* `AlgebraicGeometry.tensorStalkTmul_stalkSpecializes`: the product commutes with specialization.
* `AlgebraicGeometry.span_singleton_tensorStalkTmul_eq_top` and
  `AlgebraicGeometry.isStalkBasis_tensorStalkTmul`: generators multiply to a generator, and
  stalk bases multiply to a stalk basis.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.tensorObj` is a reducible abbreviation for
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.sheaf.obj X.ringCatSheaf.property`,
which is the tensor product the development's invertibility (Tag 01CS) and Picard group (Tag
01CX) are stated for. No second tensor product is introduced: the abbreviation exists because
`AlgebraicGeometry.Scheme.Modules` is a `def` over `SheafOfModules X.ringCatSheaf`, so the field
notation `(… : X.Modules).presheaf` does not resolve on a term whose inferred type is written at
the `SheafOfModules` spelling.

Likewise `AlgebraicGeometry.tensorStalkEquiv` is `PresheafOfModules.tensorSheafStalkEquiv`
restated, and carries no `@[stacks 01CB]` attribute: Tag 01CB is already carried by
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, of which that is itself a
transport. The restatement is needed because the stalks and the local ring in the original are
spelled `TopCat.Presheaf.stalk X.sheaf.obj x`, and mixing that with `X.presheaf.stalk x` — the
spelling the order-of-vanishing API uses — leaves instance search unable to find the module
structure on the tensor product of the stalks.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace TensorProduct

/-- If multiplication by `m` is a bijection `R → M` and multiplication by `n` is a bijection
`R → N`, then multiplication by `m ⊗ n` is a bijection `R → M ⊗[R] N`: both factors are free of
rank one on the given element, hence so is their tensor product on the pure tensor. -/
theorem bijective_smul_tmul {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {m : M} {n : N}
    (hm : Function.Bijective fun r : R => r • m)
    (hn : Function.Bijective fun r : R => r • n) :
    Function.Bijective fun r : R => r • (m ⊗ₜ[R] n) := by
  let eM : R ≃ₗ[R] M := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M m) hm
  let eN : R ≃ₗ[R] N := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R N n) hn
  let e : R ≃ₗ[R] M ⊗[R] N :=
    (TensorProduct.lid R R).symm.trans (TensorProduct.congr eM eN)
  have h1 : eM (1 : R) = m := one_smul R m
  have he : ∀ r : R, e r = r • (m ⊗ₜ[R] n) := by
    intro r
    change TensorProduct.congr eM eN ((TensorProduct.lid R R).symm r) = _
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul, h1]
    exact tmul_smul r m n
  convert e.bijective using 1
  exact funext fun r => (he r).symm

end TensorProduct

namespace Submodule

/-- The pure tensor of a generator of `M` and a generator of `N` generates `M ⊗[R] N`: every
pure tensor is a scalar multiple of it, and pure tensors generate. -/
theorem span_singleton_tmul_eq_top {R : Type*} [CommSemiring R] {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {m : M} {n : N}
    (hm : span R {m} = ⊤) (hn : span R {n} = ⊤) :
    span R {m ⊗ₜ[R] n} = ⊤ := by
  refine eq_top_iff'.2 fun z => ?_
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact add_mem ha hb
  | tmul a b =>
      obtain ⟨r, hr⟩ := mem_span_singleton.1 (eq_top_iff'.1 hm a)
      obtain ⟨s, hs⟩ := mem_span_singleton.1 (eq_top_iff'.1 hn b)
      refine mem_span_singleton.2 ⟨r * s, ?_⟩
      exact (TensorProduct.smul_tmul_smul r s m n).symm.trans (by rw [hr, hs])

end Submodule

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (L N : X.Modules)

/-- The tensor product `L ⊗_{𝒪_X} N` of two `𝒪_X`-modules on a scheme, read as an object of
`AlgebraicGeometry.Scheme.Modules`. This is the tensor product of Tag 01CA that the
invertibility of Tag 01CS is stated for; see the implementation notes. -/
abbrev Scheme.Modules.tensorObj : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj (L)).obj (N))

/-- **Tag 01CB** for `𝒪_X`-modules on a scheme: the stalk at `x` of `L ⊗_{𝒪_X} N` is
`L_x ⊗_{𝒪_{X,x}} N_x`. This is `PresheafOfModules.tensorSheafStalkEquiv` with its stalks
spelled at `X.presheaf`; the attribute stays on the original, see the implementation notes. -/
def tensorStalkEquiv (x : X) :
    (Scheme.Modules.tensorObj L N).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      L.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x :=
  PresheafOfModules.tensorSheafStalkEquiv X.sheaf L N x

/-- The comparison of Tag 01CB carries the germ at `x` of the image of a pure tensor of
sections over `U` to the pure tensor of their germs. -/
theorem tensorStalkEquiv_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (m : L.val.obj (op U)) (n : N.val.obj (op U)) :
    tensorStalkEquiv L N x (PresheafOfModules.tensorSheafGerm X.sheaf L N x U hx m n) =
      L.presheaf.germ U x hx m ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx n :=
  PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm X.sheaf L N x U hx m n

/-- The product in the stalk of `L ⊗_{𝒪_X} N` at `x` of an element of `L_x` and an element of
`N_x`: their pure tensor, read through the comparison of Tag 01CB. -/
def tensorStalkTmul (x : X) (m : L.presheaf.stalk x) (n : N.presheaf.stalk x) :
    (Scheme.Modules.tensorObj L N).presheaf.stalk x :=
  (tensorStalkEquiv L N x).symm (m ⊗ₜ n)

/-- The comparison of Tag 01CB carries the product of two stalk elements to their pure
tensor. -/
theorem tensorStalkEquiv_tensorStalkTmul (x : X) (m : L.presheaf.stalk x)
    (n : N.presheaf.stalk x) :
    tensorStalkEquiv L N x (tensorStalkTmul L N x m n) = m ⊗ₜ[X.presheaf.stalk x] n :=
  (tensorStalkEquiv L N x).apply_symm_apply _

/-- The product of the germs at `x` of two sections over `U` is the germ at `x` of the image of
their pure tensor in `L ⊗_{𝒪_X} N`. -/
theorem tensorStalkTmul_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (m : L.val.obj (op U)) (n : N.val.obj (op U)) :
    tensorStalkTmul L N x (L.presheaf.germ U x hx m) (N.presheaf.germ U x hx n) =
      PresheafOfModules.tensorSheafGerm X.sheaf L N x U hx m n :=
  (tensorStalkEquiv L N x).injective
    ((tensorStalkEquiv_tensorStalkTmul L N x _ _).trans
      (tensorStalkEquiv_germ L N x U hx m n).symm)

/-- The product of two stalk elements is bilinear, in the form the order of vanishing of Tag
02SF needs: scaling the two factors by `a` and `b` scales the product by `a * b`. -/
theorem tensorStalkTmul_smul_smul (x : X) (a b : X.presheaf.stalk x)
    (m : L.presheaf.stalk x) (n : N.presheaf.stalk x) :
    tensorStalkTmul L N x (a • m) (b • n) = (a * b) • tensorStalkTmul L N x m n := by
  change (tensorStalkEquiv L N x).symm ((a • m) ⊗ₜ (b • n)) = _
  rw [TensorProduct.smul_tmul_smul]
  exact map_smul (tensorStalkEquiv L N x).symm (a * b) _

/-- Restricting a section `p0` over `U` to `W ≤ U` does not change the germ at `y ∈ W`, and the
specialization to `x ⤳ y` of that germ is the germ at `x` of the restriction. -/
private theorem germ_res_eq_and_stalkSpecializes_eq {P : X.Modules} {x y : X}
    (h : x ⤳ y) {U W : X.Opens} (hyW : y ∈ W) (hxW : x ∈ W) (i : W ⟶ U) (p0 : P.val.obj (op U))
    {p : P.presheaf.stalk y} (hp : P.presheaf.germ U y (leOfHom i hyW) p0 = p) :
    P.presheaf.germ W y hyW (P.presheaf.map i.op p0) = p ∧
      P.presheaf.stalkSpecializes h p = P.presheaf.germ W x hxW (P.presheaf.map i.op p0) := by
  have hg : P.presheaf.germ W y hyW (P.presheaf.map i.op p0) = p :=
    (P.presheaf.germ_res_apply i y hyW p0).trans hp
  exact ⟨hg, (congrArg (P.presheaf.stalkSpecializes h) hg.symm).trans
    (TopCat.Presheaf.germ_stalkSpecializes_apply ..)⟩

/-- **The product of two stalk elements commutes with specialization.** Both sides are the germ
at `x` of the image of one pure tensor of sections over a neighbourhood of `y`. -/
theorem tensorStalkTmul_stalkSpecializes {x y : X} (h : x ⤳ y) (m : L.presheaf.stalk y)
    (n : N.presheaf.stalk y) :
    tensorStalkTmul L N x (L.presheaf.stalkSpecializes h m) (N.presheaf.stalkSpecializes h n) =
      (Scheme.Modules.tensorObj L N).presheaf.stalkSpecializes h
        (tensorStalkTmul L N y m n) := by
  obtain ⟨U, hyU, m0, hm0⟩ := L.presheaf.exists_germ_eq m
  obtain ⟨V, hyV, n0, hn0⟩ := N.presheaf.exists_germ_eq n
  have hyW : y ∈ U ⊓ V := ⟨hyU, hyV⟩
  have hxW : x ∈ U ⊓ V := h.mem_open (U ⊓ V).isOpen hyW
  set m1 := L.presheaf.map (homOfLE (inf_le_left (a := U) (b := V))).op m0
  set n1 := N.presheaf.map (homOfLE (inf_le_right (a := U) (b := V))).op n0
  obtain ⟨hgm, hsm⟩ := germ_res_eq_and_stalkSpecializes_eq h hyW hxW (homOfLE inf_le_left) m0 hm0
  obtain ⟨hgn, hsn⟩ := germ_res_eq_and_stalkSpecializes_eq h hyW hxW (homOfLE inf_le_right) n0 hn0
  have hL : tensorStalkTmul L N x (L.presheaf.stalkSpecializes h m)
        (N.presheaf.stalkSpecializes h n) =
      PresheafOfModules.tensorSheafGerm X.sheaf L N x (U ⊓ V) hxW m1 n1 :=
    (congrArg₂ (tensorStalkTmul L N x) hsm hsn).trans
      (tensorStalkTmul_germ L N x (U ⊓ V) hxW m1 n1)
  have hR : tensorStalkTmul L N y m n =
      PresheafOfModules.tensorSheafGerm X.sheaf L N y (U ⊓ V) hyW m1 n1 :=
    (congrArg₂ (tensorStalkTmul L N y) hgm.symm hgn.symm).trans
      (tensorStalkTmul_germ L N y (U ⊓ V) hyW m1 n1)
  refine hL.trans (Eq.trans ?_ (congrArg
    ((Scheme.Modules.tensorObj L N).presheaf.stalkSpecializes h) hR.symm))
  exact (TopCat.Presheaf.germ_stalkSpecializes_apply ..).symm

/-- **Generator times generator generates.** If `m` generates `L_x` and `n` generates `N_x`
over the local ring at `x`, then their product generates the stalk of `L ⊗_{𝒪_X} N` at `x`. This
is the generation statement the order of vanishing of Tag 02SF is read against. -/
theorem span_singleton_tensorStalkTmul_eq_top (x : X) {m : L.presheaf.stalk x}
    {n : N.presheaf.stalk x}
    (hm : Submodule.span (X.presheaf.stalk x) {m} = ⊤)
    (hn : Submodule.span (X.presheaf.stalk x) {n} = ⊤) :
    Submodule.span (X.presheaf.stalk x) {tensorStalkTmul L N x m n} = ⊤ := by
  have hmap : Submodule.span (X.presheaf.stalk x) {tensorStalkTmul L N x m n} =
      Submodule.map (tensorStalkEquiv L N x).symm.toLinearMap
        (Submodule.span (X.presheaf.stalk x) {m ⊗ₜ[X.presheaf.stalk x] n}) := by
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  rw [hmap, Submodule.span_singleton_tmul_eq_top hm hn]
  simp

/-- **Basis times basis is a basis.** The product of a stalk basis of `L` at `x` and a stalk
basis of `N` at `x` is a stalk basis of `L ⊗_{𝒪_X} N` at `x`. -/
theorem isStalkBasis_tensorStalkTmul (x : X) {m : L.presheaf.stalk x}
    {n : N.presheaf.stalk x} (hm : Stacks.Divisors.IsStalkBasis L x m)
    (hn : Stacks.Divisors.IsStalkBasis N x n) :
    Stacks.Divisors.IsStalkBasis (Scheme.Modules.tensorObj L N) x
      (tensorStalkTmul L N x m n) := by
  have hfun : (fun r : X.presheaf.stalk x => r • tensorStalkTmul L N x m n) =
      (tensorStalkEquiv L N x).symm ∘
        fun r : X.presheaf.stalk x => r • (m ⊗ₜ[X.presheaf.stalk x] n) :=
    funext fun r => (map_smul (tensorStalkEquiv L N x).symm r _).symm
  change Function.Bijective fun r : X.presheaf.stalk x => r • tensorStalkTmul L N x m n
  rw [hfun]
  exact (tensorStalkEquiv L N x).symm.bijective.comp
    (TensorProduct.bijective_smul_tmul hm hn)

end AlgebraicGeometry

end
