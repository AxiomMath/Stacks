module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeExt
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Kunneth
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.PerfectProperSmooth
import StacksCore.Tactic.StacksAttribute

/-!
# The transformed resolution of the diagonal in Situation [Stacks, Tag 0G08]

Let `k` be a field, let `X` and `Y` be schemes proper and smooth over `k`, let
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` be a `k`-linear exact fully faithful functor, and let

`… → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0`

be a resolution of the diagonal of `X` by external tensor products of finite locally free
modules. That is Situation [Stacks, Tag 0G08], and
`AlgebraicGeometry.exists_kunnethComplex_of_tensorPairings` states there the conclusion of
[Stacks, Tag 0G0A]: the complex

`… → ℰ₂ ⊠ F(𝒢₂) → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)`

on `X ×_k Y`, with the differentials of the resolution read through an identification of Hom
groups carrying each pure map `a ⊠ b` to `a ⊠ F(b)`.

`AlgebraicGeometry.DiagonalResolution.kunnethComplex` of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Kunneth` builds that complex
from three inputs, `hbox`, `himage` and `hker`. What this file contributes is that **`hker` is
not an input**: at the hypotheses of [Stacks, Tag 0G08] it follows from the other two, once
those are stated in the canonical Künneth shape. So the complex rests on one statement, taken
at each of the two products, and nothing else.

## The shape of the Künneth input

`AlgebraicGeometry.IsTensorPairing` says of a pairing of two `k`-modules `M` and `N`, extended
additively to formal integral combinations of pairs, that it is surjective and that its kernel
is exactly the subgroup of `k`-bilinearity relations — equivalently, that the induced `k`-linear
map `M ⊗_k N ⟶ P` is bijective. Taking `M` and `N` to be the Hom groups of the two families of
factors, that is the Künneth formula for Ext of [Stacks, Tag 0FXZ] in degree `q = 0`.

It is phrased through `FreeAbelianGroup` rather than as the bijectivity of a map out of
`M ⊗_k N` because the library does not construct that map: doing so needs the
bi-`k`-linearity of `⊠` on morphisms, where the available
`AlgebraicGeometry.externalTensorProductMap_add_left` and its companions give only
bi-additivity. The two formulations are equivalent, and the one used here is the one the
existing `hbox` and `himage` already have, strengthened by the kernel clause.

## Why `hker` is the clause that can be discharged

The implementation notes of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Kunneth` record that no two
of `hbox`, `himage` and `hker` imply the third: surjectivity with a known kernel on one side
gives, through a common kernel, an injection into the other side and no more. That is right about
the three as stated. What changes here is that each Künneth input is strengthened from
"surjective" to "surjective with the bilinearity relations for its kernel", at which point both
kernels are *named* — each is the kernel of
`AlgebraicGeometry.freeAbelianGroupToTensor` — and the comparison becomes a statement about the
two subgroups of relations rather than about the two Hom groups.

Those two subgroups correspond because the pairings differ only by reindexing the second factor
along `Hom(𝒢ᵢ, 𝒢ⱼ) ≃ Hom(F(𝒢ᵢ), F(𝒢ⱼ))`, and that bijection is `k`-linear:
`AlgebraicGeometry.DiagonalResolution.secondFactorLinearEquiv` upgrades
`AlgebraicGeometry.DiagonalResolution.secondFactorHomEquiv` to a `k`-linear equivalence. Its
three steps are each `k`-linear — `DerivedCategory.singleFunctor` is a `k`-linear functor,
`CategoryTheory.ObjectProperty.homMk` is the identity on the underlying `k`-module of a Hom
group of a full subcategory, and `F` is `k`-linear by hypothesis — and the middle one is what
the notes of `…TransformedDiagonal.Kunneth` list as missing, "nothing records that
`CategoryTheory.ObjectProperty.homMk` is additive". Reindexing by a `k`-linear equivalence is
`M ⊗ e` on the tensor product, hence injective, so it carries one subgroup of relations exactly
onto the other.

This is also where the `k`-linearity of `F` of [Stacks, Tag 0G08] is consumed, and consumed
unavoidably: the notes of `…TransformedDiagonal.Kunneth` exhibit a formal combination,
`(a • a', b) - (a', a • b)`, that lies in the kernel of the box pairing for every `F` and in the
kernel of the transformed pairing only when `F(a • b) = a • F(b)`.

## Main definitions

* `AlgebraicGeometry.freeAbelianGroupToTensor`: the additive map
  `FreeAbelianGroup (M × N) ⟶ M ⊗_k N` sending a generator to a pure tensor. Its kernel is the
  subgroup of `k`-bilinearity relations.
* `AlgebraicGeometry.IsTensorPairing`: a pairing exhibits its target as `M ⊗_k N`.
* `AlgebraicGeometry.freeAbelianGroupMapRight`: reindexing the second factor of the pairs along
  a `k`-linear map.
* `AlgebraicGeometry.DiagonalResolution.secondFactorLinearEquiv`: the identification of
  `Hom(𝒢ᵢ, 𝒢ⱼ)` with `Hom(F(𝒢ᵢ), F(𝒢ⱼ))` as `k`-modules.
* `AlgebraicGeometry.DiagonalResolution.kunnethHomDataOfTensorPairings`: the Künneth input of
  `AlgebraicGeometry.DiagonalResolution.KunnethHomData` assembled from the two Künneth
  identifications alone, with the equality of kernels proved.

## Main results

* `AlgebraicGeometry.surjective_freeAbelianGroupToTensor`: the pure tensors span `M ⊗_k N`.
* `AlgebraicGeometry.ker_freeAbelianGroupToTensor_comap`: reindexing the second factor by a
  `k`-linear equivalence does not change the subgroup of bilinearity relations.
* `AlgebraicGeometry.subsingleton_hom_singleFunctor_shift`: there are no negative Exts between
  two objects placed in degree zero.
* `AlgebraicGeometry.DiagonalResolution.subsingleton_hom_map_secondFactor_shift`: exactness and
  full faithfulness of `F` make `Ext^{-p}_Y(F(𝒢ᵢ), F(𝒢ⱼ))` vanish for `p > 0`, which is what
  collapses the source's sum over `p` to its `p = 0` summand.
* `AlgebraicGeometry.DiagonalResolution.transformedPairing_eq_comp`: the transformed pairing is
  the pairing on the images of the second factors, reindexed along
  `AlgebraicGeometry.DiagonalResolution.secondFactorLinearEquiv`.
* `AlgebraicGeometry.exists_kunnethComplex_of_tensorPairings`: **the conclusion of
  [Stacks, Tag 0G0A] in Situation [Stacks, Tag 0G08]**, from the Künneth identification at each
  of the two products.

## Implementation notes

*Which of the two Künneth inputs is available, and where the tag is registered.* The input on
`X ×_k X`, `hbox`, **is** available: it is
`AlgebraicGeometry.DiagonalResolution.isTensorPairing_boxPairing` of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.SituationBoxPairing`, and
`AlgebraicGeometry.exists_kunnethComplex_of_imagePairing` there is
`AlgebraicGeometry.exists_kunnethComplex_of_tensorPairings` with that hypothesis discharged,
carrying the one remaining input and nothing else. No statement carrying a Künneth input is
registered under [Stacks, Tag 0G0A]: the tag sits on the generic declarations of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Basic` and on the statement
at the hypotheses of [Stacks, Tag 0G08] that carries none.

Through the duality of the box product `hbox` is the surjectivity of
`Γ(X, 𝒜) ⊗_k Γ(X, ℬ) ⟶ Γ(X ×_k X, 𝒜 ⊠ ℬ)` for finite locally free `𝒜` and `ℬ`, and the two
things that reduction needs are now both proved: the value of
`AlgebraicGeometry.externalTensorDualTensorHomEquiv` at a pure map `a ⊠ b`, which is
`AlgebraicGeometry.app_externalTensorDualTensorHomEquiv_externalTensorProductMap`, and the global
degree-zero Künneth statement for sections, which is
`AlgebraicGeometry.bijective_globalBoxSectionMap_of_isProper` — the chart-local
`Stacks.FibreProductAffineChart.Chart.boxSectionOfTensor_surjective` glued over a finite affine
covering.

*What the input on `X ×_k Y` would still take.* `himage` is the same canonical statement at the
other product, where the second factor is `F(𝒢ᵢ)` and the Hom groups are those of the derived
category. It is **not** reachable by the route that discharges `hbox`, and not for one reason but
two.

* *The duality route does not run there.* The proof of `hbox` turns a Hom group into a group of
  global sections using that both of its arguments are finite locally free modules in degree
  zero. `F(𝒢ᵢ)` is an arbitrary perfect complex — nothing in [Stacks, Tag 0G08] makes it a module
  — so `AlgebraicGeometry.dualTensorHomLinearEquiv` does not apply to it, and
  `AlgebraicGeometry.bijective_globalBoxSectionMap_of_isProper` is a statement about
  quasi-coherent modules and not about objects of `D(𝒪_Y)`.
* *[Stacks, Tag 0FXZ] as the library has it is about objects, and `himage` is about elements.*
  `Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_fibreProduct` asserts the
  invertibility of `Stacks.Cohomology.DerivedKunnethExt.kunnethExtMap`, a morphism of objects of
  `D(𝒪_S)`; `himage` says which *elements* of a Hom group the pure maps `a ⊠ c` hit. Nothing in
  the library computes `kunnethExtMap` at a pure tensor, so an invertible comparison of the two
  Hom groups does not give the surjectivity clause of `AlgebraicGeometry.IsTensorPairing`, let
  alone its kernel clause. This gap is independent of the model and is the one that is not a
  matter of spelling.

  On top of it there is the model mismatch: `kunnethExtMap` is *defined* under
  `attribute [local instance] CategoryTheory.HasDerivedCategory.standard`
  (`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt`), so the
  standard model's morphism universe is written into the constant's argument types, while
  `AlgebraicGeometry.perfectDerived` takes no `HasDerivedCategory` binder and is therefore pinned
  to the locally small model. There is consequently no statement of [Stacks, Tag 0FXZ] at the
  Hom groups occurring here to prove; making one expressible means turning that local attribute
  into a binder in `…KunnethMapForExt` and in every file the definition is built from, and the
  notes of `…TransformedDiagonal.Kunneth` list what making it *provable* would then take.

What the hypotheses `[F.CommShift ℤ]` and `[F.IsTriangulated]` of [Stacks, Tag 0G08] contribute
here is the additivity of `F`, which `CategoryTheory.Functor.Linear` asks for as a prerequisite.
They do not reduce the Künneth input on `X ×_k Y` to the one on `X ×_k X`: exactness of `F`
collapses the source's sum over `p` to its `p = 0` summand — the vanishing of
`Ext^{-p}_Y(F(𝒢ᵢ), F(𝒢ⱼ))` for `p > 0`, which is
`AlgebraicGeometry.DiagonalResolution.subsingleton_hom_map_secondFactor_shift` above — but the
first equality of that display, the Künneth formula on `X ×_k Y`, is not a consequence of the
Künneth formula on `X ×_k X`.

*Where the smoothness and properness hypotheses go.* Properness of `X` is consumed, in the proof
of `hbox`: `AlgebraicGeometry.bijective_globalBoxSectionMap_of_isProper` spends it twice, once as
quasi-compactness, to make the affine coverings of the two factors finite, and once as
separatedness, to make their pairwise intersections affine. Both uses are load-bearing, and
without the first the statement is false — the notes of `…TransformedDiagonal.Kunneth` exhibit a
resolution of the diagonal of `X = ∐_{n : ℕ} Spec k`, which is not quasi-compact, for which
`hbox` fails because the pure maps span only the morphisms of finite rank. Smoothness is **not**
consumed anywhere, by this file or by `…SituationBoxPairing`; it is carried because the statement
is the one of [Stacks, Tag 0G08], where it is what the section's later lemmas need.

## References

* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.PerfectComplexes

universe u

namespace AlgebraicGeometry

/-! ### Pairings that exhibit a group as a tensor product -/

section TensorPairing

variable (k : Type*) [CommRing k] (M N : Type*) [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

/-- The additive map `FreeAbelianGroup (M × N) ⟶ M ⊗_k N` carrying a formal generator `(m, n)`
to the pure tensor `m ⊗ n`. Its kernel is the subgroup of formal integral combinations of pairs
cut out by the `k`-bilinearity relations, and nothing else. -/
def freeAbelianGroupToTensor : FreeAbelianGroup (M × N) →+ TensorProduct k M N :=
  FreeAbelianGroup.lift fun p => p.1 ⊗ₜ[k] p.2

/-- The map `freeAbelianGroupToTensor` carries the formal generator `(m, n)` to `m ⊗ n`. -/
@[simp]
theorem freeAbelianGroupToTensor_of (p : M × N) :
    freeAbelianGroupToTensor k M N (FreeAbelianGroup.of p) = p.1 ⊗ₜ[k] p.2 :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **Every element of `M ⊗_k N` is a formal integral combination of pure tensors.** -/
theorem surjective_freeAbelianGroupToTensor :
    Function.Surjective (freeAbelianGroupToTensor k M N) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul m n => exact ⟨FreeAbelianGroup.of (m, n), freeAbelianGroupToTensor_of k M N (m, n)⟩
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]⟩

/-- **A pairing exhibits its target as the tensor product over `k`.** The additive extension of
a pairing of `M` and `N` to formal integral combinations of pairs is surjective, and its kernel
is exactly the subgroup of `k`-bilinearity relations; equivalently, the induced `k`-bilinear map
`M ⊗_k N ⟶ P` is bijective.

This is the shape in which the Künneth formula for Ext of [Stacks, Tag 0FXZ] enters the
construction of the complex of [Stacks, Tag 0G0A] in degree `q = 0`: `M` and `N` are the Hom
groups of the two families of factors, `P` is the Hom group between the external tensor
products, and the pairing is `(a, b) ↦ a ⊠ b`. Phrasing it through the free abelian group avoids
having to construct the `k`-bilinear map out of `M ⊗_k N`, which would need the bi-`k`-linearity
of `⊠` on morphisms; the two statements are equivalent. -/
structure IsTensorPairing {P : Type*} [AddCommGroup P]
    (p : FreeAbelianGroup (M × N) →+ P) : Prop where
  /-- Every element of `P` is a formal integral combination of pure values of the pairing. -/
  surjective : Function.Surjective p
  /-- A formal integral combination of pairs is annihilated by the pairing exactly when the
  `k`-bilinearity relations force it to be. -/
  ker_eq : p.ker = (freeAbelianGroupToTensor k M N).ker

end TensorPairing

section TensorPairingTransport

variable {k : Type*} [CommRing k] {M N N' : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N']

/-- Reindexing the second factor of the pairs by a `k`-linear map, as a map of formal integral
combinations. -/
def freeAbelianGroupMapRight (e : N →ₗ[k] N') :
    FreeAbelianGroup (M × N) →+ FreeAbelianGroup (M × N') :=
  FreeAbelianGroup.lift fun p => FreeAbelianGroup.of (p.1, e p.2)

omit [AddCommGroup M] [Module k M] in
/-- The map `freeAbelianGroupMapRight e` carries the formal generator `(m, n)` to `(m, e n)`. -/
@[simp]
theorem freeAbelianGroupMapRight_of (e : N →ₗ[k] N') (p : M × N) :
    freeAbelianGroupMapRight e (FreeAbelianGroup.of p) = FreeAbelianGroup.of (p.1, e p.2) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **Reindexing by a `k`-linear equivalence is `M ⊗ e` on the tensor product.** -/
theorem freeAbelianGroupToTensor_comp_mapRight (e : N ≃ₗ[k] N')
    (u : FreeAbelianGroup (M × N)) :
    freeAbelianGroupToTensor k M N' (freeAbelianGroupMapRight (e : N →ₗ[k] N') u) =
      TensorProduct.congr (LinearEquiv.refl k M) e (freeAbelianGroupToTensor k M N u) := by
  induction u using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p => simp
  | neg p hp => simp only [map_neg, hp]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Reindexing the second factor by a `k`-linear equivalence does not change the subgroup of
bilinearity relations.** The induced map on the tensor product is `M ⊗ e`, which is injective,
so a combination of pairs satisfies the relations after reindexing exactly when it did
before. -/
theorem ker_freeAbelianGroupToTensor_comap (e : N ≃ₗ[k] N') :
    (freeAbelianGroupToTensor k M N).ker =
      (freeAbelianGroupToTensor k M N').ker.comap
        (freeAbelianGroupMapRight (e : N →ₗ[k] N')) := by
  ext u
  simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_ker,
    freeAbelianGroupToTensor_comp_mapRight]
  exact ⟨fun h => by rw [h, map_zero],
    fun h => (TensorProduct.congr (LinearEquiv.refl k M) e).injective (by rw [h, map_zero])⟩

end TensorPairingTransport

/-! ### No negative Ext between modules placed in degree zero -/

/-- If `Hom(A, B)` is a subsingleton and `B' ≅ B`, then `Hom(A, B')` is a subsingleton. -/
private theorem subsingleton_hom_of_iso {C : Type*} [Category C] {A B B' : C} (e : B' ≅ B)
    [Subsingleton (A ⟶ B)] : Subsingleton (A ⟶ B') :=
  (Iso.homCongr (Iso.refl A) e).injective.subsingleton

/-- **There are no negative Exts between two objects placed in degree zero.** A morphism from
`M` in degree zero to the shift by `p < 0` of `N` in degree zero vanishes: the shift puts `N` in
degree `-p > 0`, and there are no morphisms from a lower degree to a higher one.

This is `DerivedCategory.hom_singleFunctor_obj_eq_zero` read at a shift rather than at two
single functors, the two being compared by the shift isomorphism of
`DerivedCategory.singleFunctors`. The model of the derived category is a binder, as it is
there. -/
theorem subsingleton_hom_singleFunctor_shift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (M N : C) (p : ℤ) (hp : p < 0) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.singleFunctor C 0).obj N)⟦p⟧) := by
  have h : Subsingleton ((DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C (-p)).obj N) :=
    ⟨fun φ ψ => by
      rw [DerivedCategory.hom_singleFunctor_obj_eq_zero M N 0 (-p) (by omega) φ,
        DerivedCategory.hom_singleFunctor_obj_eq_zero M N 0 (-p) (by omega) ψ]⟩
  exact subsingleton_hom_of_iso
    (((DerivedCategory.singleFunctors C).shiftIso p (-p) 0 (by omega)).app N)

/-! ### The second factors, `k`-linearly -/

attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

namespace DiagonalResolution

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [Linear k X.Modules] [Linear k Y.Modules]
  (R : DiagonalResolution f) (g : Y ⟶ Spec (.of k))
  (F : perfectDerived X ⥤ perfectDerived Y)

/-- **Full faithfulness and `k`-linearity of `F` identify `Hom(𝒢ᵢ, 𝒢ⱼ)` with
`Hom(F(𝒢ᵢ), F(𝒢ⱼ))` as `k`-modules.** This is
`AlgebraicGeometry.DiagonalResolution.secondFactorHomEquiv`, the second equality in the source's
computation of `Ext^q(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))`, upgraded from a bijection to a `k`-linear
equivalence. The three steps it is composed of are each `k`-linear: placing a module in degree
zero is a `k`-linear functor, the inclusion of the Hom group of `D(𝒪_X)` into that of
`D_perf(𝒪_X)` is the identity on the underlying `k`-module, and `F` is `k`-linear. -/
def secondFactorLinearEquiv [F.Full] [F.Faithful] [F.Additive] [F.Linear k] (i j : ℕ) :
    (R.right i ⟶ R.right j) ≃ₗ[k]
      (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j)) where
  toFun b := F.map (R.secondFactorHom b)
  map_add' b b' := by
    have h : R.secondFactorHom (b + b') = R.secondFactorHom b + R.secondFactorHom b' := by
      apply ObjectProperty.hom_ext
      exact (DerivedCategory.singleFunctor X.Modules 0).map_add
    rw [h, CategoryTheory.Functor.map_add]
  map_smul' c b := by
    have h : R.secondFactorHom (c • b) = c • R.secondFactorHom b := by
      apply ObjectProperty.hom_ext
      exact (DerivedCategory.singleFunctor X.Modules 0).map_smul c b
    rw [RingHom.id_apply, h, CategoryTheory.Functor.map_smul]
  invFun := R.secondFactorHomEquiv F i j |>.symm
  left_inv := (R.secondFactorHomEquiv F i j).left_inv
  right_inv := (R.secondFactorHomEquiv F i j).right_inv

/-- The equivalence `secondFactorLinearEquiv` carries `b` to `F.map (R.secondFactorHom b)`. -/
theorem secondFactorLinearEquiv_apply [F.Full] [F.Faithful] [F.Additive] [F.Linear k] {i j : ℕ}
    (b : R.right i ⟶ R.right j) :
    R.secondFactorLinearEquiv F i j b = F.map (R.secondFactorHom b) :=
  rfl

/-! ### The vanishing that collapses the source's sum over `p` -/

omit [Linear k X.Modules] [Linear k Y.Modules] in
/-- **Exactness and full faithfulness of `F` make the negative Exts between the images of the
second factors vanish.** `Ext^{-p}_Y(F(𝒢ᵢ), F(𝒢ⱼ)) = 0` for `p > 0`, written here as the
vanishing of `Hom(F(𝒢ᵢ), F(𝒢ⱼ)⟦p⟧)` for `p < 0`.

This is the second of the two things the source's computation of
`Ext^q(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))` needs, and the one that does follow from the hypotheses of
[Stacks, Tag 0G08]: `[F.CommShift ℤ]` moves the shift inside `F`, full faithfulness then
replaces `Hom(F(𝒢ᵢ), F(𝒢ⱼ⟦p⟧))` by `Hom(𝒢ᵢ, 𝒢ⱼ⟦p⟧)`, and that group vanishes by
`AlgebraicGeometry.subsingleton_hom_singleFunctor_shift` because both second factors are
modules placed in degree zero. It is what collapses the sum over `p` to its `p = 0` summand.

It does *not* give the Künneth decomposition on `X ×_k Y` that is the first equality of that
computation, which is why it does not on its own discharge the Künneth input at that
product. -/
theorem subsingleton_hom_map_secondFactor_shift [F.CommShift ℤ] (hff : F.FullyFaithful)
    (i j : ℕ) (p : ℤ) (hp : p < 0) :
    Subsingleton (F.obj (R.secondFactor i) ⟶ (F.obj (R.secondFactor j))⟦p⟧) := by
  have h0 : Subsingleton ((R.secondFactor i).obj ⟶ ((R.secondFactor j)⟦p⟧).obj) :=
    have := subsingleton_hom_singleFunctor_shift (R.right i) (R.right j) p hp
    subsingleton_hom_of_iso (B := ((R.secondFactor j).obj)⟦p⟧)
      (((ObjectProperty.ι _).commShiftIso p).app (R.secondFactor j))
  have hsub : Subsingleton (R.secondFactor i ⟶ (R.secondFactor j)⟦p⟧) :=
    (perfectDerivedHomEquiv (R.secondFactor i) ((R.secondFactor j)⟦p⟧)).symm.injective.subsingleton
  have : Subsingleton (F.obj (R.secondFactor i) ⟶ F.obj ((R.secondFactor j)⟦p⟧)) :=
    (hff.homEquiv (X := R.secondFactor i)
      (Y := (R.secondFactor j)⟦p⟧)).symm.injective.subsingleton
  exact subsingleton_hom_of_iso (B := F.obj ((R.secondFactor j)⟦p⟧))
    ((F.commShiftIso p).app (R.secondFactor j)).symm

/-! ### The transformed pairing is the Künneth pairing on the images, reindexed -/

/-- **The transformed pairing is the pairing on the images of the second factors, reindexed
along the identification of `Hom(𝒢ᵢ, 𝒢ⱼ)` with `Hom(F(𝒢ᵢ), F(𝒢ⱼ))`.** The two pairings have the
same pure values, taken over index sets that full faithfulness of `F` puts in bijection; this
records that, so that the kernel of one is the preimage of the kernel of the other. -/
theorem transformedPairing_eq_comp [F.Full] [F.Faithful] [F.Additive] [F.Linear k] (i j : ℕ)
    (u : FreeAbelianGroup (R.FactorPair i j)) :
    R.transformedPairing g F i j u =
      R.transformedImagePairing g F i j
        (freeAbelianGroupMapRight (R.secondFactorLinearEquiv F i j).toLinearMap u) := by
  induction u using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p =>
    rw [R.transformedPairing_of g F, freeAbelianGroupMapRight_of,
      R.transformedImagePairing_of g F]
    rfl
  | neg p hp => simp only [map_neg, hp]
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The Künneth input, with the equality of kernels discharged -/

/-- **The Künneth input of the complex of [Stacks, Tag 0G0A], from the two Künneth
identifications alone.** The equality of the kernels of the two pairings — the third field of
`AlgebraicGeometry.DiagonalResolution.KunnethHomData`, which is not a consequence of the two
surjectivity statements and is false without the `k`-linearity of `F` — is *proved* here rather
than assumed.

What is assumed is that each of the two pairings exhibits its Hom group as the tensor product
over `k` of the Hom groups of the factors: on `X ×_k X` for the pure maps `a ⊠ b`, and on
`X ×_k Y` for the maps `a ⊠ c` with `c : F(𝒢ᵢ) ⟶ F(𝒢ⱼ)`. Those two are the same canonical
statement at the two products, the Künneth formula for Ext of [Stacks, Tag 0FXZ] in degree
`q = 0`, whereas the equality of kernels is not a Künneth statement at all. It follows because
the two subgroups of bilinearity relations correspond under
`AlgebraicGeometry.DiagonalResolution.secondFactorLinearEquiv`, which is `k`-linear exactly
because `F` is. -/
theorem kunnethHomDataOfTensorPairings [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
    (hbox : ∀ i j, IsTensorPairing k (R.left i ⟶ R.left j) (R.right i ⟶ R.right j)
      (R.boxPairing i j))
    (himage : ∀ i j, IsTensorPairing k (R.left i ⟶ R.left j)
      (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j))
      (R.transformedImagePairing g F i j)) :
    KunnethHomData R g F :=
  KunnethHomData.of R g F (fun i j => (hbox i j).surjective)
    (fun i j => (himage i j).surjective)
    fun i j => by
      have hcomp : (R.transformedPairing g F i j).ker =
          ((R.transformedImagePairing g F i j).ker).comap
            (freeAbelianGroupMapRight (R.secondFactorLinearEquiv F i j).toLinearMap) := by
        ext u
        simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap,
          R.transformedPairing_eq_comp g F i j u]
      rw [(hbox i j).ker_eq, hcomp, (himage i j).ker_eq,
        ← ker_freeAbelianGroupToTensor_comap (R.secondFactorLinearEquiv F i j)]

end DiagonalResolution

/-! ### The complex of [Stacks, Tag 0G0A] in Situation [Stacks, Tag 0G08] -/

open DiagonalResolution in
/-- **The complex of [Stacks, Tag 0G0A], at the hypotheses of Situation [Stacks, Tag 0G08].**
Let `k` be a field, let `X` and `Y` be proper and smooth over `k`, let
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` be `k`-linear, exact and fully faithful, and let `R` be a
resolution of the diagonal of `X` by external tensor products of finite locally free modules.
Then there is a complex

`… ⟶ ℰ₂ ⊠ F(𝒢₂) ⟶ ℰ₁ ⊠ F(𝒢₁) ⟶ ℰ₀ ⊠ F(𝒢₀)`

on `X ×_k Y` whose term of index `i` is `ℰᵢ ⊠ F(𝒢ᵢ)` and whose differentials are those of `R`,
read through an identification of Hom groups that carries each pure map `a ⊠ b` to `a ⊠ F(b)`.

`k`-linearity of `F` is with respect to the canonical structures of
`AlgebraicGeometry.modulesLinear`, and exactness is the pair `[F.CommShift ℤ]`,
`[F.IsTriangulated]` that
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic` fixes as the convention
for an exact functor of triangulated categories; `AlgebraicGeometry.perfectDerived` is
triangulated by `AlgebraicGeometry.isTriangulated_isPerfect_locallySmall`, turned on as a local
instance above.

The Künneth input is the two hypotheses `hbox` and `himage`, one on each of the two products:
each says that the pairing `(a, b) ↦ a ⊠ b` exhibits the Hom group between the terms as the
tensor product over `k` of the Hom groups of the factors. That is the Künneth formula for Ext of
[Stacks, Tag 0FXZ] in degree `q = 0`, the same canonical statement twice, and nothing else is
assumed: the equality of the kernels of the two pairings, which
`AlgebraicGeometry.DiagonalResolution.KunnethHomData` asks for as a third input and which the
implementation notes of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Kunneth` show is not a
consequence of the other two, is proved from the `k`-linearity of `F` by
`AlgebraicGeometry.DiagonalResolution.kunnethHomDataOfTensorPairings`. -/
theorem exists_kunnethComplex_of_tensorPairings (k : Type u) [Field k]
    (X Y : Over (Spec (.of k))) [Smooth X.hom] [Smooth Y.hom]
    [IsProper X.hom] [IsProper Y.hom] :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom),
        (∀ i j, IsTensorPairing k (R.left i ⟶ R.left j) (R.right i ⟶ R.right j)
          (R.boxPairing i j)) →
        (∀ i j, IsTensorPairing k (R.left i ⟶ R.left j)
          (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j))
          (R.transformedImagePairing Y.hom F i j)) →
        ∃ T : ImageHomTransport R Y.hom F,
          (∀ i, T.complex.X i = R.imageTerm Y.hom F i) ∧
          (∀ i, T.complex.d (i + 1) i = T.hom (i + 1) i (R.boxDifferential i)) ∧
          ∀ (i j : ℕ) (a : R.left i ⟶ R.left j) (b : R.right i ⟶ R.right j),
            T.hom i j (externalTensorProductMap X.hom X.hom a b) =
              R.transformedMap Y.hom F a b := by
  let _ : Linear k X.left.Modules := modulesLinear k X
  let _ : Linear k Y.left.Modules := modulesLinear k Y
  intro F _ _ hlin hff R hbox himage
  let _ := hlin
  let _ := hff.some.full
  let _ := hff.some.faithful
  let K := kunnethHomDataOfTensorPairings R Y.hom F hbox himage
  exact ⟨K.homTransport, fun i => rfl, K.homTransport_complex_d,
    fun i j a b => K.homEquiv_boxMap a b⟩

end AlgebraicGeometry

end
