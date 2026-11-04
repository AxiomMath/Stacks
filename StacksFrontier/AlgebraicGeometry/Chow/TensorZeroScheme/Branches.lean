module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-!
# The two branches of the zero scheme of a section of a tensor product

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`. The scheme `p : L → Y` of
[Stacks, Tag 0F97], its two sections `s₁` of `p^*L₁` and `s₂` of `p^*L₂`, and its two branches
`D₁ = Z(s₁)` and `D₂ = Z(s₂)` are built in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic`, which also proves the tag's
conditions (1) and (3).

This file adds the scheme-theoretic inverse image `p^{-1}D` and the two projections `p₁`, `p₂`
of the tag's diagram. The inverse image is computed exactly: `p^{-1}D` is the zero scheme of
`s₁ ⊗ s₂` on `L`. Since the zero scheme of a product of two sections is contained in the zero
scheme of each factor, `p^{-1}D ≤ D₁ ⊓ D₂` — in the order on `Scheme.IdealSheafData`, which is
the order on ideals and therefore opposite to inclusion of subschemes, so this says that the
scheme-theoretic union `D₁ ∪ D₂` is a closed subscheme of `p^{-1}D`. That inequality is one
half of the tag's condition (5), and it is exactly what makes the two projections of the
diagram exist: `p₁` is `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` for the inequality
`D ≤ (D₁).map p`, which is the Galois-connection transpose of `p^{-1}D ≤ D₁`.

## Main definitions

* `Stacks.Divisors.tensorModules` and `Stacks.Divisors.tensorSection`: the tensor product of two
  `𝒪_X`-modules and the section of it cut out by a section of each factor, ascribed at the
  `Scheme.Modules` spelling the zero scheme is formed at.
* `Stacks.Divisors.tensorSectionRight` and `Stacks.Divisors.tensorSectionLeft`: pairing with a
  fixed section of one factor, as a linear map in the section of the other.
* `Stacks.Chow.TensorZeroScheme.zeroIdeal`: **the closed subscheme `i : D → Y`** of the tag, the
  zero scheme of `s`.
* `Stacks.Chow.TensorZeroScheme.proj₁` and `Stacks.Chow.TensorZeroScheme.proj₂`: **the two
  projections `p₁ : D₁ ⟶ D` and `p₂ : D₂ ⟶ D`** of the tag's diagram.

## Main results

* `Stacks.Divisors.zeroScheme_tensorSection_le_inf`: the zero scheme of `a ⊗ b` is contained in
  the zero scheme of `a` and in the zero scheme of `b`.
* `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj`: `p^{-1}D = Z(s₁ ⊗ s₂)`.
* `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj_le_inf`: **one half of Tag 0F97(5)**,
  `p^{-1}D ≤ D₁ ⊓ D₂`.
* `Stacks.Chow.TensorZeroScheme.branch₁_subschemeι_comp_proj` and
  `branch₂_subschemeι_comp_proj`: **the two squares of the tag's diagram commute.**

## Implementation notes

*Why the projections are definitional.* Building `pᵢ` out of the factorization clause of
[Stacks, Tag 02OR] would produce it by `Classical.choose` from an existence statement, which is
not an acceptable body for a morphism of a diagram. The route taken here is
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap`, whose defining property
`subschemeMap_subschemeι` *is* the commuting square, so the square needs no proof of its own.

*Where the other conditions are.* The reverse inequality `D₁ ⊓ D₂ ≤ p^{-1}D` of condition (5),
and conditions (2), (4), (6) and (7), are proved in the other files of
`StacksDraft.AlgebraicGeometry.Chow.TensorZeroScheme` and assembled in
`…TensorZeroScheme.DecompositionExistence`. In the source they all rest on
the affine-local presentation `p^{-1}(Spec A) = Spec A[z₁, z₂]/(z₁z₂ - f)` of the tag's proof,
over an affine open of `Y` trivializing both `L₁` and `L₂`. For condition (5) the local content
is that `z₂` is a nonzerodivisor on `A[z₁, z₂]/(z₁z₂ - f, z₁) = (A/f)[z₂]`, whence
`(z₁) ∩ (z₂) = (z₁z₂)`; for (2) it is the freeness of `A[z₁, z₂]/(z₁z₂ - f)` over `A` on the
basis `{z₁ⁿ}ₙ ∪ {z₂ᵐ}ₘ₌₁…`, which gives flatness, and the dimension of the fibres.

*The spelling of the tensor product.* Everything is written at
`Stacks.SheafOfModules.Tensor.sheafTensor`, the spelling the comparison of
[Stacks, Tag 01CD] and the zero-scheme machinery of this project are stated at.
`Stacks.Divisors.tensorModules` is the same term ascribed as an `AlgebraicGeometry.Scheme.Modules`
object: without the ascription the `Module Γ(X, U) Γ(-, U)` instance, which is registered for
`Scheme.Modules`, is not found by instance search.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.TensorSheafification (toSheafify)
open Stacks.SheafOfModules (tensorSectionsAt)
open Stacks.PullbackTensorIso (pullbackTensorSection)
open scoped TensorProduct

universe u

@[expose] public noncomputable section

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- The tensor product of two `𝒪_X`-modules, ascribed as an `𝒪_X`-module. -/
abbrev tensorModules (M N : X.Modules) : X.Modules :=
  ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
      (X.ringCatSheaf.property)⟩).obj (M)).obj (N)))

/-- The section of `M ⊗ N` cut out by a section of `M` and a section of `N`. -/
abbrev tensorSection (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    Γ(tensorModules M N, U) :=
  tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U) M N m n

/-- The section of `M ⊗ N` cut out by a pair of sections is compatible with restriction. -/
theorem tensorSection_restrict (M N : X.Modules) {V W : X.Opens} (f : W ⟶ V)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    (tensorModules M N).presheaf.map f.op (tensorSection M N V m n) =
      tensorSection M N W (M.presheaf.map f.op m) (N.presheaf.map f.op n) := by
  have h := (toSheafify X.sheaf.obj X.ringCatSheaf.property (M.val ⊗ N.val)).naturality f.op
  have hh := congrArg (fun k => k.hom (m ⊗ₜ[X.sheaf.obj.obj (op V)] n)) h
  change ((toSheafify X.sheaf.obj X.ringCatSheaf.property (M.val ⊗ N.val)).app (op W)).hom
    ((M.val.map f.op).hom m ⊗ₜ[X.sheaf.obj.obj (op W)] (N.val.map f.op).hom n) = _ at hh
  exact hh.symm

/-- Pairing with a fixed section of `N` is linear in the section of `M`. -/
def tensorSectionRight (M N : X.Modules) (U : X.Opens) (n : Γ(N, U)) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(tensorModules M N, U) :=
  ((toSheafify X.sheaf.obj X.ringCatSheaf.property (M.val ⊗ N.val)).app (op U)).hom ∘ₗ
    (TensorProduct.mk Γ(X, U) Γ(M, U) Γ(N, U)).flip n

/-- Pairing with a fixed section of `M` is linear in the section of `N`. -/
def tensorSectionLeft (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    Γ(N, U) →ₗ[Γ(X, U)] Γ(tensorModules M N, U) :=
  ((toSheafify X.sheaf.obj X.ringCatSheaf.property (M.val ⊗ N.val)).app (op U)).hom ∘ₗ
    TensorProduct.mk Γ(X, U) Γ(M, U) Γ(N, U) m

/-- Pairing on the right, evaluated. -/
@[simp] theorem tensorSectionRight_apply (M N : X.Modules) (U : X.Opens) (n : Γ(N, U))
    (m : Γ(M, U)) : tensorSectionRight M N U n m = tensorSection M N U m n := by
  simp only [tensorSectionRight]
  rfl

/-- Pairing on the left, evaluated. -/
@[simp] theorem tensorSectionLeft_apply (M N : X.Modules) (U : X.Opens) (m : Γ(M, U))
    (n : Γ(N, U)) : tensorSectionLeft M N U m n = tensorSection M N U m n := by
  simp only [tensorSectionLeft]
  rfl

variable (M N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The zero scheme of `e` is contained in that of `c` when some linear maps `ℓ U` take `c` to
`e` on every open. -/
private theorem zeroScheme_le_of_linearMap {P : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P]
    (e : Γ(tensorModules M N, ⊤)) (c : Γ(P, ⊤))
    (ℓ : ∀ U : X.Opens, Γ(P, U) →ₗ[Γ(X, U)] Γ(tensorModules M N, U))
    (h : ∀ U : X.Opens, (tensorModules M N).presheaf.map (homOfLE le_top).op e =
      ℓ U (P.presheaf.map (homOfLE le_top).op c)) :
    zeroScheme X (tensorModules M N) e ≤ zeroScheme X P c := by
  refine Scheme.IdealSheafData.ofIdeals_mono fun U => Ideal.span_mono ?_
  rintro _ ⟨φ, rfl⟩
  exact ⟨φ ∘ₗ ℓ U.1, congrArg φ (h U.1)⟩

/-- **The zero scheme of `a ⊗ b` contains the zero scheme of `a`** as a closed subscheme: the
defining ideal of `Z(a ⊗ b)` is contained in that of `Z(a)`, since a functional on the sections
of `M ⊗ N` paired with the restriction of `b` is a functional on the sections of `M` taking the
same value at the restriction of `a`. -/
theorem zeroScheme_tensorSection_le_left (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b) ≤ zeroScheme X M a :=
  zeroScheme_le_of_linearMap M N _ a
    (fun U => tensorSectionRight M N U (N.presheaf.map (homOfLE le_top).op b)) fun _ =>
    by simpa using tensorSection_restrict M N (homOfLE le_top) a b

/-- **The zero scheme of `a ⊗ b` contains the zero scheme of `b`** as a closed subscheme, by the
argument of `zeroScheme_tensorSection_le_left` in the other factor. -/
theorem zeroScheme_tensorSection_le_right (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b) ≤ zeroScheme X N b :=
  zeroScheme_le_of_linearMap M N _ b
    (fun U => tensorSectionLeft M N U (M.presheaf.map (homOfLE le_top).op a)) fun _ =>
    by simpa using tensorSection_restrict M N (homOfLE le_top) a b

/-- **The zero scheme of `a ⊗ b` contains the scheme-theoretic union of `Z(a)` and `Z(b)`**: the
defining ideal of `Z(a ⊗ b)` is contained in the intersection `Z(a) ⊓ Z(b)` of the two defining
ideals, which is the ideal of the scheme-theoretic union. -/
theorem zeroScheme_tensorSection_le_inf (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b) ≤
      zeroScheme X M a ⊓ zeroScheme X N b :=
  le_inf (zeroScheme_tensorSection_le_left M N a b) (zeroScheme_tensorSection_le_right M N a b)

end Stacks.Divisors

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include h₁ h₂ in
/-- **The closed subscheme `i : D → Y` of Tag 0F97**: the zero scheme of `s`. -/
def zeroIdeal : Y.IdealSheafData :=
  Stacks.Divisors.zeroScheme Y (Stacks.Divisors.tensorModules L₁ L₂) s

include h₁ h₂ in
/-- **The scheme-theoretic inverse image `p^{-1}D` is the zero scheme of `s₁ ⊗ s₂`.** The zero
scheme of a section commutes with pullback ([Stacks, Tag 0B6Y]), the comparison of [Stacks,
Tag 01CD] identifies `p^*(L₁ ⊗ L₂)` with `p^*L₁ ⊗ p^*L₂` carrying `p^*s` to the reading of it
used in Tag 0F97(1), and that condition rewrites the section as `s₁ ⊗ s₂`. -/
theorem comap_zeroIdeal_proj :
    (zeroIdeal Y L₁ L₂ s).comap (proj Y L₁ L₂ s) =
      Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
        (Stacks.Divisors.tensorModules
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂))
        (Stacks.Divisors.tensorSection _ _ ⊤ (section₁ Y L₁ L₂ s) (section₂ Y L₁ L₂ s)) := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible
      (spaceIdeal Y L₁ L₂ s).subscheme.sheaf.obj
      (spaceIdeal Y L₁ L₂ s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj
        (Stacks.Divisors.tensorModules L₁ L₂)) :=
    Stacks.Divisors.pullback_isInvertible _ _
  have h₀ := (Stacks.Divisors.zeroScheme_pullback (proj Y L₁ L₂ s)
    (Stacks.Divisors.tensorModules L₁ L₂) s).symm
  have h₁' := AlgebraicGeometry.zeroScheme_eq_of_iso
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (proj Y L₁ L₂ s) L₁ L₂)
    (t := pullbackTensorSection (proj Y L₁ L₂ s) L₁ L₂ s) rfl
  have h₂' := congrArg (fun t => Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
    (Stacks.Divisors.tensorModules
      ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
      ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂)) t)
    (pullbackTensorSection_proj Y L₁ L₂ s)
  exact h₀.trans (h₁'.trans h₂')

include h₁ h₂ in
/-- **One half of Stacks Project, Tag 0F97(5)**: the scheme-theoretic union `D₁ ∪ D₂` is a
closed subscheme of `p^{-1}D`. In the order on `Scheme.IdealSheafData`, which is the order on
ideals and so opposite to inclusion of subschemes, this reads `p^{-1}D ≤ D₁ ⊓ D₂`. -/
theorem comap_zeroIdeal_proj_le_inf :
    (zeroIdeal Y L₁ L₂ s).comap (proj Y L₁ L₂ s) ≤
      branch₁ Y L₁ L₂ s ⊓ branch₂ Y L₁ L₂ s := by
  rw [comap_zeroIdeal_proj, branch₁_eq_zeroScheme, branch₂_eq_zeroScheme]
  exact Stacks.Divisors.zeroScheme_tensorSection_le_inf _ _ (section₁ Y L₁ L₂ s)
    (section₂ Y L₁ L₂ s)

include h₁ h₂ in
/-- **The projection `p₁ : D₁ ⟶ D` of the diagram of Tag 0F97.** -/
def proj₁ : (branch₁ Y L₁ L₂ s).subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme :=
  Scheme.IdealSheafData.subschemeMap (branch₁ Y L₁ L₂ s) (zeroIdeal Y L₁ L₂ s) (proj Y L₁ L₂ s)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_trans (comap_zeroIdeal_proj_le_inf Y L₁ L₂ s) inf_le_left))

include h₁ h₂ in
/-- **The projection `p₂ : D₂ ⟶ D` of the diagram of Tag 0F97.** -/
def proj₂ : (branch₂ Y L₁ L₂ s).subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme :=
  Scheme.IdealSheafData.subschemeMap (branch₂ Y L₁ L₂ s) (zeroIdeal Y L₁ L₂ s) (proj Y L₁ L₂ s)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_trans (comap_zeroIdeal_proj_le_inf Y L₁ L₂ s) inf_le_right))

include h₁ h₂ in
/-- **The left-hand square of the diagram of Tag 0F97 commutes**: `i₁ ≫ p = p₁ ≫ i`. -/
theorem branch₁_subschemeι_comp_proj :
    (branch₁ Y L₁ L₂ s).subschemeι ≫ proj Y L₁ L₂ s =
      proj₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι :=
  (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm

include h₁ h₂ in
/-- **The right-hand square of the diagram of Tag 0F97 commutes**: `i₂ ≫ p = p₂ ≫ i`. -/
theorem branch₂_subschemeι_comp_proj :
    (branch₂ Y L₁ L₂ s).subschemeι ≫ proj Y L₁ L₂ s =
      proj₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι :=
  (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm

end Stacks.Chow.TensorZeroScheme

end
