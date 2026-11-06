module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FibrePowerSite

/-!
# Peeling one factor off a finite product

An induction on the number of factors of a `Fin n`-fold product needs the product to be
presented as a binary product of its zeroth factor with the product of the remaining ones, and
needs that presentation with *named* projections, so that the two sides of an induction step can
be compared componentwise. This file supplies it: `Stacks.FinProd.piTail` is the morphism which
forgets the zeroth factor, and `Stacks.FinProd.isLimitBinaryFanPiSucc` says that the zeroth
projection together with it exhibit the `Fin (n + 1)`-fold product as a binary product.

The second half of the file identifies `AlgebraicGeometry.Space.overProdObj` — the finite fibre
power over the base, as an object of the big fppf category over `S` — as the `Fin n`-indexed
*product* in that category, and transports that through the Yoneda embedding. This is what makes
a morphism into the fibre power over the base checkable one component at a time, both inside the
site and on the presheaves it represents.

## Main definitions

* `Stacks.FinProd.piTail`: the morphism `∏ᶜ A ⟶ ∏ᶜ (fun i ↦ A i.succ)` forgetting the zeroth
  factor.
* `Stacks.FinProd.isLimitBinaryFanPiSucc`: the zeroth projection and `Stacks.FinProd.piTail`
  exhibit a `Fin (n + 1)`-fold product as a binary product.
* `AlgebraicGeometry.Space.isLimitFanOverProdObj`: the fibre power over the base is the
  `Fin n`-indexed product in the big fppf category over `S`.
* `AlgebraicGeometry.Space.yonedaOverProdObjIso`: the presheaf represented by the fibre power
  over the base is the product of the presheaves represented by the factors.

## Main results

* `Stacks.FinProd.isIso_pi_π_fin_one`: a `Fin 1`-fold product is its unique factor.
* `AlgebraicGeometry.Space.overProdObj_hom_ext`: a morphism of the big fppf category over `S`
  into the fibre power over the base is determined by its components.
* `AlgebraicGeometry.Space.yonedaOverProdObjIso_hom_comp_π`: the identification of the
  represented presheaf with the product is compatible with the projections.

## What is and is not proved

Nothing here carries a Stacks attribute: the first half is pure category theory about finite
products, and the second half is the universal property of `Stacks.Chow.overProd`, which is a
chosen limit and carries no tag, transported into the big fppf category over `S` and then along
Yoneda.

Nothing is said about *when* the big fppf category over `S` has all finite products; what is
proved is that the particular cone `AlgebraicGeometry.Space.overProdObj` with its projections is
a limit cone, which is all an induction on the number of factors consumes.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.FinProd

variable {C : Type u} [Category.{v} C]

/-- **The morphism forgetting the zeroth factor of a `Fin (n + 1)`-fold product.** -/
def piTail {n : ℕ} (A : Fin (n + 1) → C) [HasProduct A]
    [HasProduct fun i : Fin n ↦ A i.succ] :
    ∏ᶜ A ⟶ ∏ᶜ fun i : Fin n ↦ A i.succ :=
  Pi.lift fun i : Fin n ↦ Pi.π A i.succ

/-- Composing `Stacks.FinProd.piTail` with the `i`-th projection is the `(i + 1)`-st projection. -/
@[simp]
theorem piTail_comp_π {n : ℕ} (A : Fin (n + 1) → C) [HasProduct A]
    [HasProduct fun i : Fin n ↦ A i.succ] (i : Fin n) :
    piTail A ≫ Pi.π (fun i : Fin n ↦ A i.succ) i = Pi.π A i.succ :=
  Pi.lift_comp_π _ i

/-- **A `Fin (n + 1)`-fold product is the binary product of its zeroth factor with the
`Fin n`-fold product of the remaining factors.** The two legs are the zeroth projection and
`Stacks.FinProd.piTail`. -/
def isLimitBinaryFanPiSucc {n : ℕ} (A : Fin (n + 1) → C) [HasProduct A]
    [HasProduct fun i : Fin n ↦ A i.succ] :
    IsLimit (BinaryFan.mk (Pi.π A 0) (piTail A)) := by
  refine BinaryFan.isLimitMk
    (fun s ↦ Pi.lift fun j ↦ Fin.cases (motive := fun j ↦ s.pt ⟶ A j) s.fst
      (fun i ↦ s.snd ≫ Pi.π (fun i : Fin n ↦ A i.succ) i) j)
    (fun s ↦ by simp) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Category.assoc, piTail_comp_π, Pi.lift_comp_π]
    exact Fin.cases_succ _
  · refine Pi.hom_ext _ _ fun j ↦ ?_
    rw [Pi.lift_comp_π]
    induction j using Fin.cases with
    | zero => simpa using h₁
    | succ i => rw [Fin.cases_succ, ← piTail_comp_π A i, ← Category.assoc, h₂]

/-- **A `Fin 1`-fold product is its unique factor**, through the only projection. -/
instance isIso_pi_π_fin_one (A : Fin 1 → C) [HasProduct A] : IsIso (Pi.π A 0) := by
  refine ⟨Pi.lift fun j ↦ Fin.cases (motive := fun j ↦ A 0 ⟶ A j) (𝟙 (A 0))
    (fun i ↦ i.elim0) j, ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun j ↦ ?_
    induction j using Fin.cases with
    | zero => simp
    | succ i => exact i.elim0
  · simp

end Stacks.FinProd

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the big fppf category over `S` into the finite fibre power over the base is
determined by its components.** -/
theorem overProdObj_hom_ext {n : ℕ} (Y : Fin n → BigFppfOver B S hS)
    {T : BigFppfOver B S hS} {f g : T ⟶ overProdObj B S hS Y}
    (h : ∀ i, f ≫ overProdObjπ B S hS Y i = g ≫ overProdObjπ B S hS Y i) : f = g := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  refine Stacks.Chow.overProd_hom_ext (fun i ↦ B.inclusion.map (Y i).hom) _ _ ?_ fun i ↦ ?_
  · have key : ∀ k : T ⟶ overProdObj B S hS Y,
        (BigFppfOver.toScheme B S hS).map k ≫ (Stacks.Chow.overProd
            fun i ↦ B.inclusion.map (Y i).hom).hom = B.inclusion.map T.hom := by
      intro k
      rw [← overProdObj_hom B S hS Y,
        show (BigFppfOver.toScheme B S hS).map k = B.inclusion.map k.left from rfl,
        ← Functor.map_comp, Over.w]
    exact (key f).trans (key g).symm
  · have hi := congrArg (BigFppfOver.toScheme B S hS).map (h i)
    rw [Functor.map_comp, Functor.map_comp, overProdObjπ_toScheme] at hi
    exact hi

/-- **The finite fibre power over the base is the `Fin n`-indexed product in the big fppf
category over `S`.** The lift is `AlgebraicGeometry.Space.overProdObjLift` and uniqueness is
`AlgebraicGeometry.Space.overProdObj_hom_ext`. -/
def isLimitFanOverProdObj {n : ℕ} (Y : Fin n → BigFppfOver B S hS) :
    IsLimit (Fan.mk (overProdObj B S hS Y) (overProdObjπ B S hS Y)) :=
  Fan.IsLimit.mk _ (fun s ↦ overProdObjLift B S hS Y s.pt fun i ↦ s.proj i)
    (fun s i ↦ overProdObjLift_comp_π B S hS Y s.pt _ i)
    fun s m hm ↦ overProdObj_hom_ext B S hS Y fun i ↦ by
      rw [overProdObjLift_comp_π]
      exact hm i

/-- **The presheaf represented by the finite fibre power over the base is the product of the
presheaves represented by the factors.** -/
def yonedaOverProdObjIso {n : ℕ} (Y : Fin n → BigFppfOver B S hS) :
    (∏ᶜ fun i ↦ yoneda.obj (Y i)) ≅ yoneda.obj (overProdObj B S hS Y) :=
  (productIsProduct fun i ↦ yoneda.obj (Y i)).conePointUniqueUpToIso
    (isLimitFanMkObjOfIsLimit yoneda Y _ (isLimitFanOverProdObj B S hS Y))

/-- The isomorphism `AlgebraicGeometry.Space.yonedaOverProdObjIso` is compatible with the
projections: its forward map followed by the image of the `i`-th projection under `yoneda` is the
`i`-th product projection. -/
@[simp]
theorem yonedaOverProdObjIso_hom_comp_π {n : ℕ} (Y : Fin n → BigFppfOver B S hS) (i : Fin n) :
    (yonedaOverProdObjIso B S hS Y).hom ≫ yoneda.map (overProdObjπ B S hS Y i) =
      Pi.π (fun i ↦ yoneda.obj (Y i)) i :=
  (productIsProduct fun i ↦ yoneda.obj (Y i)).conePointUniqueUpToIso_hom_comp
    (isLimitFanMkObjOfIsLimit yoneda Y _ (isLimitFanOverProdObj B S hS Y)) ⟨i⟩

end AlgebraicGeometry.Space

end
