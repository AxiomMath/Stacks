module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback

/-!
# The tensor product of a family of invertible modules on a scheme

Let `X` be a scheme and let `L : ι → 𝒪_X`-Mod be a family of invertible modules. This file
forms `⨂_{i ∈ l} L i` for a *list* `l` of indices, proves it invertible, and computes its class
in `Pic(X)` and the class of its pullback: both are the corresponding sums over `l`. Read at
`l = s.toList` for a `Finset s` — in particular at `l = Finset.univ.toList` for a finite index
type — these are the sums over `s`.

## Main definitions

* `Stacks.SheafOfModules.schemeTensorList`: `⨂_{i ∈ l} L i`, by recursion on the list, with the
  structure sheaf for the empty list.

## Main results

* `Stacks.SheafOfModules.isInvertible_schemeTensorList`: it is invertible when each factor is.
* `Stacks.SheafOfModules.picardClass_schemeTensorList` and
  `Stacks.SheafOfModules.picardClass_schemeTensorList_toList`: its class in `Pic(X)` is the sum
  of the classes, over the list and over a `Finset` respectively.
* `Stacks.SheafOfModules.pullbackPicardClass_schemeTensorList` and
  `Stacks.SheafOfModules.pullbackPicardClass_schemeTensorList_toList`: the class of its pullback
  along `φ : X ⟶ Y` is the sum of the pullback classes.

## Implementation notes

The tensor product of sheaves of modules is associative and commutative only up to isomorphism,
so the product is formed by `List.foldr` rather than `Finset.fold`, which requires
`Std.Associative` and `Std.Commutative` for the operation itself. The object `⨂_{i ∈ l} L i`
depends on the order and the repetitions of `l`, but its class in `Pic(X)` does not:
`Finset.sum_map_toList` identifies the sum over `s.toList` with the sum over `s`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

variable {ι : Type*} {X Y : Scheme.{u}}

/-- **The tensor product of a family of modules on a scheme over a list of indices**,
`⨂_{i ∈ l} L i`, nested to the right and with the structure sheaf for the empty list. -/
noncomputable def schemeTensorList (X : Scheme.{u})
    (L : ι → SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (l : List ι) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  l.foldr (fun i M => schemeTensor X (L i) M)
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))

/-- The tensor product over the empty list is the structure sheaf. -/
@[simp]
theorem schemeTensorList_nil (X : Scheme.{u})
    (L : ι → SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    schemeTensorList X L [] = SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  rfl

/-- The tensor product over `i :: l` is `L i ⊗ ⨂_{j ∈ l} L j`. -/
@[simp]
theorem schemeTensorList_cons (X : Scheme.{u})
    (L : ι → SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (i : ι) (l : List ι) :
    schemeTensorList X L (i :: l) = schemeTensor X (L i) (schemeTensorList X L l) :=
  rfl

/-- **A tensor product of invertible modules over a list is invertible**, by Tag 01CT and the
invertibility of the structure sheaf. -/
theorem isInvertible_schemeTensorList (X : Scheme.{u})
    (L : ι → SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : ∀ i, IsInvertible X.presheaf X.ringCatIsSheaf (L i)) (l : List ι) :
    IsInvertible X.presheaf X.ringCatIsSheaf (schemeTensorList X L l) := by
  induction l with
  | nil => exact isInvertible_unit X.presheaf X.ringCatIsSheaf
  | cons i l ih => exact isInvertible_schemeTensor X (L i) (schemeTensorList X L l) (hL i) ih

/-- **The class in `Pic(X)` of `⨂_{i ∈ l} L i` is the sum over `l` of the classes.** -/
theorem picardClass_schemeTensorList (X : Scheme.{u})
    (L : ι → SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : ∀ i, IsInvertible X.presheaf X.ringCatIsSheaf (L i)) (l : List ι) :
    picardClass X.presheaf X.ringCatIsSheaf (schemeTensorList X L l)
        (isInvertible_schemeTensorList X L hL l) =
      (l.map fun i => picardClass X.presheaf X.ringCatIsSheaf (L i) (hL i)).sum := by
  induction l with
  | nil =>
      rw [List.map_nil, List.sum_nil]
      exact (picardClass_eq_zero_iff X.presheaf X.ringCatIsSheaf _
        (isInvertible_schemeTensorList X L hL [])).mpr ⟨Iso.refl _⟩
  | cons i l ih =>
      have h := picardClass_schemeTensor X (L i) (schemeTensorList X L l) (hL i)
        (isInvertible_schemeTensorList X L hL l)
      rw [List.map_cons, List.sum_cons, ← ih]
      exact h

/-- **The class in `Pic(X)` of `⨂_{i ∈ s} L i` is the sum over the `Finset` `s` of the
classes.** The object is formed over `s.toList`; the class does not depend on which list of the
elements of `s` is chosen, because this sum does not. -/
theorem picardClass_schemeTensorList_toList (X : Scheme.{u})
    (L : ι → SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : ∀ i, IsInvertible X.presheaf X.ringCatIsSheaf (L i)) (s : Finset ι) :
    picardClass X.presheaf X.ringCatIsSheaf (schemeTensorList X L s.toList)
        (isInvertible_schemeTensorList X L hL s.toList) =
      ∑ i ∈ s, picardClass X.presheaf X.ringCatIsSheaf (L i) (hL i) := by
  rw [picardClass_schemeTensorList, Finset.sum_map_toList]

/-- **The pullback class of `⨂_{i ∈ l} L i` is the sum over `l` of the pullback classes**, by
Tag 01CD and the triviality of the pullback of the structure sheaf. -/
theorem pullbackPicardClass_schemeTensorList (φ : X ⟶ Y)
    (L : ι → SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : ∀ i, IsInvertible Y.presheaf Y.ringCatIsSheaf (L i)) (l : List ι) :
    pullbackPicardClass φ (schemeTensorList Y L l)
        (isInvertible_schemeTensorList Y L hL l) =
      (l.map fun i => pullbackPicardClass φ (L i) (hL i)).sum := by
  induction l with
  | nil =>
      rw [List.map_nil, List.sum_nil]
      exact pullbackPicardClass_unit φ (isInvertible_unit Y.presheaf Y.ringCatIsSheaf)
  | cons i l ih =>
      have h := pullbackPicardClass_schemeTensor φ (L i) (schemeTensorList Y L l) (hL i)
        (isInvertible_schemeTensorList Y L hL l)
      rw [List.map_cons, List.sum_cons, ← ih]
      exact h

/-- **The pullback class of `⨂_{i ∈ s} L i` is the sum over the `Finset` `s` of the pullback
classes.** -/
theorem pullbackPicardClass_schemeTensorList_toList (φ : X ⟶ Y)
    (L : ι → SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : ∀ i, IsInvertible Y.presheaf Y.ringCatIsSheaf (L i)) (s : Finset ι) :
    pullbackPicardClass φ (schemeTensorList Y L s.toList)
        (isInvertible_schemeTensorList Y L hL s.toList) =
      ∑ i ∈ s, pullbackPicardClass φ (L i) (hL i) := by
  rw [pullbackPicardClass_schemeTensorList, Finset.sum_map_toList]

end Stacks.SheafOfModules

end
