module

public import StacksFrontier.AlgebraicGeometry.Segre.DivBySectionTensor

/-!
# Dividing by a tensor of three nonvanishing sections

Let `L` be an invertible sheaf of modules on a ringed space with local stalks and let `s` be a
global section of `L`. Over an open contained in the nonvanishing locus of `s`, division by `s`
(`Stacks.SheafOfModules.divBySection`) is additive in the numerator
(`Stacks.SheafOfModules.divBySection_add`); this file packages that additivity as an additive
map, so that a quotient of a finite sum is the sum of the quotients and a quotient of an integer
multiple is that multiple of the quotient. Those are the two identities needed to divide an
antisymmetrised sum, such as a determinant formed from tensors of sections, by a single tensor.

For three invertible modules `F`, `G`, `H` the file also records the three-factor form of
`Stacks.SheafOfModules.divBySection_tensorSections`: the quotient of `tF ⊗ tG ⊗ tH` by
`sF ⊗ sG ⊗ sH` is the product `(tF / sF) · (tG / sG) · (tH / sH)` on any open where the three
denominators are nonvanishing. The tensor is bracketed as `(F ⊗ G) ⊗ H`, which is the bracketing
of `Stacks.SheafOfModules.Tensor.sheafTensor` iterated on the left.

## Main definitions

* `Stacks.SheafOfModules.divBySectionHom`: division by a nonvanishing global section as an
  additive map from the sections of `L` over an open to the sections of the structure sheaf.

## Main results

* `Stacks.SheafOfModules.divBySection_zero`, `Stacks.SheafOfModules.divBySection_neg`,
  `Stacks.SheafOfModules.divBySection_sum` and `Stacks.SheafOfModules.divBySection_zsmul`: the
  quotient respects the additive structure of the numerator.
* `Stacks.SheafOfModules.le_nonvanishingOpen_tensorSections₃`: an open on which three sections
  are nonvanishing is one on which their tensor is nonvanishing.
* `Stacks.SheafOfModules.divBySection_tensorSections₃`: **`(tF ⊗ tG ⊗ tH) / (sF ⊗ sG ⊗ sH)
  = (tF / sF) · (tG / sG) · (tH / sH)`.**

## Implementation notes

The additive map is built with `AddMonoidHom.mk'`, whose only input is additivity, so
`Stacks.SheafOfModules.divBySection_sum` and `Stacks.SheafOfModules.divBySection_zsmul` are
`map_sum` and `map_zsmul` and nothing is re-derived. The three-factor computation is two
applications of the two-factor one, the inner application being to the first factor of the outer
tensor; the containment hypothesis of the outer application is the two-factor
`Stacks.SheafOfModules.le_nonvanishingOpen_tensorSections` applied to the two inner denominators,
which is the same term that appears in the statement, so no transport is needed.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

section Additive

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [IsInvertible X.presheaf (structureSheafRing X).property L]

/-- `0 / s = 0`. -/
public theorem divBySection_zero (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) : divBySection L s hV 0 = 0 :=
  divBySection_eq_of_smul_eq L s hV (zero_smul _ _)

/-- **Division by a nonvanishing global section as an additive map.** -/
public def divBySectionHom (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) : L.val.obj (op V) →+ X.presheaf.obj (op V) :=
  AddMonoidHom.mk' (divBySection L s hV) (divBySection_add L s hV)

/-- The additive map `divBySectionHom L s hV` sends `t` to `t / s`. -/
@[simp] public theorem divBySectionHom_apply (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (t : L.val.obj (op V)) :
    divBySectionHom L s hV t = divBySection L s hV t := rfl

/-- `(-t) / s = -(t / s)`. -/
public theorem divBySection_neg (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (t : L.val.obj (op V)) :
    divBySection L s hV (-t) = -divBySection L s hV t :=
  map_neg (divBySectionHom L s hV) t

/-- **The quotient of a finite sum is the sum of the quotients.** -/
public theorem divBySection_sum {ι : Type*} (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (t : ι → L.val.obj (op V)) (u : Finset ι) :
    divBySection L s hV (∑ i ∈ u, t i) = ∑ i ∈ u, divBySection L s hV (t i) :=
  map_sum (divBySectionHom L s hV) t u

/-- **The quotient of an integer multiple is that multiple of the quotient.** -/
public theorem divBySection_zsmul (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (n : ℤ) (t : L.val.obj (op V)) :
    divBySection L s hV (n • t) = n • divBySection L s hV t :=
  map_zsmul (divBySectionHom L s hV) n t

end Additive

section Triple

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (F G H : _root_.SheafOfModules.{u} (structureSheafRing X))
  [IsInvertible X.presheaf (structureSheafRing X).property F]
  [IsInvertible X.presheaf (structureSheafRing X).property G]
  [IsInvertible X.presheaf (structureSheafRing X).property H]
  [IsInvertible X.presheaf (structureSheafRing X).property
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)]
  [IsInvertible X.presheaf (structureSheafRing X).property
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)).obj H)]

/-- **An open on which three global sections are nonvanishing is one on which their tensor is
nonvanishing.** -/
public theorem le_nonvanishingOpen_tensorSections₃ (sF : F.sections) (sG : G.sections)
    (sH : H.sections) {V : Opens X.carrier} (hVF : V ≤ nonvanishingOpen F sF)
    (hVG : V ≤ nonvanishingOpen G sG) (hVH : V ≤ nonvanishingOpen H sH) :
    V ≤ nonvanishingOpen
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)).obj H)
      (tensorSections _ H (tensorSections F G sF sG) sH) :=
  le_nonvanishingOpen_tensorSections _ H _ sH
    (le_nonvanishingOpen_tensorSections F G sF sG hVF hVG) hVH

/-- **The quotient of a tensor of three sections by a tensor of three sections is the product of
the three quotients**: `(tF ⊗ tG ⊗ tH) / (sF ⊗ sG ⊗ sH) = (tF / sF) · (tG / sG) · (tH / sH)`. -/
public theorem divBySection_tensorSections₃ (sF tF : F.sections) (sG tG : G.sections)
    (sH tH : H.sections) {V : Opens X.carrier} (hVF : V ≤ nonvanishingOpen F sF)
    (hVG : V ≤ nonvanishingOpen G sG) (hVH : V ≤ nonvanishingOpen H sH) :
    divBySection
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)).obj H)
        (tensorSections _ H (tensorSections F G sF sG) sH)
        (le_nonvanishingOpen_tensorSections₃ F G H sF sG sH hVF hVG hVH)
        ((tensorSections _ H (tensorSections F G tF tG) tH).eval (op V))
      = divBySection F sF hVF (tF.eval (op V)) * divBySection G sG hVG (tG.eval (op V))
        * divBySection H sH hVH (tH.eval (op V)) := by
  rw [divBySection_tensorSections
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) H
      (tensorSections F G sF sG) (tensorSections F G tF tG) sH tH
      (le_nonvanishingOpen_tensorSections F G sF sG hVF hVG) hVH,
    divBySection_tensorSections F G sF tF sG tG hVF hVG]

end Triple

end Stacks.SheafOfModules

end
