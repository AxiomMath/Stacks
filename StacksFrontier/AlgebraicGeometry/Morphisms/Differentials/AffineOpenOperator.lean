module

public import StacksFrontier.AlgebraicGeometry.DifferentialsAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DerivationGluing

/-!
# A derivation of the coordinate ring of an affine open is an operator over that open

Let `Y` be a scheme and `U` an affine open of `Y`. A single additive map `Γ(Y, U) → Γ(Y, U)`
obeying the Leibniz rule extends, uniquely, to a restriction-compatible Leibniz family of
additive maps on the sections over every open contained in `U`
(`Stacks.AlgebraicGeometry.DifferentialsAffine.existsUnique_restrictions`, the affine-open form
of Tag 01UO). This file reads such a family as a `DiffOp.RawOp` on the structure sheaf over `U`
— the shape in which the gluing of differential operators, and hence the gluing of relative
derivations, consumes local data.

## Main results

* `Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz` — **a Leibniz additive
  map on the coordinate ring of an affine open `U` is the value on `U` of a raw operator over
  `U` on the structure sheaf**, which is natural, obeys the Leibniz rule at every open contained
  in `U`, and sends a section restricted from `U` to the restriction of its image.
* `Stacks.AlgebraicGeometry.DifferentialsAffine.rawOp_ext` — two such raw operators which agree
  on `U` are equal.

## Implementation notes

The sections of `SheafOfModules.unit Y.ringCatSheaf` over an open are the sections of `𝒪_Y`
there, and the scalar action is the multiplication; the two are the same type presented
differently, so every statement below is written at the ring sections (through
`DiffOp.RawOp.unitOp`) and the passage to the module spelling is by definitional equality only.
That is the same discipline as in
`StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DerivationGluing`, and it is what keeps a
product of a ring section with an operator value from silently picking up the wrong `SMul`
instance.

The third conclusion of `exists_rawOp_of_leibniz` is the one that makes the result usable for a
derivation *relative to a base*: the value of the operator on a section restricted from `U` is
the restriction of the value on `U`, so the operator annihilates the restrictions of exactly
what the given map annihilates.

## References

* [Stacks Project, Tag 01UO](https://stacks.math.columbia.edu/tag/01UO)
* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.DifferentialsAffine

variable {Y : Scheme.{u}} {U : Y.Opens}

/-- **A Leibniz additive map on the coordinate ring of an affine open is a raw operator over
that open.** For `U` an affine open of a scheme `Y`, an additive map `Γ(Y, U) → Γ(Y, U)` obeying
the Leibniz rule is the value on `U` of a raw operator on the structure sheaf over `U` which is
compatible with restriction, obeys the Leibniz rule on the sections over every open contained in
`U`, and sends a section restricted from `U` to the restriction of its image. -/
theorem exists_rawOp_of_leibniz (hU : IsAffineOpen U) (D : Γ(Y, U) →+ Γ(Y, U))
    (hD : ∀ a b : Γ(Y, U), D (a * b) = a * D b + b * D a) :
    ∃ d : DiffOp.RawOp (SheafOfModules.unit Y.ringCatSheaf)
      (SheafOfModules.unit Y.ringCatSheaf) U,
      d.IsNatural ∧
      (∀ (W : Over U) (a b : Y.ringCatSheaf.obj.obj (op W.left)),
        d.unitOp W (a * b) = a * d.unitOp W b + b * d.unitOp W a) ∧
      (∀ (W : Over U) (a : Γ(Y, U)),
        d.unitOp W ((Y.presheaf.map (homOfLE W.hom.le).op).hom a) =
          (Y.presheaf.map (homOfLE W.hom.le).op).hom (D a)) := by
  obtain ⟨e, hmul, hres, htop⟩ :=
    exists_restrictions (M := SheafOfModules.unit Y.ringCatSheaf) hU D hD
  refine ⟨fun W ↦ e W.left W.hom.le, fun W W' h s ↦ hres W'.left W.left W'.hom.le h.left.le s,
    fun W a b ↦ hmul W.left W.hom.le a b, fun W a ↦ ?_⟩
  have h := hres U W.left le_rfl W.hom.le a
  rw [htop] at h
  exact h

/-- **Two raw operators over an affine open which agree on it are equal.** This is the
uniqueness half of `Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz`. -/
theorem rawOp_ext (hU : IsAffineOpen U)
    (d d' : DiffOp.RawOp (SheafOfModules.unit Y.ringCatSheaf)
      (SheafOfModules.unit Y.ringCatSheaf) U)
    (hnat : d.IsNatural) (hnat' : d'.IsNatural)
    (hmul : ∀ (W : Over U) (a b : Y.ringCatSheaf.obj.obj (op W.left)),
      d.unitOp W (a * b) = a * d.unitOp W b + b * d.unitOp W a)
    (hmul' : ∀ (W : Over U) (a b : Y.ringCatSheaf.obj.obj (op W.left)),
      d'.unitOp W (a * b) = a * d'.unitOp W b + b * d'.unitOp W a)
    (htop : d (Over.mk (CategoryStruct.id U)) = d' (Over.mk (CategoryStruct.id U))) :
    d = d' := by
  have key := eq_of_eq_on_affineOpen (M := SheafOfModules.unit Y.ringCatSheaf) hU
    (fun W hW ↦ d (Over.mk (homOfLE hW))) (fun W hW ↦ d' (Over.mk (homOfLE hW)))
    (fun W hW a b ↦ hmul (Over.mk (homOfLE hW)) a b)
    (fun W hW a b ↦ hmul' (Over.mk (homOfLE hW)) a b)
    (fun W W' hW h a ↦ hnat (Over.mk (homOfLE (h.trans hW))) (Over.mk (homOfLE hW))
      (Over.homMk (homOfLE h) (Subsingleton.elim _ _)) a)
    (fun W W' hW h a ↦ hnat' (Over.mk (homOfLE (h.trans hW))) (Over.mk (homOfLE hW))
      (Over.homMk (homOfLE h) (Subsingleton.elim _ _)) a)
    htop
  funext W
  exact congrFun (congrFun key W.left) W.hom.le

end Stacks.AlgebraicGeometry.DifferentialsAffine

end
