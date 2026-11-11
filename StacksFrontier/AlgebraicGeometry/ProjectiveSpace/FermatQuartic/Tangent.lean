module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.TopExtVanishing

/-!
# The top `Ext` of the tangent sheaf of the Fermat quartic

Let `X ⊆ 𝐏³_k` be the Fermat quartic surface. Granting that `X` is smooth and proper over `k`,
equidimensional of dimension `2`, with no nonzero global `1`-forms, Serre duality gives
`Ext²_X(Ω_{X/k}, ω_X) = 0`; if moreover `ω_X ≅ 𝒪_X`, then `Ext²_X(Ω_{X/k}, 𝒪_X) = 0`, i.e.
`H²(X, T_X) = 0`: first-order deformations of `X` are unobstructed.

The hypotheses are the geometric inputs on `X`; this file only specialises
`Stacks.Duality.subsingleton_ext_relativeDifferentials_dualizingModule` and
`Stacks.Duality.subsingleton_ext_relativeDifferentials_of_iso` to `X`.

## Main results

* `AlgebraicGeometry.FermatQuartic`
  `.subsingleton_ext_relativeDifferentials_dualizingModule_of_vanishing`: `Ext²(Ω_{X/k}, ω_X) = 0`.
* `AlgebraicGeometry.FermatQuartic.subsingleton_ext_relativeDifferentials_unit_of_vanishing`:
  `Ext²(Ω_{X/k}, 𝒪_X) = 0` when `ω_X ≅ 𝒪_X`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k] [IsProper (toSpec k)] [AlgebraicGeometry.Smooth (toSpec k)]

/-- **`Ext²(Ω_{X/k}, ω_X) = 0` on the Fermat quartic `X`**, for `X` smooth and proper over `k`,
equidimensional of dimension `2`, with `H⁰(X, Ω_{X/k}) = 0`. -/
theorem subsingleton_ext_relativeDifferentials_dualizingModule_of_vanishing
    (hequi : TopologicalSpace.Equidimensional (fermatQuartic k))
    (hd : topologicalKrullDim (fermatQuartic k) = (2 : ℕ))
    (h0 : Subsingleton (SheafOfModules.unit (fermatQuartic k).ringCatSheaf ⟶
      Scheme.Hom.relativeDifferentials (toSpec k))) :
    Subsingleton (Ext.{u} (Scheme.Hom.relativeDifferentials (toSpec k))
      (Stacks.Duality.dualizingModule (toSpec k)) 2) :=
  Stacks.Duality.subsingleton_ext_relativeDifferentials_dualizingModule (toSpec k) hequi 2 hd h0

/-- **`Ext²(Ω_{X/k}, 𝒪_X) = 0` on the Fermat quartic `X`**, for `X` smooth and proper over `k`,
equidimensional of dimension `2`, with `H⁰(X, Ω_{X/k}) = 0` and `ω_X ≅ 𝒪_X`. -/
theorem subsingleton_ext_relativeDifferentials_unit_of_vanishing
    (hequi : TopologicalSpace.Equidimensional (fermatQuartic k))
    (hd : topologicalKrullDim (fermatQuartic k) = (2 : ℕ))
    (h0 : Subsingleton (SheafOfModules.unit (fermatQuartic k).ringCatSheaf ⟶
      Scheme.Hom.relativeDifferentials (toSpec k)))
    (hω : Nonempty (Stacks.Duality.dualizingModule (toSpec k) ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf)) :
    Subsingleton (Ext.{u} (Scheme.Hom.relativeDifferentials (toSpec k))
      (SheafOfModules.unit (fermatQuartic k).ringCatSheaf) 2) :=
  Stacks.Duality.subsingleton_ext_relativeDifferentials_of_iso (toSpec k) hequi 2 hd h0
    hω.some.symm

end AlgebraicGeometry.FermatQuartic

end
