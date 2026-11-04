module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ClosedPointResidueField
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.RingTheory.Dualizing.NormalizedFiniteMap
public import StacksFrontier.RingTheory.Dualizing.NormalizedOverField

/-!
# Normalization of a relative dualizing complex at a closed point

Let `S` be a Noetherian scheme carrying a dualizing complex `ω_S^•`, let `p : X ⟶ S` be of
finite type and let `ω_X^•` be the dualizing complex normalized relative to `ω_S^•`. At a point
`x ∈ X` which is closed in `X` and lies over a closed point `s = p x` of `S`, the complex
`ω_{X,x}^•` is a normalized dualizing complex over `𝒪_{X,x}` as soon as `ω_{S,s}^•` is one over
`𝒪_{S,s}`. This is [Stacks, Tag 0AWL], which is
`Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex`.
This file proves the step of the source's argument downstream of [Stacks, Tag 0AA2].

The source's proof shrinks `X` to an affine neighbourhood of `x`, so that `ω_X^• = p^!ω_S^•`,
and then computes
`RHom_{𝒪_{X,x}}(κ(x), ω_{X,x}^•) = i_x^!ω_X^• = i_x^!p^!ω_S^• = π^!i_s^!ω_S^•`,
where `i_x : Spec κ(x) → X` and `i_s : Spec κ(s) → S` are the two closed immersions and
`π : Spec κ(x) → Spec κ(s)` is the induced morphism, finite because `κ(x)/κ(s)` is a finite
extension ([Stacks, Tag 01TF]). The identification of the first three terms is
[Stacks, Tag 0AA2] together with the compatibility of exceptional inverse image with
composition; it is the only step that mentions `p^!`, and *scheme-level exceptional inverse
image is not part of this development*. It is therefore carried here as an explicit hypothesis
`hiso`, in the shape the rest of the argument consumes: an isomorphism

`RHom_{𝒪_{X,x}}(κ(x), ω_{X,x}^•) ≅ RHom_{κ(s)}(κ(x), RHom_{𝒪_{S,s}}(κ(s), ω_{S,s}^•))`

in `D(κ(x))`. Nothing is chosen from an existence statement: `ω_X^•` is a parameter, and the
only thing said about it is `hiso`.

What the result below proves is the part of the argument downstream of that identification. The
right-hand side is handled by [Stacks, Tag 0AX1]
(`Dualizing.isNormalizedDualizingComplex_derivedHom`) applied twice: first along the residue map
`𝒪_{S,s} → κ(s)`, which is finite because it is surjective, turning the normalization hypothesis at
`s` into the statement that `RHom_{𝒪_{S,s}}(κ(s), ω_{S,s}^•)` is a normalized dualizing complex over
`κ(s)`; then along `κ(s) → κ(x)`, whose finiteness is
`AlgebraicGeometry.finite_residueField_of_isClosed`, the closed-point case of [Stacks, Tag 01TF].
Transporting along `hiso` shows that `RHom_{𝒪_{X,x}}(κ(x), ω_{X,x}^•)` is a normalized dualizing
complex over `κ(x)`, which is `Stacks.Duality.isNormalizedDualizingComplex_derivedHom_derivedStalk`.

## Main results

* `Stacks.Duality.isNormalizedDualizingComplex_derivedHom_derivedStalk` — granted the
  identification `hiso`, derived Hom from `κ(x)` into the derived stalk of `ω_X^•` is a
  normalized dualizing complex over `κ(x)`.

## Implementation notes

*The carried hypothesis.* `hiso` is the identification discussed above, the one step that uses
`p^!`, and it is the only link between `ω_X^•` and `ω_S^•`.

*The complex is taken in the unbounded derived category.* The source's `ω_X^•` lies in
`D⁺_{QCoh}(𝒪_X)`. The result below does not need that, so it takes an arbitrary object of
`D(𝒪_X)`; a complex in the bounded-below quasi-coherent category is a special case. Likewise
`ω_S^•` is an arbitrary object of `D(𝒪_S)`.

*The module universe.* `Dualizing.IsNormalizedDualizingComplex.{u, 0}` is the reading of the
predicate in which the module category is `ModuleCat.{u}`, which is where
`AlgebraicGeometry.derivedStalkFunctor` lands.

## References

* [Stacks Project, Tag 0AWL](https://stacks.math.columbia.edu/tag/0AWL)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {S X : Scheme.{u}}

/-- **Derived Hom from the residue field at a closed point is normalized over that field.**
Granted the identification `hiso` of [Stacks, Tag 0AA2] — derived Hom from `κ(x)` into the
derived stalk of `ω_X^•` is derived Hom from `κ(x)` over `κ(s)` of derived Hom from `κ(s)` into
the derived stalk of `ω_S^•` — normalization of `ω_{S,s}^•` over `𝒪_{S,s}` propagates to the
left-hand side.

Both steps are [Stacks, Tag 0AX1]: along the residue map `𝒪_{S,s} → κ(s)`, which is finite
because it is surjective, and then along `κ(s) → κ(x)`, which is finite because `x` is a closed
point of `X` ([Stacks, Tag 01TF]). -/
public theorem isNormalizedDualizingComplex_derivedHom_derivedStalk
    (p : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType p]
    {ωS : DerivedCategory S.Modules} {ωX : DerivedCategory X.Modules} {x : X}
    (hx : IsClosed ({x} : Set X))
    (hωSx : Dualizing.IsNormalizedDualizingComplex.{u, 0}
      ((derivedStalkFunctor (p x)).obj ωS))
    (hiso : Nonempty
      ((Dualizing.derivedHom.{u, 0} (IsLocalRing.residue (X.presheaf.stalk x))).obj
          ((derivedStalkFunctor x).obj ωX) ≅
        (Dualizing.derivedHom.{u, 0}
            (IsLocalRing.ResidueField.map (p.stalkMap x).hom)).obj
          ((Dualizing.derivedHom.{u, 0}
              (IsLocalRing.residue (S.presheaf.stalk (p x)))).obj
            ((derivedStalkFunctor (p x)).obj ωS)))) :
    Dualizing.IsNormalizedDualizingComplex.{u, 0}
      ((Dualizing.derivedHom.{u, 0} (IsLocalRing.residue (X.presheaf.stalk x))).obj
        ((derivedStalkFunctor x).obj ωX)) := by
  have hres : (IsLocalRing.residue (S.presheaf.stalk (p x))).Finite :=
    RingHom.Finite.of_surjective _ IsLocalRing.residue_surjective
  have h1 := Dualizing.isNormalizedDualizingComplex_derivedHom.{u, 0}
    (IsLocalRing.residue (S.presheaf.stalk (p x))) hres _ hωSx
  have hfin : (IsLocalRing.ResidueField.map (p.stalkMap x).hom).Finite :=
    finite_residueField_of_isClosed p hx
  have h2 := Dualizing.isNormalizedDualizingComplex_derivedHom.{u, 0}
    (IsLocalRing.ResidueField.map (p.stalkMap x).hom) hfin _ h1
  obtain ⟨e⟩ := hiso
  exact (Dualizing.isNormalizedDualizingComplex_congr.{u, 0} e).2 h2

end Stacks.Duality

end
