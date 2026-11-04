module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension

/-!
# Projective towers

The projective bundle `P(𝒪_U^{n+1}) ⟶ U` with its twist `𝒪(1)` has the following recursive
structure, which is everything the proof of the projective space bundle formula
[Stacks, Tag 02TX] uses about a trivial projective bundle: the zero scheme `D` of the
coordinate section `T₀` of `𝒪(1)` is a relative effective Cartier divisor over `U`, the pair
`(D ⟶ U, 𝒪(1)|_D)` is again of this form one fibre dimension lower, and the complement of `D`
is an affine-space bundle over `U`. In fibre dimension zero the projection is an isomorphism and
`𝒪(1)` is trivial.

`Stacks.Chow.IsProjectiveTower n π L` records this structure for a morphism `π : P ⟶ U` and a
module `L` on `P`, as an inductive predicate; it is the interface between the scheme theory of
projective bundles and the intersection theory that consumes it.

## Main definitions

* `Stacks.Chow.zeroSchemeComplement` — the open complement of the zero scheme of a section.
* `Stacks.Chow.IsProjectiveTower` — the recursive structure.
* `Stacks.Chow.IsLocallyProjectiveTower` — the same, locally on the base.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The open complement of the zero scheme of a global section of an invertible module. -/
def zeroSchemeComplement (P : Scheme.{u}) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) : P.Opens :=
  ⟨((Stacks.Divisors.zeroScheme P L s).support : Set P)ᶜ,
    (Stacks.Divisors.zeroScheme P L s).support.isClosed.isOpen_compl⟩

/-- **A projective tower of fibre dimension `n`.** In fibre dimension zero the projection is an
isomorphism and the module is trivial. In fibre dimension `n + 1` the module `L` is invertible
and has a global section `s` whose zero scheme `D` is a relative effective Cartier divisor over
the base, flat over it of relative dimension `n`, such that `D` with the restriction of `L` is a
projective tower of fibre dimension `n` and the complement of `D` is an affine-space bundle of
rank `n + 1` over the base. The projection itself is flat, proper, locally of finite type and of
relative dimension `n + 1`.

This is the structure of `P(𝒪_U^{n+2}) ⟶ U` with `𝒪(1)` and the section `T₀`. -/
inductive IsProjectiveTower : (n : ℕ) → {P U : Scheme.{u}} → (π : P ⟶ U) → P.Modules → Prop
  | zero {P U : Scheme.{u}} (π : P ⟶ U) (L : P.Modules) (h : IsIso π)
      (hL : Nonempty (L ≅ SheafOfModules.unit P.ringCatSheaf)) :
      IsProjectiveTower 0 π L
  | succ {P U : Scheme.{u}} (n : ℕ) (π : P ⟶ U) (L : P.Modules)
      [hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
      [LocallyOfFiniteType π] [Flat π] [IsProper π]
      (hπ : AlgebraicGeometry.RelativeDimension π (n + 1)) (s : Γ(L, ⊤))
      (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π
        (Stacks.Divisors.zeroScheme P L s))
      [LocallyOfFiniteType ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)]
      (hq : AlgebraicGeometry.RelativeDimension
        ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π) n)
      (htower : IsProjectiveTower n ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme P L s).subschemeι).obj L))
      (haff : IsAffineSpaceBundle ((zeroSchemeComplement P L s).ι ≫ π) (n + 1)) :
      IsProjectiveTower (n + 1) π L

/-- **A morphism which is a projective tower locally on the base.** Every point of the base has
an open neighbourhood over which the restriction of `π`, with the restriction of `L`, is a
projective tower of fibre dimension `n`. -/
def IsLocallyProjectiveTower (n : ℕ) {P U : Scheme.{u}} (π : P ⟶ U) (L : P.Modules) : Prop :=
  ∀ x : U, ∃ V : U.Opens, x ∈ V ∧
    IsProjectiveTower n (π ∣_ V) ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)

end Stacks.Chow

end
