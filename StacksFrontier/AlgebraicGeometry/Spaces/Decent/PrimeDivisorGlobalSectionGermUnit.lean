module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGlobalSectionCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeInvertibleIdeal

/-!
# The germ of a global section is a unit off its zero scheme

Let `X` be a decent algebraic space over a scheme `S`, let `ℒ` be an invertible `𝒪_X`-module,
let `σ ∈ Γ(X, ℒ)` be a global section and let `Z ⊂ X` be a prime divisor with generic point `ξ`
and chosen affine elementary étale neighbourhood `(U, u)`.  This file proves

> if `ξ ∉ |Z(σ)|` then the coefficient of `σ` against the generator `s_ξ`, read as a germ in
> `𝒪_{U, u}` (`AlgebraicGeometry.Space.PrimeDivisor.globalSectionGerm`), is a unit.

`AlgebraicGeometry.Space.PrimeDivisor.span_globalSectionGerm_eq_map` identifies the principal
ideal of that germ with the extension to `𝒪_{U, u}` of the evaluation ideal of `σ` over `U`,
which for an invertible `ℒ` is the defining ideal of the zero scheme `Z(σ)` of Stacks 0845 over
`U` (`AlgebraicGeometry.Space.definingIdealAt_zeroScheme_eq_of_isInvertible`).  So the statement
is `Ideal.span_singleton_eq_top` applied to the general fact proved first here: the extension to
`𝒪_{U, u}` of the defining ideal of a closed subspace `Y ⊆ X` over `U` is the unit ideal as soon
as `ξ ∉ |Y|`.

That general fact is the contrapositive of the first half of the argument of
`AlgebraicGeometry.Space.PrimeDivisor.exists_closedSubspaceComponentImage_of_map_ne_top`: if the
extension is not the unit ideal then `u` lies in the zero locus over `U` of the defining ideal,
which is the image of the base change `Y ×_X U ⟶ U`
(`AlgebraicGeometry.Space.range_rep_snd_eq_zeroLocus_definingIdealAt`, Stacks 03H4), so `ξ` lies
in `|Y|`.  Only that half is used: no closure argument, no integrality, and no δ-dimension
bookkeeping, so nothing beyond decency of `X` is needed.

## Implementation notes

The statement is not derived by composing
`AlgebraicGeometry.Space.ker_closedSubspaceBaseChangeChartProj_zeroScheme` with
`AlgebraicGeometry.Space.range_closedSubspaceBaseChangeChartProj`, since these pass through
`AlgebraicGeometry.Space.closedSubspaceBaseChangeChart`, an `abbrev` over
`AlgebraicGeometry.Space.smallBaseChange` whose appearance in a statement makes the elaborator
unfold choice terms on every defeq check. Instead
`AlgebraicGeometry.Space.range_rep_snd_eq_zeroLocus_definingIdealAt` gives the same content (the
base change of a closed immersion along an affine chart is a closed immersion whose image is the
zero locus of its kernel) in terms of `AlgebraicGeometry.Space.definingIdealAt` alone.

The statement is not derived from the order of vanishing:
`AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_globalSectionMeromorphic` computes
`ord_{Z,ℒ}(σ)` as `(Ring.ord 𝒪_{U,u} a).toNat`, and `Ring.ord = 0 → IsUnit` is not available for
a ring that is not assumed normal; only the converse `Stacks.Chow.ord_eq_zero_of_isUnit` is.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.map_germ_definingIdealAt_eq_top_of_notMem`: the extension
  to `𝒪_{U, u}` of the defining ideal of a closed subspace missing `ξ` is the unit ideal.
* `AlgebraicGeometry.Space.PrimeDivisor.isUnit_globalSectionGerm_of_notMem_zeroScheme`:
  **the germ of a global section against `s_ξ` is a unit when `ξ ∉ |Z(σ)|`.**

## References

* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### A closed subspace missing the generic point extends to the unit ideal -/

/-- **The defining ideal of a closed subspace missing `ξ` extends to the unit ideal of
`𝒪_{U, u}`.**  Let `Z` be a prime divisor of a decent algebraic space `X` with generic point `ξ`
and chosen affine elementary étale neighbourhood `(U, u)`, and let `Y ⊆ X` be a closed subspace
with `ξ ∉ |Y|`.  Then the extension along `Γ(U) ⟶ 𝒪_{U, u}` of the defining ideal of `Y` over
`U` is all of `𝒪_{U, u}`. -/
theorem PrimeDivisor.map_germ_definingIdealAt_eq_top_of_notMem
    (Y : ClosedSubspaces B S hS X)
    (h : Z.genericPoint B S hS X ∉ subspacePointSet B S hS X Y.1) :
    Ideal.map ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.germ ⊤
          (Z.genericChart B S hS hX hdec).point trivial).hom
        (definingIdealAt B S hS ⟨X, hX⟩ Y (op (Z.genericEtaleChart B S hS hX hdec))) = ⊤ := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (Z.genericEtaleChart B S hS hX hdec).1.left) :=
    Z.isAffine_genericChart B S hS hX hdec
  by_contra hne
  have hzero : (Z.genericChart B S hS hX hdec).point ∈
      ((BigFppfOver.toScheme B S hS).obj
        (Z.genericEtaleChart B S hS hX hdec).1.left).zeroLocus
          {k | k ∈ definingIdealAt B S hS ⟨X, hX⟩ Y
            (op (Z.genericEtaleChart B S hS hX hdec))} := by
    refine (Scheme.mem_zeroLocus_iff _ _ _).2 fun k hk hku => hne ?_
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hk)
      ((Scheme.mem_basicOpen _ k (Z.genericChart B S hS hX hdec).point trivial).1 hku)
  have hz' : (Z.genericChart B S hS hX hdec).point ∈
      Set.range ((BigFppfOver.toScheme B S hS).map
        (Y.2.2.rep.snd (Z.genericEtaleChart B S hS hX hdec).1.hom)) :=
    (range_rep_snd_eq_zeroLocus_definingIdealAt B S hS ⟨X, hX⟩ Y
      (Z.genericEtaleChart B S hS hX hdec)) ▸ hzero
  refine h ?_
  rw [← (Z.genericChart B S hS hX hdec).map_point,
    mem_range_pointsMap_ι_iff B S hS ⟨X, hX⟩ Y (Z.genericChart B S hS hX hdec).toSpace,
    pointsToScheme_presheafPoint]
  exact hz'

/-! ### The germ of a global section off its zero scheme -/

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

include hL in
/-- **The germ of a global section against `s_ξ` is a unit off the zero scheme.**  Let `σ` be a
global section of an invertible `𝒪_X`-module on a decent algebraic space and let `Z` be a prime
divisor whose generic point `ξ` does *not* lie on the zero scheme `Z(σ)` of Stacks 0845.  Then
the coefficient of `σ` against the generator `s_ξ`, read as a germ in `𝒪_{U, u}`, is a unit. -/
theorem PrimeDivisor.isUnit_globalSectionGerm_of_notMem_zeroScheme (σ : L.sections)
    (h : Z.genericPoint B S hS X ∉
      subspacePointSet B S hS X (zeroScheme B S hS ⟨X, hX⟩ L σ).1) :
    IsUnit (Z.globalSectionGerm B S hS hX hdec L hL σ) := by
  refine Ideal.span_singleton_eq_top.1 ?_
  rw [Z.span_globalSectionGerm_eq_map B S hS hX hdec L hL σ,
    ← definingIdealAt_zeroScheme_eq_of_isInvertible B S hS ⟨X, hX⟩ L σ
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)
      (Z.genericEtaleChart B S hS hX hdec) (Z.isAffine_genericChart B S hS hX hdec)]
  exact Z.map_germ_definingIdealAt_eq_top_of_notMem B S hS hX hdec
    (zeroScheme B S hS ⟨X, hX⟩ L σ) h

end AlgebraicGeometry.Space

end
