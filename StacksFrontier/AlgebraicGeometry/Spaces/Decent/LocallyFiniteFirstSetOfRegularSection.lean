module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHonestChartMemGenericModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCodimensionZeroHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionHonestChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallyFiniteNotMemGenericModuleStalk

/-!
# Stacks 0EPS, the first set

Let `S` be a scheme, let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ`
be an invertible `𝒪_X`-module and let `s` be a regular meromorphic section of `ℒ`.  Then

`{Z ⊂ X | Z a prime divisor with generic point ξ and s ∉ ℒ_ξ}`

is locally finite in `|X|`.  This is the first of the two collections of Stacks 0EPS, at the
hypotheses of the source.

## Main results

* `AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_memGenericModuleStalk_of_isIntegral`:
  **the first set of Stacks 0EPS.**

## Implementation notes

The proof has two steps.

*The honest chart.*
`AlgebraicGeometry.Space.exists_nonempty_chart_eval_eq_toMeromorphicSectionValue` produces an
étale chart `W` of `X` with nonempty underlying scheme over which `s` is an honest section of
`ℒ`, from hypotheses (a) and (b) of Stacks 0ENA — supplied by
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralCodimensionZeroHypotheses` from "locally Noetherian
integral" — and from a point of some chart of `X`, supplied by a surjective atlas chart and the
nonemptiness of `|X|`.  The open subset `U ⊆ |X|` of the source's argument is the image of `W`
on points, open because the structure morphism of an étale chart is open on points.

*The germ at a prime divisor whose generic point lies in `U`.*
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq_of_mem_range` puts the
germ of `s` at such a `ξ` inside `ℒ_ξ`.  Local finiteness of the remaining prime divisors is then
the Stacks 0EE5 step
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`.

Regularity of `s` is a hypothesis of the statement but is **not used**: the argument only uses
that `s` is a section of `ℒ` over a nonempty open subspace, which holds for every meromorphic
section of an invertible module.

Decency of `X` is both a consequence of integrality and a parameter `hdec`: the predicate
`AlgebraicGeometry.Space.PrimeDivisor.MemGenericModuleStalk` and the family `RR` of
henselizations cannot be written down without it, so it has to be in scope before the integrality
hypothesis can be stated.  The two proofs of it agree by proof irrelevance.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (RR : PrimeDivisor B S hS X → Type u) [∀ Z, CommRing (RR Z)] [∀ Z, IsLocalRing (RR Z)]
    [∀ Z : PrimeDivisor B S hS X,
      Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point) (RR Z)]
    [∀ Z : PrimeDivisor B S hS X, IsLocalRing.IsHenselization
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)
      (IsLocalRing.ResidueField
        ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point)) (RR Z)]
    (hRR : ∀ Z : PrimeDivisor B S hS X, B.Contains (Spec (.of (RR Z))))

include hX hdec in
/-- **Stacks 0EPS, the first set.**  Let `S` be a scheme, let `X` be a locally Noetherian
integral algebraic space over `S`, let `ℒ` be an invertible `𝒪_X`-module and let `s` be a regular
meromorphic section of `ℒ`.  Then the prime divisors `Z` of `X` whose generic point `ξ` satisfies
`s ∉ ℒ_ξ` are locally finite in `|X|`. -/
@[stacks 0EPS "the first set: the prime divisors whose generic point ξ has s ∉ ℒ_ξ are locally
  finite -- unconditionally, at the hypotheses of the source, the nonempty open subspace of the
  source's first sentence being produced rather than assumed"]
theorem locallyFinite_primeDivisor_not_memGenericModuleStalk_of_isIntegral
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hint : IsIntegralSpace B S hS X) (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    [DecidablePred fun Z : PrimeDivisor B S hS X ↦
      ¬ Z.MemGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s] :
    LocallyFinite fun Z : PrimeDivisor B S hS X ↦
      if ¬ Z.MemGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s then
        Z.support B S hS X
      else ∅ := by
  classical
  have hirr : IrreducibleSpace (points B S hS X) := hint.irreducibleSpace B S hS X
  -- A point of the scheme of a surjective atlas chart of `X`.
  obtain ⟨A, f, hfS, hfE⟩ := hX.exists_atlas
  obtain ⟨x, -⟩ := surjective_chartSchemeToPoints B S hS X
    (⟨CostructuredArrow.mk f, hfE⟩ : SmallEtale B S hS X)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX A f).1 hfS) hirr.toNonempty.some
  -- The honest chart, and the nonempty open subset of `|X|` it cuts out.
  obtain ⟨W, -, e, ⟨w⟩, he⟩ := exists_nonempty_chart_eval_eq_toMeromorphicSectionValue B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS)
    (forall_localRingDimension_eq_zero_of_isIntegralSpace B S hS
      (⟨X, hX⟩ : AlgebraicSpaces B S hS) hint)
    (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS
      (hF := hX) (hN := hN)) L hL s
    (⟨CostructuredArrow.mk f, hfE⟩ : SmallEtale B S hS X) x
  have hUopen : IsOpen (Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.1.hom)) :=
    isOpen_range_pointsMap_of_isEtale B S hS W.1.hom
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X).obj W)) hX
      ((isEtale_iff_presheaf_of_yoneda B S hS W.1.hom).mpr W.property)
  have hUne : (Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.1.hom)).Nonempty :=
    ⟨chartSchemeToPoints B S hS X W w,
      (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj W)).symm w,
      (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X W w).symm⟩
  -- Stacks 0EE5: the prime divisors whose generic point avoids that open are locally finite.
  exact locallyFinite_primeDivisor_of_genericPoint_notMem B S hS hX hN hirr
    (fun Z ↦ ¬ Z.MemGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s) _ hUopen hUne
    fun Z hZ hmem ↦ hZ (Z.memGenericModuleStalk_of_eval_eq_of_mem_range B S hS hX hdec (RR Z)
      (hRR Z) L hL s W e he hmem)

end AlgebraicGeometry.Space

end
