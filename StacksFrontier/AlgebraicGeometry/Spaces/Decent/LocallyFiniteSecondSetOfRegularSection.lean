module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericFreeGeneratorOfHonestChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallyFiniteFirstSetOfRegularSection
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingChart

/-!
# Stacks 0EPS, the second set

Let `S` be a scheme, let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ`
be an invertible `𝒪_X`-module and let `s` be a regular meromorphic section of `ℒ`.  Then

`{Z ⊂ X | Z a prime divisor with generic point ξ and s does not generate ℒ_ξ}`

is locally finite in `|X|`, at the hypotheses of the source.  The second collection of
Stacks 0EPS — the prime divisors with `ord_{Z, ℒ}(s) ≠ 0` — is *contained* in that set, because
`ord_{Z, ℒ}(s) = 0` wherever `s` generates `ℒ_ξ`: the ratio `s / s_ξ` of Stacks 0EPR is then a
unit of `𝒪^h_{X, ξ}`.

## Main results

* `locallyFinite_primeDivisor_not_generatesGenericModuleStalk_of_isIntegral`: **the generating
  set of Stacks 0EPS** is locally finite, at the source's hypotheses.
* `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_of_isIntegral`: **the second
  set of Stacks 0EPS**, from the single hypothesis `hord` that `ord_{Z, ℒ}(s)` vanishes wherever
  `s` generates `ℒ_ξ`.

## Implementation notes

The proof of the first statement has two steps.

*The generating chart.*
`AlgebraicGeometry.Space.exists_nonempty_generating_chart_eval_eq_toMeromorphicSectionValue`
produces an étale chart `W` of `X` with nonempty underlying scheme over which `s` is a *free
generator* of `ℒ`, there and over every chart below; this is where regularity of `s` is used.
The open subset `U ⊆ |X|` of the source's argument is the image of `W` on points.

*The germ at a prime divisor whose generic point lies in `U`.*
`AlgebraicGeometry.Space.PrimeDivisor.generatesGenericModuleStalk_of_eval_eq_of_mem_range` makes
the germ of `s` at such a `ξ` a free generator of `ℒ_ξ`.  Local finiteness of the remaining prime
divisors is then the Stacks 0EE5 step
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`.

*What `hord` is, and why it is a hypothesis.*  The second statement replaces the quadruple
`(U, hUopen, hUne, hgen)` of
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero` — the open subspace that the
source produces and that statement assumes — by the algebraic hypothesis that
`ord_{Z, ℒ}(s) = 0` at a prime divisor where `s` generates `ℒ_ξ`.  The whole geometry of
Stacks 0EPS is discharged; what is left is a property of the *ratio*, and it is a hypothesis for
the reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection`: `ord_{Z, ℒ}(s)` is taken
there against an unconstrained parameter `ratio`, so nothing ties it to the germ of `s` at `ξ`.
For the canonical ratio of
`AlgebraicGeometry.Space.PrimeDivisor.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm`,
`hord` is the composite of two statements — a free generator of `ℒ_ξ` makes the ratio the
image of a unit of `𝒪^h_{X, ξ}`, and
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit` then gives `0`.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
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
/-- **Stacks 0EPS, the generating set.**  Let `S` be a scheme, let `X` be a locally Noetherian
integral algebraic space over `S`, let `ℒ` be an invertible `𝒪_X`-module and let `s` be a regular
meromorphic section of `ℒ`.  Then the prime divisors `Z` of `X` whose generic point `ξ` is such
that `s` does **not** generate `ℒ_ξ` are locally finite in `|X|`. -/
@[stacks 0EPS "the generating set: the prime divisors whose generic point ξ has s not generating
  ℒ_ξ are locally finite -- unconditionally, at the hypotheses of the source, the nonempty open
  subspace of the source's first sentence being produced rather than assumed; the second set of
  the source is contained in this one"]
theorem locallyFinite_primeDivisor_not_generatesGenericModuleStalk_of_isIntegral
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hint : IsIntegralSpace B S hS X) (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    [DecidablePred fun Z : PrimeDivisor B S hS X ↦
      ¬ Z.GeneratesGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s] :
    LocallyFinite fun Z : PrimeDivisor B S hS X ↦
      if ¬ Z.GeneratesGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s then
        Z.support B S hS X
      else ∅ := by
  classical
  have hirr : IrreducibleSpace (points B S hS X) := hint.irreducibleSpace B S hS X
  -- A point of the scheme of a surjective atlas chart of `X`.
  obtain ⟨A, f, hfS, hfE⟩ := hX.exists_atlas
  obtain ⟨x, -⟩ := surjective_chartSchemeToPoints B S hS X
    (⟨CostructuredArrow.mk f, hfE⟩ : SmallEtale B S hS X)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX A f).1 hfS) hirr.toNonempty.some
  -- The generating chart, and the nonempty open subset of `|X|` it cuts out.
  obtain ⟨W, -, e, ⟨w⟩, he, hfree⟩ :=
    exists_nonempty_generating_chart_eval_eq_toMeromorphicSectionValue B S hS
      (⟨X, hX⟩ : AlgebraicSpaces B S hS)
      (forall_localRingDimension_eq_zero_of_isIntegralSpace B S hS
        (⟨X, hX⟩ : AlgebraicSpaces B S hS) hint)
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS
        (hF := hX) (hN := hN)) L hL s hreg
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
    (fun Z ↦ ¬ Z.GeneratesGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s) _ hUopen hUne
    fun Z hZ hmem ↦ hZ (Z.generatesGenericModuleStalk_of_eval_eq_of_mem_range B S hS hX hdec
      (RR Z) (hRR Z) L hL s W e he hfree hmem)

section Order

variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

include hX hdec in
/-- **Stacks 0EPS, the second set.**  Let `S` be a scheme, let `X` be a locally Noetherian
integral algebraic space over `S`, let `ℒ` be an invertible `𝒪_X`-module and let `s` be a regular
meromorphic section of `ℒ`.  Then the prime divisors `Z` with `ord_{Z, ℒ}(s) ≠ 0` are locally
finite in `|X|`, provided `ord_{Z, ℒ}(s) = 0` wherever `s` generates `ℒ_ξ`.

That proviso, `hord`, is the only hypothesis beyond the source's. -/
@[stacks 0EPS "the second set: the prime divisors with ord_{Z,ℒ}(s) ≠ 0 are locally finite, at
  the hypotheses of the source together with `hord`, the vanishing of ord_{Z,ℒ}(s) where s
  generates ℒ_ξ -- which the ratio parameter of orderOfVanishingSection does not supply by
  itself"]
theorem locallyFinite_divisorCoefficients_ne_zero_of_isIntegral
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hint : IsIntegralSpace B S hS X) (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (ratio : LocalRatioFamily.{u, u} B S hS hX hdec L)
    (hord : ∀ Z : PrimeDivisor B S hS X,
      Z.GeneratesGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s →
        divisorCoefficients.{u, u} B S hS hX hdec L s ratio Z = 0) :
    LocallyFinite fun Z : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, u} B S hS hX hdec L s ratio Z = 0 then ∅
      else Z.support B S hS X := by
  classical
  refine (locallyFinite_primeDivisor_not_generatesGenericModuleStalk_of_isIntegral B S hS hX
    hdec RR hRR hN hint L hL s hreg).subset fun Z ↦ ?_
  by_cases hZ : divisorCoefficients.{u, u} B S hS hX hdec L s ratio Z = 0
  · simp [hZ]
  · simp [hZ, mt (hord Z) hZ]

end Order

end AlgebraicGeometry.Space

end
