module

public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.EtaleFlatUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

/-!
# Purity of the branch locus in dimension one

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes, let `x` be a point of `X` and let
`y = f x`. Assume the local ring of `X` at `x` is normal, the local ring of `Y` at `y` is
regular, `f` is quasi-finite at `x`, the two local rings have the same dimension, and `f` is
unramified at every point specializing to `x` whose local ring has dimension one. Purity of the
branch locus, [Stacks, Tag 0BMB], asserts that `f` is then étale at `x`. This file proves the
case in which the common dimension is `1`, which is the base case of the induction on the
dimension by which the source proves the tag.

The proof is the source's. The target local ring `A` is regular of dimension one, hence a
discrete valuation ring ([Stacks, Tag 00PD]); the source local ring `B` is a Noetherian normal
local ring of dimension one, hence also a discrete valuation ring, by the same tag. The
hypothesis on one-dimensional generizations applies to `x` itself, so `f` is unramified at `x`,
and over a locally Noetherian target that is G-unramifiedness. What remains is flatness of
`A → B`, and over a discrete valuation ring flatness is torsion-freeness, so it is enough that
`A → B` be injective. Injectivity is where quasi-finiteness enters: the kernel is a prime of
`A`, because `B` is a domain; were it nonzero it would be the maximal ideal of `A`, `A` being a
principal ideal domain; but then the zero ideal and the maximal ideal of `B` would be two
distinct primes of `B` with the same contraction to `A`, which a quasi-finite map does not admit
(`Algebra.QuasiFinite.eq_of_le_of_under_eq`). Étaleness at `x` is then flatness together with
G-unramifiedness there, [Stacks, Tag 02GV].

## Main results

* `Stacks.PurityDimensionOne.injective_of_quasiFinite` — a quasi-finite local
  homomorphism from a one-dimensional regular local ring to a one-dimensional normal local ring
  is injective.
* `Stacks.PurityDimensionOne.flat_of_quasiFinite` — such a homomorphism is flat.
* `AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_eq_one` —
  **[Stacks, Tag 0BMB] in the case `dim 𝒪_{X,x} = dim 𝒪_{Y,y} = 1`.**

## The rest of the tag

The dimension of the local ring at `x` is the induction variable, and this module is its base
case `d = 1`. The range `1 ≤ d ≤ 2` is
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two` in
`PurityBranchLocus.DimensionAtMostTwo`, which subsumes the statement here: there flatness comes
from miracle flatness at the stalks, a normal local ring of dimension at most two being
Cohen-Macaulay, so no input from [Stacks, Tag 0BMA] is needed.

Above dimension two the residual content is exactly flatness of `𝒪_{Y,y} → 𝒪_{X,x}`, that is,
Cohen-Macaulayness of `𝒪_{X,x}`: see
`…_of_isMaximalCohenMacaulay` in `PurityBranchLocus.UnramifiedCodimensionOne`, which concludes
the tag at every dimension from that one property. Supplying it is the content of
[Stacks, Tag 0BMA] clause (2) at a general `d`, and for the *quasi-finite* algebra `𝒪_{X,x}`
rather than a finite one — `𝒪_{X,x}` is a localization of a finite algebra. The source crosses
from finite to quasi-finite by working étale locally on source and target
([Stacks, Tags 02VN, 036W]) and making `f` finite near `x` ([Stacks, Tag 02LK]); that crossing
also needs ascent of regularity along an étale morphism, [Stacks, Tags 0AGY, 025L].

## Implementation notes

**Normality** of the source local ring is `IsNormalRing`, the predicate of
`StacksFrontier/RingTheory/IntegrallyClosed/Defs.lean`: every localization at a prime is an
integrally closed domain. For a local ring that is the source's "normal", by
`IsNormalRing.of_isLocalRing`.

**The dimension hypothesis** is stated as the tag states it, `dim 𝒪_{X,x} = dim 𝒪_{Y,y}`,
together with the case restriction `dim 𝒪_{X,x} = 1` in place of the tag's `1 ≤ dim 𝒪_{X,x}`.

**Unramifiedness in codimension one** is the tag's hypothesis (5) verbatim. In dimension one it
is used only at `x` itself, where it is the source's own reading of the case ("in that case we
are assuming that `f` is unramified at `x`"); the content proved here is flatness.

`gUnramifiedAt_of_unramifiedAt` is restated here, as
`gUnramifiedAt_of_unramifiedAt_of_isLocallyNoetherian`, rather than imported: it is private in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityBranchLocus/UnramifiedCodimensionOne.lean`.

## References

* [Stacks Project, Tag 0BMB](https://stacks.math.columbia.edu/tag/0BMB)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
* [Stacks Project, Tag 02GV](https://stacks.math.columbia.edu/tag/02GV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.PurityDimensionOne

/-- A one-dimensional regular local ring is a discrete valuation ring. -/
private theorem isDomain_and_isDiscreteValuationRing_of_regular {A : Type u} [CommRing A]
    (hA : IsRegularLocalRing A) (hdA : ringKrullDim A = 1) :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  have := (isDiscreteValuationRing_tfae A).out 3 1
  exact this.mp ⟨hA, hdA⟩

/-- A quasi-finite local homomorphism from a one-dimensional regular local ring to a
one-dimensional normal local ring is injective.

Both rings are discrete valuation rings by [Stacks, Tag 00PD]. The kernel is a prime of the
source, the target being a domain, and a nonzero prime of a principal ideal domain is maximal,
hence equal to the maximal ideal. That would make the zero ideal and the maximal ideal of the
target two distinct primes with the same contraction, which quasi-finiteness forbids. -/
theorem injective_of_quasiFinite {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hA : IsRegularLocalRing A) (hB : IsNormalRing B)
    (hdA : ringKrullDim A = 1) (hdB : ringKrullDim B = 1) (hqf : φ.QuasiFinite) :
    Function.Injective φ := by
  let _ := hA
  let _ : Algebra A B := φ.toAlgebra
  have halg : algebraMap A B = φ := φ.algebraMap_toAlgebra
  have hqfA : Algebra.QuasiFinite A B :=
    RingHom.quasiFinite_algebraMap.mp (by rwa [halg])
  obtain ⟨hdomB, hicB⟩ := hB.of_isLocalRing
  let _ : IsDomain B := hdomB
  let _ : IsIntegrallyClosed B := hicB
  obtain ⟨_, _⟩ := isDomain_and_isDiscreteValuationRing_of_regular hA hdA
  have htfaeB := (isDiscreteValuationRing_tfae B).out 5 1
  obtain ⟨_, hdvrB⟩ := htfaeB.mp ⟨inferInstance, inferInstance, hdomB, hicB, hdB⟩
  let _ : IsDiscreteValuationRing B := hdvrB
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hker : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hkerm : RingHom.ker φ = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (_root_.IsPrime.to_maximal_ideal hne)
  have hunder : (⊥ : Ideal B).under A = (IsLocalRing.maximalIdeal B).under A := by
    rw [Ideal.under_def, Ideal.under_def, halg, ← RingHom.ker_eq_comap_bot,
      IsLocalRing.maximalIdeal_comap φ, hkerm]
  exact IsDiscreteValuationRing.not_a_field B
    (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) ⊥ (IsLocalRing.maximalIdeal B)
      bot_le hunder).symm

/-- A quasi-finite local homomorphism from a one-dimensional regular local ring to a
one-dimensional normal local ring is flat.

The source is a discrete valuation ring, in particular a Dedekind domain, over which a
torsion-free module is flat; and the target is a torsion-free module because it is a domain and
the homomorphism is injective. -/
@[ega "0 6.3.4" "special case"]
theorem flat_of_quasiFinite {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hA : IsRegularLocalRing A) (hB : IsNormalRing B)
    (hdA : ringKrullDim A = 1) (hdB : ringKrullDim B = 1) (hqf : φ.QuasiFinite) :
    φ.Flat := by
  let _ := hA
  let _ : Algebra A B := φ.toAlgebra
  have halg : algebraMap A B = φ := φ.algebraMap_toAlgebra
  have hinj : Function.Injective φ :=
    injective_of_quasiFinite φ hA hB hdA hdB hqf
  obtain ⟨hdomB, -⟩ := hB.of_isLocalRing
  let _ : IsDomain B := hdomB
  obtain ⟨_, _⟩ := isDomain_and_isDiscreteValuationRing_of_regular hA hdA
  have : NoZeroSMulDivisors A B := by
    refine ⟨fun {a b} hab => ?_⟩
    rw [Algebra.smul_def, halg] at hab
    rcases mul_eq_zero.mp hab with h | h
    · exact Or.inl (hinj (by rwa [map_zero]))
    · exact Or.inr h
  rw [← halg, RingHom.flat_algebraMap_iff]
  infer_instance

end Stacks.PurityDimensionOne

namespace AlgebraicGeometry

/-- Over a locally Noetherian target, unramifiedness at a point is G-unramifiedness there.

This restates a lemma which is private in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityBranchLocus/UnramifiedCodimensionOne.lean`
and cannot be imported. -/
theorem gUnramifiedAt_of_unramifiedAt_of_isLocallyNoetherian {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] (x : X) (h : UnramifiedAt f x) : GUnramifiedAt f x := by
  obtain ⟨V, hV, hxV, U, hU, hVU, halg⟩ := h
  let _ : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have _ : IsNoetherianRing Γ(Y, U) :=
    IsLocallyNoetherian.component_noetherian (⟨U, hU⟩ : Y.affineOpens)
  exact ⟨V, hV, hxV, U, hU, hVU,
    { formallyUnramified := halg.formallyUnramified
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp halg.finiteType }⟩

/-- **Purity of the branch locus, [Stacks, Tag 0BMB], in dimension one.** Let `f : X ⟶ Y` be a
morphism of locally Noetherian schemes and let `x : X` be a point whose local ring is normal,
with regular local ring at `f x`, at which `f` is quasi-finite, and such that the two local
rings have the same dimension, equal to one. If `f` is unramified at every point specializing
to `x` whose local ring has dimension one, then `f` is étale at `x`.

This is the tag with its hypothesis `1 ≤ dim 𝒪_{X,x}` restricted to `dim 𝒪_{X,x} = 1`, the base
case of the source's induction on the dimension. The whole range `1 ≤ dim 𝒪_{X,x} ≤ 2` is
`etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two` in
`PurityBranchLocus.DimensionAtMostTwo`, which subsumes this statement. -/
@[stacks 0BMB "the case `dim 𝒪_{X,x} = dim 𝒪_{Y,f x} = 1`, which is the base case of the
source's induction on the dimension; hypotheses (1), (2), (3) and (5) are the tag's own and
hypothesis (4) is the tag's with `1 ≤ d` restricted to `d = 1`. The range `1 ≤ d ≤ 2` is
`etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two` in
`PurityBranchLocus.DimensionAtMostTwo`.", ega "IV 21.12.14" "(v)", sga "1 X 3.1" "partial"]
theorem etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : quasiFiniteAt f x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hone : ringKrullDim (X.presheaf.stalk x) = 1)
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → UnramifiedAt f x') :
    EtaleAt f x :=
  (etaleAt_iff_isFlatAt_and_gUnramifiedAt f x).mpr
    ⟨Stacks.PurityDimensionOne.flat_of_quasiFinite (f.stalkMap x).hom hY hX
      (hdim.symm.trans hone) hone hqf.2,
      gUnramifiedAt_of_unramifiedAt_of_isLocallyNoetherian f x
        (hunr x (specializes_refl x) hone)⟩

end AlgebraicGeometry

end
