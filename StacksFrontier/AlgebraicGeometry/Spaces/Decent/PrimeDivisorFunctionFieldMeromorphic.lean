module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartFraction
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassRescaling
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsMeromorphicChartFraction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionsMeromorphic

/-!
# The embedding of Stacks 0ENK is computed by the meromorphic function of a rational function

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`. For a prime
divisor `Z` of `X` with generic point `ξ` there are two routes from the function field `R(X)`
into the total ring of fractions `Q(𝒪^h_{X, ξ})` of the henselian local ring at `ξ`:

* the embedding of Stacks 0ENK,
  `AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing`, which
  evaluates a rational function on `Spec Q(Γ(U, 𝒪_U))` for `(U, u)` the chosen affine elementary
  étale neighbourhood of `ξ` and then pushes along `Γ(U, 𝒪_U) → 𝒪_{U, u} → 𝒪^h_{X, ξ}`; and
* the passage `R(X) → Γ(X, 𝒦_X)` to a global meromorphic function of Stacks 0ENA, followed by
  the pullback of that meromorphic function to `Spec(𝒪_{U, u})` and the push into
  `Q(𝒪^h_{X, ξ})` used by the canonical ratio of Stacks 0EPR.

This file proves that **the two agree**, which is the first assertion of Stacks 0EPT, and
packages the statement as the hypothesis `hcomp` of
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul`.

Both routes are composed from the two halves proved elsewhere: over the chart `U` the two
images of a rational function in `Q(Γ(U, 𝒪_U))` are the same fraction `p / q` of regular
functions, by `AlgebraicGeometry.Space.exists_eq_mk'_rationalFunctionsToTotalFractionRing`, and
the two routes out of `𝒦_X(U)` into `Q(𝒪^h_{X, ξ})` agree on such a fraction, by
`AlgebraicGeometry.Space.PrimeDivisor.genericChartMeromorphicToGeneric_eq_mk'`.

## Main results

* `AlgebraicGeometry.Space.genericStalkMeromorphicToGeneric_rationalToMeromorphic_eq_emb`: the
  agreement for an arbitrary rational function, with the presentation of the schematic locus a
  parameter so that one and the same comparison `R(X) → Γ(X, 𝒦_X)` serves both directions.
* `AlgebraicGeometry.Space.exists_units_meromorphicFunctionEval_eq_emb`: **the hypothesis
  `hcomp`**. Every invertible rational function is an invertible global meromorphic function
  whose image in `Q(𝒪^h_{X, ξ})` is its image under the embedding of Stacks 0ENK, at every
  prime divisor at once.
* `AlgebraicGeometry.Space.exists_units_rationalFunctions_meromorphicFunctionEval_eq_emb`: the
  same read backwards — every invertible global meromorphic function is the meromorphic function
  of an invertible *rational* function, compatibly with the embedding. Surjectivity of
  `R(X) → Γ(X, 𝒦_X)` is the third conclusion of Stacks 0ENA; this is what carries the ratio of
  two regular meromorphic sections from `Γ(X, 𝒦_X)^*` into `R(X)^*`.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- **The two routes from `R(X)` into `Q(𝒪^h_{X, ξ})` agree**, for an arbitrary rational
function and at a given presentation `P` of the schematic locus at the codimension-zero points:
the meromorphic function of `x` of Stacks 0ENA, pulled back to `Spec(𝒪_{U, u})` and pushed along
`𝒪_{U, u} → 𝒪^h_{X, ξ}`, is the image of `x` under the embedding of Stacks 0ENK.

This is the content of the file; `P` is a parameter rather than chosen inside, so that the
*same* comparison `R(X) → Γ(X, 𝒦_X)` can be used in both directions — a rational function has
this image (`AlgebraicGeometry.Space.exists_units_meromorphicFunctionEval_eq_emb`) and, that
comparison being surjective by the third conclusion of Stacks 0ENA, every invertible global
meromorphic function arises from an invertible rational function with this image
(`AlgebraicGeometry.Space.exists_units_rationalFunctions_meromorphicFunctionEval_eq_emb`). -/
theorem genericStalkMeromorphicToGeneric_rationalToMeromorphic_eq_emb
    (P : CodimensionZeroPresentation B S hS X)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (x : rationalFunctions B S hS hX) (W : PrimeDivisor B S hS X) :
    W.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
        (chartMeromorphicRingedSitePullbackHom B S hS
          (W.genericStalkMorphism B S hS hX hdec)
          (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
          (W.genericStalkChartDiagram B S hS hX hdec)
          (meromorphicFunctionEval B S hS hX (W.genericEtaleChart B S hS hX hdec)
            (rationalToMeromorphic (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P hwa hfin x))) =
      (genericFractionEmbedding B S hS hX hdec hInt hN).emb W x := by
  have : IsAffine (W.genericEtaleChart B S hS hX hdec).obj.left.left.1 :=
    W.isAffine_genericChart B S hS hX hdec
  have : IsReduced (W.genericEtaleChart B S hS hX hdec).obj.left.left.1 :=
    W.isReduced_genericChart B S hS hX hdec hInt
  have : IsLocallyNoetherian (W.genericEtaleChart B S hS hX hdec).obj.left.left.1 :=
    W.isLocallyNoetherian_genericChart B S hS hX hdec hN
  have : IsLocalRing ↥(W.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (W.genericPoint B S hS X) hdec
  obtain ⟨p, q, hm, hA⟩ := exists_eq_mk'_rationalFunctionsToTotalFractionRing
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P hwa hfin (W.genericEtaleChart B S hS hX hdec) x
  refine Eq.trans (W.genericChartMeromorphicToGeneric_eq_mk' B S hS hX hdec hInt hN
    (meromorphicFunctionEval B S hS hX (W.genericEtaleChart B S hS hX hdec)
      (rationalToMeromorphic (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P hwa hfin x))
    p q hm) ?_
  exact (congrArg (W.chartTotalFractionRingToGeneric B S hS hX hdec) hA).symm

/-- The inputs of Stacks 0ENA on an integral, locally Noetherian, decent space. -/
private theorem exists_inputs_codimensionZeroPresentation
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :
    (∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0) ∧ HasLocallyFiniteIrreducibleComponents B S hS X ∧
      Nonempty (CodimensionZeroPresentation B S hS X) := by
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  exact ⟨fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz, hfin,
    ⟨(exists_codimensionZeroPresentation B S hS hX hfin
      (IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
        ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩)).some⟩⟩

include hInt hN in
/-- **The first assertion of Stacks 0EPT, in the form the conditional Stacks 0EPX needs.**  An
invertible rational function `f` on a decent, locally Noetherian, integral algebraic space is an
invertible global meromorphic function, and at the generic point of every prime divisor the
image of that meromorphic function in `Q(𝒪^h_{X, ξ})` — pulled back to `Spec(𝒪_{U, u})` and
pushed along `𝒪_{U, u} → 𝒪^h_{X, ξ}` — is the image of `f` under the embedding of Stacks 0ENK.

This is the hypothesis `hcomp` of
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul`,
read at the embedding `AlgebraicGeometry.Space.genericFractionEmbedding` of Stacks 0ENK. -/
theorem exists_units_meromorphicFunctionEval_eq_emb
    (f : (rationalFunctions B S hS hX)ˣ) :
    ∃ g : (↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ,
      ∀ W : PrimeDivisor B S hS X,
        W.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
            (chartMeromorphicRingedSitePullbackHom B S hS
              (W.genericStalkMorphism B S hS hX hdec)
              (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
              (W.genericStalkChartDiagram B S hS hX hdec)
              (meromorphicFunctionEval B S hS hX
                (W.genericEtaleChart B S hS hX hdec) g)) =
          (genericFractionEmbedding B S hS hX hdec hInt hN).emb W
            (f : rationalFunctions B S hS hX) := by
  -- the three inputs of Stacks 0ENA on such an `X`
  obtain ⟨hwa, hfin, ⟨P⟩⟩ := exists_inputs_codimensionZeroPresentation B S hS hX hInt hN
  exact ⟨Units.map (rationalToMeromorphicRingHom P hwa hfin).toMonoidHom f, fun W =>
    genericStalkMeromorphicToGeneric_rationalToMeromorphic_eq_emb B S hS hX hdec hInt hN P hwa
      hfin (f : rationalFunctions B S hS hX) W⟩

include hInt hN in
/-- **The first assertion of Stacks 0EPT read backwards.** Every *invertible global meromorphic
function* `g` on a decent, locally Noetherian, integral algebraic space is the meromorphic
function of an invertible rational function `f`, compatibly with the embedding of Stacks 0ENK:
at the generic point of every prime divisor the image of `g` in `Q(𝒪^h_{X, ξ})` is the image of
`f` under that embedding.

This is what turns the ratio of two regular meromorphic sections — an element of
`Γ(X, 𝒦_X)^*` by
`AlgebraicGeometry.Space.existsUnique_units_smul_eq_of_isRegularMeromorphicSection` — into an
element of `R(X)^*` read through the embedding, which is what the order of vanishing of Stacks
0EPR is stated against. Surjectivity of `R(X) → Γ(X, 𝒦_X)` is the third conclusion of Stacks
0ENA; invertibility of the preimage is injectivity of the same comparison applied to
`g · g⁻¹ = 1`. -/
theorem exists_units_rationalFunctions_meromorphicFunctionEval_eq_emb
    (g : (↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ) :
    ∃ f : (rationalFunctions B S hS hX)ˣ,
      ∀ W : PrimeDivisor B S hS X,
        W.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
            (chartMeromorphicRingedSitePullbackHom B S hS
              (W.genericStalkMorphism B S hS hX hdec)
              (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
              (W.genericStalkChartDiagram B S hS hX hdec)
              (meromorphicFunctionEval B S hS hX
                (W.genericEtaleChart B S hS hX hdec) g)) =
          (genericFractionEmbedding B S hS hX hdec hInt hN).emb W
            (f : rationalFunctions B S hS hX) := by
  obtain ⟨hwa, hfin, ⟨P⟩⟩ := exists_inputs_codimensionZeroPresentation B S hS hX hInt hN
  obtain ⟨x, hx⟩ := surjective_rationalToMeromorphic
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P hwa hfin g.val
  obtain ⟨y, hy⟩ := surjective_rationalToMeromorphic
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P hwa hfin g⁻¹.val
  have hxy : x * y = 1 := injective_rationalToMeromorphic
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P hwa hfin (by
      rw [rationalToMeromorphic_mul, rationalToMeromorphic_one, hx, hy]
      exact g.mul_inv)
  refine ⟨⟨x, y, hxy, (mul_comm y x).trans hxy⟩, fun W => ?_⟩
  refine Eq.trans ?_ (genericStalkMeromorphicToGeneric_rationalToMeromorphic_eq_emb B S hS hX
    hdec hInt hN P hwa hfin x W)
  exact congrArg (fun m : ↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)) =>
    W.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
      (chartMeromorphicRingedSitePullbackHom B S hS
        (W.genericStalkMorphism B S hS hX hdec)
        (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
        (W.genericStalkChartDiagram B S hS hX hdec)
        (meromorphicFunctionEval B S hS hX (W.genericEtaleChart B S hS hX hdec) m))) hx.symm

include hInt hN in
/-- **The hypothesis `hscale` of Stacks 0EPX at the canonical ratio, unconditionally.**  Every
invertible rational function rescales the chosen regular meromorphic section of an invertible
`𝒪_X`-module: there is a meromorphic section `t` with `s / s_ξ = f · (t / s_ξ)` at the generic
point of every prime divisor, with the image of `f` taken under the embedding of Stacks 0ENK.

This is `AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul`
with its single hypothesis discharged by
`AlgebraicGeometry.Space.exists_units_meromorphicFunctionEval_eq_emb`. -/
theorem exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (f : (rationalFunctions B S hS hX)ˣ) :
    ∃ t : MeromorphicSection.{u, u} B S hS X hX L,
      IsRegularMeromorphicSection.{u, u} B S hS X hX L t ∧
        ∀ W : PrimeDivisor B S hS X,
          (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W
              (regularMeromorphicSection B S hS hX hInt hN L hL) :
            W.genericTotalFractionRing B S hS hX hdec) =
            (genericFractionEmbedding B S hS hX hdec hInt hN).emb W
                (f : rationalFunctions B S hS hX) *
              (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W t :
                W.genericTotalFractionRing B S hS hX hdec) :=
  exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul B S hS hX hdec hInt hN
    (genericFractionEmbedding B S hS hX hdec hInt hN)
    (exists_units_meromorphicFunctionEval_eq_emb B S hS hX hdec hInt hN) L hL f

end AlgebraicGeometry.Space

end
