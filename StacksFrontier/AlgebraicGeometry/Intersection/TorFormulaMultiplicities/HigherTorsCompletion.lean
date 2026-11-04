module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionMultiplicity
public import
  StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.HigherTorsMultiplicity
public import
  StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.MultiplicityFlatBaseChange

/-!
# The example of Tag 0B2S on a scheme

Let `X` be a nonsingular variety of dimension `4` over `ℂ`, let `p ∈ X` be a closed point and let
`V, W ⊂ X` be closed subvarieties, and assume there is an isomorphism
`𝒪_{X, p}^∧ ≅ ℂ[[x, y, z, w]]` carrying the ideal of `V` to `(xz, xw, yz, yw)` and the ideal of
`W` to `(x - z, y - w)`. Tag 0B2S asserts that then

* `length 𝒪_{X, p} ⧸ (I_V + I_W) = 3`, and
* `e(X, V · W, p) = 2`, the intersection multiplicity of the chapter, given by the Tor formula
  over `𝒪_{X, p}`.

`StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.HigherTorsMultiplicity`
computes both numbers inside `ℂ[[x, y, z, w]]`. This file transfers them to `𝒪_{X, p}` along the
completion map composed with the given isomorphism: for a Noetherian local ring that map is flat
and carries the maximal ideal onto the maximal ideal, so it preserves lengths and the Tor-formula
multiplicity (`Ideal.length_quotient_map_of_flat` and
`Ideal.localIntersectionMultiplicity_map_of_flat`).

## Main results

* `length_stalk_quotient_sup_eq_three_and_intersectionMultiplicity_eq_two`, in the namespace
  `Stacks.Intersection.TwoPlanes`: the two numbers of Tag 0B2S, for any locally Noetherian
  scheme, point and pair of closed subschemes with the stated completed local ring.

## Implementation notes

The ideal of `V` in `𝒪_{X, p}^∧` is the extension `I_{V, p} · 𝒪_{X, p}^∧` of the stalk of its
ideal sheaf, which is also the ideal of the completion of the local ring of `V` at `p`, since
completion commutes with quotients over a Noetherian ring. The isomorphism is only asked to be a
ring isomorphism.

Of the hypotheses of the source the proof uses only that the local ring at `p` is Noetherian,
which holds on every variety; nonsingularity and the dimension of `X` follow from the isomorphism
anyway, and neither the closedness of `p` nor the integrality of `V` and `W` is used. The theorem
is therefore stated for a locally Noetherian scheme, an arbitrary point and arbitrary closed
subschemes. That such `X, p, V, W` exist, with `X = 𝔸⁴_ℂ` and `V`, `W` integral, is
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.HigherTorsExistence`.

The multiplicity `Stacks.Intersection.intersectionMultiplicity V W p` is the alternating sum of
the lengths of `Tor_i(𝒪_{X, p} ⧸ I_V, 𝒪_{X, p} ⧸ I_W)`, while the computation in `ℂ[[x, y, z, w]]`
was done with the two arguments the other way round; the symmetry of Tor
(`Ideal.localIntersectionMultiplicity_quotient_comm`) reconciles the two.

## References

* [Stacks Project, Tag 0B2S](https://stacks.math.columbia.edu/tag/0B2S)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Stacks.Intersection.TwoPlanes

/-- **Tag 0B2S, the two numbers of the example.** Let `X` be a locally Noetherian scheme (for
instance a nonsingular variety of dimension `4` over `ℂ`), let `p ∈ X` and let `V`, `W` be closed
subschemes of `X`, given by their ideal sheaves. Assume there is a ring isomorphism
`e : 𝒪_{X, p}^∧ ≅ ℂ[[x, y, z, w]]` carrying the ideal of `V` in `𝒪_{X, p}^∧` to
`(xz, xw, yz, yw)` and the ideal of `W` to `(x - z, y - w)`. Then
`length_{𝒪_{X, p}} 𝒪_{X, p} ⧸ (I_V + I_W) = 3`, while the intersection multiplicity given by the
Tor formula over `𝒪_{X, p}` is `e(X, V · W, p) = 2`.

The proof transfers the computation in `ℂ[[x, y, z, w]]` along `𝒪_{X, p} → 𝒪_{X, p}^∧ ≅
ℂ[[x, y, z, w]]`, which is flat, local, and carries the maximal ideal onto the maximal ideal, so
that it preserves lengths and commutes with Tor. -/
@[stacks 0B2S "the example as stated: for X, p, V, W with an isomorphism of the completed local \
ring at p with ℂ[[x, y, z, w]] carrying the ideals of V and W to (xz, xw, yz, yw) and \
(x - z, y - w), the length of 𝒪_{X,p} / (I_V + I_W) is 3 and the chapter's intersection \
multiplicity e(X, V · W, p) is 2; stated for any locally Noetherian X, any point and any closed \
subschemes, which contains the source's nonsingular fourfold, closed point and subvarieties"]
theorem length_stalk_quotient_sup_eq_three_and_intersectionMultiplicity_eq_two
    {X : Scheme.{0}} [IsLocallyNoetherian X] (V W : X.IdealSheafData) (p : X)
    (e : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃+*
      MvPowerSeries (Fin 4) ℂ)
    (hV : ((IdealSheafData.stalk V p).map (algebraMap (X.presheaf.stalk p)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)))).map e =
        unionOfPlanes)
    (hW : ((IdealSheafData.stalk W p).map (algebraMap (X.presheaf.stalk p)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)))).map e =
        diagonalPlane) :
    Module.length (X.presheaf.stalk p)
        ((X.presheaf.stalk p) ⧸ IdealSheafData.stalk (V ⊔ W) p) = 3 ∧
      Stacks.Intersection.intersectionMultiplicity V W p = 2 := by
  set R := X.presheaf.stalk p
  let φ : R →+* MvPowerSeries (Fin 4) ℂ :=
    (e : AdicCompletion (maximalIdeal R) R →+* MvPowerSeries (Fin 4) ℂ).comp
      (algebraMap R (AdicCompletion (maximalIdeal R) R))
  have hflat : φ.Flat :=
    (RingHom.flat_algebraMap_iff.mpr inferInstance).comp
      (RingHom.Flat.of_bijective (f := (e : AdicCompletion (maximalIdeal R) R →+*
        MvPowerSeries (Fin 4) ℂ)) e.bijective)
  have hm : (maximalIdeal R).map φ = maximalIdeal (MvPowerSeries (Fin 4) ℂ) := by
    rw [← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map]
    exact map_ringEquiv_maximalIdeal e
  have hcoe : ∀ J : Ideal (AdicCompletion (maximalIdeal R) R),
      J.map e = J.map (e : AdicCompletion (maximalIdeal R) R →+* MvPowerSeries (Fin 4) ℂ) :=
    fun J => rfl
  have hV' : (IdealSheafData.stalk V p).map φ = unionOfPlanes := by
    rw [← hV, hcoe, Ideal.map_map]
  have hW' : (IdealSheafData.stalk W p).map φ = diagonalPlane := by
    rw [← hW, hcoe, Ideal.map_map]
  refine ⟨?_, ?_⟩
  · rw [← Ideal.length_quotient_map_of_flat φ hflat hm, IdealSheafData.stalk_sup, Ideal.map_sup,
      hV', hW']
    exact length_quotient_sup_eq_three
  · rw [Stacks.Intersection.intersectionMultiplicity_eq,
      ← Ideal.localIntersectionMultiplicity_map_of_flat φ hflat hm, hV', hW',
      Ideal.localIntersectionMultiplicity_quotient_comm]
    exact localIntersectionMultiplicity_eq_two

end Stacks.Intersection.TwoPlanes

end
