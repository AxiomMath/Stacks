module

public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicSectionsConstant
public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishingPrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData

/-!
# The order of vanishing of a regular meromorphic section along a prime divisor

Let `X` be a locally Noetherian integral scheme, let `L` be an invertible sheaf of
`𝒪_X`-modules, let `s` be a regular meromorphic section of `L` and let `Z` be a prime divisor of
`X` with generic point `ξ`. Writing `s = a • s_ξ` for a generator `s_ξ` of `L_ξ` and a scalar `a`
in the function field, the order of `a` in the local ring `𝒪_{X, ξ}` does not depend on the
generator, and that integer is the order of vanishing of `s` along `Z`.

Here `s` is read in the generic stalk through
`AlgebraicGeometry.meromorphicSectionSheafIsoConstant`, the isomorphism of Tag 01X5 part (2)
between the sheaf of meromorphic sections of a quasi-coherent module and the constant sheaf on
its generic stalk.

## Main definitions

* `AlgebraicGeometry.orderOfVanishingMeromorphicData`: a choice of the coordinate data, together
  with the quasi-coherence of `L`.
* `AlgebraicGeometry.orderOfVanishingMeromorphic`: the order of vanishing of `s` along `Z`.

## Main results

* `AlgebraicGeometry.nonempty_orderOfVanishingMeromorphicData`: the image of a meromorphic
  section under the comparison isomorphism has a coordinate with respect to some generator of
  `L_ξ`, and one integer is the order of that coordinate for every generator.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Let `X` be a locally Noetherian integral scheme, `L` an
invertible sheaf of `𝒪_X`-modules, `s` a meromorphic section of `L` and `Z` a prime divisor of
`X` with generic point `ξ`. Then the image of `s` under the comparison isomorphism of Tag 01X5
part (2) has a coordinate in the function field with respect to some generator of `L_ξ`, and the
order of that coordinate is one and the same integer for every generator. The data is packaged
with a witness of the quasi-coherence of `L`. -/
theorem nonempty_orderOfVanishingMeromorphicData
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : MeromorphicSection X.sheaf L)
    (Z : PrimeDivisor X) :
    Nonempty { q : PSigma (fun _ : L.IsQuasicoherent => ℤ) //
      letI : L.IsQuasicoherent := q.1
      let ξ := Z.genericPoint
      let R := X.presheaf.stalk ξ
      let K := X.functionField
      letI : Module R (L.presheaf.stalk ξ) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val ξ
      letI : Module K (L.presheaf.stalk (genericPoint X)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val (genericPoint X)
      let isCoordinate := fun (m : L.presheaf.stalk ξ) (a : K) =>
        ((meromorphicSectionSheafIsoConstant X L).val.hom.val.app
          (op (⊤ : X.Opens))) (s.val (op ⊤)) =
          constantGenericStalkModuleSection X L ⊤
            (a • (L.presheaf.stalkSpecializes
              ((genericPoint_spec X).specializes trivial)) m)
      (∃ m : L.presheaf.stalk ξ,
        (Submodule.span R {m} = ⊤) ∧ (∃ a : K, isCoordinate m a)) ∧
      (∀ (m : L.presheaf.stalk ξ)
        (_ : Submodule.span R {m} = ⊤) (a : K),
        isCoordinate m a → q.2 = X.ord a ξ) } := by
  have hqc : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  obtain ⟨q, hq⟩ := nonempty_orderOfVanishingData_primeDivisor X L Z
    ((meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
      (s.val (op ⊤)))
  exact ⟨⟨⟨hqc, q.2⟩, hq⟩⟩

/-- A choice of the data provided by
`AlgebraicGeometry.nonempty_orderOfVanishingMeromorphicData`: the quasi-coherence of `L`, the
order of vanishing of the regular meromorphic section `s` along the prime divisor `Z`, and its
characterization as the order of the coordinate of `s` with respect to any generator of `L` at
the generic point of `Z`. -/
@[stacks 02SF]
def orderOfVanishingMeromorphicData
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : MeromorphicSection X.sheaf L)
    (_hs : IsRegularMeromorphicSection X.sheaf L s)
    (Z : PrimeDivisor X) :
    { q : PSigma (fun _ : L.IsQuasicoherent => ℤ) //
      letI : L.IsQuasicoherent := q.1
      let ξ := Z.genericPoint
      let R := X.presheaf.stalk ξ
      let K := X.functionField
      letI : Module R (L.presheaf.stalk ξ) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val ξ
      letI : Module K (L.presheaf.stalk (genericPoint X)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val (genericPoint X)
      let isCoordinate := fun (m : L.presheaf.stalk ξ) (a : K) =>
        ((meromorphicSectionSheafIsoConstant X L).val.hom.val.app
          (op (⊤ : X.Opens))) (s.val (op ⊤)) =
          constantGenericStalkModuleSection X L ⊤
            (a • (L.presheaf.stalkSpecializes
              ((genericPoint_spec X).specializes trivial)) m)
      (∃ m : L.presheaf.stalk ξ,
        (Submodule.span R {m} = ⊤) ∧ (∃ a : K, isCoordinate m a)) ∧
      (∀ (m : L.presheaf.stalk ξ)
        (_ : Submodule.span R {m} = ⊤) (a : K),
        isCoordinate m a → q.2 = X.ord a ξ) } :=
  Classical.choice (nonempty_orderOfVanishingMeromorphicData X L s Z)

/-- The order of vanishing along a prime divisor `Z` of a regular meromorphic section `s` of an
invertible module `L` on a locally Noetherian integral scheme: the order in `𝒪_{X, ξ}` of the
coordinate of `s` with respect to a generator of `L_ξ`, where `ξ` is the generic point of `Z`. -/
@[stacks 02SF]
def orderOfVanishingMeromorphic
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (Z : PrimeDivisor X) : ℤ :=
  (orderOfVanishingMeromorphicData X L s hs Z).val.2

end AlgebraicGeometry

end
