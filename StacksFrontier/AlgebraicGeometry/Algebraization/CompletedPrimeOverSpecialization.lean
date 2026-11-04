module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesLocallyFreeOutside
public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.RingTheory.AdicCompletion.DepthMinimalPrime
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.RingTheory.Catenary.Universes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A prime of the completed local ring over a specialization

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)`, the closed subscheme `Y = V(I)` and the open complement `U = X \ V(𝔞)`. Let
`x ⤳ y` be a specialization of points of `U`, so that `x` is the more generic of the two, and
write `𝔭 ⊆ A` for the prime of `x`.

The local ring `𝒪_{U,y}` is the localization `A_𝔮` at the prime `𝔮` of `y`, and the point `x`
is visible inside it as the prime `𝔭 𝒪_{U,y}`, which is also the contraction of the maximal
ideal of `𝒪_{U,x}` along the specialization map. The file identifies those two descriptions,
computes the dimension of the fibre `𝒪_{U,y} / 𝔭 𝒪_{U,y}` as the height of the image of `𝔮` in
`A/𝔭`, and then lifts the prime to the `I`-adically completed local ring `𝒪_{U,y}^∧`: over a
point of `U ∩ Y` the completion is faithfully flat, so some prime of it minimal over
`𝔭 𝒪_{U,y}^∧` still lies over `𝔭 𝒪_{U,y}`, it avoids `I 𝒪_{U,y}^∧` as soon as `I ⊄ 𝔭`, and the
dimension splitting of [Stacks, Tag 0EHW] bounds the dimension of its quotient by the same
height. This is the local input of the dimension bookkeeping in [Stacks, Tag 0EJ5].

## Main results

* `Stacks.Algebraization.isLocalization_atPrime_pointStalk` — `𝒪_{U,y}` is the localization of
  `A` at the prime under `y`, for the algebra structure given by `baseToPointStalk`.
* `Stacks.Algebraization.stalkSpecializes_comp_baseToPointStalk` — the specialization map on
  stalks is compatible with the maps out of `A`.
* `Stacks.Algebraization.baseIdeal_le_underlyingPrime_of_specializes` — the prime of `x` is
  contained in the prime of `y`.
* `Stacks.Algebraization.comap_under_maximalIdeal_stalk_eq` and
  `Stacks.Algebraization.under_maximalIdeal_stalk_eq_map` — the contraction of the maximal
  ideal of `𝒪_{U,x}` to `𝒪_{U,y}` is `𝔭 𝒪_{U,y}`, and it contracts to `𝔭` on `A`.
* `Stacks.Algebraization.le_baseIdeal_iff_stalk_idealOnOpen_le_map` — `I 𝒪_{U,y}` lies in
  `𝔭 𝒪_{U,y}` exactly when `I ⊆ 𝔭`.
* `Stacks.Algebraization.ringKrullDim_quotient_map_baseToPointStalk` — the dimension of the
  fibre of `U` over `x` at `y`.
* `Stacks.Algebraization.exists_primeSpectrum_completedLocalRing_of_specializes` — the prime of
  the completed local ring, with its three properties.

## Implementation notes

The algebra structure `Algebra 𝒪_{U,y} 𝒪_{U,x}` is the one induced by
`TopCat.Presheaf.stalkSpecializes`, introduced as a `let` in each statement rather than
registered as an instance, exactly as in
`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`: an instance would place an
`Algebra` between the stalks at every specializing pair of points of every scheme.

The identification of `𝒪_{U,y}` with `A_𝔮` is taken through `pointStalkRingEquiv`, whose
compatibility with the maps out of `A` is
`Stacks.Algebraization.pointStalkRingEquiv_baseToPointStalk_apply`; from it the whole
`IsLocalization` package on the stalk follows, which is what the ideal-theoretic statements are
proved with. The composite of `baseToPointStalk` at `y` with the specialization map is
`baseToPointStalk` at `x`, which is what makes the two descriptions of the prime of `x` agree.

The dimension statement is phrased with `Ideal.height` on the quotient `A/𝔭` rather than with
`ringKrullDim`, because that is the form in which the bound enters [Stacks, Tag 0EJ5]: there the
height is bounded by the dimension of a quotient of `A/I`, and the conclusion is compared
against an integer through `krullDimToEInt`.

## References

* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.Algebraization

/-- **The local ring of `U` at `y` is a localization of `A`.** For any algebra structure on
`𝒪_{U,y}` over `A` whose structure map is `baseToPointStalk`, the stalk is the localization of
`A` at the prime under `y`. -/
public theorem isLocalization_atPrime_pointStalk (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) [Algebra S.A (S.U.toScheme.presheaf.stalk y)]
    (h : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y) :
    IsLocalization.AtPrime (S.U.toScheme.presheaf.stalk y) (underlyingPrime S y).asIdeal := by
  set q := (underlyingPrime S y).asIdeal
  let e := pointStalkRingEquiv S y
  have hcomp : ∀ a : S.A, e (algebraMap S.A (S.U.toScheme.presheaf.stalk y) a) =
      algebraMap S.A (Localization.AtPrime q) a := by
    intro a
    rw [h]
    exact pointStalkRingEquiv_baseToPointStalk_apply S y a
  let eAlg : Localization.AtPrime q ≃ₐ[S.A] S.U.toScheme.presheaf.stalk y :=
    { e.symm with
      commutes' := fun a => by
        apply e.injective
        show e (e.symm (algebraMap S.A (Localization.AtPrime q) a)) = _
        rw [e.apply_symm_apply, hcomp a] }
  exact IsLocalization.isLocalization_of_algEquiv q.primeCompl eAlg

/-- The stalk is the localization of `A` at the prime under `y`, for the algebra structure
`(baseToPointStalk S y).toAlgebra`. -/
private theorem isLocalization_atPrime_pointStalk_toAlgebra (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) :
    letI : Algebra S.A (S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
    IsLocalization.AtPrime (S.U.toScheme.presheaf.stalk y) (underlyingPrime S y).asIdeal :=
  @isLocalization_atPrime_pointStalk S y (baseToPointStalk S y).toAlgebra rfl

/-- The specialization map on stalks is compatible with the maps out of `A`. -/
public theorem stalkSpecializes_comp_baseToPointStalk (S : AlgebraizationSituation.{u})
    (x y : S.U.toScheme) (hxy : x ⤳ y) :
    (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.comp (baseToPointStalk S y) =
      baseToPointStalk S x := by
  ext a
  show (S.U.toScheme.presheaf.stalkSpecializes hxy).hom
      ((S.U.ι.stalkMap y).hom ((S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom
        ((Scheme.ΓSpecIso (.of S.A)).inv.hom a))) = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply S.U.ι x y hxy,
    TopCat.Presheaf.germ_stalkSpecializes_apply]
  rfl

/-- **Tag 0EJ5, the prime of the generic point.** If `x ⤳ y` in `U`, the prime of `A` at `x` is
contained in the prime at `y`. -/
public theorem baseIdeal_le_underlyingPrime_of_specializes (S : AlgebraizationSituation.{u})
    (x y : S.U.toScheme) (hxy : x ⤳ y) :
    (S.U.ι.base x).asIdeal ≤ (underlyingPrime S y).asIdeal :=
  (PrimeSpectrum.le_iff_specializes _ _).mpr (hxy.map S.U.ι.continuous)

/-- The contraction to `A` of the prime of `𝒪_{U,y}` cut out by the maximal ideal of `𝒪_{U,x}`
is the prime of `A` at `x`. -/
public theorem comap_under_maximalIdeal_stalk_eq (S : AlgebraizationSituation.{u})
    (x y : S.U.toScheme) (hxy : x ⤳ y) :
    letI : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
      (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
    ((maximalIdeal (S.U.toScheme.presheaf.stalk x)).under
        (S.U.toScheme.presheaf.stalk y)).comap (baseToPointStalk S y) =
      (S.U.ι.base x).asIdeal := by
  let _ : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
    (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
  let _ : Algebra S.A (S.U.toScheme.presheaf.stalk x) := (baseToPointStalk S x).toAlgebra
  have hloc := isLocalization_atPrime_pointStalk_toAlgebra S x
  show ((maximalIdeal (S.U.toScheme.presheaf.stalk x)).comap
    (algebraMap (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x))).comap
      (baseToPointStalk S y) = _
  rw [Ideal.comap_comap,
    show (algebraMap (S.U.toScheme.presheaf.stalk y)
        (S.U.toScheme.presheaf.stalk x)).comp (baseToPointStalk S y) =
      baseToPointStalk S x from stalkSpecializes_comp_baseToPointStalk S x y hxy]
  exact IsLocalization.AtPrime.under_maximalIdeal (S.U.toScheme.presheaf.stalk x)
    (underlyingPrime S x).asIdeal

/-- **Tag 0EJ5, the prime of `𝒪_{U,y}` at `x`.** The contraction to `𝒪_{U,y}` of the maximal
ideal of `𝒪_{U,x}` is the ideal generated by the prime of `x`. -/
public theorem under_maximalIdeal_stalk_eq_map (S : AlgebraizationSituation.{u})
    (x y : S.U.toScheme) (hxy : x ⤳ y) :
    letI : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
      (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
    (maximalIdeal (S.U.toScheme.presheaf.stalk x)).under (S.U.toScheme.presheaf.stalk y) =
      (S.U.ι.base x).asIdeal.map (baseToPointStalk S y) := by
  let _ : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
    (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
  let _ : Algebra S.A (S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
  have hloc := isLocalization_atPrime_pointStalk_toAlgebra S y
  rw [← IsLocalization.map_under (underlyingPrime S y).asIdeal.primeCompl
    (S.U.toScheme.presheaf.stalk y)
    ((maximalIdeal (S.U.toScheme.presheaf.stalk x)).under (S.U.toScheme.presheaf.stalk y))]
  exact congrArg (Ideal.map (baseToPointStalk S y))
    (comap_under_maximalIdeal_stalk_eq S x y hxy)

/-- **Tag 0EJ5, the stalk of `I𝒪_U` against the prime of `x`.** The stalk of `I𝒪_U` at `y` lies
inside the ideal generated by the prime of `x` exactly when `I` lies inside that prime. -/
public theorem le_baseIdeal_iff_stalk_idealOnOpen_le_map (S : AlgebraizationSituation.{u})
    (x y : S.U.toScheme) (hxy : x ⤳ y) :
    S.I ≤ (S.U.ι.base x).asIdeal ↔
      IdealSheafData.stalk (idealOnOpen S) y ≤
        (S.U.ι.base x).asIdeal.map (baseToPointStalk S y) := by
  let _ : Algebra S.A (S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
  have hloc := isLocalization_atPrime_pointStalk_toAlgebra S y
  have _ : (S.U.ι.base x).asIdeal.IsPrime := (S.U.ι.base x).isPrime
  have hcontract : ((S.U.ι.base x).asIdeal.map (baseToPointStalk S y)).comap
      (baseToPointStalk S y) = (S.U.ι.base x).asIdeal :=
    Ideal.under_map_of_isLocalizationAtPrime (S := S.U.toScheme.presheaf.stalk y)
      (underlyingPrime S y).asIdeal (p := (S.U.ι.base x).asIdeal)
      (baseIdeal_le_underlyingPrime_of_specializes S x y hxy)
  rw [stalk_idealOnOpen_eq_map, Ideal.map_le_iff_le_comap, hcontract]

/-- **Tag 0EJ5, the dimension of the fibre over `x`.** The fibre of `U` over the point `x` has,
at `y`, the dimension of the height of the image of the prime of `y` in `A/𝔭_x`. -/
public theorem ringKrullDim_quotient_map_baseToPointStalk (S : AlgebraizationSituation.{u})
    (x y : S.U.toScheme) (hxy : x ⤳ y) :
    ringKrullDim (S.U.toScheme.presheaf.stalk y ⧸
        (S.U.ι.base x).asIdeal.map (baseToPointStalk S y)) =
      (((underlyingPrime S y).asIdeal.map
        (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).height : WithBot ℕ∞) := by
  set q := (underlyingPrime S y).asIdeal
  set p := (S.U.ι.base x).asIdeal
  have hpq : p ≤ q := baseIdeal_le_underlyingPrime_of_specializes S x y hxy
  have hmap : p.map (algebraMap S.A (Localization.AtPrime q)) =
      (p.map (baseToPointStalk S y)).map (pointStalkRingEquiv S y).toRingHom := by
    rw [Ideal.map_map, show (pointStalkRingEquiv S y).toRingHom.comp (baseToPointStalk S y) =
      algebraMap S.A (Localization.AtPrime q) from
        RingHom.ext (pointStalkRingEquiv_baseToPointStalk_apply S y)]
  rw [ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv (p.map (baseToPointStalk S y))
        (p.map (algebraMap S.A (Localization.AtPrime q))) (pointStalkRingEquiv S y) hmap),
    Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime p q hpq]

/-- A prime minimal over an ideal has height zero in the quotient by that ideal. -/
private alias height_map_quotient_eq_zero :=
  Stacks.KrullDimension.FibreHeight.height_map_quotient_eq_zero_of_mem_minimalPrimes

/-- A Krull dimension equal to the cast of an extended natural number bounded by `d.toNat`
is at most `d` in the extended integers, provided `d` is nonnegative. -/
private theorem krullDimToEInt_coe_le_intCast {h : ℕ∞} {d : ℤ} (hd : 0 ≤ d)
    (hh : h ≤ (d.toNat : ℕ∞)) : krullDimToEInt ((h : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℤ) : EInt) := by
  have hcoe (k : ℕ∞) : krullDimToEInt (k : WithBot ℕ∞) = enatToEInt k := by
    cases k using ENat.recTopCoe <;> rfl
  have hd' : enatToEInt ((d.toNat : ℕ) : ℕ∞) = ((d : ℤ) : EInt) := by
    rw [show enatToEInt ((d.toNat : ℕ) : ℕ∞) = ((d.toNat : ℤ) : EInt) from rfl,
      Int.toNat_of_nonneg hd]
  rw [hcoe]
  exact (enatToEInt_mono hh).trans hd'.le

/-- Universal catenarity of `A` passes to the local ring of `U` at `y`. -/
@[ega "IV 10.7.2" "more general", ega "IV 7.8.2" "Direction, special case"]
private theorem isUniversallyCatenary_pointStalk (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) (hcat : Ring.IsUniversallyCatenary S.A) :
    Ring.IsUniversallyCatenary (S.U.toScheme.presheaf.stalk y) :=
  Ring.IsUniversallyCatenary.of_surjective'
    (f := (pointStalkRingEquiv S y).symm.toRingHom) (pointStalkRingEquiv S y).symm.surjective
    (Ring.IsUniversallyCatenary.localization (underlyingPrime S y).asIdeal.primeCompl
      (Localization.AtPrime (underlyingPrime S y).asIdeal) hcat)

/-- **Stacks Project, Tag 0EJ5 (the prime of the completed local ring).** Let `x ⤳ y` be a
specialization in `U` with `y` on `Y`, let `A` be universally catenary and suppose the prime
`𝔭` of `x` does not contain `I`. If the height of the image of the prime of `y` in `A/𝔭` is at
most a nonnegative integer `d`, then the completed local ring `𝒪_{U,y}^∧` carries a prime `P`
lying over `𝔭 𝒪_{U,y}` and minimal over `𝔭 𝒪_{U,y}^∧`, not containing `I 𝒪_{U,y}^∧`, whose
quotient has dimension at most `d`. -/
public theorem exists_primeSpectrum_completedLocalRing_of_specializes
    (S : AlgebraizationSituation.{u}) (x y : S.U.toScheme) (hxy : x ⤳ y)
    (r : S.Y) (hyr : S.U.ι.base y = S.Yι.base r)
    (hcat : Ring.IsUniversallyCatenary S.A)
    (hInotp : ¬ S.I ≤ (S.U.ι.base x).asIdeal)
    (d : ℤ) (hd : 0 ≤ d)
    (hheight : ((underlyingPrime S y).asIdeal.map
      (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).height ≤ (d.toNat : ℕ∞)) :
    letI : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
      (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
    ∃ P : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
      P.asIdeal.LiesOver ((maximalIdeal (S.U.toScheme.presheaf.stalk x)).under
          (S.U.toScheme.presheaf.stalk y)) ∧
      P.asIdeal ∈ (((maximalIdeal (S.U.toScheme.presheaf.stalk x)).under
          (S.U.toScheme.presheaf.stalk y)).map
          (algebraMap (S.U.toScheme.presheaf.stalk y)
            (completedLocalRing (idealOnOpen S) y))).minimalPrimes ∧
      ¬ completedLocalIdeal (idealOnOpen S) y ≤ P.asIdeal ∧
      krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ P.asIdeal))
        ≤ ((d : ℤ) : EInt) := by
  let _ : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
    (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
  let _ : Algebra S.A (S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
  have hloc := isLocalization_atPrime_pointStalk_toAlgebra S y
  have _ : IsNoetherianRing (S.U.toScheme.presheaf.stalk y) :=
    IsLocalization.isNoetherianRing (underlyingPrime S y).asIdeal.primeCompl
      (S.U.toScheme.presheaf.stalk y) S.noetherianA
  have hJmax : IdealSheafData.stalk (idealOnOpen S) y ≤
      maximalIdeal (S.U.toScheme.presheaf.stalk y) :=
    stalk_idealOnOpen_le_maximalIdeal S y r hyr
  have _ : IsLocalRing (completedLocalRing (idealOnOpen S) y) :=
    Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hJmax
  have _ : Module.FaithfullyFlat (S.U.toScheme.presheaf.stalk y)
      (completedLocalRing (idealOnOpen S) y) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _ (by
      rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact hJmax)
  have hQmap := under_maximalIdeal_stalk_eq_map S x y hxy
  obtain ⟨P, hPmin, hPover⟩ :=
    Ideal.exists_mem_minimalPrimes_map_liesOver_of_faithfullyFlat
      (S := completedLocalRing (idealOnOpen S) y)
      ((maximalIdeal (S.U.toScheme.presheaf.stalk x)).under (S.U.toScheme.presheaf.stalk y))
  have _ : P.IsPrime := hPmin.1.1
  have _ : P.LiesOver ((maximalIdeal (S.U.toScheme.presheaf.stalk x)).under
    (S.U.toScheme.presheaf.stalk y)) := hPover
  refine ⟨⟨P, inferInstance⟩, hPover, hPmin, ?_, ?_⟩
  · intro hle
    rw [Ideal.map_le_iff_le_comap] at hle
    refine hInotp ((le_baseIdeal_iff_stalk_idealOnOpen_le_map S x y hxy).mpr ?_)
    rw [← hQmap]
    exact hle.trans hPover.over.ge
  · have hsplit :=
      AdicCompletionDimension.height_add_ringKrullDim_quotient_eq_ringKrullDim_quotient
        (isUniversallyCatenary_pointStalk S y hcat) hJmax
        ((maximalIdeal (S.U.toScheme.presheaf.stalk x)).under
          (S.U.toScheme.presheaf.stalk y)) P
    simp only [height_map_quotient_eq_zero hPmin, WithBot.coe_zero, zero_add] at hsplit
    rw [hsplit, hQmap, ringKrullDim_quotient_map_baseToPointStalk S x y hxy]
    exact krullDimToEInt_coe_le_intCast hd hheight

end Stacks.Algebraization

end
