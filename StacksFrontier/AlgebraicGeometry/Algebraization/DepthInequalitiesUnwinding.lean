module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesCohomologicalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceLocalDimension

/-!
# Unwinding the `(2, 3)`-inequalities at the dimension-one points

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`, and let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. Assume
`A` is local with `𝔞 = 𝔪` and that `cd(A, I) = 1`.

For a point `y ∈ U ∩ Y` whose closure has dimension one the distance `δ^Y_Z(y)` equals `1`: the
closed point of `Y` is then the only proper specialization of `y`, so the one-leg zigzag from
`Z = {𝔪}` to `{y}‾` has weight one. Combined with Stacks 0EKW, which in cohomological dimension
one rewrites the `(2, 3)`-inequalities as

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > 3`,

this gives the necessity half of Stacks 0EJA: the `(2, 3)`-inequalities force

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2`

at every `y ∈ U ∩ Y` with `dim({y}‾) = 1` and every prime `𝔭 ⊆ 𝒪_{X,y}^∧` with
`𝔭 ∉ V(I𝒪_{X,y}^∧)`.

## Main results

* `Stacks.Algebraization.two_lt_depth_add_dim_of_satisfiesDepthInequalities` — the necessity
  half of Stacks 0EJA.
* `Stacks.Algebraization.distanceToZ_le_height` — in the local situation with `𝔞 = 𝔪` the
  distance `δ^Y_Z` at a point of `Y` is at most the dimension of the closure of that point.

## Implementation notes

`dim({y}‾)` is the height of the point in the specialization order of the scheme `X`, which is
the coheight of the corresponding prime in the inclusion order of `Spec(A)`; the scheme order is
`a ≤ b ↔ b ⤳ a`, so the elements below a point are exactly its specializations and their chains
compute the dimension of its closure.

The bound `δ^Y_Z(y) ≤ dim({y}‾)` is obtained from Stacks 0EIY, in the form
`Stacks.Algebraization.distanceFunction_le_closureLocalDimension`, applied at the closed point
of `Y`: that bounds the distance by the coheight of the closed point inside `{y}‾`, and a chain
in `{y}‾` is a chain of specializations of `y`, hence is bounded by the height of `y`. Only the
height of `y` computed in `Y` is needed, and the closed immersion `Y ⟶ X` is injective and
monotone for the specialization orders, so the height in `Y` is at most the height in `X`.
Neither inequality needs a catenary hypothesis.

The depth, the dimension of the quotient and the distance are compared in `EInt`, as in the
definition of the `(2, 3)`-inequalities, and the passage from the bound `3` to the bound `2`
uses that translation by `1` is an order isomorphism of `EInt`.

## References

* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EKW](https://stacks.math.columbia.edu/tag/0EKW), cohomological
  dimension one.
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY), the distance function.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Extended-integer arithmetic -/

/-- In the extended integers `3 < x + 1` exactly when `2 < x`: translation by `1` is an order
isomorphism. -/
private theorem three_lt_add_one_iff_two_lt (x : EInt) :
    ((3 : ℤ) : EInt) < x + ((1 : ℤ) : EInt) ↔ ((2 : ℤ) : EInt) < x := by
  have h3 : ((3 : ℤ) : EInt) = ((2 : ℤ) : EInt) + ((1 : ℤ) : EInt) := by
    rw [← Stacks.Chow.coe_add_coe_eq_coe_add]
    norm_num
  rw [h3, ← Stacks.Chow.eintAddRight_apply 1 x,
    ← Stacks.Chow.eintAddRight_apply 1 ((2 : ℤ) : EInt)]
  exact (Stacks.Chow.eintAddRight 1).lt_iff_lt

/-- From `3 < d + e` and `e ≤ 1` in the extended integers one gets `2 < d`. -/
private theorem two_lt_of_three_lt_add {d e : EInt} (h : ((3 : ℤ) : EInt) < d + e)
    (he : e ≤ ((1 : ℤ) : EInt)) : ((2 : ℤ) : EInt) < d :=
  (three_lt_add_one_iff_two_lt d).mp (lt_of_lt_of_le h (add_le_add (le_refl d) he))

/-- The extended-integer image of a value of `ℕ∞` at most `1` is at most `1`. -/
private theorem enatToEInt_le_one {n : ℕ∞} (hn : n ≤ 1) :
    enatToEInt n ≤ ((1 : ℤ) : EInt) := by
  cases n using ENat.recTopCoe with
  | top => exact absurd hn (by simp)
  | coe k =>
    have hk : k ≤ 1 := by exact_mod_cast hn
    change ((k : ℤ) : EInt) ≤ ((1 : ℤ) : EInt)
    exact WithBotTop.coe_le_coe.mpr (by omega)

/-! ### Chains in the closure of a point -/

/-- A chain in the closure of `z` is a chain of specializations of `z`, so the coheight of any
point of `{z}‾`, computed inside `{z}‾`, is at most the height of `z`. -/
private theorem coheight_closure_le_height {Y : Scheme.{u}} (z w : Y)
    (hw : w ∈ closure ({z} : Set Y)) :
    Order.coheight (⟨w, hw⟩ : (closure ({z} : Set Y) : Set Y)) ≤ Order.height z := by
  refine Order.coheight_le fun q _ => ?_
  let r : LTSeries Y := ⟨q.length, fun i => ((q i : (closure ({z} : Set Y) : Set Y)) : Y),
    fun i => q.step i⟩
  have hlast : r.last ≤ z :=
    Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr q.last.2)
  exact Order.length_le_height hlast

/-! ### The distance to `Z` at a point of dimension-one closure -/

/-- In a local algebraization situation with `𝔞 = 𝔪` the quotient `A/I` is local. -/
private theorem isLocalRing_quotient (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (ha : S.a = maximalIdeal S.A) : IsLocalRing (S.A ⧸ S.I) := by
  have hne : S.I ≠ ⊤ := by
    intro h
    refine (maximalIdeal.isMaximal S.A).ne_top (top_le_iff.mp ?_)
    rw [← ha]
    exact h ▸ S.I_le_a
  have : Nontrivial (S.A ⧸ S.I) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk S.I) Ideal.Quotient.mk_surjective

/-- In a local algebraization situation with `𝔞 = 𝔪` the distance `δ^Y_Z` at a point of
`Y = V(I)` is at most the dimension of the closure of that point. -/
public theorem distanceToZ_le_height (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (ha : S.a = maximalIdeal S.A) (z : S.Y) :
    S.distanceToZ z ≤ Order.height z := by
  classical
  have hB : IsLocalRing (S.A ⧸ S.I) := isLocalRing_quotient S ha
  have : IsLocalHom (Ideal.Quotient.mk S.I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  set m : S.Y := (closedPoint (S.A ⧸ S.I) : PrimeSpectrum (S.A ⧸ S.I))
  have hmZ : m ∈ (S.closedSubsetZ : Set S.Y) := by
    change S.a.map (Ideal.Quotient.mk S.I) ≤ (closedPoint (S.A ⧸ S.I)).asIdeal
    rw [Ideal.map_le_iff_le_comap]
    change S.a ≤ (maximalIdeal (S.A ⧸ S.I)).comap (Ideal.Quotient.mk S.I)
    rw [IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk S.I), ha]
  have hmz : m ∈ closure ({z} : Set S.Y) :=
    specializes_iff_mem_closure.mp
      (IsLocalRing.specializes_closedPoint (z : PrimeSpectrum (S.A ⧸ S.I)))
  exact WithBot.coe_le_coe.mp <|
    (distanceFunction_le_closureLocalDimension S.Y S.closedSubsetZ z m hmz hmZ).trans
      (WithBot.coe_le_coe.mpr (coheight_closure_le_height z m hmz))

/-! ### Heights along the closed immersion `Y ⟶ X` -/

/-- Contracting along a surjection reflects the inclusion order of prime ideals. -/
private theorem comap_quotientMk_le_iff {A : Type u} [CommRing A] (I : Ideal A)
    (a b : PrimeSpectrum (A ⧸ I)) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I) a ≤
        PrimeSpectrum.comap (Ideal.Quotient.mk I) b ↔ a ≤ b := by
  rw [← PrimeSpectrum.asIdeal_le_asIdeal, ← PrimeSpectrum.asIdeal_le_asIdeal,
    PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
  refine ⟨fun h => ?_, fun h => Ideal.comap_mono h⟩
  have h1 := Ideal.map_mono (f := Ideal.Quotient.mk I) h
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h1

/-- The closed immersion `Y = Spec(A/I) ⟶ X = Spec(A)` reflects specializations. -/
private theorem specializes_Yι_iff (S : AlgebraizationSituation.{u}) (a b : S.Y) :
    S.Yι.base a ⤳ S.Yι.base b ↔ a ⤳ b :=
  ⟨fun h => (PrimeSpectrum.le_iff_specializes a b).mp
    ((comap_quotientMk_le_iff S.I a b).mp ((PrimeSpectrum.le_iff_specializes _ _).mpr h)),
    fun h => h.map S.Yι.base.hom.continuous⟩

/-- The underlying map of `Y = Spec(A/I) ⟶ X = Spec(A)` is strictly monotone for the
specialization orders, so it does not decrease heights. -/
private theorem height_le_height_Yι (S : AlgebraizationSituation.{u}) (z : S.Y) :
    Order.height z ≤ Order.height (S.Yι.base z) := by
  refine Order.height_le_height_apply_of_strictMono _ (fun a b hab => ?_) z
  rw [lt_iff_le_not_ge] at hab ⊢
  refine ⟨Scheme.le_iff_specializes.mpr
      ((Scheme.le_iff_specializes.mp hab.1).map
        S.Yι.base.hom.continuous), fun hcon => hab.2 ?_⟩
  exact Scheme.le_iff_specializes.mpr
    ((specializes_Yι_iff S a b).mp (Scheme.le_iff_specializes.mp hcon))

/-! ### Stacks 0EJA, the necessity half -/

/-- **Stacks Project, Tag 0EJA.** In Situation 0EHC with `A` local, `𝔞 = 𝔪` and `cd(A, I) = 1`,
if `(ℱ_n)` satisfies the `(2, 3)`-inequalities then `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2`
for every `y ∈ U ∩ Y` with `dim({y}‾) = 1` and every prime `𝔭 ⊆ 𝒪_{X,y}^∧` not containing
`I𝒪_{X,y}^∧`. -/
public theorem two_lt_depth_add_dim_of_satisfiesDepthInequalities
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (ha : S.a = maximalIdeal S.A)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (h : SatisfiesDepthInequalities S F 2 3)
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (hdim : Order.height (S.U.ι.base y) = 1)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal) :
    enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
        krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) >
      ((2 : ℤ) : EInt) := by
  have hthree := (satisfiesDepthInequalities_two_three_iff S F hcd).mp h y z hyz p hp
  have hzle : Order.height z ≤ 1 := by
    rw [← hdim, hyz]
    exact height_le_height_Yι S z
  exact two_lt_of_three_lt_add hthree
    (enatToEInt_le_one (le_trans (distanceToZ_le_height S ha z) hzle))

end Stacks.Algebraization

end
