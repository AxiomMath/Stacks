module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponentChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.StalkDimension
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Grouping the cycle coefficients over the components of a chart lying over one component

Let `X/B` be a good algebraic space in Situation 0EDT, let `V` be a surjective étale scheme chart
of `X`, let `X' ⊆ X` be an integral closed subspace whose point set is an irreducible component of
`|X|`, and let `Dz` be an ideal sheaf on the chart scheme. At a point `v` of the support of `Dz` of
relative dimension `k`, this file proves

  `[(V ×_X X') ∩ Dz]_k` at `v`  `=`  `∑ over W a component of V over |X'| of [W ∩ Dz]_k` at `v`,

the cycles being those of Stacks 02QU for the base situation on the chart
(`AlgebraicGeometry.Space.chartChowSituation`). Writing `R = 𝒪_{V, v}`, `I` for the stalk of the
ideal sheaf of `V ×_X X'` and `b` for a generator of the stalk of `Dz`, it is the identity

  `length R (R ⧸ (b, I))  =  ∑ over q minimal over I of length R (R ⧸ (b, q))`,

which is Stacks 02QG over the reduced quotient `R ⧸ I`.

## Main results

* `AlgebraicGeometry.natCast_length_quotient_span_sup_eq_finsum_minimalPrimes_of_isReduced`:
  Stacks 02QG over a reduced quotient, with no multiplicities.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_length_quotient_idealStalk`: the
  coefficient of the cycle of Stacks 02QU at a point of maximal δ-dimension is the colength of
  the stalk of the ideal sheaf.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_sup_eq_finsum_components_of_isReduced`: the
  grouping, for ideal sheaves on a scheme.
* `AlgebraicGeometry.Space.subset_preimage_iff_closure_singleton_chartSchemeToPoints_eq`: a
  component `W` of the chart lies over a component `T` of `|X|` exactly when `T` is the closure of
  the image of the generic point of `W`.
* `AlgebraicGeometry.Space.deltaDimension_eq_of_subset_preimage_subspacePointSet`: such a
  component of the chart has the δ-dimension of the component of `X` below it.
* `AlgebraicGeometry.Space.cycleAssociatedToClosedSubscheme_componentChart_sup_eq_finsum`: the
  grouping on an étale chart of an algebraic space.

## References

* [Stacks Project, Tag 00EW](https://stacks.math.columbia.edu/tag/00EW)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Colengths along a quotient -/

/-- **The colength of `I ⊔ J` is the colength of the image of `J` in `R ⧸ I`.** -/
theorem length_quotient_sup_eq_length_quotient_map_mk {R : Type*} [CommRing R] (I J : Ideal R) :
    Module.length R (R ⧸ (I ⊔ J)) =
      Module.length (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) := by
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have hmap : J.map (Ideal.Quotient.mk I) = J.map (Ideal.Quotient.mkₐ R I) := rfl
  rw [hmap, ← Module.length_eq_of_surjective (S := R) (R := R ⧸ I)
    (M := (R ⧸ I) ⧸ J.map (Ideal.Quotient.mkₐ R I)) hsurj]
  exact ((DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv.length_eq).symm

/-- The localization of a reduced ring at a minimal prime has length one over itself. -/
theorem length_localization_atPrime_eq_one_of_isReduced {R : Type*} [CommRing R]
    [_root_.IsReduced R] (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = 1 := by
  have hfield : IsField (Localization.AtPrime p.asIdeal) :=
    isField_localizationAtPrime_of_minimal R p.asIdeal hp
  refine Module.length_eq_one_iff.mpr (isSimpleModule_self_iff_isUnit.mpr ⟨⟨hfield.exists_pair_ne⟩,
    fun x hx => ?_⟩)
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
  exact ⟨⟨x, y, hy, (hfield.mul_comm _ _).trans hy⟩, rfl⟩

/-- **Stacks 02QG over a reduced quotient: the multiplicities are all one.** If `R ⧸ I` is a
reduced one-dimensional Noetherian local ring on which `b` is a nonzerodivisor, the colength of
`(b, I)` is the *plain* sum, over the minimal primes `q` above `I`, of the colengths of
`(b, q)`. -/
@[ega "IV 21.10.17.7" "special case"]
theorem natCast_length_quotient_span_sup_eq_finsum_minimalPrimes_of_isReduced
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (b : R) (I : Ideal R)
    (hItop : I ≠ ⊤) (hred : _root_.IsReduced (R ⧸ I))
    (hb : IsSMulRegular (R ⧸ I) (Ideal.Quotient.mk I b))
    (hdim : ringKrullDim (R ⧸ I) = 1)
    (hfinite : Module.length R (R ⧸ (Ideal.span {b} ⊔ I)) ≠ ⊤) :
    ((Module.length R (R ⧸ (Ideal.span {b} ⊔ I))).toNat : ℤ) =
      ∑ᶠ q : {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes},
        ((Module.length R (R ⧸ (Ideal.span {b} ⊔ q.1.asIdeal))).toNat : ℤ) := by
  classical
  have _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hcolength (J : Ideal R) (hIJ : I ≤ J) :
      Module.length R (R ⧸ (Ideal.span {b} ⊔ J)) =
        Module.length (R ⧸ I) ((R ⧸ I) ⧸
          (Ideal.span {Ideal.Quotient.mk I b} ⊔ J.map (Ideal.Quotient.mk I))) := by
    rw [show Ideal.span {b} ⊔ J = I ⊔ (Ideal.span {b} ⊔ J) from
        (sup_eq_right.mpr (le_sup_of_le_right hIJ)).symm,
      length_quotient_sup_eq_length_quotient_map_mk I (Ideal.span {b} ⊔ J), Ideal.map_sup,
      Ideal.map_span, Set.image_singleton]
  have hbot : Module.length R (R ⧸ (Ideal.span {b} ⊔ I)) =
      Module.length (R ⧸ I) ((R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I b}) := by
    rw [hcolength I le_rfl, Ideal.map_quotient_self, sup_bot_eq]
  rw [hbot, AlgebraicGeometry.natCast_length_quotient_span_eq_sum_minimalPrimes
    (Ideal.Quotient.mk I b) hb hdim (by rwa [← hbot])]
  refine finsum_eq_of_bijective
    (fun p : {p : PrimeSpectrum (R ⧸ I) // p.asIdeal ∈ minimalPrimes (R ⧸ I)} =>
      (⟨PrimeSpectrum.comap (Ideal.Quotient.mk I) p.1, by
        rw [Ideal.minimalPrimes_eq_comap]
        exact ⟨p.1.asIdeal, p.2, rfl⟩⟩ :
        {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes}))
    ⟨fun p p' h => Subtype.ext (PrimeSpectrum.comap_injective_of_surjective _
      Ideal.Quotient.mk_surjective (congrArg Subtype.val h)), fun q => ?_⟩ ?_
  · obtain ⟨p, hp, hpq⟩ := (Ideal.minimalPrimes_eq_comap (I := I)).le q.2
    exact ⟨⟨⟨p, hp.1.1⟩, hp⟩, Subtype.ext (PrimeSpectrum.ext hpq)⟩
  · intro p
    have hIp : I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk I) p.1).asIdeal :=
      fun x hx => by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    rw [hcolength _ hIp, PrimeSpectrum.comap_asIdeal, Ideal.map_comap_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p.1.asIdeal,
      length_localization_atPrime_eq_one_of_isReduced p.1 p.2]
    simp

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The coefficient of the cycle of a closed subscheme at a point of maximal dimension -/

/-- **A prime of the local ring at `x` contains the stalk of an ideal sheaf exactly when the
point it names lies in the support.** The point is the image of the prime under
`Spec 𝒪_{Y, x} ⟶ Y`. -/
theorem stalk_le_iff_mem_support_fromSpecStalk {Y : Scheme.{u}} (E : Y.IdealSheafData) (x : Y)
    (q : PrimeSpectrum (Y.presheaf.stalk x)) :
    AlgebraicGeometry.IdealSheafData.stalk E x ≤ q.asIdeal ↔
      Y.fromSpecStalk x q ∈ E.support := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  have hU : IsAffineOpen U.1 := U.2
  let _ : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hpt : Y.fromSpecStalk x q =
      hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hxU).hom q) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
    rfl
  have hmemU : Y.fromSpecStalk x q ∈ (U.1 : Set Y) := by
    rw [hpt, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ E x U hxU, Ideal.map_le_iff_le_comap,
    ← Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    Scheme.IdealSheafData.mem_supportSet_iff_of_mem hmemU]
  constructor
  · intro h
    have hmem : Y.fromSpecStalk x q ∈ Y.zeroLocus (U := U.1) (E.ideal U) ∩ (U.1 : Set Y) := by
      rw [← hU.fromSpec_image_zeroLocus, hpt]
      exact ⟨_, (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun z hz => h hz), rfl⟩
    exact hmem.1
  · intro h
    have hmem : Y.fromSpecStalk x q ∈ Y.zeroLocus (U := U.1) (E.ideal U) ∩ (U.1 : Set Y) :=
      ⟨h, hmemU⟩
    rw [← hU.fromSpec_image_zeroLocus, hpt] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    have heq : p = PrimeSpectrum.comap (Y.presheaf.germ U.1 x hxU).hom q :=
      hU.fromSpec.isOpenEmbedding.injective hpe
    intro z hz
    rw [← PrimeSpectrum.comap_asIdeal, ← heq]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hp hz

/-- **The coefficient at a point of maximal δ-dimension of the cycle of a closed subscheme is the
colength of the stalk of its ideal sheaf.** Let `E` cut out a closed subscheme of δ-dimension at
most `k`, and let `x` be a point of the support of `E` of relative dimension `k`. Then the
coefficient at `x` of the `k`-cycle of Stacks 02QU of that subscheme is the colength of the stalk
of `E` at `x`. The special case in which the stalk of `E` is the sum of a principal ideal and a
prime is `Stacks.Chow.cycleAssociatedToClosedSubscheme_sup_apply_eq_length`. -/
theorem cycleAssociatedToClosedSubscheme_apply_eq_length_quotient_idealStalk
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    (E : Y.IdealSheafData) {k : ℤ}
    (hE : schemeDeltaDimension C (E.subschemeι ≫ f) ≤ (k : EInt))
    (x : Y) (hxE : x ∈ E.support)
    (hxdim : relativeDimension C.dimensionFunction f x = k) :
    (cycleAssociatedToClosedSubscheme C f E.subschemeι k).1 x =
      (Module.length (Y.presheaf.stalk x)
        (Y.presheaf.stalk x ⧸ AlgebraicGeometry.IdealSheafData.stalk E x)).toNat := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  have hxrange : x ∈ Set.range E.subschemeι := by
    change x ∈ (E.support : Set Y) at hxE
    simpa only [Scheme.IdealSheafData.range_subschemeι] using hxE
  obtain ⟨y, hy⟩ := hxrange
  have hyξ : relativeDimension C.dimensionFunction f (E.subschemeι y) = k := by
    simpa [hy] using hxdim
  obtain ⟨V, hV⟩ := isGenericPoint_component_of_relativeDimension_eq C f E.subschemeι hE y hyξ
  have hyEq : y = (genericPoints.ofComponent V).1 :=
    hV.eq (genericPoints.isGenericPoint_ofComponent V)
  have hξx : E.subschemeι (genericPoints.ofComponent V).1 = x := by rw [← hyEq]; exact hy
  have hξdim : relativeDimension C.dimensionFunction f
      (E.subschemeι (genericPoints.ofComponent V).1) = k := by simpa [hξx] using hxdim
  have hcycle := cycleAssociatedToClosedSubscheme_apply C f E.subschemeι k
    (genericPoints.ofComponent V) hξdim
  rw [hξx] at hcycle
  have hmult := componentMultiplicity_eq_length_quotient_stalk E.subschemeι
    (genericPoints.ofComponent V) U.1 U.2 (by simpa [hξx] using hxU)
  rw [hξx, Scheme.IdealSheafData.ker_subschemeι] at hmult
  rw [hcycle, hmult]


/-! ### The grouping of the coefficients over the components inside a reduced closed subscheme -/

/-- The cycle of `E ⊓ D` has coefficient zero at every point outside the support of `E`. -/
private theorem cycle_sup_apply_eq_zero_of_notMem_support (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ C.S) [LocallyOfFiniteType f] (E D : Y.IdealSheafData) (k : ℤ) {x : Y}
    (hx : x ∉ (E.support : Set Y)) :
    (cycleAssociatedToClosedSubscheme C f (E ⊔ D).subschemeι k).1 x = 0 := by
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f _ k fun h => hx ?_
  rw [Scheme.IdealSheafData.range_subschemeι, SetLike.mem_coe,
    Scheme.IdealSheafData.support_sup] at h
  exact h.1

/-- **The coefficient of `[A ∩ D]_k` is the sum of the coefficients of the `[W ∩ D]_k`**, over
the irreducible components `W` of `Y` lying inside the support of `A`.

Here `A` and `D` are ideal sheaves on a scheme `Y` of δ-dimension at most `k + 1` locally of
finite type over the base situation, `D` cuts out a scheme of δ-dimension at most `k` and is
generated at the point `x` of relative dimension `k` by a nonzerodivisor `a` of finite colength,
and `A` cuts out a closed subscheme which is **reduced at `x`** (`hred`) and whose branches at `x`
are branches of `Y` (`hcomp`). -/
theorem cycleAssociatedToClosedSubscheme_sup_eq_finsum_components_of_isReduced
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    (A D : Y.IdealSheafData) (k : ℤ)
    (hY : schemeDeltaDimension C f ≤ (k + 1 : EInt))
    (hD : schemeDeltaDimension C (D.subschemeι ≫ f) ≤ (k : EInt))
    (x : Y) (hxA : x ∈ A.support) (hxD : x ∈ D.support)
    (hxdim : relativeDimension C.dimensionFunction f x = k)
    (U : Y.affineOpens) (hxU : x ∈ U.1) (a : Γ(Y, U.1))
    (haD : AlgebraicGeometry.IdealSheafData.stalk D x =
      Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a})
    (ha : IsSMulRegular (Y.presheaf.stalk x) ((Y.presheaf.germ U.1 x hxU).hom a))
    (ham : (Y.presheaf.germ U.1 x hxU).hom a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    (hfinite : Module.length (Y.presheaf.stalk x)
      (Y.presheaf.stalk x ⧸ Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a}) ≠ ⊤)
    (hred : _root_.IsReduced (Y.presheaf.stalk x ⧸
      AlgebraicGeometry.IdealSheafData.stalk A x))
    (hcomp : ∀ q : PrimeSpectrum (Y.presheaf.stalk x),
      q.asIdeal ∈ (AlgebraicGeometry.IdealSheafData.stalk A x).minimalPrimes →
        closure ({Y.fromSpecStalk x q} : Set Y) ∈ irreducibleComponents Y) :
    (cycleAssociatedToClosedSubscheme C f ((A ⊔ D).subschemeι) k).1 x =
      ∑ᶠ W : {W : irreducibleComponents Y // (W.1 : Set Y) ⊆ (A.support : Set Y)},
        (cycleAssociatedToClosedSubscheme C f
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ D).subschemeι) k).1 x := by
  classical
  have hLN : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  set R := Y.presheaf.stalk x with hR
  set b := (Y.presheaf.germ U.1 x hxU).hom a with hb
  set I := AlgebraicGeometry.IdealSheafData.stalk A x with hI
  have hsupdim : ∀ E : Y.IdealSheafData,
      schemeDeltaDimension C ((E ⊔ D).subschemeι ≫ f) ≤ (k : EInt) := by
    intro E
    have h := schemeDeltaDimension_le_of_isClosedImmersion C (D.subschemeι ≫ f)
      (Scheme.IdealSheafData.inclusion (le_sup_right : D ≤ E ⊔ D)) (k := k) hD
    simpa only [← Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι (le_sup_right : D ≤ E ⊔ D)] using h
  have hLHS : (cycleAssociatedToClosedSubscheme C f ((A ⊔ D).subschemeι) k).1 x =
      ((Module.length R (R ⧸ (Ideal.span {b} ⊔ I))).toNat : ℤ) := by
    rw [cycleAssociatedToClosedSubscheme_apply_eq_length_quotient_idealStalk C f (A ⊔ D)
        (hsupdim A) x (by rw [Scheme.IdealSheafData.support_sup]; exact ⟨hxA, hxD⟩) hxdim,
      AlgebraicGeometry.IdealSheafData.stalk_sup, haD, sup_comm]
  have hkey : ∀ q : PrimeSpectrum R, q.asIdeal ∈ I.minimalPrimes →
      ∃ W : {W : {W : irreducibleComponents Y // (W.1 : Set Y) ⊆ (A.support : Set Y)} //
          x ∈ (W.1.1 : Set Y)},
        (irreducibleComponentsEquivMinimalPrimes x ⟨W.1.1, W.2⟩).1 = q := by
    intro q hq
    have hηx : Y.fromSpecStalk x q ⤳ x :=
      Scheme.range_fromSpecStalk.subset ⟨q, rfl⟩
    have hc := hcomp q hq
    have hCA : closure ({Y.fromSpecStalk x q} : Set Y) ⊆ (A.support : Set Y) :=
      (A.support.isClosed).closure_subset_iff.2
        (Set.singleton_subset_iff.2 ((stalk_le_iff_mem_support_fromSpecStalk A x q).mp hq.1.2))
    refine ⟨⟨⟨⟨closure ({Y.fromSpecStalk x q} : Set Y), hc⟩, hCA⟩, hηx.mem_closure⟩, ?_⟩
    refine (Y.fromSpecStalk x).isEmbedding.injective ?_
    rw [fromSpecStalk_irreducibleComponentsEquivMinimalPrimes x _]
    exact ((genericPoints.isGenericPoint_ofComponent
      (⟨closure ({Y.fromSpecStalk x q} : Set Y), hc⟩ :
        irreducibleComponents Y)).eq (rfl : IsGenericPoint (Y.fromSpecStalk x q) _))
  have hmin : ∀ q : PrimeSpectrum R, q.asIdeal ∈ I.minimalPrimes →
      q.asIdeal ∈ minimalPrimes R := by
    intro q hq
    obtain ⟨W, hW⟩ := hkey q hq
    exact hW ▸ (irreducibleComponentsEquivMinimalPrimes x ⟨W.1.1, W.2⟩).2
  have hImax : I ≤ IsLocalRing.maximalIdeal R :=
    (AlgebraicGeometry.IdealSheafData.stalk_le_maximalIdeal_iff_mem_support A x).mpr hxA
  have hItop : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hImax))
  have _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have _ : _root_.IsReduced (R ⧸ I) := hred
  have hbnzdR : b ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_left.mpr fun r hr =>
    ha (by simpa only [smul_eq_mul, mul_zero] using hr)
  have hbnzd : Ideal.Quotient.mk I b ∈ nonZeroDivisors (R ⧸ I) :=
    Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes (Ideal.Quotient.mk I)
      (fun q hq => by
        have hq' : Ideal.comap (Ideal.Quotient.mk I) q ∈ I.minimalPrimes := by
          rw [Ideal.minimalPrimes_eq_comap]
          exact ⟨q, hq, rfl⟩
        exact hmin ⟨Ideal.comap (Ideal.Quotient.mk I) q, hq'.1.1⟩ hq') hbnzdR
  have hbreg : IsSMulRegular (R ⧸ I) (Ideal.Quotient.mk I b) := by
    intro y z hyz
    have h : Ideal.Quotient.mk I b * (y - z) = 0 := by
      simpa only [mul_sub, sub_eq_zero, smul_eq_mul] using hyz
    exact sub_eq_zero.mp (mem_nonZeroDivisors_iff_left.mp hbnzd (y - z) h)
  have hspan_ne_top : Ideal.span {Ideal.Quotient.mk I b} ≠ (⊤ : Ideal (R ⧸ I)) := by
    intro h
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp (Ideal.span_singleton_eq_top.mp h)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v
    have h1 : b * c - 1 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by
      rw [map_sub, map_mul, map_one, hv, sub_self])
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have h3 : b * c - (b * c - 1) = 1 := by ring
      exact h3 ▸ Ideal.sub_mem _ (Ideal.mul_mem_right c _ ham) (hImax h1)
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  have _ : Nontrivial ((R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I b}) :=
    Ideal.Quotient.nontrivial_iff.mpr hspan_ne_top
  have hdim : ringKrullDim (R ⧸ I) = 1 := by
    refine le_antisymm ((ringKrullDim_quotient_le I).trans
      (ringKrullDim_stalk_le_one C f (k := k) hY x hxdim)) ?_
    exact (show (1 : WithBot ℕ∞) ≤
        ringKrullDim ((R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I b}) + 1 by
      simpa only [zero_add, add_comm] using add_le_add_right (ringKrullDim_nonneg_of_nontrivial
        (R := (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I b})) 1).trans
      (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hbnzd)
  have hfin' : Module.length R (R ⧸ (Ideal.span {b} ⊔ I)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (Module.length_le_of_surjective
      (Ideal.Quotient.factorₐ R (le_sup_left : Ideal.span {b} ≤ Ideal.span {b} ⊔ I)).toLinearMap
      (fun y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ z, rfl⟩))
  have hstalkW : ∀ (W : irreducibleComponents Y) (hxW : x ∈ (W.1 : Set Y)),
      AlgebraicGeometry.IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩) x =
        (irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩).1.asIdeal := by
    intro W hxW
    refine stalk_vanishingIdeal_eq_of_mem_minimalPrimes x W hxW _
      (irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩).2 ?_
    rw [fromSpecStalk_irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩]
    exact (genericPoints.isGenericPoint_ofComponent W).mem
  have hcoeff : ∀ (W : irreducibleComponents Y) (hxW : x ∈ (W.1 : Set Y)),
      (cycleAssociatedToClosedSubscheme C f
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ ⊔ D).subschemeι) k).1 x =
        ((Module.length R (R ⧸ (Ideal.span {b} ⊔
          (irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩).1.asIdeal))).toNat : ℤ) := by
    intro W hxW
    have hxsupp : x ∈ (Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ ⊔ D).support := by
      rw [Scheme.IdealSheafData.support_sup]
      refine ⟨?_, hxD⟩
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hxW
    rw [cycleAssociatedToClosedSubscheme_apply_eq_length_quotient_idealStalk C f _
        (hsupdim _) x hxsupp hxdim, AlgebraicGeometry.IdealSheafData.stalk_sup, haD,
      hstalkW W hxW, sup_comm]
  have hmem : ∀ (W : irreducibleComponents Y) (hxW : x ∈ (W.1 : Set Y)),
      (W.1 : Set Y) ⊆ (A.support : Set Y) →
        (irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩).1.asIdeal ∈ I.minimalPrimes := by
    intro W hxW hWA
    have hp := (irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩).2
    have hle : A ≤ Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ :=
      Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hWA
    have hIle : I ≤ (irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩).1.asIdeal := by
      rw [← hstalkW W hxW, hI, AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ A x U hxU,
        AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U hxU]
      exact Ideal.map_mono (hle U)
    exact ⟨⟨hp.1.1, hIle⟩, fun J hJ hJle => hp.2 ⟨hJ.1, bot_le⟩ hJle⟩
  let F : {W : irreducibleComponents Y // (W.1 : Set Y) ⊆ (A.support : Set Y)} → ℤ := fun W =>
    (cycleAssociatedToClosedSubscheme C f
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ D).subschemeι) k).1 x
  have hrestrict : (∑ᶠ W, F W) = ∑ᶠ W : {W // x ∈ (W.1.1 : Set Y)}, F W.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    refine finsum_congr fun W => ?_
    by_cases hxW : x ∈ (W.1.1 : Set Y)
    · simp only [hxW, finsum_true]
    · simp only [hxW, finsum_false]
      exact cycle_sup_apply_eq_zero_of_notMem_support C f _ D k (by
        rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal])
  change _ = ∑ᶠ W, F W
  rw [hLHS, AlgebraicGeometry.natCast_length_quotient_span_sup_eq_finsum_minimalPrimes_of_isReduced
    b I hItop hred hbreg hdim hfin', hrestrict]
  refine (finsum_eq_of_bijective
    (fun W : {W : {W : irreducibleComponents Y // (W.1 : Set Y) ⊆ (A.support : Set Y)} //
        x ∈ (W.1.1 : Set Y)} =>
      (⟨(irreducibleComponentsEquivMinimalPrimes x ⟨W.1.1, W.2⟩).1, hmem W.1.1 W.2 W.1.2⟩ :
        {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes}))
    ⟨fun W W' h => ?_, fun q => ?_⟩ fun W => hcoeff W.1.1 W.2).symm
  · have h0 : ((irreducibleComponentsEquivMinimalPrimes x ⟨W.1.1, W.2⟩).1 : PrimeSpectrum R) =
        ((irreducibleComponentsEquivMinimalPrimes x ⟨W'.1.1, W'.2⟩).1 : PrimeSpectrum R) :=
      congrArg (fun q : {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes} =>
        (q : PrimeSpectrum R)) h
    have h2 := (irreducibleComponentsEquivMinimalPrimes x).injective (Subtype.ext h0)
    refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
    exact congrArg (fun V : {W : irreducibleComponents Y // x ∈ (W : Set Y)} =>
      ((V.1 : irreducibleComponents Y) : Set Y)) h2
  · obtain ⟨W, hW⟩ := hkey q.1 q.2
    exact ⟨W, Subtype.ext hW⟩

end Stacks.Chow


namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The inverse image of an integral closed subspace on a chart -/

/-- **The chart of an integral closed subspace is reduced at every point**, read as the quotient
of the local ring of the ambient chart by the stalk of the ideal sheaf of the projection. -/
theorem isReduced_quotient_idealStalk_ker_closedSubspaceBaseChangeChartProj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z)
    (hZint : IsIntegralSpace B S hS Z.toFunctor)
    (V : SmallEtale B S hS X)
    (t : chartScheme (closedSubspaceBaseChangeChart B S hS hX Z hZ V)) :
    _root_.IsReduced ((chartScheme V).presheaf.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX Z hZ V t) ⧸
      AlgebraicGeometry.IdealSheafData.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX Z hZ V).ker
        (closedSubspaceBaseChangeChartProj B S hS hX Z hZ V t)) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX Z hZ V
  have : _root_.IsReduced ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX Z hZ V)).presheaf.stalk t) :=
    isReduced_stalk_chartScheme_of_isIntegralSpace hZ.1 hZint _ t
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem
    (closedSubspaceBaseChangeChartProj B S hS hX Z hZ V t)
  let e := (Ideal.quotEquivOfEq (stalk_ker_eq_of_affine_target
      (closedSubspaceBaseChangeChartProj B S hS hX Z hZ V) t U.1 U.2 hU)).trans
    (RingHom.quotientKerEquivOfSurjective
      ((closedSubspaceBaseChangeChartProj B S hS hX Z hZ V).stalkMap_surjective t))
  exact isReduced_of_injective e.toRingHom e.injective

/-- **A component of a chart lies over a component of `|X|` exactly when it is the one that
component of `|X|` is the closure of.** For an irreducible component `W` of the scheme of an
étale chart and an irreducible component `T` of `|X|`, the inverse image of `T` contains `W`
exactly when `T` is the closure of the image of the generic point of `W` — that is, when `W` is
one of the branches `AlgebraicGeometry.Space.componentOfChartComponent` assigns to `T`. -/
theorem subset_preimage_iff_closure_singleton_chartSchemeToPoints_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (V : SmallEtale B S hS X)
    (W : irreducibleComponents (chartScheme V)) {T : Set (points B S hS X)}
    (hT : T ∈ irreducibleComponents (points B S hS X)) :
    (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints B S hS X V ⁻¹' T ↔
      closure ({chartSchemeToPoints B S hS X V (genericPoints.ofComponent W).1} :
        Set (points B S hS X)) = T := by
  have hcl := mem_irreducibleComponents_closure_singleton_chartSchemeToPoints B S hS hX hdec V W
  refine ⟨fun hsub => ?_, fun hclT w hw => ?_⟩
  · have hcT := (isClosed_of_mem_irreducibleComponents T hT).closure_subset_iff.2
      (Set.singleton_subset_iff.2 (hsub (genericPoints.isGenericPoint_ofComponent W).mem))
    exact subset_antisymm hcT (hcl.2 hT.1 hcT)
  · rw [Set.mem_preimage, ← hclT]
    exact (((genericPoints.isGenericPoint_ofComponent W).specializes hw).map
      (continuous_chartSchemeToPoints B S hS V)).mem_closure

/-- **A component of the chart lying over an irreducible component of `|X|` has that component's
δ-dimension.** Here the δ-dimension of the component of the chart is taken for the base situation
`AlgebraicGeometry.Space.chartChowSituation` on the chart. -/
theorem deltaDimension_eq_of_subset_preimage_subspacePointSet
    (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZcomp : subspacePointSet D.site D.base D.base_mem X Z.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (W : irreducibleComponents (chartScheme V))
    (hW : (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
      subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    Stacks.Chow.deltaDimension (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V))
        ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ =
      deltaDimension D sX Z := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hdec : IsDecentSpace D.site D.base D.base_mem X := D.isDecentSpace_of_isGood sX hX
  have _ : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hdec
  have hgen : chartSchemeToPoints D.site D.base D.base_mem X V
      (genericPoints.ofComponent W).1 = Z.ambientGenericPoint D.site D.base D.base_mem :=
    (show IsGenericPoint (chartSchemeToPoints D.site D.base D.base_mem X V
        (genericPoints.ofComponent W).1)
        (subspacePointSet D.site D.base D.base_mem X Z.subspace) from
      (subset_preimage_iff_closure_singleton_chartSchemeToPoints_eq D.site D.base D.base_mem
        hX.1 hdec V W hZcomp).mp hW).eq
      (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1)
  rw [Stacks.Chow.deltaDimension_eq_of_isGenericPoint (chartChowSituation D sX hX V hs)
      (𝟙 (chartScheme V)) _ (genericPoints.ofComponent W).1
      (genericPoints.isGenericPoint_ofComponent W)]
  exact (deltaDimension_eq_relativeDimension_id_chartChowSituation D sX hX V hs Z _ hgen).symm

/-- **The regrouping of the zero-cycle coefficients over the components of a chart lying over one
irreducible component of the space.** Let `X/B` be a good algebraic space, let `Z ⊆ X` be an
integral closed subspace whose point set is an irreducible component of `|X|`, let `V` be a
surjective étale scheme chart of `X` and let `Dz` be an ideal sheaf on the chart scheme. At a point
`v` of the chart in the support of `Dz`, of relative dimension `k`, with `Dz` generated at `v` by a
nonzerodivisor of finite colength and the chart of δ-dimension at most `k + 1`: the coefficient at
`v` of the `k`-cycle of Stacks 02QU of the scheme-theoretic intersection of the chart `V ×_X Z` of
`Z` with `Dz` is the **sum**, over the irreducible components `W` of the chart scheme lying over
`|Z|`, of the coefficients at `v` of the `k`-cycles of `W ∩ Dz`. -/
theorem cycleAssociatedToClosedSubscheme_componentChart_sup_eq_finsum
    (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZcomp : subspacePointSet D.site D.base D.base_mem X Z.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (Dz : (chartScheme V).IdealSheafData) (k : ℤ) (v : chartScheme V)
    (hvD : v ∈ Dz.support)
    (U : (chartScheme V).affineOpens) (hvU : v ∈ U.1) (a : Γ(chartScheme V, U.1))
    (haD : AlgebraicGeometry.IdealSheafData.stalk Dz v =
      Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a})
    (ha : IsSMulRegular ((chartScheme V).presheaf.stalk v)
      (((chartScheme V).presheaf.germ U.1 v hvU).hom a))
    (ham : ((chartScheme V).presheaf.germ U.1 v hvU).hom a ∈
      IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk v))
    (hfinite : Module.length ((chartScheme V).presheaf.stalk v)
      ((chartScheme V).presheaf.stalk v ⧸
        Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a}) ≠ ⊤) :
    haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI : @LocallyOfFiniteType _ (chartChowSituation D sX hX V hs).S
        (Dz.subschemeι ≫ 𝟙 (chartScheme V)) :=
      inferInstanceAs (LocallyOfFiniteType (Dz.subschemeι ≫ 𝟙 (chartScheme V)))
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) ≤ (k + 1 : EInt) →
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        (Dz.subschemeι ≫ 𝟙 (chartScheme V)) ≤ (k : EInt) →
    Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartScheme V)) v = k →
    (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V))
        (((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Z.subspace
          Z.isClosedSubspace V).ker ⊔ Dz).subschemeι) k).1 v =
      ∑ᶠ W : {W : irreducibleComponents (chartScheme V) //
          (W.1 : Set (chartScheme V)) ⊆
            chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
              subspacePointSet D.site D.base D.base_mem X Z.subspace},
        (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
          (𝟙 (chartScheme V))
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ Dz).subschemeι)
          k).1 v := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hftD : @LocallyOfFiniteType _ (chartChowSituation D sX hX V hs).S
      (Dz.subschemeι ≫ 𝟙 (chartScheme V)) :=
    inferInstanceAs (LocallyOfFiniteType (Dz.subschemeι ≫ 𝟙 (chartScheme V)))
  intro hYdim hDdim hvdim
  have hci := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    hX.1 Z.subspace Z.isClosedSubspace V
  have hdec : IsDecentSpace D.site D.base D.base_mem X := D.isDecentSpace_of_isGood sX hX
  have hTclosed : IsClosed (chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
      subspacePointSet D.site D.base D.base_mem X Z.subspace) :=
    (isClosed_of_mem_irreducibleComponents _ hZcomp).preimage
      (continuous_chartSchemeToPoints D.site D.base D.base_mem V)
  have hAsupp : ((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Z.subspace
        Z.isClosedSubspace V).ker.support : Set (chartScheme V)) =
      chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
        subspacePointSet D.site D.base D.base_mem X Z.subspace := by
    rw [Scheme.Hom.support_ker, range_closedSubspaceBaseChangeChartProj]
    exact hTclosed.closure_eq
  by_cases hvZ : chartSchemeToPoints D.site D.base D.base_mem X V v ∈
      subspacePointSet D.site D.base D.base_mem X Z.subspace
  case neg =>
    have hvA : v ∉ ((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Z.subspace
        Z.isClosedSubspace V).ker.support : Set (chartScheme V)) := by
      rwa [hAsupp]
    have hzero : ∀ E : (chartScheme V).IdealSheafData,
        (E.support : Set (chartScheme V)) ⊆
            ((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Z.subspace
              Z.isClosedSubspace V).ker.support : Set (chartScheme V)) →
          (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V)) (E ⊔ Dz).subschemeι k).1 v = 0 := by
      intro E hE
      exact Stacks.Chow.cycle_sup_apply_eq_zero_of_notMem_support _ _ _ _ _ (fun h => hvA (hE h))
    rw [hzero _ le_rfl]
    refine ((finsum_congr fun W => hzero _ ?_).trans finsum_zero).symm
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hAsupp]
    exact W.2
  have hvA : v ∈ (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Z.subspace
      Z.isClosedSubspace V).ker.support := by
    change v ∈ (_ : Set (chartScheme V))
    rwa [hAsupp]
  obtain ⟨t, ht⟩ := exists_closedSubspaceBaseChangeChartProj_eq D.site D.base D.base_mem
    hX.1 Z.subspace Z.isClosedSubspace V v hvZ
  have hred := ht ▸ isReduced_quotient_idealStalk_ker_closedSubspaceBaseChangeChartProj
    D.site D.base D.base_mem hX.1 Z.subspace Z.isClosedSubspace Z.isIntegralSpace V t
  have hcomp : ∀ q : PrimeSpectrum ((chartScheme V).presheaf.stalk v),
      q.asIdeal ∈ (AlgebraicGeometry.IdealSheafData.stalk
          (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Z.subspace
            Z.isClosedSubspace V).ker v).minimalPrimes →
        closure ({(chartScheme V).fromSpecStalk v q} : Set (chartScheme V)) ∈
          irreducibleComponents (chartScheme V) := by
    intro q hq
    have hηv : (chartScheme V).fromSpecStalk v q ⤳ v :=
      Scheme.range_fromSpecStalk.subset ⟨q, rfl⟩
    have hη : (chartScheme V).fromSpecStalk v q ∈
        chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
          subspacePointSet D.site D.base D.base_mem X Z.subspace := by
      have h := (Stacks.Chow.stalk_le_iff_mem_support_fromSpecStalk _ v q).mp hq.1.2
      change _ ∈ (_ : Set (chartScheme V)) at h
      rwa [hAsupp] at h
    refine mem_irreducibleComponents_of_maximal_subset_preimage D.site D.base D.base_mem
      hX.1 hdec V hZcomp isIrreducible_singleton.closure
      (hTclosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hη)) ?_
    intro E hEirr hEsub hCE
    obtain ⟨w, hw⟩ := QuasiSober.sober hEirr.closure isClosed_closure
    have hvw : v ∈ closure ({w} : Set (chartScheme V)) := by
      rw [hw]
      exact subset_closure (hCE hηv.mem_closure)
    obtain ⟨q', hq'⟩ : ∃ q' : PrimeSpectrum ((chartScheme V).presheaf.stalk v),
        (chartScheme V).fromSpecStalk v q' = w := by
      have h : w ∈ Set.range ((chartScheme V).fromSpecStalk v) := by
        rw [Scheme.range_fromSpecStalk]
        exact specializes_iff_mem_closure.mpr hvw
      exact h
    have hwle : AlgebraicGeometry.IdealSheafData.stalk
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Z.subspace
          Z.isClosedSubspace V).ker v ≤ q'.asIdeal := by
      refine (Stacks.Chow.stalk_le_iff_mem_support_fromSpecStalk _ v q').mpr ?_
      change _ ∈ (_ : Set (chartScheme V))
      rw [hAsupp, hq']
      exact hTclosed.closure_subset_iff.2 hEsub (hw ▸ subset_closure rfl)
    have hq'q : q' ≤ q := by
      refine (PrimeSpectrum.le_iff_specializes q' q).mpr ?_
      refine ((chartScheme V).fromSpecStalk v).isEmbedding.isInducing.specializes_iff.mp ?_
      rw [hq']
      refine specializes_iff_mem_closure.mpr ?_
      rw [hw]
      exact subset_closure (hCE (subset_closure rfl))
    have hqeq : q = q' :=
      PrimeSpectrum.ext (le_antisymm
        (hq.2 ⟨q'.2, hwle⟩ (show q'.asIdeal ≤ q.asIdeal from hq'q))
        (show q'.asIdeal ≤ q.asIdeal from hq'q))
    rw [hqeq, hq', hw]
    exact subset_closure
  rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_sup_eq_finsum_components_of_isReduced
    (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) _ Dz k hYdim hDdim v hvA hvD hvdim
    U hvU a haD ha ham hfinite hred hcomp]
  refine finsum_eq_of_bijective (fun W => ⟨W.1, W.2.trans hAsupp.subset⟩) ⟨?_, ?_⟩ fun W => rfl
  · intro W W' h
    have h1 : (W.1.1 : Set (chartScheme V)) = (W'.1.1 : Set (chartScheme V)) :=
      congrArg (fun q => ((q.1 : irreducibleComponents (chartScheme V)) :
        Set (chartScheme V))) h
    exact Subtype.ext (Subtype.ext h1)
  · exact fun W => ⟨⟨W.1, W.2.trans hAsupp.ge⟩, Subtype.ext rfl⟩

end AlgebraicGeometry.Space

end
