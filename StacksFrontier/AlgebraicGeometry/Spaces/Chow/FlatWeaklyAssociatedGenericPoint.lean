module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback
public import StacksFrontier.AlgebraicGeometry.SpecTotalFractionRing
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedReduced
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatTensorProduct

/-!
# A weakly associated point of a flat space over an integral one lies over the generic point

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` with `X` locally Noetherian and
`Y` integral. Every *weakly associated* point of `X` is carried by `f` to the generic point of
`Y`. Consequently, for a flat chart `c : V ⟶ Y` whose scheme is affine and locally Noetherian —
**and not assumed reduced** — every point of `Spec Q(Γ(V, 𝒪_V))` lies over the generic point of
`Y`.

For a *reduced* chart the last statement follows from
`AlgebraicGeometry.Scheme.mem_genericPoints_fromSpecTotalFractionRing`: the image of
`Spec Q(Γ(V, 𝒪_V))` in `|V|` then consists of generic points of irreducible components. In a ring
with nilpotents a prime consisting of zerodivisors need not be minimal — it need only be contained
in a weakly associated prime — so the generic points are replaced by the weakly associated points.

Local finiteness of the irreducible components of `X` is not needed, nor openness of `|f|`, nor
any hypothesis on `Y` beyond integrality; in particular `Y` is not assumed locally Noetherian.

## Main results

* `minimalPrimes_finite_of_flat_of_isLocalHom`: a local ring admitting a flat local
  homomorphism to a Noetherian local ring has finitely many minimal primes.
* `isWeaklyAssociatedPrime_maximalIdeal_of_flat_of_isLocalHom`: weak association of the maximal
  ideal descends along a flat local homomorphism, the source having finitely many weakly
  associated primes.
* `exists_isWeaklyAssociatedPrime_ge_of_disjoint_nonZeroDivisors`: a prime of a Noetherian ring
  consisting of zerodivisors is contained in a weakly associated prime.
* `AlgebraicGeometry.Scheme.exists_mem_schemeWeaklyAssociatedPoints_specializes`: the image of
  `Spec Q(Γ(T, ⊤))` specializes into the weakly associated points of `T`.
* `AlgebraicGeometry.Space.exists_geometricPoint_isWeaklyAssociatedPrime_etaleLocalRing`: a
  weakly associated point of an algebraic space carries a geometric point at which the maximal
  ideal of the étale local ring is weakly associated to that ring.
* `Space.pointsMap_eq_genericPoint_of_mem_weaklyAssociatedPointsOfSpace_of_isFlat`:
  a weakly associated point of a flat space over an integral one lies over the generic point.
* `Space.pointsMap_eq_genericPoint_of_isFlat_of_mem_range_fromSpecTotalFractionRing`:
  every point of `Spec Q(Γ(V, 𝒪_V))` on a flat affine chart lies over the generic point.

## Implementation notes

Statements about the chart `V` are phrased at the `V.left.1` spelling of its scheme. The
`(BigFppfOver.toScheme B S hS).obj V` spelling of the étale-local-property API is definitionally
equal but not reducibly so, so instances are transported with `inferInstanceAs`.

## References

* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0EMA](https://stacks.math.columbia.edu/tag/0EMA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors TensorProduct

universe u

/-- A local ring admitting a flat local homomorphism to a Noetherian local ring has only
finitely many minimal primes. -/
theorem minimalPrimes_finite_of_flat_of_isLocalHom (R : Type*) (S : Type*) [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] :
    (minimalPrimes R).Finite := by
  have _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hsurj := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S)
  refine Set.Finite.subset
    ((minimalPrimes.finite_of_isNoetherianRing S).image (Ideal.comap (algebraMap R S))) ?_
  intro p hp
  obtain ⟨P, hP⟩ := hsurj ⟨p, hp.1.1⟩
  have hPp : Ideal.comap (algebraMap R S) P.asIdeal = p := congrArg PrimeSpectrum.asIdeal hP
  have _ : P.asIdeal.IsPrime := P.2
  obtain ⟨q, hq, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := P.asIdeal) bot_le
  have _ : q.IsPrime := hq.1.1
  have h1 : Ideal.comap (algebraMap R S) q ≤ p := hPp ▸ Ideal.comap_mono hqle
  exact ⟨q, hq, le_antisymm h1 (hp.2 ⟨Ideal.IsPrime.comap _, bot_le⟩ h1)⟩

/-- Weak association of the maximal ideal descends along a flat local homomorphism: if
`R → S` is a flat local homomorphism of local rings, `R` has finitely many weakly associated
primes, and the maximal ideal of `S` is weakly associated to `S`, then the maximal ideal of `R`
is weakly associated to `R`. -/
theorem isWeaklyAssociatedPrime_maximalIdeal_of_flat_of_isLocalHom (R : Type*) (S : Type*)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] (hfin : (weaklyAssociatedPrimes R R).Finite)
    (h : IsWeaklyAssociatedPrime S S (IsLocalRing.maximalIdeal S)) :
    IsWeaklyAssociatedPrime R R (IsLocalRing.maximalIdeal R) := by
  have h' : IsWeaklyAssociatedPrime S (S ⊗[R] R) (IsLocalRing.maximalIdeal S) :=
    (LinearEquiv.isWeaklyAssociatedPrime_iff
      (Algebra.TensorProduct.rid R S S).toLinearEquiv _).mpr h
  have hcomap := Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct
    (N := S) (M := R) hfin h'
  rwa [IsLocalRing.maximalIdeal_comap] at hcomap

/-- A prime of a Noetherian ring consisting of zerodivisors is contained in a weakly
associated prime. -/
theorem exists_isWeaklyAssociatedPrime_ge_of_disjoint_nonZeroDivisors (A : Type*) [CommRing A]
    [IsNoetherianRing A] (p : Ideal A) (hdisj : Disjoint (p : Set A) (A⁰ : Set A)) :
    ∃ q : Ideal A, IsWeaklyAssociatedPrime A A q ∧ p ≤ q := by
  have hsub : (p : Set A) ⊆ ⋃ q ∈ associatedPrimes A A, (q : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors A]
    exact fun a ha hmem => (hdisj.le_bot ⟨ha, hmem⟩ : a ∈ (⊥ : Set A)).elim
  obtain ⟨q, hq, hle⟩ :=
    (Ideal.subset_union_prime_finite (associatedPrimes.finite A A) (f := id) ⊥ ⊥
      (fun _ hi _ _ => hi.1)).mp hsub
  rw [associatedPrimes_eq_setOf_exists_mem_minimalPrimes_annihilator] at hq
  exact ⟨q, hq, hle⟩

/-- On an affine locally Noetherian scheme `T`, the image of every point of the spectrum of the
total ring of fractions of `Γ(T, ⊤)` specializes to a weakly associated point of `T`. -/
theorem AlgebraicGeometry.Scheme.exists_mem_schemeWeaklyAssociatedPoints_specializes
    (T : Scheme.{u}) [IsAffine T] [IsLocallyNoetherian T]
    (z : Spec (CommRingCat.of (FractionRing Γ(T, ⊤)))) :
    ∃ t : T, T.fromSpecTotalFractionRing.base z ⤳ t ∧
      t ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints T := by
  have _ : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  set p : PrimeSpectrum Γ(T, ⊤) :=
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))))).base z with hpdef
  have hdisj : Disjoint ((p.asIdeal : Set Γ(T, ⊤))) ((Γ(T, ⊤))⁰ : Set Γ(T, ⊤)) := by
    have hrange := PrimeSpectrum.localization_comap_range
      (S := FractionRing Γ(T, ⊤)) (R := Γ(T, ⊤)) (Γ(T, ⊤))⁰
    have hmem : p ∈ Set.range (PrimeSpectrum.comap
        (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)))) := ⟨z, rfl⟩
    rw [hrange] at hmem
    exact Disjoint.symm hmem
  obtain ⟨q, hq, hle⟩ :=
    exists_isWeaklyAssociatedPrime_ge_of_disjoint_nonZeroDivisors Γ(T, ⊤) p.asIdeal hdisj
  have hqp : q.IsPrime := hq.isPrime
  let hU := isAffineOpen_top T
  let pq : PrimeSpectrum Γ(T, ⊤) := ⟨q, hqp⟩
  refine ⟨hU.fromSpec pq, ?_, ?_⟩
  · have hspec : p ⤳ pq := (PrimeSpectrum.le_iff_specializes p pq).mp hle
    have hmap := hspec.map hU.fromSpec.continuous
    rwa [show hU.fromSpec p = T.fromSpecTotalFractionRing.base z from by
      rw [IsAffineOpen.fromSpec_top]; rfl] at hmap
  · have htU : hU.fromSpec pq ∈ (⊤ : T.Opens) := trivial
    have hqx : q = (hU.primeIdealOf ⟨hU.fromSpec pq, htU⟩).asIdeal :=
      (congrArg PrimeSpectrum.asIdeal <| hU.fromSpec.isOpenEmbedding.injective
        (hU.fromSpec_primeIdealOf ⟨hU.fromSpec pq, htU⟩)).symm
    rw [Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff,
      ← AlgebraicGeometry.isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
        (SheafOfModules.unit T.ringCatSheaf) ⊤ hU _ htU, ← hqx]
    exact hq

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A weakly associated point of an algebraic space carries a geometric point at which the
maximal ideal of the étale local ring is weakly associated to that ring. -/
theorem exists_geometricPoint_isWeaklyAssociatedPrime_etaleLocalRing
    (X : AlgebraicSpaces B S hS) {x : points B S hS X.1}
    (hx : x ∈ weaklyAssociatedPointsOfSpace B S hS X) :
    ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
      letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
        isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
        (etaleLocalRing B S hS X.1 xbar) (IsLocalRing.maximalIdeal _) := by
  obtain ⟨xbar, hlies, hwa⟩ := (isWeaklyAssociatedPoint_iff_moduleStalkLarge B S hS X _ x).mp hx
  refine ⟨xbar, hlies, ?_⟩
  have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  have : IsLocalRing
      (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X xbar).symm.isLocalRing
  have hfib : IsWeaklyAssociatedPrime
      (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj)
      (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) (IsLocalRing.maximalIdeal _) :=
    (isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv (RingEquiv.refl _)
      (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 xbar X.2)
        (smallEtaleRingedTopos B S hS X).O).toAddEquiv
      (fun r z => (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 xbar X.2)
        (smallEtaleRingedTopos B S hS X).O).map_smul r z)).mp hwa
  exact (isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv
    (pointStalkRingEquiv B S hS X xbar) (pointStalkRingEquiv B S hS X xbar).toAddEquiv
    (fun r z => map_mul (pointStalkRingEquiv B S hS X xbar) r z)).mp hfib

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A point of an integral algebraic space whose closure is everything is the generic point. -/
private theorem eq_genericPoint_of_isGenericPoint_univ (hY : IsAlgebraicSpace B S hS Y)
    (hintY : IsIntegralSpace B S hS Y) (p : points B S hS Y)
    (h : IsGenericPoint p (Set.univ : Set (points B S hS Y))) :
    p = genericPoint B S hS hY hintY := by
  have : T0Space (points B S hS Y) :=
    t0Space_points_of_isDecentSpace B S hS hY hintY.isDecentSpace
  have : IrreducibleSpace (points B S hS Y) := hintY.2.2
  exact h.eq (isGenericPoint_genericPoint B S hS hY hintY)

/-- A weakly associated point of a flat algebraic space over an integral one is carried to the
generic point. Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` with `X` locally
Noetherian and `Y` integral. Then every weakly associated point of `X` is carried by `f` to the
generic point of `Y`. Neither is `X` assumed reduced nor `Y` locally Noetherian. -/
theorem pointsMap_eq_genericPoint_of_mem_weaklyAssociatedPointsOfSpace_of_isFlat
    (hX : IsAlgebraicSpace B S hS X)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFlat B S hS f) {x : points B S hS X}
    (hx : x ∈ weaklyAssociatedPointsOfSpace B S hS ⟨X, hX⟩) :
    pointsMap B S hS X f x = genericPoint B S hS hY hintY := by
  obtain ⟨xbar, hlies, hwa⟩ :=
    exists_geometricPoint_isWeaklyAssociatedPrime_etaleLocalRing B S hS ⟨X, hX⟩ hx
  set ybar := geometricPointMap f xbar with hybar
  have : IsLocalRing (etaleLocalRing B S hS X xbar) :=
    isLocalRing_etaleLocalRing B S hS X hX xbar
  have : IsLocalRing (etaleLocalRing B S hS Y ybar) :=
    isLocalRing_etaleLocalRing B S hS Y hY ybar
  let : Algebra (etaleLocalRing B S hS Y ybar) (etaleLocalRing B S hS X xbar) :=
    (etaleLocalRingMap hX f xbar).toAlgebra
  have : Module.Flat (etaleLocalRing B S hS Y ybar) (etaleLocalRing B S hS X xbar) :=
    flat_etaleLocalRingMap B S hS hX hY f hf xbar
  have : IsLocalHom
      (algebraMap (etaleLocalRing B S hS Y ybar) (etaleLocalRing B S hS X xbar)) :=
    isLocalHom_etaleLocalRingMap B S hS hX hY f xbar
  have : IsNoetherianRing (etaleLocalRing B S hS X xbar) :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS X hX hNX xbar
  have : _root_.IsReduced (etaleLocalRing B S hS Y ybar) :=
    (isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint hY ybar).mpr
      ((isReduced_iff_forall_localRing_isReduced B S hS Y hY).mp
        hintY.hasEtaleLocalProperty_isReduced ybar.image)
  have hfin : (weaklyAssociatedPrimes (etaleLocalRing B S hS Y ybar)
      (etaleLocalRing B S hS Y ybar)).Finite := by
    rw [weakAss_eq_minimalPrimes0EMA]
    exact minimalPrimes_finite_of_flat_of_isLocalHom _ (etaleLocalRing B S hS X xbar)
  have hdim : ringKrullDim (etaleLocalRing B S hS Y ybar) = 0 :=
    (isWeaklyAssociatedPrime_maximalIdeal_self_iff_ringKrullDim_eq_zero _).mp
      (isWeaklyAssociatedPrime_maximalIdeal_of_flat_of_isLocalHom _
        (etaleLocalRing B S hS X xbar) hfin hwa)
  have hloc : localRingDimension B S hS ybar.image = 0 := by
    have hcast := ringKrullDim_etaleLocalRing_eq_localRingDimension hY ybar
    rw [hdim] at hcast
    exact_mod_cast hcast.symm
  have himg : ybar.image = pointsMap B S hS X f x := by
    rw [hybar, geometricPointMap_image, hlies]
  have hgp : pointsMap B S hS X f x ∈ genericPoints (points B S hS Y) := by
    refine (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY
      hintY.isDecentSpace _).mpr ?_
    rwa [← himg]
  have : IrreducibleSpace (points B S hS Y) := hintY.2.2
  exact eq_genericPoint_of_isGenericPoint_univ B S hS hY hintY _
    (Set.eq_univ_of_univ_subset
      (hgp.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _)))

/-- A weakly associated point of the scheme underlying an object `V` of the site is a weakly
associated point of the algebraic space represented by `V`. -/
theorem mem_weaklyAssociatedPointsOfSpace_pointsEquivScheme_symm (V : BigFppfOver B S hS)
    (t : (BigFppfOver.toScheme B S hS).obj V)
    (ht : t ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints
      ((BigFppfOver.toScheme B S hS).obj V)) :
    (pointsEquivScheme B S hS V).symm t ∈
      weaklyAssociatedPointsOfSpace B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ := by
  set X : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ with hXdef
  set U₀ : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (𝟙 (yoneda.obj V)),
      (isMultiplicative_presheaf_etale B S hS).id_mem _⟩ with hU₀
  have hc : chartSchemeToPoints B S hS X.1 U₀ t = (pointsEquivScheme B S hS V).symm t := by
    rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
    exact pointsMap_id_apply B S hS _
  rw [← hc]
  exact mem_weaklyAssociatedPointsOfSpace_chartSchemeToPoints B S hS X U₀ t ht

/-- Every point of `Spec Q(Γ(V, 𝒪_V))` lies over the generic point of `Y`, for a flat affine
chart which is not assumed reduced. Let `Y` be an integral algebraic space over `S` and let
`c : V ⟶ Y` be a flat chart whose scheme is affine and locally Noetherian. Then every point of
the spectrum of the total ring of fractions of `Γ(V, 𝒪_V)` is carried to the generic point
of `Y`. -/
theorem pointsMap_eq_genericPoint_of_isFlat_of_mem_range_fromSpecTotalFractionRing
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hintY : IsIntegralSpace B S hS Y) (V : BigFppfOver B S hS) [IsAffine V.left.1]
    [IsLocallyNoetherian V.left.1] (c : yoneda.obj V ⟶ Y)
    (hc : IsFlat B S hS c) (η : points B S hS (yoneda.obj V))
    (z : Spec (CommRingCat.of (FractionRing Γ(V.left.1, ⊤))))
    (hη : pointsEquivScheme B S hS V η = V.left.1.fromSpecTotalFractionRing.base z) :
    pointsMap B S hS (yoneda.obj V) c η = genericPoint B S hS hY hintY := by
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    inferInstanceAs (IsLocallyNoetherian V.left.1)
  have hNV : HasEtaleLocalProperty B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).2 inferInstance
  obtain ⟨t, hspec, ht⟩ := V.left.1.exists_mem_schemeWeaklyAssociatedPoints_specializes z
  have htgen : pointsMap B S hS (yoneda.obj V) c ((pointsEquivScheme B S hS V).symm t) =
      genericPoint B S hS hY hintY :=
    pointsMap_eq_genericPoint_of_mem_weaklyAssociatedPointsOfSpace_of_isFlat B S hS
      (isAlgebraicSpace_yoneda B S hS V) hNV hY hintY c hc
      (mem_weaklyAssociatedPointsOfSpace_pointsEquivScheme_symm B S hS V t ht)
  have hηt : η ⤳ (pointsEquivScheme B S hS V).symm t := by
    have hmap := (hη ▸ hspec).map (schemePointsHomeomorph B S hS V).symm.continuous
    rwa [show (schemePointsHomeomorph B S hS V).symm
      (pointsEquivScheme B S hS V η) = η from
      (schemePointsHomeomorph B S hS V).symm_apply_apply η] at hmap
  have hsp : pointsMap B S hS (yoneda.obj V) c η ⤳ genericPoint B S hS hY hintY :=
    htgen ▸ hηt.map (continuous_pointsMap B S hS c)
  refine eq_genericPoint_of_isGenericPoint_univ B S hS hY hintY _
    (Set.eq_univ_of_univ_subset ?_)
  rw [← (isGenericPoint_genericPoint B S hS hY hintY).def]
  exact hsp.closure_subset

end AlgebraicGeometry.Space

end
