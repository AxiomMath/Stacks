module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport

/-!
# Proper pushforward of a principal divisor

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
integral and locally of finite type over `S` with `dim_δ(X) = dim_δ(Y) = n`, and let `p : X ⟶ Y`
be a proper dominant morphism over `S`. Then `p` induces a finite extension `R(Y) ⊆ R(X)` of
function fields, and for a nonzero rational function `f` on `X`

  `p_* div(f) = div(Nm_{R(X)/R(Y)}(f))`.

This is Stacks 02RT: the pushforward of a principal divisor along a generically finite morphism
is again a principal divisor.

## Main results

* `Stacks.Chow.properPushforward_principalDivisorCycle` — Stacks 02RT.
* `Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite` — for a finite morphism, the coefficient
  of `p_*div(f)` at the generic point of a prime divisor of `Y` is the order of vanishing of the
  norm there.
* `Stacks.Chow.finsum_ord_mul_residueDegree_of_coheight_eq_one` — the same for a proper morphism
  which is merely finite over a neighbourhood of that point.
* `Stacks.Chow.finsum_ord_mul_weight_of_coheight_ne_one` — elsewhere both sides vanish.

## Implementation notes

Both cycles are determined by their coefficients, so the proof computes the coefficient of each
side at a point `y` of `Y`.

Away from codimension one both sides vanish. The order of vanishing of the norm at `y` is zero by
convention, and every point `x` above `y` either has codimension other than one, where the order
of vanishing of `f` vanishes, or has codimension one, where the relative dimension of `x` is
`n - 1` and hence differs from that of `y`, so that the pushforward weight vanishes. That the
relative dimension of a point is `n - 1` exactly in codimension one is Stacks 02RK, available as
`Stacks.Chow.relativeDimension_eq_sub_one_iff_coheight_eq_one`.

At a point `y` of codimension one the computation is local, and this is where the content lies.
By `Stacks.Chow.exists_isFinite_morphismRestrict_of_coheight_eq_one` the morphism `p` is finite
over an open neighbourhood `V` of `y`. The computation is therefore carried out twice: once for a
genuinely finite morphism, and once to reduce `p` to its restriction over `V`.

For a finite morphism `g : X ⟶ Y`, shrinking to an affine open `W ∋ y` presents the situation as a
finite ring map `φ : Γ(Y, W) ⟶ Γ(X, g⁻¹W)` of Noetherian domains. Localizing at the prime of `y`
gives a one-dimensional Noetherian local domain `A = 𝒪_{Y,y}` with fraction field `R(Y)`, a finite
`A`-algebra `B` with fraction field `R(X)`, and a bijection between the fibre of `g` over `y` and
the maximal ideals of `B` (the two directions are the prime of a point of an affine open and the
point of a prime; the localization order isomorphism `IsLocalization.primeSpectrumOrderIso`
identifies the primes of `B` with the primes of `Γ(X, g⁻¹W)` disjoint from the multiplicative set,
and those above the prime of `y` are maximal because `B` is integral over the local ring `A`).
Under that bijection the coefficient of `div(f)` at a point of the fibre is the `ordInt` of the
corresponding localization of `B`, the pushforward weight is the inertia degree, and the
coefficient of `div(Nm(f))` at `y` is the `ordInt` of `A` at the norm. The identity to be proved is
therefore exactly the determinant computation of Stacks 02MJ, proved as
`ord_norm_eq_sum_inertiaDeg_mul_ord`.

The reduction of `p` to the finite morphism `p ∣_ V` passes from `V` and `p⁻¹V` back to `Y` and `X`
— for the order of vanishing, the residue degree, and the norm — using the transport lemmas of
`StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport`; the function
field of a nonempty open subscheme of an integral scheme is the function field of the whole, and
neither the order of vanishing nor the residue degree sees the difference. Keeping that reduction
in a lemma of its own is also what keeps either declaration well inside the default elaboration
budget.

The function-field extension of `p` is carried as an instance argument together with the
hypothesis that its structure map is `AlgebraicGeometry.dominantFunctionFieldMap p`, so that the
auxiliary statements do not have to repeat the `letI` of the main one.

## References

* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02MJ](https://stacks.math.columbia.edu/tag/02MJ)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The coefficient at a prime divisor of a finite morphism -/

/-- **Stacks 02RT, the coefficient at a prime divisor of a finite morphism.** Let `g : X ⟶ Y` be a
finite dominant morphism of integral locally Noetherian schemes, let `y` be a point of `Y` of
codimension one whose fibre consists of points of codimension one, and let `f` be a nonzero
rational function on `X`. Then the coefficient at `y` of the proper pushforward of `div(f)` is the
order of vanishing at `y` of the norm of `f` in the extension `R(Y) ⊆ R(X)` of function fields.

Restricting `g` over an affine open neighbourhood of `y` presents the situation as a finite ring
map of Noetherian domains; localizing at the prime of `y` identifies the fibre with the maximal
ideals of the resulting finite algebra, the order of vanishing of `f` with the `ordInt` of the
corresponding localization and the residue degree with the degree of a residue-field extension.
The identity to be proved is therefore the determinant computation of Stacks 02MJ, proved as
`ord_norm_eq_sum_inertiaDeg_mul_ord`. -/
theorem finsum_ord_mul_residueDegree_of_isFinite {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [Algebra Y.functionField X.functionField]
    (halg : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap g)
    (f : X.functionField) (hf : f ≠ 0) (y : Y) (hy : Order.coheight y = 1)
    (hfibercoh : ∀ x : X, g.base x = y → Order.coheight x = 1) :
    (∑ᶠ x ∈ g.base ⁻¹' {y}, X.ord f x * (g.residueDegree x : ℤ)) =
      Y.ord (Algebra.norm Y.functionField f) y := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let yW : W := ⟨y, hyW⟩
  let _ : IsAffine W := hW
  let _ : IsAffine (g ⁻¹ᵁ W) := hW.preimage g
  let A₀ := Γ(Y, W)
  let B₀ := Γ(X, g ⁻¹ᵁ W)
  let φ : A₀ →+* B₀ := (g.app W).hom
  let P : PrimeSpectrum A₀ := hW.primeIdealOf yW
  let A := Y.presheaf.stalk y
  let _ : Algebra A₀ A := (Y.presheaf.germ W yW hyW).hom.toAlgebra
  let _ : IsLocalization.AtPrime A P.asIdeal := hW.isLocalization_stalk yW
  let _ : Algebra (↑A₀) (↑B₀) := φ.toAlgebra
  let B := Localization (Submonoid.map φ P.asIdeal.primeCompl)
  let _ : IsLocalization (Submonoid.map φ P.asIdeal.primeCompl) B :=
    Localization.isLocalization
  let _ : IsLocalization (Algebra.algebraMapSubmonoid B₀ P.asIdeal.primeCompl) B :=
    Localization.isLocalization
  have hunit : ∀ s : P.asIdeal.primeCompl,
      IsUnit (((algebraMap B₀ B).comp φ) s) := fun s =>
    IsLocalization.map_units (M := Submonoid.map φ P.asIdeal.primeCompl) B
      ⟨φ s.1, ⟨s.1, s.2, rfl⟩⟩
  let φAB : A →+* B := IsLocalization.lift (M := P.asIdeal.primeCompl)
    (g := (algebraMap B₀ B).comp φ) hunit
  let _ : Algebra A B := φAB.toAlgebra
  let _ : Algebra A₀ B := Algebra.compHom B (algebraMap A₀ A)
  let _ : SMul B₀ B := (inferInstance : Algebra B₀ B).toSMul
  let _ : SMul A B := (inferInstance : Algebra A B).toSMul
  let _ : SMul A₀ B := (inferInstance : Algebra A₀ B).toSMul
  have hAB : (algebraMap B₀ B).comp φ = φAB.comp (algebraMap A₀ A) :=
    (IsLocalization.lift_comp hunit).symm
  have hABeval (a : A₀) : algebraMap B₀ B (φ a) = algebraMap A B (algebraMap A₀ A a) :=
    RingHom.congr_fun hAB a
  let _ : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A₀ B₀ B :=
    IsScalarTower.of_algebraMap_eq' (R := A₀) (S := B₀) (A := B) hAB.symm
  have _ : Module.Finite (↑A₀) (↑B₀) := IsFinite.finite_app g W hW
  have _ : Module.Finite A B := Module.Finite.of_isLocalization A₀ B₀ P.asIdeal.primeCompl
  let S₀ : Submonoid (↑B₀) := Submonoid.map φ P.asIdeal.primeCompl
  let eLoc : PrimeSpectrum B ≃o
      {q : PrimeSpectrum B₀ // Disjoint (S₀ : Set B₀) q.asIdeal} :=
    IsLocalization.primeSpectrumOrderIso S₀ B
  have hQmap (v : MaximalSpectrum B) :
      ((eLoc v.toPrimeSpectrum).1.asIdeal).map (algebraMap B₀ B) = v.asIdeal := by
    change (Ideal.under B₀ v.asIdeal).map (algebraMap B₀ B) = v.asIdeal
    exact IsLocalization.map_under S₀ B v.asIdeal
  have hQdisj (Q : PrimeSpectrum B₀) (hQP : Q.comap φ = P) :
      Disjoint (S₀ : Set B₀) Q.asIdeal := by
    rw [Set.disjoint_left]
    intro z hzS hzQ
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hzS
    have hmem : (s : ↑A₀) ∈ (Q.comap φ).asIdeal := hzQ
    rw [hQP] at hmem
    exact hs hmem
  have hfiberMax (Q : PrimeSpectrum B₀) (hQP : Q.comap φ = P) :
      (eLoc.symm ⟨Q, hQdisj Q hQP⟩).asIdeal.IsMaximal := by
    let Q' : Ideal B := Q.asIdeal.map (algebraMap B₀ B)
    have hQ'prime : Q'.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint S₀ B Q.asIdeal Q.isPrime
        (hQdisj Q hQP)
    let _ : Q'.IsPrime := hQ'prime
    let J : Ideal A := Q'.comap (algebraMap A B)
    have hJne : J ≠ ⊤ := Ideal.comap_ne_top _ hQ'prime.ne_top
    have hJmax : J.IsMaximal := by
      have hPmap : P.asIdeal.map (algebraMap A₀ A) = IsLocalRing.maximalIdeal A :=
        IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal A
      have hmaxle : IsLocalRing.maximalIdeal A ≤ J := by
        rw [← hPmap]
        apply Ideal.map_le_iff_le_comap.mpr
        intro a ha
        change algebraMap A B (algebraMap A₀ A a) ∈ Q'
        have haQ : φ a ∈ Q.asIdeal := by
          have hmem : a ∈ (Q.comap φ).asIdeal := by rw [hQP]; exact ha
          exact Ideal.mem_comap.mp hmem
        rw [← hABeval a]
        exact Ideal.mem_map_of_mem (algebraMap B₀ B) haQ
      have hEq : IsLocalRing.maximalIdeal A = J :=
        (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hJne hmaxle
      rw [← hEq]
      exact IsLocalRing.maximalIdeal.isMaximal A
    have _ : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    change Q'.IsMaximal
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) Q' hJmax
  let _ : Ring.KrullDimLE 1 A := AlgebraicGeometry.krullDimLE_of_coheight_le hy.le
  have hpreimageW : Nonempty (g ⁻¹ᵁ W) := by
    obtain ⟨z, hzW, hzRange⟩ :=
      g.denseRange.inter_open_nonempty W W.2 ⟨yW, yW.property⟩
    obtain ⟨x, rfl⟩ := hzRange
    exact ⟨⟨x, hzW⟩⟩
  let _ : Nonempty W := ⟨yW⟩
  let _ : Nonempty (g ⁻¹ᵁ W) := hpreimageW
  have hφinj : Function.Injective φ := by
    let _ : IsSchemeTheoreticallyDominant g :=
      IsSchemeTheoreticallyDominant.of_isDominant g
    exact g.app_injective W
  have hS0 : S₀ ≤ nonZeroDivisors B₀ :=
    map_le_nonZeroDivisors_of_injective φ hφinj P.asIdeal.primeCompl_le_nonZeroDivisors
  have hABinj : Function.Injective φAB := by
    change Function.Injective (IsLocalization.lift hunit : A →+* B)
    rw [IsLocalization.lift_injective_iff]
    refine fun a b => ⟨fun hab => ?_, fun hab => ?_⟩
    · obtain rfl := IsLocalization.injective A P.asIdeal.primeCompl_le_nonZeroDivisors hab
      simp
    · obtain rfl := hφinj (IsLocalization.injective B hS0 hab)
      simp
  have _ : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hcomap (v : MaximalSpectrum B) :
      v.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) v.asIdeal)
  have hQcontract (v : MaximalSpectrum B) :
      (eLoc v.toPrimeSpectrum).1.comap φ = P := by
    let Q := (eLoc v.toPrimeSpectrum).1
    have hunder : v.asIdeal.under B₀ = Q.asIdeal := by
      have h := IsLocalization.under_map_of_isPrime_disjoint S₀ B
        Q.isPrime (eLoc v.toPrimeSpectrum).2
      rw [hQmap v] at h
      exact h.symm
    have hPcontract : (IsLocalRing.maximalIdeal A).under A₀ = P.asIdeal :=
      IsLocalization.AtPrime.under_maximalIdeal A P.asIdeal
    apply PrimeSpectrum.ext
    ext a
    change φ a ∈ Q.asIdeal ↔ a ∈ P.asIdeal
    rw [← hunder]
    change algebraMap B₀ B (φ a) ∈ v.asIdeal ↔ a ∈ P.asIdeal
    rw [hABeval a]
    change algebraMap A₀ A a ∈ v.asIdeal.comap (algebraMap A B) ↔
      a ∈ P.asIdeal
    rw [hcomap v, ← hPcontract, Ideal.mem_under]
  let pA : PrimeSpectrum A :=
    ⟨IsLocalRing.maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩
  have hfiniteFiber : (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {pA}).Finite :=
    Algebra.QuasiFinite.finite_comap_preimage_singleton pA
  have _ : Finite {q : PrimeSpectrum B //
      q ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {pA}} := hfiniteFiber.to_subtype
  have _ : Finite (MaximalSpectrum B) :=
    Finite.of_injective (fun v : MaximalSpectrum B =>
        (⟨v.toPrimeSpectrum, PrimeSpectrum.ext (hcomap v)⟩ :
          {q : PrimeSpectrum B // q ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {pA}}))
      fun v w h =>
        MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal (congrArg Subtype.val h))
  have hU : IsAffineOpen (g ⁻¹ᵁ W) := hW.preimage g
  let x₀ : g ⁻¹ᵁ W := Classical.choice hpreimageW
  let _ : Algebra B₀ (X.presheaf.stalk x₀.1) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x₀
  let _ : IsScalarTower B₀ (X.presheaf.stalk x₀.1) X.functionField :=
    AlgebraicGeometry.functionField_isScalarTower X (g ⁻¹ᵁ W) x₀
  have hB₀L (b : B₀) :
      algebraMap B₀ X.functionField b = (X.germToFunctionField (g ⁻¹ᵁ W)).hom b := by
    calc
      algebraMap B₀ X.functionField b =
          algebraMap (X.presheaf.stalk x₀.1) X.functionField
            (algebraMap B₀ (X.presheaf.stalk x₀.1) b) :=
        IsScalarTower.algebraMap_apply (R := B₀) (S := X.presheaf.stalk x₀.1)
          (A := X.functionField) b
      _ = (X.germToFunctionField (g ⁻¹ᵁ W)).hom b := by
        change algebraMap (X.presheaf.stalk x₀.1) X.functionField
          (X.presheaf.germ (g ⁻¹ᵁ W) x₀.1 x₀.2 b) = _
        exact Scheme.algebraMap_germ_eq_germToFunctionField
          (X := X) (U := g ⁻¹ᵁ W) (x := x₀) x₀.property b
  let _ : IsFractionRing A Y.functionField := inferInstance
  let _ : IsFractionRing B₀ X.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X (g ⁻¹ᵁ W) (hW.preimage g)
  let _ : Algebra B₀ X.functionField := inferInstance
  let _ : Algebra B X.functionField :=
    IsLocalization.localizationAlgebraOfSubmonoidLe B X.functionField S₀
      (nonZeroDivisors B₀) hS0
  let _ : IsScalarTower B₀ B X.functionField :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B X.functionField S₀
      (nonZeroDivisors B₀) hS0
  let _ : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hS0
  let _ : IsFractionRing B X.functionField :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S₀ B X.functionField
  let _ : Algebra A X.functionField := Algebra.compHom X.functionField (algebraMap A B)
  let _ : IsScalarTower A B X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have hAtoLinj : Function.Injective (algebraMap A X.functionField) := by
    intro a b hab
    have hB : algebraMap B X.functionField (algebraMap A B a) =
        algebraMap B X.functionField (algebraMap A B b) := hab
    have hAB : algebraMap A B a = algebraMap A B b :=
      IsFractionRing.injective B X.functionField hB
    exact hABinj (show φAB a = φAB b by
      change algebraMap A B a = algebraMap A B b
      exact hAB)
  let _ : FaithfulSMul A X.functionField :=
    (faithfulSMul_iff_algebraMap_injective A X.functionField).mpr hAtoLinj
  let _ : IsScalarTower A₀ A Y.functionField :=
    AlgebraicGeometry.functionField_isScalarTower Y W yW
  have hfieldCompat := appLE_germToFunctionField_commutes g W (g ⁻¹ᵁ W) le_rfl
  have hA0L : (algebraMap A X.functionField).comp (algebraMap A₀ A) =
      ((algebraMap Y.functionField X.functionField).comp
        (algebraMap A Y.functionField)).comp (algebraMap A₀ A) := by
    ext a
    have hAK : algebraMap A Y.functionField (algebraMap A₀ A a) =
        (Y.germToFunctionField W).hom a := by
      change algebraMap (Y.presheaf.stalk y) Y.functionField
          ((Y.presheaf.germ W y yW.property).hom a) = _
      exact Scheme.algebraMap_germ_eq_germToFunctionField
        (X := Y) (U := W) (x := yW) yW.property a
    calc
      (algebraMap A X.functionField) ((algebraMap A₀ A) a) =
          algebraMap B X.functionField (algebraMap A B (algebraMap A₀ A a)) := rfl
      _ = algebraMap B X.functionField (algebraMap B₀ B (φ a)) := by rw [← hABeval a]
      _ = algebraMap B₀ X.functionField (φ a) := by
        rw [← IsScalarTower.algebraMap_apply B₀ B X.functionField]
      _ = (dominantFunctionFieldMap g) ((Y.germToFunctionField W).hom a) := by
        have h := congrArg (fun k : A₀ →+* X.functionField => k a) hfieldCompat
        calc
          algebraMap B₀ X.functionField (φ a) =
              (X.germToFunctionField (g ⁻¹ᵁ W)).hom (φ a) := hB₀L (φ a)
          _ = (dominantFunctionFieldMap g) ((Y.germToFunctionField W).hom a) := by
            simpa [A₀, B₀, φ, Scheme.Hom.appLE_eq_app] using h
      _ = algebraMap Y.functionField X.functionField
            (algebraMap A Y.functionField (algebraMap A₀ A a)) := by
        rw [hAK, halg]
  have hAtoL : algebraMap A X.functionField =
      (algebraMap Y.functionField X.functionField).comp (algebraMap A Y.functionField) :=
    IsLocalization.ringHom_ext (P.asIdeal.primeCompl) hA0L
  clear hA0L hB₀L hfieldCompat hQmap hfiniteFiber
  let _ : IsScalarTower A Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq' hAtoL
  let _ : Module.Finite Y.functionField X.functionField :=
    finiteDimensional_fractionRing_of_finite A B Y.functionField X.functionField hABinj
  let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let _ : Ring.DimensionLEOne A :=
    ⟨fun {q} hq _ => Ideal.isMaximal_of_isPrime_of_ne_bot q hq⟩
  let _ : Ring.DimensionLEOne B := Ring.DimensionLEOne.of_isIntegral (R := A) B
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let _ : ∀ v : MaximalSpectrum B,
      IsNoetherianRing (Localization.AtPrime v.asIdeal) := fun _ => inferInstance
  let _ : ∀ v : MaximalSpectrum B,
      Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal) := fun v => by
    rw [Ring.krullDimLE_iff,
      IsLocalization.AtPrime.ringKrullDim_eq_height v.asIdeal]
    exact le_trans Ideal.height_le_ringKrullDim_of_isPrime
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 B))
  let _ : ∀ v : MaximalSpectrum B,
      Algebra (Localization.AtPrime v.asIdeal) X.functionField := fun v =>
    let _ : v.asIdeal.IsPrime := v.isMaximal.isPrime
    IsLocalization.localizationAlgebraOfSubmonoidLe
        (Localization.AtPrime v.asIdeal) X.functionField v.asIdeal.primeCompl
        (nonZeroDivisors B) v.asIdeal.primeCompl_le_nonZeroDivisors
  let _ : ∀ v : MaximalSpectrum B,
      IsScalarTower B (Localization.AtPrime v.asIdeal) X.functionField := fun v =>
    let _ : v.asIdeal.IsPrime := v.isMaximal.isPrime
    IsLocalization.localization_isScalarTower_of_submonoid_le
        (Localization.AtPrime v.asIdeal) X.functionField v.asIdeal.primeCompl
        (nonZeroDivisors B) v.asIdeal.primeCompl_le_nonZeroDivisors
  let _ : ∀ v : MaximalSpectrum B,
      IsFractionRing (Localization.AtPrime v.asIdeal) X.functionField := fun v =>
    let _ : v.asIdeal.IsPrime := v.isMaximal.isPrime
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) X.functionField
  let fiberPoint : {x : X // g.base x = y} → g ⁻¹ᵁ W := fun x =>
    ⟨x.1, by
      change g.base x.1 ∈ W
      rw [x.2]
      exact hyW⟩
  let fiberPrime : {x : X // g.base x = y} → PrimeSpectrum B₀ :=
    fun x => hU.primeIdealOf (fiberPoint x)
  let hfiberToMax : {x : X // g.base x = y} → MaximalSpectrum B := fun x => by
    let Q : PrimeSpectrum B₀ := fiberPrime x
    have hQP : Q.comap φ = P := by
      have h := AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE
        (f := g) (x := (fiberPoint x).1) W hW (g ⁻¹ᵁ W) hU le_rfl
          (fiberPoint x).property
      have hpoint : (⟨g.base (fiberPoint x).1,
          (show g.base (fiberPoint x).1 ∈ W from (fiberPoint x).property)⟩ : W) = yW :=
        Subtype.ext x.2
      have h' : (fiberPrime x).comap φ =
          hW.primeIdealOf ⟨g.base (fiberPoint x).1, (fiberPoint x).property⟩ := by
        simpa only [fiberPrime, Scheme.Hom.appLE_eq_app] using h
      change (fiberPrime x).comap φ = P
      rw [h', hpoint]
    exact ⟨(eLoc.symm ⟨Q, hQdisj Q hQP⟩).asIdeal, hfiberMax Q hQP⟩
  let specPoint : MaximalSpectrum B → Spec B₀ :=
    fun v => (eLoc v.toPrimeSpectrum).1
  let hfiberFromMax : MaximalSpectrum B → {x : X // g.base x = y} := fun v => by
    let Q : Spec B₀ := specPoint v
    have hQP : Q.comap φ = P := hQcontract v
    have hSpecMap : Spec.map (g.appLE W (g ⁻¹ᵁ W) le_rfl) Q = P := by
      apply PrimeSpectrum.ext
      change (Q.comap (CommRingCat.Hom.hom
        (g.appLE W (g ⁻¹ᵁ W) le_rfl))).asIdeal = P.asIdeal
      rw [Scheme.Hom.appLE_eq_app]
      exact congrArg PrimeSpectrum.asIdeal hQP
    let zW : g ⁻¹ᵁ W := hU.isoSpec.inv Q
    have hmap := AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec
      (f := g) hW hU le_rfl
    have hgz : g.base zW.1 = y := by
      have hb := congrArg (fun f : Scheme.Hom _ _ => f.base) hmap
      have hpt := congrArg (fun f => f Q) hb
      change hW.fromSpec (Spec.map (g.appLE W (g ⁻¹ᵁ W) le_rfl) Q) =
        g.base (hU.fromSpec Q) at hpt
      calc
        g.base zW.1 = hW.fromSpec (Spec.map (g.appLE W (g ⁻¹ᵁ W) le_rfl) Q) := hpt.symm
        _ = hW.fromSpec P := congrArg hW.fromSpec hSpecMap
        _ = y := by simpa only [P] using hW.fromSpec_primeIdealOf yW
    exact ⟨zW.1, hgz⟩
  have hmaxToPrime (q : PrimeSpectrum B) (hq : q.asIdeal.IsMaximal) :
      (⟨q.asIdeal, hq⟩ : MaximalSpectrum B).toPrimeSpectrum = q := by
    apply PrimeSpectrum.ext
    rfl
  have hfiberLeft (x : {x : X // g.base x = y}) :
      hfiberFromMax (hfiberToMax x) = x := by
    apply Subtype.ext
    dsimp only [hfiberFromMax, hfiberToMax]
    unfold specPoint
    rw [hmaxToPrime, eLoc.apply_symm_apply]
    change hU.fromSpec (fiberPrime x) = x.1
    dsimp [fiberPrime]
    rw [hU.fromSpec_primeIdealOf]
  let xWof : MaximalSpectrum B → ↥(g ⁻¹ᵁ W) := fun v => hU.isoSpec.inv (specPoint v)
  have hQpoint (v : MaximalSpectrum B) : hU.primeIdealOf (xWof v) = specPoint v := by
    change hU.isoSpec.hom (hU.isoSpec.inv (specPoint v)) = specPoint v
    rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
    rfl
  have hfiberRight (v : MaximalSpectrum B) :
      hfiberToMax (hfiberFromMax v) = v := by
    apply MaximalSpectrum.ext
    have hQ : fiberPrime (hfiberFromMax v) = (eLoc v.toPrimeSpectrum).1 :=
      hQpoint v
    have hspec :
        (⟨fiberPrime (hfiberFromMax v),
          hQdisj (fiberPrime (hfiberFromMax v)) (by
            rw [hQ]
            exact hQcontract v)⟩ :
          {q : PrimeSpectrum B₀ // Disjoint (S₀ : Set B₀) q.asIdeal}) =
        eLoc v.toPrimeSpectrum :=
      Subtype.ext hQ
    have hloc := congrArg eLoc.symm hspec
    change (eLoc.symm
        ⟨fiberPrime (hfiberFromMax v),
          hQdisj (fiberPrime (hfiberFromMax v)) (by
            rw [hQ]
            exact hQcontract v)⟩).asIdeal = v.asIdeal
    rw [hloc, eLoc.symm_apply_apply]
    rfl
  let _ : ∀ v : MaximalSpectrum B, Algebra B₀ (X.presheaf.stalk (xWof v).1) := fun v =>
    TopCat.Presheaf.algebra_section_stalk X.presheaf (xWof v)
  let _ : ∀ v : MaximalSpectrum B,
      IsLocalization.AtPrime (X.presheaf.stalk (xWof v).1) (specPoint v).asIdeal := fun v => by
    simpa only [hQpoint v] using hU.isLocalization_stalk (xWof v)
  let _ : ∀ v : MaximalSpectrum B,
      IsLocalization.AtPrime (Localization.AtPrime v.asIdeal) (specPoint v).asIdeal := fun v =>
    IsLocalization.isLocalization_atPrime_localization_atPrime S₀ v.asIdeal
  let _ : ∀ v : MaximalSpectrum B,
      IsScalarTower B₀ (X.presheaf.stalk (xWof v).1) X.functionField := fun v =>
    AlgebraicGeometry.functionField_isScalarTower X (g ⁻¹ᵁ W) (xWof v)
  let eBof : ∀ v : MaximalSpectrum B,
      Localization.AtPrime v.asIdeal ≃ₐ[B₀] X.presheaf.stalk (xWof v).1 := fun v =>
    IsLocalization.algEquiv (specPoint v).asIdeal.primeCompl _ _
  have hlocalOrder (v : MaximalSpectrum B)
      (hcoh : Order.coheight (hfiberFromMax v).1 = 1) :
      ordInt (Localization.AtPrime v.asIdeal) f hf =
        Scheme.ord f (hfiberFromMax v).1 := by
    let xW : g ⁻¹ᵁ W := xWof v
    let Sx := X.presheaf.stalk xW.1
    let eB : Localization.AtPrime v.asIdeal ≃ₐ[B₀] Sx := eBof v
    let eL : X.functionField ≃+* X.functionField :=
      IsFractionRing.ringEquivOfRingEquiv eB.toRingEquiv
    have hcohW : Order.coheight xW.1 = 1 := hcoh
    let _ : Ring.KrullDimLE 1 Sx := AlgebraicGeometry.krullDimLE_of_coheight_le hcohW.le
    have hB₀loc (b : B₀) :
        algebraMap B₀ (Localization.AtPrime v.asIdeal) b =
          algebraMap B (Localization.AtPrime v.asIdeal) (algebraMap B₀ B b) := rfl
    have hBase (b : B₀) :
        algebraMap B₀ X.functionField b =
          algebraMap (Localization.AtPrime v.asIdeal) X.functionField
            (algebraMap B₀ (Localization.AtPrime v.asIdeal) b) := by
      calc
        _ = algebraMap B X.functionField (algebraMap B₀ B b) :=
          IsScalarTower.algebraMap_apply B₀ B X.functionField b
        _ = algebraMap (Localization.AtPrime v.asIdeal) X.functionField
            (algebraMap B (Localization.AtPrime v.asIdeal) (algebraMap B₀ B b)) :=
          IsScalarTower.algebraMap_apply B (Localization.AtPrime v.asIdeal) X.functionField _
        _ = _ := by rw [← hB₀loc b]
    have hEL (b : B₀) : eL (algebraMap B₀ X.functionField b) =
        algebraMap B₀ X.functionField b := by
      calc
        eL (algebraMap B₀ X.functionField b) =
            eL (algebraMap (Localization.AtPrime v.asIdeal) X.functionField
              (algebraMap B₀ (Localization.AtPrime v.asIdeal) b)) := by rw [hBase b]
        _ = algebraMap Sx X.functionField
            (eB (algebraMap B₀ (Localization.AtPrime v.asIdeal) b)) :=
          IsFractionRing.ringEquivOfRingEquiv_algebraMap eB.toRingEquiv _
        _ = algebraMap Sx X.functionField (algebraMap B₀ Sx b) := by
          rw [eB.commutes]
        _ = _ := (IsScalarTower.algebraMap_apply B₀ Sx X.functionField b).symm
    have hhom : eL.toRingHom = (RingEquiv.refl X.functionField).toRingHom :=
      IsFractionRing.ringHom_ext (A := B₀) hEL
    have heL : eL = RingEquiv.refl X.functionField := RingEquiv.ext (RingHom.congr_fun hhom)
    have hord := ordFrac_congr eB.toRingEquiv eL
      (fun b => IsFractionRing.ringEquivOfRingEquiv_algebraMap eB.toRingEquiv b) f
    have hOrdInt : ordInt (Localization.AtPrime v.asIdeal) f hf =
        ordInt Sx (eL f) (fun h => hf (eL.injective (by simpa using h))) := by
      simp only [ordInt, hord.symm]
    calc
      ordInt (Localization.AtPrime v.asIdeal) f hf = ordInt Sx f hf := by
        simpa only [heL, RingEquiv.refl_apply] using hOrdInt
      _ = Scheme.ord f xW.1 := (ord_eq_ordInt xW.1 hcohW f hf).symm
      _ = Scheme.ord f (hfiberFromMax v).1 := rfl
  have hcoheightFiber (v : MaximalSpectrum B) :
      Order.coheight (hfiberFromMax v).1 = 1 := hfibercoh _ (hfiberFromMax v).2
  have hglobalOrder : Scheme.ord (Algebra.norm Y.functionField f) y =
      ordInt A (Algebra.norm Y.functionField f) (Algebra.norm_ne_zero_iff.mpr hf) :=
    ord_eq_ordInt y hy _ _
  have hliesOver (v : MaximalSpectrum B) :
      v.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) := ⟨(hcomap v).symm⟩
  have hresDegree (v : MaximalSpectrum B) :
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ v.asIdeal) =
        g.residueDegree (hfiberFromMax v).1 := by
    let _ := hliesOver v
    let xW : g ⁻¹ᵁ W := xWof v
    let Sx := X.presheaf.stalk xW.1
    have hgy : g.base xW.1 = y := (hfiberFromMax v).2
    let Rv := Localization.AtPrime v.asIdeal
    let eB : Rv ≃ₐ[B₀] Sx := eBof v
    let _ : Algebra A Rv := Algebra.compHom Rv (algebraMap A B)
    let gMap : A →+* Sx :=
      (eqToHom (congrArg Y.presheaf.stalk hgy.symm) ≫ g.stalkMap xW.1).hom
    have hAmap : eB.toRingEquiv.toRingHom.comp (algebraMap A Rv) = gMap := by
      apply IsLocalization.ringHom_ext (P.asIdeal.primeCompl)
      ext a
      calc
        eB (algebraMap A Rv (algebraMap A₀ A a)) =
            eB (algebraMap B₀ Rv (φ a)) :=
          congrArg (fun b => eB (algebraMap B Rv b)) (hABeval a).symm
        _ = algebraMap B₀ Sx (φ a) := eB.commutes _
        _ = gMap (algebraMap A₀ A a) := by
          have hcast :
              (eqToHom (congrArg Y.presheaf.stalk hgy.symm)).hom
                  ((Y.presheaf.germ W y hyW).hom a) =
                (Y.presheaf.germ W (g.base xW.1) xW.property).hom a := by
            simpa using RingHom.congr_fun (stalk_eqToHom_comp_germ Y hgy.symm W hyW) a
          have hgerm := Scheme.Hom.germ_stalkMap_apply (f := g) W xW.1 xW.property a
          calc
            algebraMap B₀ Sx (φ a) =
                g.stalkMap xW.1
                  ((Y.presheaf.germ W (g.base xW.1) xW.property).hom a) := by
              change (X.presheaf.germ (g ⁻¹ᵁ W) xW.1 xW.property).hom ((g.app W).hom a) = _
              exact hgerm.symm
            _ = gMap (algebraMap A₀ A a) := by
              change g.stalkMap xW.1
                  ((Y.presheaf.germ W (g.base xW.1) xW.property).hom a) =
                g.stalkMap xW.1
                  ((eqToHom (congrArg Y.presheaf.stalk hgy.symm)).hom
                    ((Y.presheaf.germ W y hyW).hom a))
              exact congrArg (g.stalkMap xW.1) hcast.symm
    let eK : A ⧸ IsLocalRing.maximalIdeal A ≃+* Y.residueField (g.base xW.1) :=
      (eqToIso (congrArg Y.residueField hgy.symm)).commRingCatIsoToRingEquiv
    let eL : B ⧸ v.asIdeal ≃+* X.residueField xW.1 :=
      (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal Rv).toRingEquiv.trans
        (IsLocalRing.ResidueField.mapEquiv eB.toRingEquiv)
    let _ : Algebra (Y.residueField (g.base xW.1)) (X.residueField xW.1) :=
      (g.residueFieldMap xW.1).hom.toAlgebra
    have hcompat :
        (algebraMap (Y.residueField (g.base xW.1)) (X.residueField xW.1)).comp eK.toRingHom =
        eL.toRingHom.comp
          (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ v.asIdeal)) := by
      apply RingHom.ext
      intro z
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      have heK : eK (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) =
          (Y.residue (g.base xW.1)).hom
            ((eqToHom (congrArg Y.presheaf.stalk hgy.symm)).hom a) :=
        RingHom.congr_fun (residueField_eqToHom_comp_residue Y hgy.symm) a
      have heL (b : B) : eL (Ideal.Quotient.mk v.asIdeal b) =
          (X.residue xW.1).hom (eB (algebraMap B Rv b)) :=
        congrArg (IsLocalRing.ResidueField.mapEquiv eB.toRingEquiv)
          (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk v.asIdeal Rv b)
      change (g.residueFieldMap xW.1).hom
          (eK (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)) =
        eL (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ v.asIdeal)
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a))
      rw [heK, Ideal.Quotient.algebraMap_mk_of_liesOver, heL]
      have hres := congrArg (fun k => k.hom
          ((eqToHom (congrArg Y.presheaf.stalk hgy.symm)).hom a))
        (Scheme.residue_residueFieldMap g xW.1)
      change (g.residueFieldMap xW.1).hom
          ((Y.residue (g.base xW.1)).hom
            ((eqToHom (congrArg Y.presheaf.stalk hgy.symm)).hom a)) =
        (X.residue xW.1).hom (gMap a) at hres
      rw [hres]
      exact congrArg (X.residue xW.1).hom (RingHom.congr_fun hAmap a).symm
    simpa only [Scheme.Hom.residueDegree] using
      (Algebra.finrank_eq_of_equiv_equiv eK eL hcompat)
  rw [hglobalOrder]
  refine Eq.trans ?_ (ord_norm_eq_sum_inertiaDeg_mul_ord A B Y.functionField X.functionField
    hABinj f hf (Algebra.norm Y.functionField f) rfl
    (Algebra.norm_ne_zero_iff.mpr hf)).symm
  let efiber : MaximalSpectrum B ≃ {x : X // g.base x = y} :=
    ⟨hfiberFromMax, hfiberToMax, hfiberRight, hfiberLeft⟩
  change (∑ᶠ x ∈ {x : X | g.base x = y},
      Scheme.ord f x * (g.residueDegree x : ℤ)) = _
  rw [← finsum_set_coe_eq_finsum_mem]
  change (∑ᶠ x : {x : X // g.base x = y},
    Scheme.ord f x.1 * (g.residueDegree x.1 : ℤ)) = _
  calc
    _ = ∑ᶠ v : MaximalSpectrum B, Scheme.ord f (hfiberFromMax v).1 *
        (g.residueDegree (hfiberFromMax v).1 : ℤ) :=
      (finsum_comp_equiv efiber).symm
    _ = _ := by
      rw [finsum_eq_sum_of_fintype]
      refine Finset.sum_congr rfl fun v _ => ?_
      let _ := hliesOver v
      rw [hlocalOrder v (hcoheightFiber v), mul_comm, ← hresDegree v]
      simp

/-! ### The coefficient at a point of codimension one -/

/-- **Stacks 02RT, the coefficient at a prime divisor.** Let `p : X ⟶ Y` be a proper dominant
morphism of integral schemes which is finite over an open neighbourhood `V` of a point `y` of
`Y` of codimension one, and whose fibre over `y` consists of points of codimension one. Then the
coefficient at `y` of the proper pushforward of `div(f)` is the order of vanishing at `y` of the
norm of `f` in the extension `R(Y) ⊆ R(X)` of function fields.

The restriction `p ∣_ V` is finite and dominant and its fibre over `y` is the fibre of `p`, so
`Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite` applies to it. Passing from `V` and `p⁻¹V`
back to `Y` and `X` — of the order of vanishing, of the residue degree, and of the norm — uses the
transport lemmas of
`StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport`. -/
theorem finsum_ord_mul_residueDegree_of_coheight_eq_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Y) [IsProper p]
    [IsDominant p] [Algebra Y.functionField X.functionField]
    (halg : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap p)
    (f : X.functionField) (hf : f ≠ 0) (y : Y) (hy : Order.coheight y = 1)
    (hfibercoh : ∀ x : X, p.base x = y → Order.coheight x = 1)
    (V : Y.Opens) (hyV : y ∈ V) (hfinite : IsFinite (p ∣_ V)) :
    (∑ᶠ x ∈ p.base ⁻¹' {y}, X.ord f x * (p.residueDegree x : ℤ)) =
      Y.ord (Algebra.norm Y.functionField f) y := by
  let g := p ∣_ V
  let _ : IsFinite g := hfinite
  let yV : V.toScheme := ⟨y, hyV⟩
  let iY : V.toScheme ⟶ Y := V.ι
  let iX : (p ⁻¹ᵁ V).toScheme ⟶ X := (p ⁻¹ᵁ V).ι
  have hpgen : p.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)
  have hgenX : genericPoint X ∈ p ⁻¹ᵁ V := by
    change p.base (genericPoint X) ∈ V
    rw [hpgen]
    exact (genericPoint_spec Y).mem_open_set_iff V.isOpen |>.mpr
      ⟨y, ⟨Set.mem_univ _, hyV⟩⟩
  let _ : Nonempty V := ⟨yV⟩
  let _ : Nonempty (p ⁻¹ᵁ V) := ⟨⟨genericPoint X, hgenX⟩⟩
  have hdom : ∀ {U Z : Scheme.{u}} [Nonempty U] [PreirreducibleSpace Z] (i : U ⟶ Z)
      [IsOpenImmersion i], IsDominant i := fun i => by
    rw [isDominant_iff]
    exact i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i.base
  let _ : IsDominant iX := hdom iX
  let _ : IsDominant iY := hdom iY
  let _ : IsDominant g := by
    have : IsDominant (g ≫ iY) := by
      change IsDominant ((p ∣_ V) ≫ V.ι)
      rw [morphismRestrict_ι]
      infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion g iY
  let _ : IsIntegral (p ⁻¹ᵁ V).toScheme := inferInstance
  let _ : IsIntegral V.toScheme := inferInstance
  let _ : Algebra V.toScheme.functionField (p ⁻¹ᵁ V).toScheme.functionField :=
    (dominantFunctionFieldMap g).toAlgebra
  have halgG : algebraMap V.toScheme.functionField (p ⁻¹ᵁ V).toScheme.functionField =
      dominantFunctionFieldMap g := RingHom.algebraMap_toAlgebra _
  let z : (p ⁻¹ᵁ V).toScheme.functionField := dominantFunctionFieldMap iX f
  have hz : z ≠ 0 := fun hz0 =>
    hf (RingHom.injective (dominantFunctionFieldMap iX) (by simpa only [map_zero] using hz0))
  have hyVcoh : Order.coheight yV = 1 := by
    rwa [← AlgebraicGeometry.coheight_eq_of_isOpenImmersion iY]
  have hbase (x : (p ⁻¹ᵁ V).toScheme) : (g.base x).1 = p.base (iX.base x) :=
    AlgebraicGeometry.morphismRestrict_base_coe p V x
  have hfibiff (x : (p ⁻¹ᵁ V).toScheme) : g.base x = yV ↔ p.base (iX.base x) = y := by
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hbase x, hx]
    · exact Subtype.ext (by rw [hbase x, hx])
  have hfibercohG : ∀ x : (p ⁻¹ᵁ V).toScheme, g.base x = yV → Order.coheight x = 1 := by
    intro x hx
    rw [← AlgebraicGeometry.coheight_eq_of_isOpenImmersion iX]
    exact hfibercoh (iX.base x) ((hfibiff x).mp hx)
  have hcore := finsum_ord_mul_residueDegree_of_isFinite g halgG z hz yV hyVcoh hfibercohG
  let Ebase : Y.functionField ≃+* V.toScheme.functionField := functionFieldEquiv_openImmersion iY
  let Esrc : X.functionField ≃+* (p ⁻¹ᵁ V).toScheme.functionField :=
    functionFieldEquiv_openImmersion iX
  have hfac : iX ≫ p = g ≫ iY := (morphismRestrict_ι p V).symm
  have hnormSquare :
      (algebraMap V.toScheme.functionField (p ⁻¹ᵁ V).toScheme.functionField).comp
          Ebase.toRingHom =
        Esrc.toRingHom.comp (algebraMap Y.functionField X.functionField) := by
    ext a
    change dominantFunctionFieldMap g (dominantFunctionFieldMap iY a) =
      dominantFunctionFieldMap iX (algebraMap Y.functionField X.functionField a)
    rw [halg]
    symm
    calc dominantFunctionFieldMap iX (dominantFunctionFieldMap p a)
        = dominantFunctionFieldMap (iX ≫ p) a :=
          congrArg (fun q : Y.functionField →+* (p ⁻¹ᵁ V).toScheme.functionField => q a)
            (dominantFunctionFieldMap_comp iX p).symm
      _ = dominantFunctionFieldMap (g ≫ iY) a := by simp only [hfac]
      _ = dominantFunctionFieldMap g (dominantFunctionFieldMap iY a) :=
          congrArg (fun q : Y.functionField →+* (p ⁻¹ᵁ V).toScheme.functionField => q a)
            (dominantFunctionFieldMap_comp g iY)
  have hnormBridge : Ebase (Algebra.norm Y.functionField f) =
      Algebra.norm V.toScheme.functionField z := by
    have h : Ebase (Algebra.norm Y.functionField f) =
        Algebra.norm V.toScheme.functionField (Esrc f) := by
      simpa only [RingEquiv.apply_symm_apply] using
        congrArg Ebase (Algebra.norm_eq_of_equiv_equiv Ebase Esrc hnormSquare f)
    rwa [show Esrc f = z from rfl] at h
  have hnorm : V.toScheme.ord (Algebra.norm V.toScheme.functionField z) yV =
      Y.ord (Algebra.norm Y.functionField f) y := by
    rw [← hnormBridge]
    exact ord_dominantFunctionFieldMap_of_isOpenImmersion iY (Algebra.norm Y.functionField f) yV
  have hsum : (∑ᶠ x ∈ p.base ⁻¹' {y}, X.ord f x * (p.residueDegree x : ℤ)) =
      ∑ᶠ x ∈ g.base ⁻¹' {yV},
        (p ⁻¹ᵁ V).toScheme.ord z x * (g.residueDegree x : ℤ) := by
    let e : {x : (p ⁻¹ᵁ V).toScheme // g.base x = yV} ≃ {x : X // p.base x = y} :=
      { toFun := fun x => ⟨iX.base x.1, (hfibiff x.1).mp x.2⟩
        invFun := fun x => ⟨⟨x.1, by
            change p.base x.1 ∈ V
            rw [x.2]
            exact hyV⟩,
          (hfibiff _).mpr x.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun x => Subtype.ext rfl }
    change (∑ᶠ x ∈ {x : X | p.base x = y}, X.ord f x * (p.residueDegree x : ℤ)) =
      ∑ᶠ x ∈ {x : (p ⁻¹ᵁ V).toScheme | g.base x = yV},
        (p ⁻¹ᵁ V).toScheme.ord z x * (g.residueDegree x : ℤ)
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_set_coe_eq_finsum_mem]
    change (∑ᶠ x : {x : X // p.base x = y}, X.ord f x.1 * (p.residueDegree x.1 : ℤ)) =
      ∑ᶠ x : {x : (p ⁻¹ᵁ V).toScheme // g.base x = yV},
        (p ⁻¹ᵁ V).toScheme.ord z x.1 * (g.residueDegree x.1 : ℤ)
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun x => ?_
    rw [show (p ⁻¹ᵁ V).toScheme.ord z x.1 = X.ord f (iX.base x.1) from
        ord_dominantFunctionFieldMap_of_isOpenImmersion iX f x.1,
      show g.residueDegree x.1 = p.residueDegree (iX.base x.1) from
        residueDegree_morphismRestrict p V x.1]
    rfl
  rw [hsum, hcore, hnorm]

/-! ### The coefficient away from codimension one -/

/-- For `x` of codimension one over `y`, the relative dimensions of `x` and `y` agree exactly when
`y` has codimension one. -/
private theorem relativeDimension_eq_iff_coheight_eq_one_of_coheight_eq_one
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) {x : X} {y : Y} (hx : Order.coheight x = 1) (hxy : p.base x = y) :
    relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (p.base x) ↔ Order.coheight y = 1 := by
  rw [hxy, relativeDimension_eq_sub_one_of_coheight_eq_one C sX hnX hx, eq_comm,
    relativeDimension_eq_sub_one_iff_coheight_eq_one C sY hnY y]

/-- **Stacks 02RT, the coefficient away from the prime divisors.** At a point of `Y` whose
codimension is not one, the coefficient of the proper pushforward of `div(f)` vanishes, as does
the order of vanishing there of every rational function on `Y`. -/
theorem finsum_ord_mul_weight_of_coheight_ne_one (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) [IsProper p] (f : X.functionField) (gg : Y.functionField)
    (y : Y) (hy : ¬ Order.coheight y = 1) :
    (∑ᶠ x ∈ p.base ⁻¹' {y}, X.ord f x *
        (if relativeDimension C.dimensionFunction sX x =
            relativeDimension C.dimensionFunction sY (p.base x)
          then (p.residueDegree x : ℤ) else 0)) = Y.ord gg y := by
  classical
  have hterm (x : X) (hxy : x ∈ p.base ⁻¹' {y}) :
      X.ord f x * (if relativeDimension C.dimensionFunction sX x =
          relativeDimension C.dimensionFunction sY (p.base x)
        then (p.residueDegree x : ℤ) else 0) = 0 := by
    by_cases hx : Order.coheight x = 1
    · simp [mt (relativeDimension_eq_iff_coheight_eq_one_of_coheight_eq_one C sX sY hnX hnY p hx
        hxy).mp hy]
    · simp [Scheme.ord_eq_zero_of_coheight_neq_one hx]
  rw [finsum_mem_congr rfl hterm]
  simp [Scheme.ord_eq_zero_of_coheight_neq_one hy]

/-! ### Stacks 02RT -/

/-- **Stacks 02RT.** For a dominant proper morphism `p : X ⟶ Y` of integral schemes locally of
finite type over the base with `dim_δ(X) = dim_δ(Y) = n`, the proper pushforward of the principal
divisor of a nonzero rational function `f` on `X` is the principal divisor of the norm of `f` in
the extension `R(Y) ⊆ R(X)` of function fields. -/
@[stacks 02RT]
theorem properPushforward_principalDivisorCycle (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX)
    (f : X.functionField) (hf : f ≠ 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
    properPushforward C sX sY p hp (n - 1) (principalDivisorCycle C sX hnX f) =
      principalDivisorCycle C sY hnY (Algebra.norm Y.functionField f) := by
  classical
  let _ : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
  have halg : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap p :=
    RingHom.algebraMap_toAlgebra _
  change properPushforward C sX sY p hp (n - 1) (principalDivisorCycle C sX hnX f) =
    principalDivisorCycle C sY hnY (Algebra.norm Y.functionField f)
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  apply Subtype.ext
  ext y
  rw [properPushforward_apply]
  simp_rw [principalDivisorCycle_apply C sX hnX f]
  rw [principalDivisorCycle_apply C sY hnY _ y]
  by_cases hy : Order.coheight y = 1
  · have hfibercoh : ∀ x : X, p.base x = y → Order.coheight x = 1 := fun x hx ↦
      (relativeDimension_eq_sub_one_iff_coheight_eq_one C sX hnX x).mp
        (relativeDimension_eq_sub_one_of_mem_fibre C sX sY hnX hnY p hp hy hx)
    have hweight (x : X) (hxy : x ∈ p.base ⁻¹' {y}) :
        X.ord f x *
            (if relativeDimension C.dimensionFunction sX x =
                relativeDimension C.dimensionFunction sY (p.base x)
              then (p.residueDegree x : ℤ) else 0) =
          X.ord f x * (p.residueDegree x : ℤ) := by
      by_cases hx : Order.coheight x = 1
      · simp [(relativeDimension_eq_iff_coheight_eq_one_of_coheight_eq_one C sX sY hnX hnY p hx
          hxy).mpr hy]
      · simp [Scheme.ord_eq_zero_of_coheight_neq_one hx]
    rw [finsum_mem_congr rfl hweight]
    obtain ⟨V, hyV, hfinite⟩ :=
      exists_isFinite_morphismRestrict_of_coheight_eq_one C sX sY hnX hnY p hp y hy
    exact finsum_ord_mul_residueDegree_of_coheight_eq_one p halg f hf y hy hfibercoh V hyV hfinite
  · exact finsum_ord_mul_weight_of_coheight_ne_one C sX sY hnX hnY p f _ y hy

end Stacks.Chow

end
