module

public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.ClassGroup
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.StalkHeightOnePrime
public import StacksFrontier.RingTheory.UniqueFactorizationDomain.HeightOneOrders
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A normal scheme with surjective first Chern class has factorial local rings

Let `X` be a normal locally Noetherian integral scheme on which the first Chern class
`Pic(X) → Cl(X)` is surjective. Then every local ring of `X` is a unique factorization domain.
This is the implication from condition (2) to condition (1) of [Stacks, Tag 0BE9].

## The argument

By the criterion of [Stacks, Tag 0AFT] it is enough to see that every height-one prime `𝔭` of
`𝒪_{X, x}` is principal. Surjectivity makes every Weil divisor locally principal: the class of a
Weil divisor `D` is the Weil divisor class of an invertible sheaf `L`, so `D` differs from the
divisor of a regular meromorphic section of `L` by a principal divisor, and near a point the
orders of that meromorphic section are the orders of a single rational function — the coordinate
of its generic value against a local trivialization of `L`. Applying this to the prime divisor
`Z` that `𝔭` cuts out produces a rational function `z` with order `1` along `Z` and order `0`
along every other prime divisor through `x`; the height-one primes of `𝒪_{X, x}` are exactly
those prime divisors, so `z` generates `𝔭`.

## Main results

* `AlgebraicGeometry.primeWeilDivisor`: the Weil divisor of a single prime divisor.
* `AlgebraicGeometry.exists_forall_ord_eq_of_surjective_picardToWeilDivisorClassGroup`: a Weil
  divisor is locally the divisor of a rational function.
* `AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_surjective_picardToWeilDivisorClassGroup`:
  **Stacks 0BE9**, the implication from condition (2) to condition (1).

## References

* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0AFT](https://stacks.math.columbia.edu/tag/0AFT)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

open scoped Classical in
/-- The Weil divisor of a single prime divisor, with coefficient `1` at it and `0` elsewhere. -/
def primeWeilDivisor (Z : PrimeDivisor X) : WeilDivisor X :=
  ⟨fun W => if W = Z then 1 else 0, by
    rw [mem_weilDivisor_iff]
    intro y
    refine ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton Z).subset fun W hW => ?_⟩
    by_contra hne
    have hne' : W ≠ Z := by simpa using hne
    simp [hne'] at hW⟩

open scoped Classical in
/-- The coefficient of `primeWeilDivisor Z` at `W` is `1` if `W = Z` and `0` otherwise. -/
@[simp]
theorem primeWeilDivisor_apply (Z W : PrimeDivisor X) :
    (primeWeilDivisor Z).val W = if W = Z then 1 else 0 := rfl

/-- **A Weil divisor is locally principal when the first Chern class is surjective.** Near any
point there is a nonzero rational function whose order along every prime divisor meeting that
neighbourhood is the coefficient of the divisor. -/
theorem exists_forall_ord_eq_of_surjective_picardToWeilDivisorClassGroup
    (hsurj : Function.Surjective (picardToWeilDivisorClassGroup X)) (D : WeilDivisor X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ z : X.functionField, z ≠ 0 ∧
      ∀ W : PrimeDivisor X, W.genericPoint ∈ U → X.ord z W.genericPoint = D.val W := by
  classical
  obtain ⟨c, hc⟩ := hsurj (D : weilDivisorClassGroup X)
  obtain ⟨L, hL, hLc⟩ :=
    Stacks.SheafOfModules.exists_picardClass_eq X.sheaf.obj X.ringCatSheaf.property c
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      L := hL.toAlgebraicGeometry _ _ _
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral X L
  have hclass : ((weilDivisorOfMeromorphicSection X L s hs : WeilDivisor X) :
      weilDivisorClassGroup X) = (D : weilDivisorClassGroup X) := by
    rw [← weilDivisorClassOfInvertibleSheaf_eq X L s hs, ← hc, ← hLc]
    exact (weilDivisorClassOfPicardClass_picardClass X L).symm
  have hzero : ((D - weilDivisorOfMeromorphicSection X L s hs : WeilDivisor X) :
      weilDivisorClassGroup X) = 0 := by
    have hsub : ((D - weilDivisorOfMeromorphicSection X L s hs : WeilDivisor X) :
        weilDivisorClassGroup X) = (D : weilDivisorClassGroup X) -
          ((weilDivisorOfMeromorphicSection X L s hs : WeilDivisor X) :
            weilDivisorClassGroup X) := rfl
    rw [hsub, hclass, sub_self]
  obtain ⟨f, hf⟩ := (mk_eq_zero_iff X _).mp hzero
  obtain ⟨U, hxU, a, ha⟩ := exists_forall_orderOfVanishingMeromorphic_eq_ord L s hs x
  set b : X.functionField := (Stacks.Chow.rationalFunctionsEquivFunctionField X).val f with hbdef
  have hb : b ≠ 0 :=
    (f.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toRingHom).ne_zero
  have hsum : ∀ W : PrimeDivisor X, W.genericPoint ∈ U →
      X.ord a W.genericPoint + X.ord b W.genericPoint = D.val W := by
    intro W hW
    have hcoeff : X.ord b W.genericPoint =
        D.val W - orderOfVanishingMeromorphic X L s hs W :=
      congrFun (congrArg Subtype.val hf) W
    rw [ha W hW] at hcoeff
    omega
  by_cases ha0 : a = 0
  · exact ⟨U, hxU, b, hb, fun W hW => by simpa [ha0] using hsum W hW⟩
  · refine ⟨U, hxU, a * b, mul_ne_zero ha0 hb, fun W hW => ?_⟩
    rw [Scheme.ord_mul ha0 hb]
    exact hsum W hW

/-- The order of a nonzero rational function in the local ring at a prime divisor `Z`, computed in
any ring isomorphic to that local ring over the function field, is `exp` of its order along `Z`. -/
private theorem ordFrac_eq_exp_of_ord_eq {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Algebra A X.functionField] [IsFractionRing A X.functionField]
    (Z : PrimeDivisor X) (e : A ≃+* X.presheaf.stalk Z.genericPoint)
    (he : ∀ a, algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField (e a) =
      algebraMap A X.functionField a)
    {z : X.functionField} (hz : z ≠ 0) {n : ℤ} (hn : X.ord z Z.genericPoint = n) :
    Ring.ordFrac A z = WithZero.exp n := by
  have hcoh : coheight Z.genericPoint = 1 := PrimeDivisor.coheight_genericPoint Z
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    krullDimLE_of_coheight_le hcoh.le
  have ht := Stacks.RingTheory.HeightOneOrders.ordFrac_ringEquiv e he z
  change X.ordHom Z.genericPoint hcoh z = _ at ht
  rw [← ht, (X.ord_eq_iff hcoh hz).mp hn]
  simp [WithZero.exp]

/-- **Stacks 0BE9, the implication from condition (2) to condition (1).** On a normal locally
Noetherian integral scheme whose first Chern class `Pic(X) → Cl(X)` is surjective, every local
ring is a unique factorization domain. -/
@[ega "IV 21.6.10" "(ii)"]
theorem uniqueFactorizationMonoid_stalk_of_surjective_picardToWeilDivisorClassGroup [IsNormal X]
    (hsurj : Function.Surjective (picardToWeilDivisorClassGroup X)) (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  classical
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  refine UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one ?_
  intro p hp hheight
  have := hp
  obtain ⟨Z, hZx, -, hZp, eZ, heZ⟩ :=
    exists_primeDivisor_stalk_eq_of_height_eq_one X x p hheight ⊤ trivial
  obtain ⟨U, hxU, z, hz, hord⟩ :=
    exists_forall_ord_eq_of_surjective_picardToWeilDivisorClassGroup hsurj
      (primeWeilDivisor Z) x
  refine Stacks.RingTheory.HeightOneOrders.isPrincipal_of_ordFrac_eq_indicator p hheight z hz
    fun q hq => ?_
  have : Ring.KrullDimLE 1 (Localization.subalgebra.ofField X.functionField _
      q.asIdeal.primeCompl_le_nonZeroDivisors) :=
    Stacks.RingTheory.HeightOneOrders.krullDimLE_one_localizationAtPrime q.asIdeal hq _
  have : IsNoetherianRing (Localization.subalgebra.ofField X.functionField _
      q.asIdeal.primeCompl_le_nonZeroDivisors) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  by_cases heq : q.asIdeal = p
  · cases heq
    have ho : X.ord z Z.genericPoint = 1 := by simpa using hord Z (hZx.mem_open U.isOpen hxU)
    simp [ordFrac_eq_exp_of_ord_eq Z eZ heZ hz ho]
  · obtain ⟨W, hWx, hWU, hWq, eW, heW⟩ :=
      exists_primeDivisor_stalk_eq_of_height_eq_one X x q.asIdeal hq U hxU
    have hne : W ≠ Z := by
      rintro rfl
      exact heq (hWq.symm.trans hZp)
    have ho : X.ord z W.genericPoint = 0 := by simpa [hne] using hord W hWU
    simp [heq, ordFrac_eq_exp_of_ord_eq W eW heW hz ho]

end AlgebraicGeometry

end
