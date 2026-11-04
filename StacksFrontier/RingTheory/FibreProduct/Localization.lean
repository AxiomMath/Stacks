module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization of a cartesian square of rings

A cartesian square of commutative rings stays cartesian after localizing the three given rings
at an element and at its images.  This is the ring-theoretic input for gluing modules along a
fibre product of rings: it identifies the localization of `B ×_R R'` at an element coming from
`B` with the fibre product of the localizations.

## Main results

* `RingFibreProduct.isPullback_localization_away` is Stacks Tag 01Z8: localizing a cartesian
  square of rings away from an element again gives a cartesian square.

## Implementation notes

The square is expressed in `CommRingCat`, with the localization maps produced by
`Localization.awayLift` and `Localization.awayMap`.  Cartesianness is checked on underlying
types and transported back along the forgetful functor, and surjectivity of the comparison map
is obtained from the exactness properties of localized modules.

## References

* [Stacks Project, Tag 01Z8](https://stacks.math.columbia.edu/tag/01Z8)
-/

section

section
public section

open CategoryTheory Limits

universe u

namespace RingFibreProduct
private theorem commRing_isPullback_of_types
    {P X Y Z : CommRingCat} {fst : P ⟶ X} {snd : P ⟶ Y}
    {right : X ⟶ Z} {bottom : Y ⟶ Z}
    (hType : IsPullback ((forget CommRingCat).map fst) ((forget CommRingCat).map snd)
      ((forget CommRingCat).map right) ((forget CommRingCat).map bottom)) :
    IsPullback fst snd right bottom :=
  have : ReflectsLimit (cospan right bottom) (forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  hType.of_map (forget CommRingCat) ((forget CommRingCat).map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hType.w]))

private def scalarLocalizationMap
    {S A T : Type*} [CommRing S] [CommRing A] [CommRing T]
    [Algebra S A] [Algebra A T] [Module S T]
    (hCompat : ∀ r : S, ∀ x : T, r • x = (algebraMap S A r) • x) :
    A →ₗ[S] T where
  toFun := algebraMap A T
  map_add' := map_add _
  map_smul' r a := by
    rw [Algebra.smul_def, map_mul, ← Algebra.smul_def, ← hCompat]
    rfl

private def ringHomLinearMap
    {S A B : Type*} [Semiring S] [Semiring A] [Semiring B]
    [Module S A] [Module S B]
    (f : A →+* B) (h : ∀ r : S, ∀ x : A, f (r • x) = r • f x) : A →ₗ[S] B where
  toFun := f
  map_add' := map_add _
  map_smul' := h

private theorem away_localization_isLocalizedModule
    {S A T : Type*} [CommRing S] [CommRing A] [CommRing T]
    [Algebra S A] [Algebra A T] [Module S T]
    (hCompat : ∀ r : S, ∀ x : T, r • x = (algebraMap S A r) • x)
    (h : S) (g : A) (hφ : algebraMap S A h = g) [IsLocalization (.powers g) T] :
    IsLocalizedModule.Away (R := S) (M := A) (M' := T) h
      (scalarLocalizationMap (S := S) (A := A) (T := T) hCompat) := by
  have hu : IsUnit (algebraMap A T g) :=
    IsLocalization.map_units T (⟨g, 1, by simp⟩ : (.powers g : Submonoid A))
  have hsmul (n : ℕ) (x : T) : h ^ n • x = algebraMap A T (g ^ n) * x := by
    rw [hCompat, map_pow, hφ, Algebra.smul_def]
  have hsmul₁ (x : T) : h • x = algebraMap A T g * x := by simpa using hsmul 1 x
  refine IsLocalizedModule.Away.mk ?_ ?_ ?_
  · refine (Module.End.isUnit_iff _).2 ⟨fun x y hxy => hu.mul_left_cancel ?_, fun x =>
      ⟨↑hu.unit⁻¹ * x, ?_⟩⟩
    · simpa [Module.algebraMap_end_apply, hsmul₁] using hxy
    · simp [Module.algebraMap_end_apply, hsmul₁, ← mul_assoc]
  · intro x
    obtain ⟨⟨a, d⟩, rfl⟩ := IsLocalization.mk'_surjective (.powers g) x
    obtain ⟨n, hn⟩ := d.2
    have hnd : g ^ n = d := by simpa using hn
    refine ⟨n, a, ?_⟩
    rw [hsmul, hnd]
    exact IsLocalization.mk'_spec' T a d
  · intro a b hab
    obtain ⟨⟨_, n, rfl⟩, hd⟩ := (IsLocalization.eq_iff_exists (.powers g) T).mp hab
    exact ⟨n, by simpa [Algebra.smul_def, hφ] using hd⟩

private theorem away_prodMap_isLocalizedModule
    {S A₁ A₂ T₁ T₂ : Type*} [CommRing S]
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup T₁] [AddCommGroup T₂]
    [Module S A₁] [Module S A₂] [Module S T₁] [Module S T₂]
    (h : S) (f₁ : A₁ →ₗ[S] T₁) (f₂ : A₂ →ₗ[S] T₂)
    [IsLocalizedModule.Away h f₁] [IsLocalizedModule.Away h f₂] :
    IsLocalizedModule.Away h (f₁.prodMap f₂) := by
  have hu₁ := (Module.End.isUnit_iff _).mp (IsLocalizedModule.Away.isUnit_algebraMap f₁ h)
  have hu₂ := (Module.End.isUnit_iff _).mp (IsLocalizedModule.Away.isUnit_algebraMap f₂ h)
  refine IsLocalizedModule.Away.mk ?_ ?_ ?_
  · refine (Module.End.isUnit_iff _).2 ⟨fun x y heq => ?_, fun x => ?_⟩
    · ext
      · exact hu₁.1 (by simpa [Module.algebraMap_end_apply] using congrArg Prod.fst heq)
      · exact hu₂.1 (by simpa [Module.algebraMap_end_apply] using congrArg Prod.snd heq)
    · obtain ⟨a, ha⟩ := hu₁.2 x.1
      obtain ⟨b, hb⟩ := hu₂.2 x.2
      exact ⟨(a, b), by simpa [Module.algebraMap_end_apply] using Prod.ext ha hb⟩
  · intro x
    obtain ⟨n, a, ha⟩ := IsLocalizedModule.Away.surj f₁ h x.1
    obtain ⟨m, b, hb⟩ := IsLocalizedModule.Away.surj f₂ h x.2
    refine ⟨n + m, (h ^ m • a, h ^ n • b), Prod.ext ?_ ?_⟩
    · simp [pow_add, mul_comm (h ^ n), mul_smul, ha]
    · simp [pow_add, mul_smul, hb]
  · intro x y heq
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq h
      (by simpa using congrArg Prod.fst heq : f₁ x.1 = f₁ y.1)
    obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq h
      (by simpa using congrArg Prod.snd heq : f₂ x.2 = f₂ y.2)
    refine ⟨n + m, Prod.ext ?_ ?_⟩
    · simp [pow_add, mul_comm (h ^ n), mul_smul, hn]
    · simp [pow_add, mul_smul, hm]

/-- Let `B' = B ×_R R'` be a fibre product of commutative rings along `s : B → R` and
`t : R' → R`, and let `h ∈ B'` map to `g ∈ B` and `f ∈ R'`, with `s g = t f`. Then the square
of localizations `B'_h → B_g`, `B'_h → R'_f`, `B_g → R_{s g}`, `R'_f → R_{s g}` is again a
pullback, that is, `B'_h ≅ B_g ×_{R_{s g}} R'_f`. -/
@[stacks 01Z8]
theorem isPullback_localization_away
    {R R' B B' : Type u}
    [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (s : B →+* R) (t : R' →+* R)
    (πB : B' →+* B) (πR' : B' →+* R')
    (hPB : IsPullback (CommRingCat.ofHom πB) (CommRingCat.ofHom πR')
      (CommRingCat.ofHom s) (CommRingCat.ofHom t))
    (h : B') (g : B) (f : R')
    (hB : πB h = g) (hR' : πR' h = f) (hcompat : s g = t f) :
    IsPullback
      (CommRingCat.ofHom
        (Localization.awayLift ((algebraMap B (Localization.Away g)).comp πB) h (by
          rw [RingHom.comp_apply, hB]
          exact IsLocalization.Away.algebraMap_isUnit g)))
      (CommRingCat.ofHom
        (Localization.awayLift ((algebraMap R' (Localization.Away f)).comp πR') h (by
          rw [RingHom.comp_apply, hR']
          exact IsLocalization.Away.algebraMap_isUnit f)))
      (CommRingCat.ofHom (Localization.awayMap s g))
      (CommRingCat.ofHom
        (Localization.awayLift ((algebraMap R (Localization.Away (s g))).comp t) f (by
          rw [RingHom.comp_apply, ← hcompat]
          exact IsLocalization.Away.algebraMap_isUnit (s g)))) := by
  let : Algebra B' B := πB.toAlgebra
  let : Algebra B' R' := πR'.toAlgebra
  let : Algebra B' R := (s.comp πB).toAlgebra
  have hbase : s.comp πB = t.comp πR' := by simpa using congrArg CommRingCat.Hom.hom hPB.w
  let : Module B' (Localization.Away g) :=
    RingHom.toModule ((algebraMap B (Localization.Away g)).comp πB)
  let : Module B' (Localization.Away f) :=
    RingHom.toModule ((algebraMap R' (Localization.Away f)).comp πR')
  let : Module B' (Localization.Away (s g)) :=
    RingHom.toModule ((algebraMap R (Localization.Away (s g))).comp (s.comp πB))
  let : DistribMulAction B' (Localization.Away (s g)) :=
    (RingHom.toModule
      ((algebraMap R (Localization.Away (s g))).comp (s.comp πB))).toDistribMulAction
  let : Module B' (Localization.Away h) :=
    RingHom.toModule (algebraMap B' (Localization.Away h))
  let : SMul B' (Localization.Away h) :=
    (inferInstance : Module B' (Localization.Away h)).toDistribSMul.toSMul
  let : SMul B' (Localization.Away g) :=
    (inferInstance : Module B' (Localization.Away g)).toDistribSMul.toSMul
  let : SMul B' (Localization.Away f) :=
    (inferInstance : Module B' (Localization.Away f)).toDistribSMul.toSMul
  let : SMul B' (Localization.Away (s g)) :=
    (inferInstance : Module B' (Localization.Away (s g))).toDistribSMul.toSMul
  let f₀ : B' →ₗ[B'] Localization.Away h :=
    scalarLocalizationMap (S := B') (A := B') (T := Localization.Away h)
      (fun r x => by rw [RingHom.toModule_smul, Algebra.smul_def]; rfl)
  let f₁ : B →ₗ[B'] Localization.Away g :=
    scalarLocalizationMap (S := B') (A := B) (T := Localization.Away g)
      (fun r x => by rw [RingHom.toModule_smul, Algebra.smul_def]; rfl)
  let f₂ : R' →ₗ[B'] Localization.Away f :=
    scalarLocalizationMap (S := B') (A := R') (T := Localization.Away f)
      (fun r x => by rw [RingHom.toModule_smul, Algebra.smul_def]; rfl)
  let f₃ : R →ₗ[B'] Localization.Away (s g) :=
    scalarLocalizationMap (S := B') (A := R) (T := Localization.Away (s g))
      (fun r x => by rw [RingHom.toModule_smul, Algebra.smul_def]; rfl)
  have hLocB : IsLocalizedModule.Away h f₁ := by
    apply away_localization_isLocalizedModule (fun r x => by
      rw [RingHom.toModule_smul, Algebra.smul_def]
      rfl) h g
    simpa only [RingHom.algebraMap_toAlgebra] using hB
  have hLocR' : IsLocalizedModule.Away h f₂ := by
    apply away_localization_isLocalizedModule (fun r x => by
      rw [RingHom.toModule_smul, Algebra.smul_def]
      rfl) h f
    simpa only [RingHom.algebraMap_toAlgebra] using hR'
  have hLocR : IsLocalizedModule.Away h f₃ := by
    apply away_localization_isLocalizedModule (fun r x => by
      rw [RingHom.toModule_smul, Algebra.smul_def]
      rfl) h (s g)
    show (s.comp πB) h = s g
    simp [RingHom.comp_apply, hB]
  have hLocB' : IsLocalizedModule.Away h f₀ := by
    apply away_localization_isLocalizedModule (fun r x => by
      rw [RingHom.toModule_smul, Algebra.smul_def]
      rfl) h h
    rfl
  have hLocProd : IsLocalizedModule.Away h
      (f₁.prodMap f₂) := away_prodMap_isLocalizedModule h f₁ f₂
  let u : B' →ₗ[B'] B × R' := Algebra.linearMap B' (B × R')
  let v : B × R' →ₗ[B'] R :=
    { toFun := fun x => s x.1 - t x.2
      map_add' x y := by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      map_smul' := by
        intro a x
        have ha : s (πB a) = t (πR' a) := congrArg (fun k : B' →+* R => k a) hbase
        simp [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ha]
        ring }
  have hu : Function.Injective u := by
    intro x y hxy
    apply Types.ext_of_isPullback (hPB.map (forget CommRingCat))
    · simpa [u, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra] using
        congrArg (fun z : B × R' => z.1) hxy
    · simpa [u, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra] using
        congrArg (fun z : B × R' => z.2) hxy
  have hExact : Function.Exact u v := by
    apply LinearMap.exact_of_comp_of_mem_range
    · ext
      simp [u, v]
    · intro x hx
      obtain ⟨y, hyB, hyR'⟩ := Types.exists_of_isPullback (hPB.map (forget CommRingCat))
        x.1 x.2 (sub_eq_zero.mp hx)
      exact ⟨y, Prod.ext hyB hyR'⟩
  let U := IsLocalizedModule.map (.powers h) f₀ (f₁.prodMap f₂) u
  let V := IsLocalizedModule.map (.powers h) (f₁.prodMap f₂) f₃ v
  let pB : Localization.Away h →+* Localization.Away g :=
    Localization.awayLift ((algebraMap B (Localization.Away g)).comp πB) h (by
      rw [RingHom.comp_apply, hB]
      exact IsLocalization.Away.algebraMap_isUnit g)
  let pR : Localization.Away h →+* Localization.Away f :=
    Localization.awayLift ((algebraMap R' (Localization.Away f)).comp πR') h (by
      rw [RingHom.comp_apply, hR']
      exact IsLocalization.Away.algebraMap_isUnit f)
  have hpBcompat (a : B') (x : Localization.Away h) : pB (a • x) = a • pB x := by
    show pB (algebraMap B' (Localization.Away h) a * x) =
      ((algebraMap B (Localization.Away g)).comp πB) a * pB x
    rw [map_mul]
    congr 1
    simp [pB, Localization.awayLift, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  have hpRcompat (a : B') (x : Localization.Away h) : pR (a • x) = a • pR x := by
    show pR (algebraMap B' (Localization.Away h) a * x) =
      ((algebraMap R' (Localization.Away f)).comp πR') a * pR x
    rw [map_mul]
    congr 1
    simp [pR, Localization.awayLift, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  let pBlin : Localization.Away h →ₗ[B'] Localization.Away g := ringHomLinearMap pB hpBcompat
  let pRlin : Localization.Away h →ₗ[B'] Localization.Away f := ringHomLinearMap pR hpRcompat
  have hUeq : U = LinearMap.prod pBlin pRlin := by
    apply IsLocalizedModule.linearMap_ext (.powers h) f₀ (f₁.prodMap f₂)
    apply LinearMap.ext
    intro a
    show U (f₀ a) = (LinearMap.prod pBlin pRlin) (f₀ a)
    rw [show U = IsLocalizedModule.map (.powers h) f₀ (f₁.prodMap f₂) u by rfl,
      IsLocalizedModule.map_apply]
    simp [pBlin, pRlin, ringHomLinearMap, LinearMap.prod_apply, f₀, f₁, f₂,
      u, Algebra.linearMap_apply, scalarLocalizationMap, pB, pR,
      Localization.awayLift, IsLocalization.Away.lift_eq, RingHom.comp_apply,
      RingHom.algebraMap_toAlgebra]
  let bMap : Localization.Away g →+* Localization.Away (s g) :=
    Localization.awayMap s g
  let qMap : Localization.Away f →+* Localization.Away (s g) :=
    Localization.awayLift ((algebraMap R (Localization.Away (s g))).comp t) f (by
      rw [RingHom.comp_apply, ← hcompat]
      exact IsLocalization.Away.algebraMap_isUnit (s g))
  have hbCompat (a : B') (x : Localization.Away g) : bMap (a • x) = a • bMap x := by
    show bMap (((algebraMap B (Localization.Away g)).comp πB) a * x) =
      ((algebraMap R (Localization.Away (s g))).comp (s.comp πB)) a * bMap x
    rw [map_mul]
    congr 1
    simp [bMap, IsLocalization.Away.map, RingHom.comp_apply]
  have hqCompat (a : B') (x : Localization.Away f) : qMap (a • x) = a • qMap x := by
    show qMap (((algebraMap R' (Localization.Away f)).comp πR') a * x) =
      ((algebraMap R (Localization.Away (s g))).comp (s.comp πB)) a * qMap x
    rw [map_mul]
    congr 1
    simp [qMap, Localization.awayLift, IsLocalization.Away.lift_eq,
      RingHom.comp_apply, hbase]
  let bLin : Localization.Away g →ₗ[B'] Localization.Away (s g) :=
    ringHomLinearMap bMap hbCompat
  let qLin : Localization.Away f →ₗ[B'] Localization.Away (s g) :=
    ringHomLinearMap qMap hqCompat
  let W : Localization.Away g × Localization.Away f →ₗ[B'] Localization.Away (s g) :=
    { toFun := fun x => bLin x.1 - qLin x.2
      map_add' x y := by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      map_smul' := by
        intro a x
        rcases x with ⟨x, y⟩
        show bLin (a • x) - qLin (a • y) = a • (bLin x - qLin y)
        rw [bLin.map_smul, qLin.map_smul, smul_sub] }
  have hVeq : V = W := by
    apply IsLocalizedModule.linearMap_ext (.powers h) (f₁.prodMap f₂) f₃
    apply LinearMap.ext
    intro z
    rcases z with ⟨b, r'⟩
    show V ((f₁.prodMap f₂) (b, r')) = W ((f₁.prodMap f₂) (b, r'))
    rw [show V = IsLocalizedModule.map (.powers h) (f₁.prodMap f₂) f₃ v by rfl,
      IsLocalizedModule.map_apply]
    simp [W, bLin, qLin, ringHomLinearMap, f₁, f₂, f₃, scalarLocalizationMap,
      v, bMap, qMap, Localization.awayLift,
      IsLocalization.Away.map, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  refine commRing_isPullback_of_types ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
  · have hcomp : bMap.comp pB = qMap.comp pR := by
      apply IsLocalization.ringHom_ext (.powers h)
      ext x
      simpa [pB, pR, bMap, qMap, Localization.awayMap, Localization.awayLift,
        IsLocalization.Away.map, IsLocalization.Away.lift] using
        congrArg (algebraMap R (Localization.Away (s g))) (DFunLike.congr_fun hbase x)
    ext x
    exact DFunLike.congr_fun hcomp x
  · intro x y hxy
    change pBlin x = pBlin y ∧ pRlin x = pRlin y at hxy
    apply IsLocalizedModule.map_injective (.powers h) f₀ (f₁.prodMap f₂) u hu
    show U x = U y
    rw [hUeq]
    exact Prod.ext hxy.1 hxy.2
  · intro x₂ x₃ hx
    have hVzero : V (x₂, x₃) = 0 := by
      rw [hVeq]
      exact sub_eq_zero.mpr hx
    obtain ⟨x₁, hxU⟩ := (IsLocalizedModule.map_exact (.powers h) f₀ (f₁.prodMap f₂) f₃ u v
      hExact (x₂, x₃)).mp hVzero
    change U x₁ = (x₂, x₃) at hxU
    rw [hUeq] at hxU
    change (pBlin x₁, pRlin x₁) = (x₂, x₃) at hxU
    exact ⟨x₁, by simpa [pBlin, ringHomLinearMap] using congrArg Prod.fst hxU,
      by simpa [pRlin, ringHomLinearMap] using congrArg Prod.snd hxU⟩

end RingFibreProduct
end

end

end
