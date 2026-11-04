module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# The pointwise flat locus of a morphism of schemes need not be open

The set of points at which a morphism of schemes is flat can be strictly larger than the
largest open subscheme on which the morphism is flat; in particular it is not in general open.
The witness is the inclusion of `ℤ` into the trivial square-zero extension of `ℤ` by
`⨁_p ℤ/p`, the direct sum over all primes.  The generic point of the spectrum of the extension
is a flat point, because the local ring of the base there is a field, while the prime `p` of
each summand carries a nonzero element killed by `p`, so the morphism is flat at no point of
any nonempty open: every nonempty open of the spectrum contains such a prime.  The largest flat
open is therefore empty while the flat locus is not.

## Main results

* `AlgebraicGeometry.exists_flat_locus_not_open` gives a morphism whose maximal flat open is a
  proper subset of its pointwise flat locus.

## Implementation notes

The maximal flat open is characterized by `IsGreatest` among opens whose restriction of the
morphism is flat.  Strict inclusion records both that every point of this open is flat and that
some flat point has no flat open neighbourhood.

The direct sum `⨁_p ℤ/p` carries two `ℤ`-module structures in the presence of the opposite
ring `ℤᵐᵒᵖ`, which the square-zero extension needs; the module structure over `ℤᵐᵒᵖ` is
transported along the canonical ring homomorphism `ℤᵐᵒᵖ →+* ℤ` and the two are identified by
`IsCentralScalar`.

## References

* [Stacks Project, Tag 04LI](https://stacks.math.columbia.edu/tag/04LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

/-- The direct sum of `ℤ/p` over all primes `p`, the module by which `ℤ` is extended. -/
private abbrev flatCounterexampleModule := DirectSum Nat.Primes (fun p => ZMod (p : ℕ))

local notation3 "M₀" => flatCounterexampleModule

/-- The canonical ring homomorphism from the opposite ring of `ℤ` to `ℤ`, available because
`ℤ` is commutative.  It transports the `ℤ`-module structure on `M₀` to a `ℤᵐᵒᵖ`-module
structure, which the trivial square-zero extension requires. -/
private def unopHomInt : ℤᵐᵒᵖ →+* ℤ where
  toFun := MulOpposite.unop
  map_one' := by simp
  map_mul' x y := mul_comm _ _
  map_zero' := by simp
  map_add' x y := rfl

private instance : Module ℤᵐᵒᵖ M₀ := Module.compHom M₀ unopHomInt

private instance : IsCentralScalar ℤ M₀ where
  op_smul_eq_smul _ _ := rfl

private instance : SMulCommClass ℤ ℤᵐᵒᵖ M₀ where
  smul_comm := by
    intro r s m
    change r • (MulOpposite.unop s • m) = MulOpposite.unop s • (r • m)
    exact smul_comm _ _ _

/-- The trivial square-zero extension of `ℤ` by `M₀`. -/
private abbrev flatCounterexampleRing := TrivSqZeroExt ℤ M₀

local notation3 "S₀" => flatCounterexampleRing

private instance : CommRing S₀ :=
  @TrivSqZeroExt.commRing ℤ M₀ (inferInstance : CommRing ℤ) (inferInstance : AddCommGroup M₀)
    (inferInstance : Module ℤ M₀) (inferInstance : Module ℤᵐᵒᵖ M₀)
    (inferInstance : IsCentralScalar ℤ M₀)

/-- The inclusion of `ℤ` into the square-zero extension. -/
private def inc₀ : ℤ →+* S₀ := TrivSqZeroExt.inlHom ℤ M₀

/-- The projection of the square-zero extension onto `ℤ`. -/
private def proj₀ : S₀ →+* ℤ := (TrivSqZeroExt.fstHom ℤ ℤ M₀).toRingHom

/-- The base ring of the counterexample, a copy of `ℤ` in universe `u`. -/
private abbrev baseRing : Type u := ULift.{u} ℤ

/-- The square-zero extension of the counterexample, in universe `u`. -/
private abbrev extensionRing : Type u := ULift.{u} S₀

private instance : IsDomain baseRing := Equiv.isDomain Equiv.ulift

/-- The morphism of rings whose spectrum is the counterexample. -/
private def inc : baseRing.{u} →+* extensionRing.{u} := RingHom.ulift inc₀

/-- The retraction of `inc`. -/
private def proj : extensionRing.{u} →+* baseRing.{u} := RingHom.ulift proj₀

/-- The generic point of the spectrum of the base ring. -/
private def genericBase : PrimeSpectrum (baseRing.{u}) := ⟨⊥, by infer_instance⟩

/-- The point of the spectrum of the extension above the generic point of the base. -/
private def genericExtension : PrimeSpectrum (extensionRing.{u}) :=
  PrimeSpectrum.comap (R := extensionRing.{u}) (S := baseRing.{u}) proj genericBase

/-- The image in the base of a point of the spectrum of the extension. -/
private def sourcePoint (q : PrimeSpectrum (extensionRing.{u})) :
    PrimeSpectrum (baseRing.{u}) :=
  PrimeSpectrum.comap inc q

/-- The local ring homomorphism induced by `inc` at a point of the spectrum of the
extension. -/
private def localAt (q : PrimeSpectrum (extensionRing.{u})) :
    Localization.AtPrime (sourcePoint q).asIdeal →+* Localization.AtPrime q.asIdeal :=
  Localization.localRingHom _ _ inc rfl

private lemma proj_comp_inc : proj.comp inc = RingHom.id baseRing := by
  ext r
  simp [proj, inc, RingHom.ulift_apply, RingHom.comp_apply, inc₀, proj₀]

private lemma generic_source_ideal :
    (sourcePoint genericExtension.{u}).asIdeal = (⊥ : Ideal baseRing.{u}) := by
  show Ideal.comap (proj.comp inc) (⊥ : Ideal baseRing.{u}) = ⊥
  rw [proj_comp_inc]
  rfl

private lemma flatAt_specMap_iff (q : PrimeSpectrum (extensionRing.{u})) :
    IsFlatAt (Spec.map.{u} (CommRingCat.ofHom inc.{u})).toLRSHom.toShHom q ↔
      (localAt.{u} q).Flat := by
  let f : CommRingCat.of baseRing.{u} ⟶ CommRingCat.of extensionRing.{u} :=
    CommRingCat.ofHom inc
  let e₁ := Spec.stalkIso (CommRingCat.of baseRing.{u}) (sourcePoint q)
  let e₂ := Spec.stalkIso (CommRingCat.of extensionRing.{u}) q
  let g := CommRingCat.ofHom (localAt.{u} q)
  have hcomp : e₂.inv.hom.comp (g.hom.comp e₁.hom.hom) = ((Spec.map.{u} f).stalkMap q).hom := by
    convert CommRingCat.hom_ext_iff.mp (Scheme.localRingHom_comp_stalkIso f q) using 1
    rfl
  show ((Spec.map.{u} f).stalkMap q).hom.Flat ↔ (localAt.{u} q).Flat
  rw [← hcomp]
  have hcancel₂ :
      (e₂.inv.hom.comp (g.hom.comp e₁.hom.hom)).Flat ↔
        (g.hom.comp e₁.hom.hom).Flat := by
    simpa [CommRingCat.hom_comp, Category.assoc] using
      (RingHom.Flat.respectsIso.cancel_right_isIso (e₁.hom ≫ g) e₂.inv)
  exact hcancel₂.trans (RingHom.Flat.respectsIso.cancel_left_isIso e₁.hom g)

private lemma flatAt_generic :
    IsFlatAt (Spec.map.{u} (CommRingCat.ofHom inc.{u})).toLRSHom.toShHom
      genericExtension.{u} := by
  show ((Spec.map.{u} (CommRingCat.ofHom inc.{u})).stalkMap genericExtension.{u}).hom.Flat
  let q := (Spec.map.{u} (CommRingCat.ofHom inc.{u})) genericExtension.{u}
  let _ : q.asIdeal.IsPrime := q.2
  let e₁ := Spec.stalkIso (CommRingCat.of baseRing.{u}) q
  have hp : q.asIdeal = (⊥ : Ideal baseRing.{u}) := generic_source_ideal
  let e : Localization.AtPrime q.asIdeal ≃+*
      Localization.AtPrime (⊥ : Ideal baseRing.{u}) :=
    Localization.localRingEquiv _ _ (RingEquiv.refl baseRing.{u}) (by rw [hp]; rfl)
  have : IsFractionRing (baseRing.{u})
      (Localization.AtPrime (⊥ : Ideal baseRing.{u})) := by
    show IsLocalization (nonZeroDivisors (baseRing.{u}))
      (Localization.AtPrime (⊥ : Ideal baseRing.{u}))
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let _ : Field (Localization.AtPrime (⊥ : Ideal baseRing.{u})) :=
    IsFractionRing.toField (baseRing.{u})
      (K := Localization.AtPrime (⊥ : Ideal baseRing.{u}))
  exact RingHom.Flat.of_isField
    ((MulEquiv.isField_congr (e₁.commRingCatIsoToRingEquiv.trans e).toMulEquiv).mpr
      (Field.toIsField _))
    ((Spec.map.{u} (CommRingCat.ofHom inc.{u})).stalkMap genericExtension.{u}).hom

/-- Reduction of the base ring modulo a prime `p`. -/
private def modMap (p : Nat.Primes) : baseRing.{u} →+* ZMod p.1 where
  toFun x := (x.down : ZMod p.1)
  map_one' := by simp
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

/-- The prime of the extension at which flatness fails for the prime `p`: the contraction of
the zero ideal of `ℤ/p` along the reduction of the retraction. -/
private def badPoint (p : Nat.Primes) : PrimeSpectrum (extensionRing.{u}) := by
  let : Fact p.1.Prime := ⟨p.2⟩
  exact PrimeSpectrum.comap ((modMap p).comp proj.{u}) ⟨⊥, Ideal.isPrime_bot⟩

/-- The square-zero element of the extension supported on the summand `ℤ/p`. -/
private def eps (p : Nat.Primes) : extensionRing.{u} :=
  ULift.up (TrivSqZeroExt.inr (DirectSum.of (fun q : Nat.Primes => ZMod q.1) p 1) : S₀)

private lemma eps_ne_zero (p : Nat.Primes) : eps.{u} p ≠ 0 := by
  intro h
  have he : DirectSum.of (fun q : Nat.Primes => ZMod q.1) p 1 = 0 := by
    simpa [eps] using congrArg (fun x : extensionRing.{u} => x.down.snd) h
  have hone : (1 : ZMod p.1) = 0 := by
    simpa [DirectSum.of_apply] using
      congrArg (fun x : DirectSum Nat.Primes (fun q : Nat.Primes => ZMod q.1) => x p) he
  have : Fact p.1.Prime := ⟨p.2⟩
  exact one_ne_zero hone

private lemma inc_mul_eps (p : Nat.Primes) :
    inc.{u} (ULift.up (p.1 : ℤ)) * eps.{u} p = 0 := by
  apply ULift.ext
  show TrivSqZeroExt.inl (p.1 : ℤ) *
    TrivSqZeroExt.inr (DirectSum.of (fun q : Nat.Primes => ZMod q.1) p 1) = 0
  rw [TrivSqZeroExt.inl_mul_inr]
  apply congrArg TrivSqZeroExt.inr
  ext q
  rcases eq_or_ne q p with rfl | h
  · simp [DirectSum.smul_apply, CharP.cast_eq_zero]
  · simp [DirectSum.smul_apply, DirectSum.of_apply, h.symm]

/-- An element of the extension lies in `badPoint p` iff its reduction modulo `p` vanishes. -/
private lemma mem_badPoint_iff (p : Nat.Primes) (c : extensionRing.{u}) :
    c ∈ (badPoint.{u} p).asIdeal ↔ modMap p (proj.{u} c) = 0 := by
  change ((modMap p).comp proj.{u}) c ∈ (⊥ : Ideal (ZMod p.1)) ↔ _
  simp [RingHom.comp_apply]

private lemma badPoint_product_eps_ne_zero (p : Nat.Primes) (c : extensionRing.{u})
    (hc : c ∉ (badPoint.{u} p).asIdeal) : c * eps.{u} p ≠ 0 := by
  have hmod : modMap p (proj.{u} c) ≠ 0 := by rwa [mem_badPoint_iff] at hc
  intro hz
  have hsum : (c.down).fst • DirectSum.of (fun q : Nat.Primes => ZMod q.1) p 1 = 0 := by
    simpa [eps, TrivSqZeroExt.snd_mul] using
      congrArg TrivSqZeroExt.snd (congrArg ULift.down hz)
  have hzero : ((c.down).fst : ZMod p.1) = 0 := by
    simpa [DirectSum.smul_apply, DirectSum.of_apply] using
      congrArg (fun x : DirectSum Nat.Primes (fun q : Nat.Primes => ZMod q.1) => x p) hsum
  apply hmod
  simpa [modMap, proj, proj₀] using hzero

/-- If every element outside the prime `P` has nonzero product with `r`, then `r` is nonzero in
the localization at `P`. -/
private lemma algebraMap_atPrime_ne_zero {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    (r : R) (h : ∀ c ∈ P.primeCompl, c * r ≠ 0) :
    algebraMap R (Localization.AtPrime P) r ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ r).mp hz
  exact h c c.2 hc

private lemma badPoint_localized_eps_ne_zero (p : Nat.Primes) :
    algebraMap extensionRing.{u} (Localization.AtPrime (badPoint.{u} p).asIdeal)
      (eps.{u} p) ≠ 0 := by
  exact algebraMap_atPrime_ne_zero _ _ fun c hc => badPoint_product_eps_ne_zero p c hc

private lemma not_flatAt_badPoint (p : Nat.Primes) :
    ¬ IsFlatAt (Spec.map.{u} (CommRingCat.ofHom inc.{u})).toLRSHom.toShHom
      (badPoint.{u} p) := by
  intro hflat
  let A := Localization.AtPrime (sourcePoint.{u} (badPoint.{u} p)).asIdeal
  let T := Localization.AtPrime (badPoint.{u} p).asIdeal
  let r : baseRing.{u} := ULift.up (p.1 : ℤ)
  have hr : r ≠ 0 := fun h =>
    (by exact_mod_cast p.2.ne_zero : (p.1 : ℤ) ≠ 0) (congrArg ULift.down h)
  have hrA : algebraMap baseRing.{u} A r ≠ 0 := by
    refine algebraMap_atPrime_ne_zero _ _ fun c hc hmul => hc ?_
    simp [(mul_eq_zero.mp hmul).resolve_right hr]
  let _ : Algebra A T := (localAt.{u} (badPoint.{u} p)).toAlgebra
  let z : T := algebraMap extensionRing.{u} T (eps.{u} p)
  have hmap : localAt.{u} (badPoint.{u} p) (algebraMap baseRing.{u} A r) =
      algebraMap extensionRing.{u} T (inc.{u} r) := by
    show Localization.localRingHom (sourcePoint.{u} (badPoint.{u} p)).asIdeal
      (badPoint.{u} p).asIdeal inc.{u} rfl (algebraMap baseRing.{u} A r) = _
    exact Localization.localRingHom_to_map _ _ inc.{u} rfl r
  have hkill : (algebraMap baseRing.{u} A r) • z = 0 := by
    show localAt.{u} (badPoint.{u} p) (algebraMap baseRing.{u} A r) * z = 0
    rw [hmap, ← map_mul]
    show algebraMap extensionRing.{u} T
      (inc.{u} (ULift.up (p.1 : ℤ)) * eps.{u} p) = 0
    rw [inc_mul_eps]
    simp
  have : Module.Flat A T := (flatAt_specMap_iff (badPoint.{u} p)).mp hflat
  exact badPoint_localized_eps_ne_zero p
    ((Module.Flat.isSMulRegular_of_nonZeroDivisors (R := A) (M := T)
      (mem_nonZeroDivisors_iff_ne_zero.mpr hrA)) (by simpa using hkill))

private lemma exists_badPoint_in_open
    (V : (Spec (CommRingCat.of extensionRing.{u})).Opens) (hV : V ≠ ⊥) :
    ∃ p : Nat.Primes, badPoint.{u} p ∈ V := by
  obtain ⟨x, hx⟩ := V.ne_bot_iff_nonempty.mp hV
  obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxB, hBV⟩ :=
    (PrimeSpectrum.isBasis_basic_opens (R := extensionRing.{u})).exists_subset_of_mem_open
      hx V.2
  have hsnot : s ∉ x.asIdeal := (PrimeSpectrum.mem_basicOpen s x).mp hxB
  have hscalar : (proj.{u} s).down ≠ 0 := by
    intro ha
    have hfst : s.down.fst = 0 := by simpa [proj, proj₀] using ha
    have hsdown : s.down = TrivSqZeroExt.inr s.down.snd := by
      apply TrivSqZeroExt.ext <;> simp [hfst]
    have hsq : s * s = 0 := by
      apply ULift.ext
      show s.down * s.down = 0
      rw [hsdown]
      simp
    apply hsnot
    apply x.2.mem_of_pow_mem 2
    simp [pow_two, hsq]
  let a : ℤ := (proj.{u} s).down
  obtain ⟨n, hnle, hnprime⟩ := Nat.exists_infinite_primes (a.natAbs + 2)
  let p : Nat.Primes := ⟨n, hnprime⟩
  have hmod : modMap p (proj.{u} s) ≠ 0 := by
    intro hz
    have hcast : (a : ZMod n) = 0 := by simpa [modMap, p, a] using hz
    have hle : n ≤ a.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hscalar)
      (Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp hcast))
    omega
  exact ⟨p, hBV ((PrimeSpectrum.mem_basicOpen s _).2 (by rwa [Ne, ← mem_badPoint_iff] at hmod))⟩

/-- If a morphism is flat after restriction to an open, then it is flat at every point of
that open. -/
private lemma flatAt_of_flat_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : X.Opens} (hV : Flat (V.ι ≫ f)) (x : V) :
    IsFlatAt f.toLRSHom.toShHom (x : X) := by
  have hcomp := (AlgebraicGeometry.Flat.iff_flat_stalkMap (f := V.ι ≫ f)).mp hV x
  have heq : ((V.ι ≫ f).stalkMap x).hom =
      (f.stalkMap (V.ι x) ≫ V.ι.stalkMap x).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp V.ι f x)
  rw [heq] at hcomp
  have : IsIso (V.ι.stalkMap x) := by
    rw [← Scheme.Opens.stalkIso_inv]
    exact (V.stalkIso x).symm.isIso_hom
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (f.stalkMap (V.ι x)) (V.ι.stalkMap x)).mp hcomp

private lemma flat_open_eq_bot (V : (Spec (CommRingCat.of extensionRing.{u})).Opens)
    (hV : Flat (V.ι ≫ Spec.map.{u} (CommRingCat.ofHom inc.{u}))) : V = ⊥ := by
  by_contra hne
  obtain ⟨p, hpV⟩ := exists_badPoint_in_open V hne
  exact not_flatAt_badPoint p (flatAt_of_flat_restriction _ hV ⟨badPoint.{u} p, hpV⟩)

/-- **Stacks Project, Tag 04LI (pointwise warning).** For some morphism of
schemes, its maximal flat open is strictly smaller than its pointwise flat
locus. -/
@[stacks 04LI "pointwise_warning"]
public theorem exists_flat_locus_not_open :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (W : X.Opens),
      IsGreatest {V : X.Opens | Flat (V.ι ≫ f)} W ∧
        (W.1 : Set X) ⊂
          {x : X | IsFlatAt f.toLRSHom.toShHom x} := by
  let X : Scheme.{u} := Spec (CommRingCat.of extensionRing.{u})
  let Y : Scheme.{u} := Spec (CommRingCat.of baseRing.{u})
  let f : X ⟶ Y := Spec.map.{u} (CommRingCat.ofHom inc.{u})
  refine ⟨X, Y, f, ⊥, ?_, ?_⟩
  · have hbot : Flat ((⊥ : X.Opens).ι ≫ f) := by
      rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
      intro x
      have hx : (x.1 : X) ∈ (⊥ : X.Opens) := x.2
      simp at hx
    exact ⟨hbot, fun V hV => (flat_open_eq_bot V hV).le⟩
  · show (∅ : Set X) ⊂ {x : X | IsFlatAt f.toLRSHom.toShHom x}
    exact Set.Nonempty.empty_ssubset ⟨genericExtension.{u}, flatAt_generic⟩

end

end AlgebraicGeometry
