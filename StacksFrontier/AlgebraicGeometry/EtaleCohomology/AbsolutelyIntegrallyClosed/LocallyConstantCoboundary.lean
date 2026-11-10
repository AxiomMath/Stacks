module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.Interpolation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.LiftingPoints
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.MultiplicativeDeformation
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed
public import StacksFrontier.RingTheory.Module.Projective.Lifting

/-!
# Locally constant coboundaries on the spectrum of an absolutely integrally closed ring

Let `R` be an absolutely integrally closed ring, let `M` be a finite abelian group and let
`f, g ∈ R`. Every locally constant `M`-valued function on the overlap
`D(f(f + g)) ∩ D(g(f + g)) = D(f(f + g) · g(f + g))` is the difference of a locally constant
function on `D(g(f + g))` and one on `D(f(f + g))`.

## Main results

* `exists_locallyConstant_coboundary_on_basicOpen_sum`: every locally constant `M`-valued
  function on `D(f(f + g) · g(f + g))` is the difference of the restrictions of a locally constant
  function on `D(g(f + g))` and one on `D(f(f + g))`.

## References

* [Stacks Project, Tag 0GY7](https://stacks.math.columbia.edu/tag/0GY7)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.LocallyConstantCoboundary

open Polynomial AlgebraicGeometry.MultiplicativeDeformation

private def deformedPointMap {A : Type*} [CommRing A] (π : A)
    {R : Type*} [CommRing R] [Algebra A R]
    {S : Type*} [CommRing S] [Algebra A S] (f : R →ₐ[A] S) :
    DeformedPoint π R →+ DeformedPoint π S where
  toFun x := ⟨f x.coord, by simpa only [map_add, map_mul, map_one, AlgHom.commutes]
    using x.isUnit_one_add.map f⟩
  map_zero' := by ext; exact map_zero f
  map_add' x y := by
    ext
    simp only [DeformedPoint.coord_add, map_add, map_mul, AlgHom.commutes]

private lemma exists_quotient_mk_eq_of_compatible {R : Type*} [CommRing R]
    (I J : Ideal R) (x : R ⧸ I) (y : R ⧸ J)
    (h : Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left) x =
      Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right) y) :
    ∃ z : R, Ideal.Quotient.mk I z = x ∧ Ideal.Quotient.mk J z = y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hab : a - b ∈ I ⊔ J := Ideal.Quotient.eq.mp h
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hab
  refine ⟨a - u, Ideal.Quotient.eq.mpr ?_, Ideal.Quotient.eq.mpr ?_⟩
  · simpa only [show a - u - a = -u by abel] using I.neg_mem hu
  · simpa only [show a - u - b = v by linear_combination -huv] using hv

private lemma isUnit_of_quotient_mk {R : Type*} [CommRing R]
    (I J : Ideal R) (hIJ : I ⊓ J = ⊥) (r : R)
    (hI : IsUnit (Ideal.Quotient.mk I r)) (hJ : IsUnit (Ideal.Quotient.mk J r)) :
    IsUnit r := by
  obtain ⟨a, ha⟩ := hI.exists_right_inv
  obtain ⟨b, hb⟩ := hJ.exists_right_inv
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hi : r * a - 1 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp
    (by simpa only [map_sub, map_mul, map_one, sub_eq_zero] using ha)
  have hj : r * b - 1 ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp
    (by simpa only [map_sub, map_mul, map_one, sub_eq_zero] using hb)
  have hz : (r * a - 1) * (r * b - 1) = 0 := by
    have hm : (r * a - 1) * (r * b - 1) ∈ I ⊓ J :=
      ⟨I.mul_mem_right _ hi, J.mul_mem_left _ hj⟩
    simpa only [hIJ, Ideal.mem_bot] using hm
  apply isUnit_iff_exists_inv.mpr
  refine ⟨a + b - r * a * b, ?_⟩
  linear_combination -hz

private lemma exists_deformedPoint_of_quotient
    {A : Type*} [CommRing A] (π : A)
    {R : Type*} [CommRing R] [Algebra A R]
    (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (x : DeformedPoint π (R ⧸ I)) (y : DeformedPoint π (R ⧸ J))
    (h : Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left) x.coord =
      Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right) y.coord) :
    ∃ z : DeformedPoint π R,
      deformedPointMap π (Ideal.Quotient.mkₐ A I) z = x ∧
      deformedPointMap π (Ideal.Quotient.mkₐ A J) z = y := by
  obtain ⟨r, hrI, hrJ⟩ := exists_quotient_mk_eq_of_compatible I J x.coord y.coord h
  have hu : IsUnit (algebraMap A R π * r + 1) := by
    apply isUnit_of_quotient_mk I J hIJ
    · rw [map_add, map_mul, map_one, hrI]
      exact x.isUnit_one_add
    · rw [map_add, map_mul, map_one, hrJ]
      exact y.isUnit_one_add
  exact ⟨⟨r, hu⟩, DeformedPoint.ext hrI, DeformedPoint.ext hrJ⟩

/-- The principal ideals of `a` and `b` meet trivially if `a * b = 0` in a reduced ring. -/
private lemma span_inf_span_eq_bot_of_mul_eq_zero {R : Type*} [CommRing R] [IsReduced R]
    (a b : R) (hab : a * b = 0) : Ideal.span {a} ⊓ Ideal.span {b} = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨hxa, hxb⟩
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hxa
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hxb
  apply Ideal.mem_bot.mpr
  apply IsNilpotent.eq_zero
  exact ⟨2, by linear_combination (-(u * a)) * hv + u * v * hab⟩

private lemma exists_deformedPoint_of_isUnit_of_sub_mem_sup
    {R : Type*} [CommRing R] (π : R) (s t : DeformedPoint π R)
    (f g b : R) (hrel : b * (b - f * g) = 0)
    (hs : s.coord - t.coord ∈ Ideal.span {b} ⊔ Ideal.span {g})
    {S : Type*} [CommRing S] [IsReduced S] [Algebra R S]
    (hf : IsUnit (algebraMap R S f)) :
    ∃ x : DeformedPoint π S,
      x.coord - algebraMap R S s.coord ∈ Ideal.span {algebraMap R S b} ∧
      x.coord - algebraMap R S t.coord ∈ Ideal.span {algebraMap R S (b - f * g)} := by
  let I : Ideal S := Ideal.span {algebraMap R S b}
  let J : Ideal S := Ideal.span {algebraMap R S (b - f * g)}
  have hIJ : I ⊓ J = ⊥ :=
    span_inf_span_eq_bot_of_mul_eq_zero _ _ (by rw [← map_mul, hrel, map_zero])
  let q : R →+* S ⧸ (I ⊔ J) := (Ideal.Quotient.mk (I ⊔ J)).comp (algebraMap R S)
  have hb : q b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show I ≤ I ⊔ J from le_sup_left) (Ideal.subset_span (Set.mem_singleton _)))
  have hbg : q (b - f * g) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show J ≤ I ⊔ J from le_sup_right) (Ideal.subset_span (Set.mem_singleton _)))
  have hfg : q f * q g = 0 := by
    simpa only [map_sub, map_mul, hb, zero_sub, neg_eq_zero] using hbg
  have hg : q g = 0 := (hf.map (Ideal.Quotient.mk (I ⊔ J))).mul_right_eq_zero.mp hfg
  have hker : Ideal.span {b} ⊔ Ideal.span {g} ≤ RingHom.ker q :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hb)
      ((Ideal.span_singleton_le_iff_mem _).mpr hg)
  have hsq : q s.coord = q t.coord := by
    have hsq : q (s.coord - t.coord) = 0 := hker hs
    simpa only [map_sub, sub_eq_zero] using hsq
  obtain ⟨x, hx, hx'⟩ := exists_deformedPoint_of_quotient π I J hIJ
    (deformedPointMap π ((Ideal.Quotient.mkₐ R I).comp (Algebra.ofId R S)) s)
    (deformedPointMap π ((Ideal.Quotient.mkₐ R J).comp (Algebra.ofId R S)) t)
    hsq
  exact ⟨x, Ideal.Quotient.eq.mp (congrArg DeformedPoint.coord hx),
    Ideal.Quotient.eq.mp (congrArg DeformedPoint.coord hx')⟩

private lemma exists_deformedPoints_of_coprime
    {R : Type*} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (π : R) (hπ : IsOfFinOrder (1 + π))
    (f g b : R) (hfg : IsCoprime f g) (hrel : b * (b - f * g) = 0)
    {S : Type*} [CommRing S] [IsReduced S] [Algebra R S]
    {T : Type*} [CommRing T] [IsReduced T] [Algebra R T]
    (hf : IsUnit (algebraMap R S f)) (hg : IsUnit (algebraMap R T g)) :
    ∃ (s : DeformedPoint π R) (x : DeformedPoint π S) (y : DeformedPoint π T),
      x.coord - algebraMap R S s.coord ∈ Ideal.span {algebraMap R S b} ∧
      y.coord - algebraMap R T s.coord ∈ Ideal.span {algebraMap R T b} ∧
      x.coord ∈ Ideal.span {algebraMap R S (b - f * g)} ∧
      y.coord - 1 ∈ Ideal.span {algebraMap R T (b - f * g)} := by
  let I : Ideal R := Ideal.span {b} ⊔ Ideal.span {g}
  let J : Ideal R := Ideal.span {b} ⊔ Ideal.span {f}
  have hIJ : I + J = ⊤ := by
    rw [Ideal.add_eq_sup]
    apply top_unique
    have hfg' : Ideal.span {g} ⊔ Ideal.span {f} = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq]
      exact (Ideal.isCoprime_span_singleton_iff g f).mpr hfg.symm
    rw [← hfg']
    exact sup_le (le_sup_of_le_left le_sup_right) (le_sup_of_le_right le_sup_right)
  obtain ⟨r, hr, hrI, hrJ⟩ :=
    exists_isUnit_one_add_mul_of_comaximal hR π hπ I J hIJ
  let s : DeformedPoint π R := ⟨r, by simpa only [Algebra.algebraMap_self,
    RingHom.id_apply, add_comm] using hr⟩
  let t : DeformedPoint π R := ⟨1, by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, mul_one, add_comm] using hπ.isUnit⟩
  obtain ⟨x, hx, hx'⟩ := exists_deformedPoint_of_isUnit_of_sub_mem_sup π s 0 f g b hrel
    (by simpa only [DeformedPoint.coord_zero, sub_zero] using hrI) hf
  obtain ⟨y, hy, hy'⟩ := exists_deformedPoint_of_isUnit_of_sub_mem_sup π s t g f b
    (by simpa only [mul_comm g f] using hrel) hrJ hg
  refine ⟨s, x, y, hx, hy, ?_, ?_⟩
  · simpa only [DeformedPoint.coord_zero, map_zero, sub_zero] using hx'
  · simpa only [t, map_one, mul_comm g f] using hy'

private lemma deformedPoint_ext_of_quotient
    {A : Type*} [CommRing A] {π : A}
    {R : Type*} [CommRing R] [Algebra A R]
    (I J : Ideal R) (hIJ : I ⊓ J = ⊥) {x y : DeformedPoint π R}
    (hI : deformedPointMap π (Ideal.Quotient.mkₐ A I) x =
      deformedPointMap π (Ideal.Quotient.mkₐ A I) y)
    (hJ : deformedPointMap π (Ideal.Quotient.mkₐ A J) x =
      deformedPointMap π (Ideal.Quotient.mkₐ A J) y) : x = y := by
  apply DeformedPoint.ext
  apply sub_eq_zero.mp
  have h : x.coord - y.coord ∈ I ⊓ J :=
    ⟨Ideal.Quotient.eq.mp (congrArg DeformedPoint.coord hI),
      Ideal.Quotient.eq.mp (congrArg DeformedPoint.coord hJ)⟩
  simpa only [hIJ, Ideal.mem_bot] using h

private lemma deformedPoint_sub_eq_of_congruences
    {A : Type*} [CommRing A] {π : A}
    {R : Type*} [CommRing R] [Algebra A R]
    (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (x y s t : DeformedPoint π R)
    (hxI : x.coord - s.coord ∈ I) (hyI : y.coord - s.coord ∈ I)
    (htI : t.coord ∈ I) (hxJ : x.coord ∈ J) (hyJ : y.coord - t.coord ∈ J) :
    y - x = t := by
  apply deformedPoint_ext_of_quotient I J hIJ
  · have hx : deformedPointMap π (Ideal.Quotient.mkₐ A I) x =
        deformedPointMap π (Ideal.Quotient.mkₐ A I) s :=
      DeformedPoint.ext (Ideal.Quotient.eq.mpr hxI)
    have hy : deformedPointMap π (Ideal.Quotient.mkₐ A I) y =
        deformedPointMap π (Ideal.Quotient.mkₐ A I) s :=
      DeformedPoint.ext (Ideal.Quotient.eq.mpr hyI)
    have ht : deformedPointMap π (Ideal.Quotient.mkₐ A I) t = 0 :=
      DeformedPoint.ext (Ideal.Quotient.eq_zero_iff_mem.mpr htI)
    rw [map_sub, hx, hy, ht, sub_self]
  · have hx : deformedPointMap π (Ideal.Quotient.mkₐ A J) x = 0 :=
      DeformedPoint.ext (Ideal.Quotient.eq_zero_iff_mem.mpr hxJ)
    have hy : deformedPointMap π (Ideal.Quotient.mkₐ A J) y =
        deformedPointMap π (Ideal.Quotient.mkₐ A J) t :=
      DeformedPoint.ext (Ideal.Quotient.eq.mpr hyJ)
    rw [map_sub, hx, hy, sub_zero]

private lemma exists_scaled_idempotent
    {R : Type*} [CommRing R] (r : R)
    {S : Type*} [CommRing S] [Algebra R S] [IsLocalization.Away r S]
    (e : S) (he : IsIdempotentElem e) :
    ∃ (n : ℕ) (b : R), b * (b - r ^ n) = 0 ∧
      e * algebraMap R S (r ^ n) = algebraMap R S b := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r e
  have hm : algebraMap R S (a * (a - r ^ n)) = algebraMap R S 0 := by
    simp only [map_mul, map_sub, map_pow, map_zero, ← ha]
    calc
      (e * algebraMap R S r ^ n) * (e * algebraMap R S r ^ n - algebraMap R S r ^ n) =
          (e * e - e) * (algebraMap R S r ^ n) ^ 2 := by ring
      _ = 0 := by rw [he, sub_self, zero_mul]
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq r hm
  simp only [mul_zero] at hk
  refine ⟨n + k, a * r ^ k, ?_, ?_⟩
  · rw [pow_add]
    linear_combination r ^ k * hk
  · simp only [map_mul, map_pow, pow_add]
    rw [← mul_assoc, ha]

private lemma algHom_map_mem_span_singleton
    {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T]
    (φ : S →ₐ[R] T) (a : R) {x : S}
    (hx : x ∈ Ideal.span {algebraMap R S a}) :
    φ x ∈ Ideal.span {algebraMap R T a} := by
  apply Ideal.mem_span_singleton.mpr
  simpa only [AlgHom.commutes] using map_dvd φ (Ideal.mem_span_singleton.mp hx)

private lemma mem_span_singleton_of_mul_eq_of_isUnit
    {R : Type*} [CommRing R] {a b c : R} (hc : IsUnit c) (h : a * c = b) :
    a ∈ Ideal.span {b} := by
  apply Ideal.mem_span_singleton.mpr
  obtain ⟨u, rfl⟩ := hc
  refine ⟨↑u⁻¹, ?_⟩
  rw [← h, mul_assoc, Units.mul_inv, mul_one]

private lemma exists_deformedPoint_coboundary_of_idempotent
    {R : Type*} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (π : R) (hπ : IsOfFinOrder (1 + π))
    (f g : R) (hfg : IsCoprime f g)
    {S : Type*} [CommRing S] [IsReduced S] [Algebra R S]
    {T : Type*} [CommRing T] [IsReduced T] [Algebra R T]
    {W : Type*} [CommRing W] [IsReduced W] [Algebra R W]
    [IsLocalization.Away (f * g) W]
    (α : S →ₐ[R] W) (β : T →ₐ[R] W)
    (hf : IsUnit (algebraMap R S f)) (hg : IsUnit (algebraMap R T g))
    (t : DeformedPoint π W) (ht : IsIdempotentElem t.coord) :
    ∃ (x : DeformedPoint π S) (y : DeformedPoint π T),
      deformedPointMap π β y - deformedPointMap π α x = t := by
  obtain ⟨n, b, hb, ht'⟩ := exists_scaled_idempotent (f * g) t.coord ht
  obtain ⟨s, x, y, hx, hy, hx', hy'⟩ :=
    exists_deformedPoints_of_coprime (S := S) (T := T) hR π hπ (f ^ n) (g ^ n) b hfg.pow
      (by simpa only [mul_pow] using hb)
      (by simpa only [map_pow] using hf.pow n)
      (by simpa only [map_pow] using hg.pow n)
  let I : Ideal W := Ideal.span {algebraMap R W b}
  let J : Ideal W := Ideal.span {algebraMap R W (b - (f * g) ^ n)}
  have hIJ : I ⊓ J = ⊥ :=
    span_inf_span_eq_bot_of_mul_eq_zero _ _ (by rw [← map_mul, hb, map_zero])
  have hu : IsUnit (algebraMap R W ((f * g) ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (f * g)).pow n
  have htI : t.coord ∈ I := mem_span_singleton_of_mul_eq_of_isUnit hu ht'
  have htJ : t.coord - 1 ∈ J :=
    mem_span_singleton_of_mul_eq_of_isUnit hu (by
      rw [sub_mul, one_mul, ht', map_sub])
  refine ⟨x, y, ?_⟩
  apply deformedPoint_sub_eq_of_congruences I J hIJ
    (deformedPointMap π α x) (deformedPointMap π β y)
    (deformedPointMap π (Algebra.ofId R W) s) t
  · simpa [deformedPointMap, I] using algHom_map_mem_span_singleton α b hx
  · simpa [deformedPointMap, I] using algHom_map_mem_span_singleton β b hy
  · exact htI
  · simpa [deformedPointMap, J, ← mul_pow] using
      algHom_map_mem_span_singleton α (b - f ^ n * g ^ n) hx'
  · have hyJ : β y.coord - 1 ∈ J := by
      simpa [J, ← mul_pow] using
        algHom_map_mem_span_singleton β (b - f ^ n * g ^ n) hy'
    change β y.coord - t.coord ∈ J
    convert J.sub_mem hyJ htJ using 1
    ring

private lemma deformedPointMap_pointOfAlgHom
    {A : Type*} [CommRing A] (π : A)
    {R : Type*} [CommRing R] [Algebra A R]
    {S : Type*} [CommRing S] [Algebra A S]
    (φ : R →ₐ[A] S) (f : coordinateRing π →ₐ[A] R) :
    deformedPointMap π φ (pointOfAlgHom π f) = pointOfAlgHom π (φ.comp f) := by
  ext
  rfl

open CategoryTheory

private lemma exists_deformedPoint_of_isPullback
    {A : Type u} [CommRing A] (π : A)
    {R S T W : CommAlgCat.{u} A}
    {r : R ⟶ S} {s : R ⟶ T} {α : S ⟶ W} {β : T ⟶ W}
    (h : IsPullback r s α β)
    (x : DeformedPoint π S) (y : DeformedPoint π T)
    (hxy : deformedPointMap π α.hom x = deformedPointMap π β.hom y) :
    ∃ z : DeformedPoint π R,
      deformedPointMap π r.hom z = x ∧ deformedPointMap π s.hom z = y := by
  obtain ⟨fx, rfl⟩ := (pointOfAlgHom_bijective π S).2 x
  obtain ⟨fy, rfl⟩ := (pointOfAlgHom_bijective π T).2 y
  have hc : CommAlgCat.ofHom fx ≫ α = CommAlgCat.ofHom fy ≫ β := by
    apply CommAlgCat.hom_ext
    apply (pointOfAlgHom_bijective π W).1
    simpa only [deformedPointMap_pointOfAlgHom, CommAlgCat.hom_comp,
      CommAlgCat.hom_ofHom] using hxy
  let z := pointOfAlgHom π (h.lift (CommAlgCat.ofHom fx) (CommAlgCat.ofHom fy) hc).hom
  exact ⟨z, DeformedPoint.ext <| congrArg
      (fun k : CommAlgCat.of A (coordinateRing π) ⟶ S ↦ k.hom (coordinateGenerator π))
      (h.lift_fst (CommAlgCat.ofHom fx) (CommAlgCat.ofHom fy) hc),
    DeformedPoint.ext <| congrArg
      (fun k : CommAlgCat.of A (coordinateRing π) ⟶ T ↦ k.hom (coordinateGenerator π))
      (h.lift_snd (CommAlgCat.ofHom fx) (CommAlgCat.ofHom fy) hc)⟩

private noncomputable def isogenyOnPointsHom
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    (R : Type*) [CommRing R] [Algebra A R] :
    DeformedPoint (ζ - 1) R →+ DeformedPoint ((ζ - 1) ^ ℓ) R :=
  AddMonoidHom.mk' (isogenyOnPoints ℓ ζ hsplit)
    (isogenyOnPoints_add ℓ ζ hsplit)

private lemma isogenyOnPointsHom_naturality
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type*} [CommRing R] [Algebra A R]
    {S : Type*} [CommRing S] [Algebra A S]
    (φ : R →ₐ[A] S) (x : DeformedPoint (ζ - 1) R) :
    isogenyOnPointsHom ℓ ζ hsplit S (deformedPointMap (ζ - 1) φ x) =
      deformedPointMap ((ζ - 1) ^ ℓ) φ (isogenyOnPointsHom ℓ ζ hsplit R x) :=
  DeformedPoint.ext (Polynomial.aeval_algHom_apply φ x.coord (isogenyPolynomial ℓ ζ))

private lemma surjective_isogenyOnPoints
    {A : Type*} [CommRing A] [Nontrivial A]
    (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (Polynomial.X - Polynomial.C (ζ ^ i.val)) =
      Polynomial.X ^ ℓ - 1)
    {R : Type*} [CommRing R] [Algebra A R]
    (hR : IsAbsolutelyIntegrallyClosed R) :
    Function.Surjective (isogenyOnPoints ℓ ζ hsplit (R := R)) := by
  have hdegree : 0 < (isogenyPolynomial ℓ ζ).natDegree := by
    simp only [isogenyPolynomial, Polynomial.natDegree_prod_of_monic _ _
      (fun i _ ↦ Polynomial.monic_X_sub_C (sigmaPoint ℓ ζ i)),
      Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, ZMod.card,
      smul_eq_mul, mul_one]
    exact Nat.pos_of_ne_zero (NeZero.ne ℓ)
  intro y
  obtain ⟨f, rfl⟩ := (pointOfAlgHom_bijective ((ζ - 1) ^ ℓ) R).2 y
  obtain ⟨g, hg⟩ :=
    surjective_precomp_localizationMap_of_isAbsolutelyIntegrallyClosed
      A (ζ - 1) ℓ (isogenyPolynomial ℓ ζ)
      (one_add_mul_pow_eq_isogenyPolynomial ℓ ζ hsplit)
      (isogenyPolynomial_monic ℓ ζ) hdegree R hR f
  refine ⟨pointOfAlgHom (ζ - 1) g, ?_⟩
  rw [← pointOfAlgHom_comp_isogeny]
  exact congrArg (pointOfAlgHom ((ζ - 1) ^ ℓ)) hg


private lemma exists_kernel_coboundary
    {A : Type u} [CommRing A] [Nontrivial A]
    (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R S T W : CommAlgCat.{u} A} (hR : IsAbsolutelyIntegrallyClosed R)
    {r : R ⟶ S} {s : R ⟶ T} {α : S ⟶ W} {β : T ⟶ W}
    (h : IsPullback r s α β)
    (x : DeformedPoint (ζ - 1) S) (y : DeformedPoint (ζ - 1) T)
    (ht : isogenyOnPointsHom ℓ ζ hsplit W
      (deformedPointMap (ζ - 1) β.hom y - deformedPointMap (ζ - 1) α.hom x) = 0) :
    ∃ (u : DeformedPoint (ζ - 1) S) (v : DeformedPoint (ζ - 1) T),
      isogenyOnPointsHom ℓ ζ hsplit S u = 0 ∧
      isogenyOnPointsHom ℓ ζ hsplit T v = 0 ∧
      deformedPointMap (ζ - 1) β.hom v - deformedPointMap (ζ - 1) α.hom u =
        deformedPointMap (ζ - 1) β.hom y - deformedPointMap (ζ - 1) α.hom x := by
  have hxy : deformedPointMap ((ζ - 1) ^ ℓ) α.hom (isogenyOnPointsHom ℓ ζ hsplit S x) =
      deformedPointMap ((ζ - 1) ^ ℓ) β.hom (isogenyOnPointsHom ℓ ζ hsplit T y) := by
    rw [map_sub, isogenyOnPointsHom_naturality, isogenyOnPointsHom_naturality] at ht
    exact (sub_eq_zero.mp ht).symm
  obtain ⟨a, ha, ha'⟩ := exists_deformedPoint_of_isPullback ((ζ - 1) ^ ℓ) h
    (isogenyOnPointsHom ℓ ζ hsplit S x) (isogenyOnPointsHom ℓ ζ hsplit T y) hxy
  obtain ⟨z, hz⟩ := surjective_isogenyOnPoints ℓ ζ hsplit hR a
  have hz' : isogenyOnPointsHom ℓ ζ hsplit R z = a := hz
  refine ⟨x - deformedPointMap (ζ - 1) r.hom z,
    y - deformedPointMap (ζ - 1) s.hom z, ?_, ?_, ?_⟩
  · rw [map_sub, isogenyOnPointsHom_naturality, hz', ha, sub_self]
  · rw [map_sub, isogenyOnPointsHom_naturality, hz', ha', sub_self]
  · have heq : deformedPointMap (ζ - 1) α.hom (deformedPointMap (ζ - 1) r.hom z) =
        deformedPointMap (ζ - 1) β.hom (deformedPointMap (ζ - 1) s.hom z) :=
      DeformedPoint.ext (congrArg (fun k : R ⟶ W ↦ k.hom z.coord) h.w)
    simp only [map_sub, heq]
    abel

private lemma exists_kernel_coboundary_of_idempotent
    {R : Type u} [CommRing R] [Nontrivial R]
    (hR : IsAbsolutelyIntegrallyClosed R)
    (ℓ : ℕ) [NeZero ℓ] (ζ : R) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    (f g : R) (hfg : IsCoprime f g)
    {S T W : CommAlgCat.{u} R} [IsReduced S] [IsReduced T] [IsReduced W]
    [IsLocalization.Away (f * g) W]
    {α : S ⟶ W} {β : T ⟶ W}
    (h : IsPullback (CommAlgCat.ofHom (Algebra.ofId R S))
      (CommAlgCat.ofHom (Algebra.ofId R T)) α β)
    (hf : IsUnit (algebraMap R S f)) (hg : IsUnit (algebraMap R T g))
    (t : DeformedPoint (ζ - 1) W) (ht : IsIdempotentElem t.coord)
    (ht' : isogenyOnPointsHom ℓ ζ hsplit W t = 0) :
    ∃ (x : DeformedPoint (ζ - 1) S) (y : DeformedPoint (ζ - 1) T),
      isogenyOnPointsHom ℓ ζ hsplit S x = 0 ∧
      isogenyOnPointsHom ℓ ζ hsplit T y = 0 ∧
      deformedPointMap (ζ - 1) β.hom y - deformedPointMap (ζ - 1) α.hom x = t := by
  have hπ : IsOfFinOrder (1 + (ζ - 1)) := by
    rw [add_comm 1, sub_add_cancel]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ℓ, Nat.pos_of_ne_zero (NeZero.ne ℓ), hζ⟩
  obtain ⟨x, y, hxy⟩ := exists_deformedPoint_coboundary_of_idempotent
    hR (ζ - 1) hπ f g hfg α.hom β.hom hf hg t ht
  obtain ⟨x', y', hx', hy', heq⟩ := exists_kernel_coboundary ℓ ζ hsplit hR h x y
    (by rw [hxy]; exact ht')
  exact ⟨x', y', hx', hy', heq.trans hxy⟩

private lemma exists_algHom_pi_of_isogeny_eq_zero
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type*} [CommRing R] [Algebra A R]
    (x : DeformedPoint (ζ - 1) R) (hx : isogenyOnPointsHom ℓ ζ hsplit R x = 0) :
    ∃ φ : (ZMod ℓ → A) →ₐ[A] R, φ (fun i ↦ sigmaPoint ℓ ζ i) = x.coord := by
  obtain ⟨f, rfl⟩ := (pointOfAlgHom_bijective (ζ - 1) R).2 x
  let I : Ideal (coordinateRing (ζ - 1)) :=
    Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))}
  have hgen : f (isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))) = 0 := by
    have hx' : pointOfAlgHom ((ζ - 1) ^ ℓ) (f.comp (isogeny ℓ ζ hsplit)) = 0 := by
      rw [pointOfAlgHom_comp_isogeny]
      exact hx
    exact congrArg DeformedPoint.coord hx'
  have hI : I ≤ RingHom.ker f := (Ideal.span_singleton_le_iff_mem _).mpr hgen
  let ψ : kernelCoordinateRing ℓ ζ hsplit →ₐ[A] R :=
    Ideal.Quotient.liftₐ I f (fun a ha ↦ hI ha)
  obtain ⟨e, he⟩ := kernelCoordinateRing_algEquiv_pi ℓ ζ hsplit hℓ
  refine ⟨ψ.comp e.symm.toAlgHom, ?_⟩
  have he' : e (Ideal.Quotient.mk I (coordinateGenerator (ζ - 1))) =
      fun i ↦ sigmaPoint ℓ ζ i := funext he
  rw [← he']
  change ψ (e.symm (e (Ideal.Quotient.mk I (coordinateGenerator (ζ - 1))))) = _
  rw [e.symm_apply_apply]
  rfl

private noncomputable def locallyConstantOfPiAlgHom
    {ι : Type*} [Finite ι] {A : Type*} [CommRing A]
    {R : Type*} [CommRing R] [Algebra A R]
    (φ : (ι → A) →ₐ[A] R) : LocallyConstant (PrimeSpectrum R) ι where
  toFun p := ((PrimeSpectrum.sigmaToPiHomeo (fun _ : ι ↦ A)).symm
    (PrimeSpectrum.comap φ.toRingHom p)).1
  isLocallyConstant := by
    have hfst : IsLocallyConstant (Sigma.fst : (Σ _ : ι, PrimeSpectrum A) → ι) := by
      intro t
      rw [isOpen_sigma_iff]
      intro i
      change IsOpen {x : PrimeSpectrum A | i ∈ t}
      by_cases hi : i ∈ t
      · simpa only [hi, Set.ofPred_true] using
          (isOpen_univ : IsOpen (Set.univ : Set (PrimeSpectrum A)))
      · simpa only [hi, Set.ofPred_false] using
          (isOpen_empty : IsOpen (∅ : Set (PrimeSpectrum A)))
    exact hfst.comp_continuous
      ((PrimeSpectrum.sigmaToPiHomeo (fun _ : ι ↦ A)).symm.continuous.comp
        (PrimeSpectrum.continuous_comap φ.toRingHom))

private lemma piAlgHom_sub_component_mem
    {ι : Type*} [Finite ι] {A : Type*} [CommRing A]
    {R : Type*} [CommRing R] [Algebra A R]
    (φ : (ι → A) →ₐ[A] R) (a : ι → A) (p : PrimeSpectrum R) :
    φ a - algebraMap A R (a (locallyConstantOfPiAlgHom φ p)) ∈ p.asIdeal := by
  let q := (PrimeSpectrum.sigmaToPiHomeo (fun _ : ι ↦ A)).symm
    (PrimeSpectrum.comap φ.toRingHom p)
  have hq : PrimeSpectrum.comap (Pi.evalRingHom (fun _ : ι ↦ A) q.1) q.2 =
      PrimeSpectrum.comap φ.toRingHom p :=
    (PrimeSpectrum.sigmaToPiHomeo (fun _ : ι ↦ A)).apply_symm_apply
      (PrimeSpectrum.comap φ.toRingHom p)
  have hmem : a - algebraMap A (ι → A) (a q.1) ∈
      (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : ι ↦ A) q.1) q.2).asIdeal := by
    change a q.1 - a q.1 ∈ q.2.asIdeal
    rw [sub_self]
    exact q.2.asIdeal.zero_mem
  rw [hq] at hmem
  change φ (a - algebraMap A (ι → A) (a q.1)) ∈ p.asIdeal at hmem
  change φ a - algebraMap A R (a q.1) ∈ p.asIdeal
  simpa only [map_sub, AlgHom.commutes] using hmem

private lemma exists_locallyConstant_of_isogeny_eq_zero
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type*} [CommRing R] [Algebra A R]
    (x : DeformedPoint (ζ - 1) R) (hx : isogenyOnPointsHom ℓ ζ hsplit R x = 0) :
    ∃ c : LocallyConstant (PrimeSpectrum R) (ZMod ℓ),
      ∀ p, x.coord - algebraMap A R (sigmaPoint ℓ ζ (c p)) ∈ p.asIdeal := by
  obtain ⟨φ, hφ⟩ := exists_algHom_pi_of_isogeny_eq_zero ℓ hℓ ζ hsplit x hx
  refine ⟨locallyConstantOfPiAlgHom φ, ?_⟩
  intro p
  simpa only [hφ] using piAlgHom_sub_component_mem φ (fun i ↦ sigmaPoint ℓ ζ i) p

private lemma piAlgHom_ext_of_sigmaPoint_eq
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type*} [CommRing R] [Algebra A R]
    {φ ψ : (ZMod ℓ → A) →ₐ[A] R}
    (h : φ (fun i ↦ sigmaPoint ℓ ζ i) = ψ (fun i ↦ sigmaPoint ℓ ζ i)) : φ = ψ := by
  obtain ⟨e, he⟩ := kernelCoordinateRing_algEquiv_pi ℓ ζ hsplit hℓ
  let q := Ideal.Quotient.mkₐ A
    (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))})
  have hcomp : (φ.comp e.toAlgHom).comp q = (ψ.comp e.toAlgHom).comp q := by
    apply (pointOfAlgHom_bijective (ζ - 1) R).1
    apply DeformedPoint.ext
    change φ (e (q (coordinateGenerator (ζ - 1)))) =
      ψ (e (q (coordinateGenerator (ζ - 1))))
    have he' : e (q (coordinateGenerator (ζ - 1))) = fun i ↦ sigmaPoint ℓ ζ i :=
      funext he
    simpa only [he'] using h
  ext a
  obtain ⟨b, hb⟩ := e.surjective a
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective b
  have := DFunLike.congr_fun hcomp c
  change φ (e (q c)) = ψ (e (q c)) at this
  simpa only [show q c = b from hc, hb] using this

private lemma sigmaPoint_injective
    {A : Type*} [CommRing A] [Nontrivial A]
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    Function.Injective (sigmaPoint ℓ ζ) := by
  classical
  intro i j hij
  have h : (Pi.evalAlgHom A (fun _ : ZMod ℓ ↦ A) i) =
      Pi.evalAlgHom A (fun _ : ZMod ℓ ↦ A) j :=
    piAlgHom_ext_of_sigmaPoint_eq ℓ hℓ ζ hsplit hij
  by_contra hne
  have h' := DFunLike.congr_fun h (Pi.single i 1)
  apply (one_ne_zero : (1 : A) ≠ 0)
  simpa only [Pi.evalAlgHom_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hne)] using h'

private lemma map_sigmaPoint {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    (f : A →+* R) (ℓ : ℕ) (ζ : A) (i : ZMod ℓ) :
    f (sigmaPoint ℓ ζ i) = sigmaPoint ℓ (f ζ) i := by
  simp only [sigmaPoint, map_sum, map_pow]

private lemma map_cyclotomic_splitting {A : Type*} [CommRing A]
    {R : Type*} [CommRing R] (f : A →+* R)
    (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    ∏ i : ZMod ℓ, (X - C ((f ζ) ^ i.val)) = X ^ ℓ - 1 := by
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_one, map_pow] using
    congrArg (Polynomial.map f) hsplit

private noncomputable def constantPointHom
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (ζ : A) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    (R : Type*) [CommRing R] [Algebra A R] :
    ZMod ℓ →+ DeformedPoint (ζ - 1) R :=
  (deformedPointMap (ζ - 1) (Algebra.ofId A R)).comp
    (AddMonoidHom.mk' (constantPoint ℓ ζ hζ) (constantPoint_add ℓ ζ hζ hsplit))

private lemma constantPointHom_injective
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (ζ : A) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    (R : Type*) [CommRing R] [Nontrivial R] [Algebra A R] :
    Function.Injective (constantPointHom ℓ ζ hζ hsplit R) := by
  intro i j h
  apply sigmaPoint_injective ℓ hℓ (algebraMap A R ζ)
    (map_cyclotomic_splitting (algebraMap A R) ℓ ζ hsplit)
  have := congrArg DeformedPoint.coord h
  change algebraMap A R (sigmaPoint ℓ ζ i) = algebraMap A R (sigmaPoint ℓ ζ j) at this
  simpa only [map_sigmaPoint] using this

private lemma deformedPoint_sub_congr_mod_prime
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (ζ : A) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type*} [CommRing R] [Algebra A R]
    (x y t : DeformedPoint (ζ - 1) R) (hxy : y - x = t)
    (p : PrimeSpectrum R) (i j k : ZMod ℓ)
    (hx : x.coord - algebraMap A R (sigmaPoint ℓ ζ i) ∈ p.asIdeal)
    (hy : y.coord - algebraMap A R (sigmaPoint ℓ ζ j) ∈ p.asIdeal)
    (ht : t.coord - algebraMap A R (sigmaPoint ℓ ζ k) ∈ p.asIdeal) : j - i = k := by
  let Q := R ⧸ p.asIdeal
  let φ := deformedPointMap (ζ - 1) (Ideal.Quotient.mkₐ A p.asIdeal)
  have hx' : φ x = constantPointHom ℓ ζ hζ hsplit Q i :=
    DeformedPoint.ext (Ideal.Quotient.eq.mpr hx)
  have hy' : φ y = constantPointHom ℓ ζ hζ hsplit Q j :=
    DeformedPoint.ext (Ideal.Quotient.eq.mpr hy)
  have ht' : φ t = constantPointHom ℓ ζ hζ hsplit Q k :=
    DeformedPoint.ext (Ideal.Quotient.eq.mpr ht)
  apply constantPointHom_injective ℓ hℓ ζ hζ hsplit Q
  rw [map_sub, ← hx', ← hy', ← ht', ← map_sub, hxy]

private lemma isUnit_one_add_mul_idempotent
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e)
    (π : R) (hπ : IsUnit (1 + π)) : IsUnit (1 + π * e) := by
  obtain ⟨a, ha⟩ := hπ.exists_right_inv
  apply isUnit_iff_exists_inv.mpr
  refine ⟨1 + (a - 1) * e, ?_⟩
  change e * e = e at he
  linear_combination π * (a - 1) * he + e * ha

private lemma eval_idempotent_of_eval_zero_of_eval_one
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e)
    (p : R[X]) (h₀ : p.eval 0 = 0) (h₁ : p.eval 1 = 0) : p.eval e = 0 := by
  have h : ∀ p : R[X], p.eval e = (1 - e) * p.eval 0 + e * p.eval 1 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [eval_add, hp, hq]; ring
    | monomial n a =>
      cases n with
      | zero => simp; ring
      | succ n =>
        simp only [eval_monomial, pow_succ, zero_pow (Nat.succ_ne_zero _),
          mul_zero, one_pow, mul_one, zero_add]
        have hn : e ^ (n + 1) = e := by
          induction n with
          | zero => simp
          | succ n ih => rw [pow_succ, ih, he]
        rw [← pow_succ, hn]
        ring
  rw [h, h₀, h₁, mul_zero, mul_zero, add_zero]

private lemma isogenyOnPointsHom_eq_zero_of_idempotent
    {A : Type*} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (ζ : A) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type*} [CommRing R] [Algebra A R]
    (t : DeformedPoint (ζ - 1) R) (ht : IsIdempotentElem t.coord) :
    isogenyOnPointsHom ℓ ζ hsplit R t = 0 := by
  apply DeformedPoint.ext
  change (isogenyPolynomial ℓ ζ).eval₂ (algebraMap A R) t.coord = 0
  have key (i : ZMod ℓ) : (isogenyPolynomial ℓ ζ).eval₂ (algebraMap A R)
      (algebraMap A R (constantPoint ℓ ζ hζ i).coord) = 0 := by
    have h := congrArg DeformedPoint.coord (isogenyOnPoints_constantPoint ℓ ζ hζ hsplit i)
    change (isogenyPolynomial ℓ ζ).eval₂ (algebraMap A A)
      (constantPoint ℓ ζ hζ i).coord = 0 at h
    rw [Algebra.algebraMap_self, Polynomial.eval₂_id] at h
    rw [Polynomial.eval₂_at_apply, h, map_zero]
  rw [← Polynomial.eval_map]
  apply eval_idempotent_of_eval_zero_of_eval_one ht
  · have hcoord : (constantPoint ℓ ζ hζ 0).coord = 0 := by simp [sigmaPoint]
    simpa only [eval_map, hcoord, map_zero] using key 0
  · have hcoord : (constantPoint ℓ ζ hζ 1).coord = 1 := by
      simp [sigmaPoint, ZMod.val_one'' hℓ.ne_one]
    simpa only [eval_map, hcoord, map_one] using key 1

/-- Membership in the pulled-back prime ideal transfers along an algebra map. -/
private lemma algHom_sub_mem_of_comap
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {W : Type*} [CommRing W] [Algebra R W]
    (φ : S →ₐ[R] W) (x : S) (c : R) (p : PrimeSpectrum W)
    (h : x - algebraMap R S c ∈ (PrimeSpectrum.comap φ.toRingHom p).asIdeal) :
    φ x - algebraMap R W c ∈ p.asIdeal := by
  change φ (x - algebraMap R S c) ∈ p.asIdeal at h
  simpa only [map_sub, AlgHom.commutes] using h

private lemma exists_locallyConstant_coboundary_of_binary
    {R : Type u} [CommRing R] [Nontrivial R]
    (hR : IsAbsolutelyIntegrallyClosed R)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (ζ : R) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    (f g : R) (hfg : IsCoprime f g)
    {S T W : CommAlgCat.{u} R} [IsReduced S] [IsReduced T] [IsReduced W]
    [IsLocalization.Away (f * g) W]
    {α : S ⟶ W} {β : T ⟶ W}
    (h : IsPullback (CommAlgCat.ofHom (Algebra.ofId R S))
      (CommAlgCat.ofHom (Algebra.ofId R T)) α β)
    (hf : IsUnit (algebraMap R S f)) (hg : IsUnit (algebraMap R T g))
    (τ : LocallyConstant (PrimeSpectrum W) (ZMod ℓ))
    (hτ : ∀ p, τ p = 0 ∨ τ p = 1) :
    ∃ (a : LocallyConstant (PrimeSpectrum S) (ZMod ℓ))
      (b : LocallyConstant (PrimeSpectrum T) (ZMod ℓ)),
      ∀ p, b (PrimeSpectrum.comap β.hom.toRingHom p) -
        a (PrimeSpectrum.comap α.hom.toRingHom p) = τ p := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨e, he, heτ⟩ := PrimeSpectrum.isClopen_iff.mp (τ.isLocallyConstant.isClopen_fiber 1)
  change {p | τ p = 1} = _ at heτ
  have heτ' (p : PrimeSpectrum W) : τ p = 1 ↔ e ∉ p.asIdeal := by
    change p ∈ {p | τ p = 1} ↔ _
    rw [heτ]
    rfl
  have hue : IsUnit (algebraMap R W (ζ - 1) * e + 1) := by
    rw [add_comm]
    apply isUnit_one_add_mul_idempotent he
    have hunit : IsUnit ζ := IsUnit.of_pow_eq_one hζ (NeZero.ne ℓ)
    simpa only [map_sub, map_one, add_sub_cancel] using hunit.map (algebraMap R W)
  let t : DeformedPoint (ζ - 1) W := ⟨e, hue⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_kernel_coboundary_of_idempotent hR ℓ ζ hζ hsplit
    f g hfg h hf hg t he
    (isogenyOnPointsHom_eq_zero_of_idempotent ℓ hℓ ζ hζ hsplit t he)
  obtain ⟨a, ha⟩ := exists_locallyConstant_of_isogeny_eq_zero ℓ hℓ ζ hsplit x hx
  obtain ⟨b, hb⟩ := exists_locallyConstant_of_isogeny_eq_zero ℓ hℓ ζ hsplit y hy
  refine ⟨a, b, fun p ↦ ?_⟩
  apply deformedPoint_sub_congr_mod_prime ℓ hℓ ζ hζ hsplit
    (deformedPointMap (ζ - 1) α.hom x) (deformedPointMap (ζ - 1) β.hom y)
    t hxy p
  · exact algHom_sub_mem_of_comap α.hom _ _ p (ha _)
  · exact algHom_sub_mem_of_comap β.hom _ _ p (hb _)
  · change e - algebraMap R W (sigmaPoint ℓ ζ (τ p)) ∈ p.asIdeal
    rcases hτ p with hp | hp
    · have hem : e ∈ p.asIdeal := by
        by_contra hn
        have heq := (heτ' p).mpr hn
        rw [hp] at heq
        exact zero_ne_one heq
      simpa only [hp, sigmaPoint, ZMod.val_zero, Finset.range_zero, Finset.sum_empty,
        map_zero, sub_zero] using hem
    · have hen : e ∉ p.asIdeal := (heτ' p).mp hp
      have hprod : e * (e - 1) ∈ p.asIdeal := by
        rw [mul_sub, mul_one, he, sub_self]
        exact p.asIdeal.zero_mem
      have hem := (p.isPrime.mem_or_mem hprod).resolve_left hen
      simpa only [hp, sigmaPoint, ZMod.val_one'' hℓ.ne_one, Finset.sum_range_one,
        pow_zero, map_one] using hem

private lemma exists_locallyConstant_coboundary_of_binary_coboundaries
    {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    (α : W → X) (β : W → Y) (ℓ : ℕ) [NeZero ℓ]
    (h : ∀ τ : LocallyConstant W (ZMod ℓ), (∀ p, τ p = 0 ∨ τ p = 1) →
      ∃ (a : LocallyConstant X (ZMod ℓ)) (b : LocallyConstant Y (ZMod ℓ)),
        ∀ p, b (β p) - a (α p) = τ p)
    (τ : LocallyConstant W (ZMod ℓ)) :
    ∃ (a : LocallyConstant X (ZMod ℓ)) (b : LocallyConstant Y (ZMod ℓ)),
      ∀ p, b (β p) - a (α p) = τ p := by
  classical
  let c (i : ZMod ℓ) : LocallyConstant W (ZMod ℓ) :=
    τ.map (fun j ↦ if j = i then 1 else 0)
  have hc (i : ZMod ℓ) (p : W) : c i p = 0 ∨ c i p = 1 := by
    dsimp [c, LocallyConstant.map]
    split_ifs <;> simp
  choose a b hab using fun i ↦ h (c i) (hc i)
  refine ⟨(LocallyConstant.unflip a).map (fun z ↦ ∑ i : ZMod ℓ, i * z i),
    (LocallyConstant.unflip b).map (fun z ↦ ∑ i : ZMod ℓ, i * z i), fun p ↦ ?_⟩
  change (∑ i : ZMod ℓ, i * b i (β p)) - (∑ i : ZMod ℓ, i * a i (α p)) = τ p
  simp only [← Finset.sum_sub_distrib, ← mul_sub, hab]
  change (∑ i : ZMod ℓ, i * (if τ p = i then 1 else 0)) = τ p
  simp

private lemma exists_locallyConstant_coboundary_of_cyclotomic_splitting
    {R : Type u} [CommRing R] [Nontrivial R]
    (hR : IsAbsolutelyIntegrallyClosed R)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (ζ : R) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    (f g : R) (hfg : IsCoprime f g)
    {S T W : CommAlgCat.{u} R} [IsReduced S] [IsReduced T] [IsReduced W]
    [IsLocalization.Away (f * g) W]
    {α : S ⟶ W} {β : T ⟶ W}
    (h : IsPullback (CommAlgCat.ofHom (Algebra.ofId R S))
      (CommAlgCat.ofHom (Algebra.ofId R T)) α β)
    (hf : IsUnit (algebraMap R S f)) (hg : IsUnit (algebraMap R T g))
    (τ : LocallyConstant (PrimeSpectrum W) (ZMod ℓ)) :
    ∃ (a : LocallyConstant (PrimeSpectrum S) (ZMod ℓ))
      (b : LocallyConstant (PrimeSpectrum T) (ZMod ℓ)),
      ∀ p, b (PrimeSpectrum.comap β.hom.toRingHom p) -
        a (PrimeSpectrum.comap α.hom.toRingHom p) = τ p := by
  apply exists_locallyConstant_coboundary_of_binary_coboundaries
    (PrimeSpectrum.comap α.hom.toRingHom) (PrimeSpectrum.comap β.hom.toRingHom) ℓ
      (fun τ hτ ↦ exists_locallyConstant_coboundary_of_binary hR ℓ hℓ ζ hζ hsplit
        f g hfg h hf hg τ hτ) τ

private lemma exists_cyclotomic_splitting
    {R : Type*} [CommRing R] [Nontrivial R] (hR : IsAbsolutelyIntegrallyClosed R)
    (n : ℕ) [NeZero n] :
    ∃ ζ : R, ζ ^ n = 1 ∧ ∏ i : ZMod n, (X - C (ζ ^ i.val)) = X ^ n - 1 := by
  let p := cyclotomic n ℤ
  let A := AdjoinRoot p
  let : IsDomain A := AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp
    (cyclotomic.irreducible (NeZero.pos n)))
  have hi : Function.Injective (AdjoinRoot.of p) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos (cyclotomic.monic n ℤ)
      (degree_cyclotomic_pos n ℤ (NeZero.pos n))
  let : CharZero A := ⟨fun i j h ↦ by
    apply Nat.cast_injective (R := ℤ)
    apply hi
    simpa only [map_natCast] using h⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root p) n := by
    apply (isRoot_cyclotomic_iff_charZero (NeZero.pos n)).mp
    simpa only [p, map_cyclotomic] using AdjoinRoot.isRoot_root p
  have hsplit : ∏ i : ZMod n, (X - C (AdjoinRoot.root p ^ i.val)) = X ^ n - 1 := by
    have hh := X_pow_sub_C_eq_prod hr (NeZero.pos n) (one_pow n : (1 : A) ^ n = 1)
    simp only [C_1, mul_one, Finset.prod_range] at hh
    rw [hh]
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  obtain ⟨ζ, hζ⟩ := hR.exists_root (cyclotomic n R) (cyclotomic.monic n R)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (NeZero.pos n))
  have hζ' : p.eval₂ (Int.castRingHom R) ζ = 0 := by
    rw [← eval_map]
    dsimp only [p]
    rw [map_cyclotomic]
    exact hζ
  let φ := AdjoinRoot.lift (Int.castRingHom R) ζ hζ'
  refine ⟨ζ, ?_, ?_⟩
  · simpa only [map_pow, map_one, φ, AdjoinRoot.lift_root] using congrArg φ hr.pow_eq_one
  · have hh := congrArg (Polynomial.map φ) hsplit
    simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, map_pow, Polynomial.map_pow, Polynomial.map_one,
      φ, AdjoinRoot.lift_root] using hh

private lemma exists_locallyConstant_coboundary_of_subgroup
    {X Y W G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    [AddCommGroup G] (α : C(W, X)) (β : C(W, Y)) (H : AddSubgroup G)
    (hH : ∀ τ : LocallyConstant W H,
      ∃ (a : LocallyConstant X H) (b : LocallyConstant Y H),
        ∀ p, b (β p) - a (α p) = τ p)
    (hQ : ∀ τ : LocallyConstant W (G ⧸ H),
      ∃ (a : LocallyConstant X (G ⧸ H)) (b : LocallyConstant Y (G ⧸ H)),
        ∀ p, b (β p) - a (α p) = τ p)
    (τ : LocallyConstant W G) :
    ∃ (a : LocallyConstant X G) (b : LocallyConstant Y G),
      ∀ p, b (β p) - a (α p) = τ p := by
  classical
  let q := QuotientAddGroup.mk' H
  obtain ⟨a, b, hab⟩ := hQ (τ.map q)
  let s : (G ⧸ H) → G := Function.surjInv (QuotientAddGroup.mk_surjective (s := H))
  have hs (x : G ⧸ H) : q (s x) = x := Function.surjInv_eq _ x
  let a' := a.map s
  let b' := b.map s
  let d : LocallyConstant W G := τ - (b'.comap β - a'.comap α)
  have hd (p : W) : d p ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change q (τ p - (s (b (β p)) - s (a (α p)))) = 0
    rw [map_sub, map_sub, hs, hs, hab]
    exact sub_self _
  let c : LocallyConstant W H := LocallyConstant.desc
    (fun p ↦ (⟨d p, hd p⟩ : H)) d rfl Subtype.val_injective
  obtain ⟨aH, bH, hH⟩ := hH c
  refine ⟨a' + aH.map H.subtype, b' + bH.map H.subtype, fun p ↦ ?_⟩
  have hh : (bH (β p) : G) - (aH (α p) : G) = τ p - (b' (β p) - a' (α p)) :=
    congrArg Subtype.val (hH p)
  change (b' (β p) + (bH (β p) : G)) - (a' (α p) + (aH (α p) : G)) = τ p
  calc
    _ = (b' (β p) - a' (α p)) + ((bH (β p) : G) - (aH (α p) : G)) := by abel
    _ = τ p := by rw [hh]; abel

private lemma exists_locallyConstant_coboundary_of_prime_coefficients
    {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    (α : C(W, X)) (β : C(W, Y))
    (hprime : ∀ (ℓ : ℕ), ℓ.Prime → ∀ τ : LocallyConstant W (ZMod ℓ),
      ∃ (a : LocallyConstant X (ZMod ℓ)) (b : LocallyConstant Y (ZMod ℓ)),
        ∀ p, b (β p) - a (α p) = τ p)
    (G : Type*) [AddCommGroup G] [Finite G] (τ : LocallyConstant W G) :
    ∃ (a : LocallyConstant X G) (b : LocallyConstant Y G),
      ∀ p, b (β p) - a (α p) = τ p := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    rcases subsingleton_or_nontrivial G with hG | hG
    · exact ⟨0, 0, fun _ ↦ Subsingleton.elim _ _⟩
    by_cases hsimple : ∀ H : AddSubgroup G, H = ⊥ ∨ H = ⊤
    · let : IsSimpleAddGroup G := ⟨fun H _ ↦ hsimple H⟩
      have hℓ : (Nat.card G).Prime := IsSimpleAddGroup.prime_card
      let e : ZMod (Nat.card G) ≃+ G := zmodAddCyclicAddEquiv inferInstance
      obtain ⟨a, b, hab⟩ := hprime (Nat.card G) hℓ (τ.map e.symm)
      refine ⟨a.map e, b.map e, fun p ↦ ?_⟩
      change e (b (β p)) - e (a (α p)) = τ p
      rw [← map_sub, hab]
      exact e.apply_symm_apply _
    · push Not at hsimple
      obtain ⟨H, hbot, htop⟩ := hsimple
      have hH : Nat.card H < n := by
        rw [← hn, ← Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup G) ≃+ G).toEquiv]
        exact AddSubgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr htop)
      have hQ : Nat.card (G ⧸ H) < n := by
        rw [← hn, H.card_eq_card_quotient_mul_card_addSubgroup]
        have : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hbot
        simpa only [Nat.mul_one] using
          Nat.mul_lt_mul_of_pos_left (Finite.one_lt_card (α := H))
            (Nat.card_pos (α := G ⧸ H))
      exact exists_locallyConstant_coboundary_of_subgroup α β H
        (fun τ ↦ ih (Nat.card H) hH H τ rfl)
        (fun τ ↦ ih (Nat.card (G ⧸ H)) hQ (G ⧸ H) τ rfl) τ

private lemma exists_locallyConstant_coboundary_of_isPullback
    {R : Type u} [CommRing R] [Nontrivial R]
    (hR : IsAbsolutelyIntegrallyClosed R) (f g : R) (hfg : IsCoprime f g)
    {S T W : CommAlgCat.{u} R} [IsReduced S] [IsReduced T] [IsReduced W]
    [IsLocalization.Away (f * g) W]
    {α : S ⟶ W} {β : T ⟶ W}
    (h : IsPullback (CommAlgCat.ofHom (Algebra.ofId R S))
      (CommAlgCat.ofHom (Algebra.ofId R T)) α β)
    (hf : IsUnit (algebraMap R S f)) (hg : IsUnit (algebraMap R T g))
    {M : Type*} [AddCommGroup M] [Finite M]
    (τ : LocallyConstant (PrimeSpectrum W) M) :
    ∃ (a : LocallyConstant (PrimeSpectrum S) M)
      (b : LocallyConstant (PrimeSpectrum T) M),
      ∀ p, b (PrimeSpectrum.comap β.hom.toRingHom p) -
        a (PrimeSpectrum.comap α.hom.toRingHom p) = τ p := by
  apply exists_locallyConstant_coboundary_of_prime_coefficients
    ⟨PrimeSpectrum.comap α.hom.toRingHom, PrimeSpectrum.continuous_comap _⟩
    ⟨PrimeSpectrum.comap β.hom.toRingHom, PrimeSpectrum.continuous_comap _⟩ _ M τ
  intro ℓ hℓ τ
  let : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨ζ, hζ, hsplit⟩ := exists_cyclotomic_splitting hR ℓ
  exact exists_locallyConstant_coboundary_of_cyclotomic_splitting hR ℓ hℓ ζ hζ hsplit
    f g hfg h hf hg τ

/-- Scaling `x * algebraMap (f ^ n) = algebraMap a` by `f ^ m` raises the power to `n + m`. -/
private lemma mul_algebraMap_pow_eq_of_eq_add
    {R : Type*} [CommRing R] (f : R) {S : Type*} [CommRing S] [Algebra R S]
    {x : S} {n m N : ℕ} {a : R} (h : x * algebraMap R S (f ^ n) = algebraMap R S a)
    (hN : N = n + m) : x * algebraMap R S (f ^ N) = algebraMap R S (f ^ m * a) := by
  subst hN
  simp only [pow_add, map_mul]
  rw [← mul_assoc, h]
  ring

private lemma exists_algebraMap_eq_of_coprime
    {R : Type*} [CommRing R] (f g : R) (hfg : IsCoprime f g)
    {S T W : Type*} [CommRing S] [CommRing T] [CommRing W]
    [Algebra R S] [Algebra R T] [Algebra R W]
    [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) W]
    (α : S →ₐ[R] W) (β : T →ₐ[R] W)
    (x : S) (y : T) (hxy : α x = β y) :
    ∃ r : R, algebraMap R S r = x ∧ algebraMap R T r = y := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f x
  obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj g y
  let N := n + m
  let A := f ^ m * a
  let B := g ^ n * b
  have hA : x * algebraMap R S (f ^ N) = algebraMap R S A :=
    mul_algebraMap_pow_eq_of_eq_add f (by rwa [← map_pow] at ha) rfl
  have hB : y * algebraMap R T (g ^ N) = algebraMap R T B :=
    mul_algebraMap_pow_eq_of_eq_add g (by rwa [← map_pow] at hb) (add_comm n m)
  have hAB : algebraMap R W (A * g ^ N) = algebraMap R W (B * f ^ N) := by
    have hA' := congrArg α hA
    have hB' := congrArg β hB
    simp only [map_mul, AlgHom.commutes] at hA' hB'
    simp only [map_mul] at hA' hB' ⊢
    rw [← hA', ← hB', hxy]
    ring
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (f * g) hAB
  let A' := f ^ k * A
  let B' := g ^ k * B
  let L := N + k
  have hAB' : A' * g ^ L = B' * f ^ L := by
    dsimp only [A', B', L]
    simp only [pow_add, mul_pow] at hk ⊢
    linear_combination hk
  have hA' : x * algebraMap R S (f ^ L) = algebraMap R S A' :=
    mul_algebraMap_pow_eq_of_eq_add f hA rfl
  have hB' : y * algebraMap R T (g ^ L) = algebraMap R T B' :=
    mul_algebraMap_pow_eq_of_eq_add g hB rfl
  obtain ⟨c, d, hcd⟩ := hfg.pow (m := L) (n := L)
  refine ⟨c * A' + d * B', ?_, ?_⟩
  · apply ((IsLocalization.Away.algebraMap_isUnit f (S := S)).pow L).mul_left_inj.mp
    rw [← map_pow, hA', ← map_mul]
    congr 1
    linear_combination A' * hcd - d * hAB'
  · apply ((IsLocalization.Away.algebraMap_isUnit g (S := T)).pow L).mul_left_inj.mp
    rw [← map_pow, hB', ← map_mul]
    congr 1
    linear_combination B' * hcd + c * hAB'

private lemma eq_of_algebraMap_eq_of_coprime
    {R : Type*} [CommRing R] (f g : R) (hfg : IsCoprime f g)
    {S T : Type*} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [IsLocalization.Away f S] [IsLocalization.Away g T]
    {x y : R} (hf : algebraMap R S x = algebraMap R S y)
    (hg : algebraMap R T x = algebraMap R T y) : x = y := by
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq f hf
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq g hg
  obtain ⟨c, d, hcd⟩ := hfg.pow (m := n) (n := m)
  linear_combination c * hn + d * hm - (x - y) * hcd

open CategoryTheory CategoryTheory.Limits
private lemma isPullback_of_localizationAway_of_coprime
    {R : Type u} [CommRing R] (f g : R) (hfg : IsCoprime f g)
    {S T W : CommAlgCat.{u} R}
    [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) W]
    (α : S ⟶ W) (β : T ⟶ W) :
    IsPullback (CommAlgCat.ofHom (Algebra.ofId R S))
      (CommAlgCat.ofHom (Algebra.ofId R T)) α β := by
  let F := (commAlgCatEquivUnder (.of R)).functor ⋙
    Under.forget (CommRingCat.of R) ⋙ forget CommRingCat
  have hw : CommAlgCat.ofHom (Algebra.ofId R S) ≫ α =
      CommAlgCat.ofHom (Algebra.ofId R T) ≫ β := by
    ext
  apply IsPullback.of_map F hw
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨by simpa only [← F.map_comp] using congrArg F.map hw, ?_, ?_⟩
  · intro x y hxy
    exact eq_of_algebraMap_eq_of_coprime (S := S) (T := T) f g hfg hxy.1 hxy.2
  · intro x y hxy
    exact exists_algebraMap_eq_of_coprime (S := S) (T := T) (W := W)
      f g hfg α.hom β.hom x y hxy

private lemma exists_locallyConstant_coboundary_of_localizationAway
    {R : Type u} [CommRing R] [Nontrivial R] [IsReduced R]
    (hR : IsAbsolutelyIntegrallyClosed R) (f g : R) (hfg : IsCoprime f g)
    {S T W : CommAlgCat.{u} R}
    [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) W]
    (α : S ⟶ W) (β : T ⟶ W)
    {M : Type*} [AddCommGroup M] [Finite M]
    (τ : LocallyConstant (PrimeSpectrum W) M) :
    ∃ (a : LocallyConstant (PrimeSpectrum S) M)
      (b : LocallyConstant (PrimeSpectrum T) M),
      ∀ p, b (PrimeSpectrum.comap β.hom.toRingHom p) -
        a (PrimeSpectrum.comap α.hom.toRingHom p) = τ p := by
  let : IsReduced S := isReduced_localizationPreserves (Submonoid.powers f) S inferInstance
  let : IsReduced T := isReduced_localizationPreserves (Submonoid.powers g) T inferInstance
  let : IsReduced W := isReduced_localizationPreserves (Submonoid.powers (f * g)) W inferInstance
  exact exists_locallyConstant_coboundary_of_isPullback hR f g hfg
    (isPullback_of_localizationAway_of_coprime f g hfg α β)
    (IsLocalization.Away.algebraMap_isUnit f) (IsLocalization.Away.algebraMap_isUnit g) τ

/-- Pulling back a prime along an algebra map, then along the structure map, commutes. -/
private lemma comap_comap_algebraMap {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [CommRing W] [Algebra R W]
    (φ : S →ₐ[R] W) (q : PrimeSpectrum W) :
    PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap φ.toRingHom q) =
      PrimeSpectrum.comap (algebraMap R W) q := by
  rw [← PrimeSpectrum.comap_comp_apply, AlgHom.toRingHom_eq_coe, φ.comp_algebraMap]

/-- Locally constant coboundaries transfer along compatible homeomorphisms of the three spaces. -/
private lemma exists_locallyConstant_coboundary_of_homeomorph
    {X Y W X' Y' W' M : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace W'] [AddCommGroup M]
    (ef : X' ≃ₜ X) (eg : Y' ≃ₜ Y) (efg : W' ≃ₜ W)
    {α : W → X} {β : W → Y} {α' : W' → X'} {β' : W' → Y'}
    (h : ∀ τ' : LocallyConstant W' M,
      ∃ (a : LocallyConstant X' M) (b : LocallyConstant Y' M), ∀ q, b (β' q) - a (α' q) = τ' q)
    (hα : ∀ q, ef (α' q) = α (efg q)) (hβ : ∀ q, eg (β' q) = β (efg q))
    (τ : LocallyConstant W M) :
    ∃ (a : LocallyConstant X M) (b : LocallyConstant Y M),
      ∀ p, b (β p) - a (α p) = τ p := by
  obtain ⟨a, b, hab⟩ := h (τ.comap ⟨efg, efg.continuous⟩)
  refine ⟨a.comap ⟨ef.symm, ef.symm.continuous⟩, b.comap ⟨eg.symm, eg.symm.continuous⟩, ?_⟩
  intro p
  obtain ⟨q, rfl⟩ := efg.surjective p
  change b (eg.symm _) - a (ef.symm _) = τ (efg q)
  rw [← hα, ← hβ, ef.symm_apply_apply, eg.symm_apply_apply]
  exact hab q

private noncomputable def localizationAwayHomeomorph
    {R : Type*} [CommRing R] (r : R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization.Away r S] :
    PrimeSpectrum S ≃ₜ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
  (PrimeSpectrum.localization_away_isOpenEmbedding S r).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (PrimeSpectrum.localization_away_comap_range S r))

private lemma exists_locallyConstant_coboundary_on_basicOpen_of_isReduced
    {R : Type u} [CommRing R] [IsReduced R]
    (hR : IsAbsolutelyIntegrallyClosed R) (f g : R) (hfg : IsCoprime f g)
    {M : Type*} [AddCommGroup M] [Finite M]
    (τ : LocallyConstant (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)) M) :
    ∃ (a : LocallyConstant (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) M)
      (b : LocallyConstant (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) M),
      ∀ p, b ⟨p.val, (PrimeSpectrum.basicOpen_mul f g).le p.property |>.2⟩ -
        a ⟨p.val, (PrimeSpectrum.basicOpen_mul f g).le p.property |>.1⟩ = τ p := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
    refine ⟨0, 0, fun p ↦ ?_⟩
    exact (p.val.2.ne_top (Subsingleton.elim _ _)).elim
  | inr h =>
    let S := Localization.Away f
    let T := Localization.Away g
    let W := Localization.Away (f * g)
    let α : S →ₐ[R] W :=
      ⟨IsLocalization.Away.awayToAwayRight f g, IsLocalization.Away.awayToAwayRight_eq f g⟩
    let β : T →ₐ[R] W :=
      ⟨IsLocalization.Away.awayToAwayLeft g f, IsLocalization.Away.awayToAwayLeft_eq g f⟩
    refine exists_locallyConstant_coboundary_of_homeomorph (localizationAwayHomeomorph f S)
      (localizationAwayHomeomorph g T) (localizationAwayHomeomorph (f * g) W)
      (fun τ' ↦ exists_locallyConstant_coboundary_of_localizationAway hR f g hfg
        (S := CommAlgCat.of R S) (T := CommAlgCat.of R T) (W := CommAlgCat.of R W)
        (CommAlgCat.ofHom α) (CommAlgCat.ofHom β) τ')
      (fun q ↦ ?_) (fun q ↦ ?_) τ
    · exact Subtype.ext (comap_comap_algebraMap α q)
    · exact Subtype.ext (comap_comap_algebraMap β q)

private lemma exists_locallyConstant_coboundary_on_basicOpen
    {R : Type u} [CommRing R]
    (hR : IsAbsolutelyIntegrallyClosed R) (f g : R) (hfg : IsCoprime f g)
    {M : Type*} [AddCommGroup M] [Finite M]
    (τ : LocallyConstant (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)) M) :
    ∃ (a : LocallyConstant (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) M)
      (b : LocallyConstant (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) M),
      ∀ p, b ⟨p.val, (PrimeSpectrum.basicOpen_mul f g).le p.property |>.2⟩ -
        a ⟨p.val, (PrimeSpectrum.basicOpen_mul f g).le p.property |>.1⟩ = τ p := by
  let R' := R ⧸ nilradical R
  let : IsReduced R' := (Ideal.isRadical_iff_quotient_reduced _).mp
    (show (nilradical R).IsRadical from Ideal.radical_isRadical ⊥)
  let ρ := Ideal.Quotient.mk (nilradical R)
  let e : PrimeSpectrum R' ≃ₜ PrimeSpectrum R :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective
      R' ρ Ideal.Quotient.mk_surjective).toIsEmbedding.toHomeomorphOfSurjective
      (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).surjective
  let ef : (PrimeSpectrum.basicOpen (ρ f) : Set (PrimeSpectrum R')) ≃ₜ
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := e.sets rfl
  let eg : (PrimeSpectrum.basicOpen (ρ g) : Set (PrimeSpectrum R')) ≃ₜ
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := e.sets rfl
  let efg : (PrimeSpectrum.basicOpen (ρ f * ρ g) : Set (PrimeSpectrum R')) ≃ₜ
      (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)) := e.sets (by
        change (PrimeSpectrum.basicOpen (ρ f * ρ g) : Set (PrimeSpectrum R')) =
          PrimeSpectrum.basicOpen (ρ (f * g))
        rw [map_mul])
  exact exists_locallyConstant_coboundary_of_homeomorph ef eg efg
    (fun τ' ↦ exists_locallyConstant_coboundary_on_basicOpen_of_isReduced
      (isAbsolutelyIntegrallyClosed_quotient R (nilradical R) hR)
      (ρ f) (ρ g) (hfg.map ρ) τ')
    (fun q ↦ rfl) (fun q ↦ rfl) τ

private noncomputable def localizationAwayBasicHomeomorph
    {R : Type u} [CommRing R] (h f : R) :
    (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away h) f) :
        Set (PrimeSpectrum (Localization.Away h))) ≃ₜ
      (PrimeSpectrum.basicOpen (f * h) : Set (PrimeSpectrum R)) := by
  let e := localizationAwayHomeomorph h (Localization.Away h)
  refine
    { toFun := fun p ↦ ⟨(e p.val).val, ?_⟩
      invFun := fun p ↦ ⟨e.symm ⟨p.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rw [PrimeSpectrum.basicOpen_mul]
    exact ⟨p.property, (e p.val).property⟩
  · exact ((PrimeSpectrum.basicOpen_mul f h).le p.property).2
  · change (e (e.symm ⟨p.val, _⟩)).val ∈ PrimeSpectrum.basicOpen f
    rw [e.apply_symm_apply]
    exact ((PrimeSpectrum.basicOpen_mul f h).le p.property).1
  · exact fun p ↦ Subtype.ext (e.symm_apply_apply p.val)
  · intro p
    apply Subtype.ext
    change (e (e.symm ⟨p.val, _⟩)).val = p.val
    exact congrArg Subtype.val (e.apply_symm_apply ⟨p.val, _⟩)
  · exact (e.continuous.comp continuous_subtype_val).subtype_val.subtype_mk _
  · exact (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- Let `R` be an absolutely integrally closed ring, `f g : R` and `M` a finite abelian group.
Every locally constant `M`-valued function `τ` on `D(f(f + g) · g(f + g))` is `b - a` on that
overlap, for a locally constant `M`-valued function `a` on `D(f(f + g))` and `b` on
`D(g(f + g))`. -/
public lemma exists_locallyConstant_coboundary_on_basicOpen_sum
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R) (f g : R)
    {M : Type*} [AddCommGroup M] [Finite M]
    (τ : LocallyConstant
      (PrimeSpectrum.basicOpen ((f * (f + g)) * (g * (f + g))) : Set (PrimeSpectrum R)) M) :
    ∃ (a : LocallyConstant (PrimeSpectrum.basicOpen (f * (f + g)) : Set (PrimeSpectrum R)) M)
      (b : LocallyConstant (PrimeSpectrum.basicOpen (g * (f + g)) : Set (PrimeSpectrum R)) M),
      ∀ p, b ⟨p.val, (PrimeSpectrum.basicOpen_mul _ _).le p.property |>.2⟩ -
        a ⟨p.val, (PrimeSpectrum.basicOpen_mul _ _).le p.property |>.1⟩ = τ p := by
  let R' := Localization.Away (f + g)
  let ρ := algebraMap R R'
  have hfg : IsCoprime (ρ f) (ρ g) := by
    obtain ⟨z, hz⟩ := IsLocalization.Away.algebraMap_isUnit (S := R') (f + g)
    refine ⟨↑z⁻¹, ↑z⁻¹, ?_⟩
    rw [← mul_add, ← map_add, ← hz, Units.inv_mul]
  let ef := localizationAwayBasicHomeomorph (f + g) f
  let eg := localizationAwayBasicHomeomorph (f + g) g
  let efg : (PrimeSpectrum.basicOpen (ρ f * ρ g) : Set (PrimeSpectrum R')) ≃ₜ
      (PrimeSpectrum.basicOpen ((f * (f + g)) * (g * (f + g))) : Set (PrimeSpectrum R)) :=
    (Homeomorph.setCongr (by rw [← map_mul])).trans
      ((localizationAwayBasicHomeomorph (f + g) (f * g)).trans
        (Homeomorph.setCongr (by simp only [PrimeSpectrum.basicOpen_mul,
          TopologicalSpace.Opens.coe_inf]; ext p; simp only [Set.mem_inter_iff]; tauto)))
  exact exists_locallyConstant_coboundary_of_homeomorph ef eg efg
    (fun τ' ↦ exists_locallyConstant_coboundary_on_basicOpen
      (isAbsolutelyIntegrallyClosed_localization R (Submonoid.powers (f + g)) R' hR)
      (ρ f) (ρ g) hfg τ')
    (fun q ↦ rfl) (fun q ↦ rfl) τ

end Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.LocallyConstantCoboundary

end
