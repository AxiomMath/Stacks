module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.Ring
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Connected generic fibres over a discrete valuation ring

A flat scheme over the spectrum of a discrete valuation ring is connected on the generic fibre
when its total space is connected and its closed fibre is reduced.

## Main results

* `AlgebraicGeometry.connectedSpace_fiber_bot_of_isReduced_fiber_closedPoint` proves that the
  generic fibre is connected under the stated hypotheses.

## Implementation notes

For the prime spectrum of a discrete valuation ring, the bottom point is its generic point and
`IsLocalRing.closedPoint R` is its unique closed point. The order-top point of the scheme
`Spec R` is instead its generic point, so the closed fibre must be specified using
`IsLocalRing.closedPoint R` explicitly.

The proof extends idempotents from the localization away from a uniformizer, using reducedness
modulo the uniformizer to lower denominators. On affine charts this makes closures of clopen
subsets of the generic fibre clopen; connectedness of the total space then gives connectedness
of the fibre.

## References

* [Stacks Project, Tag 055J](https://stacks.math.columbia.edu/tag/055J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- Reducedness modulo a nonzerodivisor lets us remove every denominator from an
idempotent in the localization. -/
private lemma lift_idempotent {A : Type u} [CommRing A] (r : A)
    (hr : r ∈ nonZeroDivisors A) [_root_.IsReduced (A ⧸ Ideal.span {r})]
    {B : Type v} [CommRing B] [Algebra A B] [IsLocalization.Away r B]
    (e : B) (he : IsIdempotentElem e) :
    ∃ a : A, IsIdempotentElem a ∧ algebraMap A B a = e := by
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B (Submonoid.powers_le.mpr hr)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r e
  induction n generalizing a with
  | zero =>
    rw [pow_zero, mul_one] at ha
    refine ⟨a, ?_, ha.symm⟩
    apply hinj
    simpa only [map_mul, ← ha] using he.eq
  | succ n ih =>
    have haa : a * a = r ^ (n + 1) * a := by
      apply hinj
      simp only [map_mul, map_pow, ← ha]
      calc
        (e * algebraMap A B r ^ (n + 1)) * (e * algebraMap A B r ^ (n + 1)) =
            (e * e) * algebraMap A B r ^ (n + 1) * algebraMap A B r ^ (n + 1) := by ring
        _ = algebraMap A B r ^ (n + 1) * (e * algebraMap A B r ^ (n + 1)) := by rw [he]; ring
    have hqa : Ideal.Quotient.mk (Ideal.span {r}) a = 0 := by
      refine IsNilpotent.eq_zero ⟨2, ?_⟩
      rw [pow_two, ← map_mul, haa, map_mul, map_pow]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self r)]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hqa)
    refine ih b ((IsLocalization.Away.algebraMap_isUnit (S := B) r).mul_right_cancel ?_)
    rw [mul_assoc, ← pow_succ, ha, hb, map_mul, mul_comm]

private lemma closure_image_of_preimage {T : Type*} {S : Type*}
    [TopologicalSpace T] [TopologicalSpace S] (g : T → S) (hg : DenseRange g)
    {s : Set T} {t : Set S} (ht : IsClopen t) (h : g ⁻¹' t = s) :
    closure (g '' s) = t := by
  rw [← h, Set.image_preimage_eq_inter_range]
  exact subset_antisymm (closure_minimal Set.inter_subset_left ht.isClosed)
    (fun x hx ↦ ht.isOpen.inter_closure ⟨hx, hg x⟩)

/-- Inverting a nonzerodivisor gives a dense range on prime spectra. -/
private lemma denseRange_comap_away {A : Type u} [CommRing A] {r : A}
    (hr : r ∈ nonZeroDivisors A) :
    DenseRange (PrimeSpectrum.comap (algebraMap A (Localization.Away r))) := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective _ (Submonoid.powers_le.mpr hr))]
  exact bot_le

private lemma isClopen_closure_image_comap {A : Type u} [CommRing A] (r : A)
    (hr : r ∈ nonZeroDivisors A) [_root_.IsReduced (A ⧸ Ideal.span {r})]
    {s : Set (PrimeSpectrum (Localization.Away r))} (hs : IsClopen s) :
    IsClopen (closure (PrimeSpectrum.comap (algebraMap A (Localization.Away r)) '' s)) := by
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  obtain ⟨a, ha, hea⟩ := lift_idempotent r hr e he
  have hc : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨a, ha, rfl⟩
  rwa [closure_image_of_preimage _ (denseRange_comap_away hr) hc (by
    change (PrimeSpectrum.basicOpen (algebraMap A (Localization.Away r) a) :
      Set (PrimeSpectrum (Localization.Away r))) = _
    rw [hea])]

open scoped TensorProduct

private lemma reduced_quotient_of_reduced_fiber
    {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    [IsReduced ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
      (IsLocalRing.closedPoint R))] :
    _root_.IsReduced (A ⧸ Ideal.span {algebraMap R A π}) := by
  let m := IsLocalRing.maximalIdeal R
  let e : (Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
      (IsLocalRing.closedPoint R) ≅ Spec (.of (m.Fiber A)) :=
    Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R A (IsLocalRing.closedPoint R))
  have : IsReduced (Spec (.of (m.Fiber A))) :=
    @isReduced_of_isOpenImmersion _ _ e.inv (IsOpenImmersion.of_isIso _) inferInstance
  have : _root_.IsReduced (m.Fiber A) := (affine_isReduced_iff (.of (m.Fiber A))).mp inferInstance
  let k : (R ⧸ m) ≃ₐ[R] m.ResidueField := AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField m)
  let l : A ⊗[R] (R ⧸ m) ≃ₐ[R] m.Fiber A :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A)) k).trans
      (Algebra.TensorProduct.comm R A m.ResidueField)
  have : _root_.IsReduced (A ⧸ m.map (algebraMap R A)) := isReduced_of_injective
    (l.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).toRingEquiv.toRingHom)
    (l.injective.comp (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).injective)
  have hm : m.map (algebraMap R A) = Ideal.span {algebraMap R A π} := by
    dsimp [m]
    rw [hπ, Ideal.map_span, Set.image_singleton]
  rwa [hm] at this

private lemma basicOpen_uniformizer {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R)) =
      {⟨⊥, inferInstance⟩} := by
  ext x
  change π ∉ x.asIdeal ↔ x = ⟨⊥, inferInstance⟩
  constructor
  · intro hx
    apply PrimeSpectrum.ext
    by_contra h
    obtain ⟨m, hm, huniq⟩ :=
      (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance |>.2
    have heq : x.asIdeal = IsLocalRing.maximalIdeal R :=
      (huniq _ ⟨h, x.isPrime⟩).trans
        (huniq _ ⟨IsDiscreteValuationRing.not_a_field R, inferInstance⟩).symm
    apply hx
    rw [heq, hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  · rintro rfl
    exact hπ.ne_zero

/-- The same equality with both sides read as subsets of the underlying space of the scheme
`Spec R`. It is stated separately because the identification of the points of `Spec R` with
`PrimeSpectrum R` is not a reducible unfolding, so a rewrite with the previous lemma does not
fire against a goal phrased on the scheme. -/
private lemma coe_basicOpen_uniformizer {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    ((PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R)) :
        Set ↥(Spec (CommRingCat.of R))) = {⟨⊥, inferInstance⟩} :=
  basicOpen_uniformizer hπ

/-- On each affine chart the generic fibre is dense, and the closure of each
clopen subset of the generic fibre is clopen. -/
private lemma affine_generic_closure
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))]
    (j : Spec A ⟶ X) [IsOpenImmersion j] :
    let U := f ⁻¹' ({⟨⊥, inferInstance⟩} : Set ↥(Spec (CommRingCat.of R)))
    Dense (j ⁻¹' U) ∧ ∀ s : Set U, IsClopen s →
      IsClopen (j ⁻¹' closure (Subtype.val '' s)) := by
  dsimp only
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  let : Algebra R ↥A := φ.hom.toAlgebra
  have : Module.Flat R ↥A := (RingHom.flat_algebraMap_iff).mp
    (Flat.SpecMap_iff.mp (by rw [hφ]; infer_instance))
  have hr : algebraMap R ↥A π ∈ nonZeroDivisors ↥A := by
    rw [mem_nonZeroDivisors_iff_left]; intro a ha
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero)
    simpa [Algebra.smul_def] using ha
  have : IsReduced ((Spec.map (CommRingCat.ofHom (algebraMap R ↥A))).fiber
      (IsLocalRing.closedPoint R)) := by
    change IsReduced ((Spec.map φ).fiber _); rw [hφ]
    exact isReduced_fiber_comp j f _
  have : _root_.IsReduced (↥A ⧸ Ideal.span {algebraMap R ↥A π}) :=
    reduced_quotient_of_reduced_fiber π hπ.maximalIdeal_eq
  let B : CommRingCat.{u} := CommRingCat.of <| Localization.Away (algebraMap R ↥A π)
  let g : PrimeSpectrum ↥B → PrimeSpectrum ↥A := PrimeSpectrum.comap (algebraMap ↥A ↥B)
  let U : Set X := f ⁻¹' ({⟨⊥, inferInstance⟩} : Set ↥(Spec (CommRingCat.of R)))
  have hgj : Set.range g = j ⁻¹' U := by
    rw [PrimeSpectrum.localization_away_comap_range ↥B (algebraMap R ↥A π)]
    dsimp only [U]; rw [← Set.preimage_comp]
    change _ = (j ≫ f) ⁻¹' _
    rw [← hφ]
    refine Eq.trans ?_
      (congrArg (Set.preimage ⇑(Spec.map φ)) (coe_basicOpen_uniformizer hπ))
    rfl
  refine ⟨hgj ▸ denseRange_comap_away hr, ?_⟩
  intro s hs
  let q : PrimeSpectrum B → U := fun z ↦
    ⟨j (g z), show g z ∈ j ⁻¹' U from hgj ▸ Set.mem_range_self z⟩
  have hq : Continuous q :=
    (j.continuous.comp (PrimeSpectrum.localization_away_isOpenEmbedding ↥B
      (algebraMap R ↥A π)).continuous).subtype_mk _
  have heq : j ⁻¹' (Subtype.val '' s) = g '' (q ⁻¹' s) := by
    ext x; constructor
    · rintro ⟨y, hy, hxy⟩
      have hx : x ∈ j ⁻¹' U := by
        change j x ∈ U; rw [← hxy]; exact y.property
      obtain ⟨z, rfl⟩ := hgj.symm ▸ hx
      refine ⟨z, ?_, rfl⟩
      have : q z = y := Subtype.ext hxy.symm
      simpa only [Set.mem_preimage, this] using hy
    · rintro ⟨z, hz, rfl⟩; exact ⟨q z, hz, rfl⟩
  rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous, heq]
  exact isClopen_closure_image_comap _ hr (hs.preimage hq)

/-- **Stacks Project, Tag 055J.** A flat degeneration of a disconnected scheme
is either disconnected or nonreduced: if a flat scheme over a discrete
valuation ring is connected and its closed fibre is reduced, then its generic
fibre is connected. -/
@[stacks 055J, ega "IV 15.5.6" "more general", ega "IV 18.9.7" "special case"]
theorem connectedSpace_fiber_bot_of_isReduced_fiber_closedPoint
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] [ConnectedSpace X]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    ConnectedSpace (f.fiber (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) := by
  let U : Set X := f ⁻¹' ({⟨⊥, inferInstance⟩} : Set ↥(Spec (CommRingCat.of R)))
  have H (i : X.affineOpenCover.I₀) := affine_generic_closure f (X.affineOpenCover.f i)
  have hd : Dense U := by
    intro x
    obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    exact (X.affineCover.f i).continuous.closure_preimage_subset U ((H i).1 y)
  have : ConnectedSpace U := by
    refine connectedSpace_iff_clopen.mpr ⟨hd.nonempty.to_subtype, fun s hs ↦ ?_⟩
    have hc : IsClopen (closure (Subtype.val '' s) : Set X) := by
      refine ⟨isClosed_closure, ?_⟩
      rw [X.affineCover.isOpenCover_opensRange.isOpen_iff_inter]
      intro i
      rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
      exact (X.affineCover.f i).isOpenEmbedding.isOpenMap _ ((H i).2 s hs).isOpen
    have heq : Subtype.val ⁻¹' closure (Subtype.val '' s) = s := by
      rw [← IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hs.isClosed.closure_eq]
    rcases isClopen_iff.mp hc with h | h
    · left
      rw [← heq, h]
      rfl
    · right
      rw [← heq, h]
      rfl
  exact (f.fiberHomeo _).connectedSpace_iff.mpr inferInstance

end AlgebraicGeometry

end
