module

public import StacksFrontier.Examples.Scheme.PuncturedAxes

/-!
# Negating one of the coordinate axes

Over a field `k`, let `A k` be the coordinate ring of the countable union of coordinate axes
through a common origin, that is the quotient of `k[x₀, x₁, …]` by the products `xᵢxⱼ` of
distinct variables (`Stacks.Examples.puncturedAxisRing`). Reversing the sign of a single
coordinate `xᵢ` and fixing the others preserves those relations, so it is an involutive
automorphism of `A k` — on `Spec(A k)` it is the reflection of the `i`-th axis in the origin.

Away from characteristic two the reflection has no fixed point on the punctured `i`-th axis
`D(xᵢ)`: a point fixed by it would have `xᵢ = -xᵢ` and `xᵢ` invertible. This file records
that in the scheme-theoretic form needed to make the graph of the reflection, restricted to
`D(xᵢ)`, one summand of an étale equivalence relation on `Spec(A k)`: every morphism from a
scheme `T` to `D(xᵢ)` which is equalized by the inclusion and by the inclusion followed by
the reflection has `T` empty.

## Main definitions

* `Stacks.Examples.axisNeg`: the automorphism of the coordinate ring reversing the sign of
  one coordinate.
* `Stacks.Examples.axesScheme`: the union of the coordinate axes as a scheme.
* `Stacks.Examples.axisOpen`: the punctured `i`-th axis, the basic open of the `i`-th
  coordinate.
* `Stacks.Examples.axesReflection`: the reflection of the `i`-th axis, as an automorphism of
  `Stacks.Examples.axesScheme`.
* `Stacks.Examples.axisOpenReflection`: its restriction to the punctured `i`-th axis.
* `Stacks.Examples.axesOriginPoint`: the origin as a `k`-point of
  `Stacks.Examples.axesScheme`.

## Main results

* `Stacks.Examples.axisNeg_involutive` and `Stacks.Examples.axesReflection_comp_self`: the
  reflection is an involution, on the ring and on the scheme.
* `Stacks.Examples.axisAugmentation_axisNeg`: the reflection fixes the origin.
* `Stacks.Examples.isEmpty_of_eq_comp_axesReflection`: away from characteristic two the
  reflection has no fixed point on the punctured `i`-th axis.

## Implementation notes

The reflection is produced by lifting the corresponding automorphism of the polynomial ring
through the quotient, so all its values on the generators are computed by
`Stacks.Examples.axisNeg_mk`. Involutivity is checked on generators by the induction
principle of `MvPolynomial`.

Freeness on the punctured axis is phrased for an arbitrary test scheme rather than for
points, because that is the form in which it feeds the monomorphism condition of an internal
equivalence relation. The argument is that the coordinate `xᵢ`, pulled back to `T`, is both
invertible — `T` maps into the basic open of `xᵢ` — and equal to its own negative, so `2` is
a zero divisor on `Γ(T, ⊤)`; as `2` is invertible in `k` and hence in `Γ(T, ⊤)`, the
coordinate pulls back to `0`, and the basic open it cuts out is both everything and nothing.

## References

* [Stacks Project, Tag 086H](https://stacks.math.columbia.edu/tag/086H)
* [Stacks Project, Tag 087I](https://stacks.math.columbia.edu/tag/087I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Examples

/-! ### The reflection on the coordinate ring -/

/-- The automorphism of `k[x₀, x₁, …]` reversing the sign of the `i`-th variable. -/
noncomputable def axisNegPolynomial (k : Type u) [CommRing k] (i : ℕ) :
    MvPolynomial ℕ k →+* MvPolynomial ℕ k :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    fun j => if j = i then -MvPolynomial.X j else MvPolynomial.X j

/-- Reversing the sign of the `i`-th variable negates it and fixes the other variables. -/
private theorem axisNegPolynomial_X (k : Type u) [CommRing k] (i j : ℕ) :
    axisNegPolynomial k i (MvPolynomial.X j) =
      if j = i then -MvPolynomial.X j else MvPolynomial.X j := by
  simp [axisNegPolynomial]

/-- Reversing the sign of a variable fixes the constants. -/
@[simp]
theorem axisNegPolynomial_C (k : Type u) [CommRing k] (i : ℕ) (a : k) :
    axisNegPolynomial k i (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [axisNegPolynomial]

/-- Reversing the sign of the `i`-th variable negates that variable. -/
@[simp]
theorem axisNegPolynomial_X_self (k : Type u) [CommRing k] (i : ℕ) :
    axisNegPolynomial k i (MvPolynomial.X i) = -MvPolynomial.X i := by
  simp [axisNegPolynomial]

/-- Reversing the sign of the `i`-th variable fixes every other variable. -/
@[simp]
theorem axisNegPolynomial_X_of_ne (k : Type u) [CommRing k] {i j : ℕ} (h : j ≠ i) :
    axisNegPolynomial k i (MvPolynomial.X j) = MvPolynomial.X j := by
  simp [axisNegPolynomial, h]

/-- Reversing the sign of the `i`-th coordinate twice is the identity on the polynomial
ring. -/
theorem axisNegPolynomial_axisNegPolynomial (k : Type u) [CommRing k] (i : ℕ)
    (f : MvPolynomial ℕ k) :
    axisNegPolynomial k i (axisNegPolynomial k i f) = f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | mul_X f j hf =>
      rw [map_mul, map_mul, hf, axisNegPolynomial_X]
      split_ifs with hj <;> simp [hj]

/-- Reversing the sign of one coordinate does not change the value at the origin: every
variable is evaluated at zero, and so is its negative. -/
theorem eval_zero_axisNegPolynomial (k : Type u) [CommRing k] (i : ℕ)
    (f : MvPolynomial ℕ k) :
    MvPolynomial.eval 0 (axisNegPolynomial k i f) = MvPolynomial.eval 0 f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
      have hzero : MvPolynomial.eval (0 : ℕ → k)
          (axisNegPolynomial k i (MvPolynomial.X j)) = 0 := by
        rw [axisNegPolynomial_X]
        split_ifs <;> simp
      rw [map_mul, map_mul, map_mul, hzero]
      simp

/-- Reversing the sign of one coordinate preserves the relations between the axes: the image
of a product of two distinct variables is that product up to sign. -/
theorem axisRelations_le_ker_axisNeg (k : Type u) [CommRing k] (i : ℕ) :
    axisRelations k ≤ RingHom.ker ((axisQuotientMap k).comp (axisNegPolynomial k i)) := by
  apply Ideal.span_le.2
  rintro _ ⟨a, b, hab, rfl⟩
  have h : axisQuotientMap k (MvPolynomial.X a) * axisQuotientMap k (MvPolynomial.X b) = 0 :=
    axisQuotientMap_X_mul_X k hab
  simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, map_mul]
  rw [axisNegPolynomial_X, axisNegPolynomial_X]
  split_ifs <;> simp [h]

/-- The endomorphism of the coordinate ring of the union of the axes reversing the sign of
the `i`-th coordinate. Geometrically it is the reflection of the `i`-th axis in the origin,
fixing every other axis. -/
noncomputable def axisNeg (k : Type u) [CommRing k] (i : ℕ) :
    puncturedAxisRing k →+* puncturedAxisRing k :=
  Ideal.Quotient.lift (axisRelations k) ((axisQuotientMap k).comp (axisNegPolynomial k i))
    fun _ hf => RingHom.mem_ker.mp (axisRelations_le_ker_axisNeg k i hf)

/-- On the class of a polynomial, `axisNeg` is induced by `axisNegPolynomial`. -/
@[simp]
theorem axisNeg_mk (k : Type u) [CommRing k] (i : ℕ) (f : MvPolynomial ℕ k) :
    axisNeg k i (axisQuotientMap k f) = axisQuotientMap k (axisNegPolynomial k i f) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The reflection of the `i`-th axis negates the `i`-th coordinate. -/
@[simp]
theorem axisNeg_apply_X_self (k : Type u) [CommRing k] (i : ℕ) :
    axisNeg k i (axisQuotientMap k (MvPolynomial.X i)) =
      -axisQuotientMap k (MvPolynomial.X i) := by
  simp

/-- The reflection of the `i`-th axis fixes every other coordinate. -/
@[simp]
theorem axisNeg_apply_X_of_ne (k : Type u) [CommRing k] {i j : ℕ} (h : j ≠ i) :
    axisNeg k i (axisQuotientMap k (MvPolynomial.X j)) =
      axisQuotientMap k (MvPolynomial.X j) := by
  simp [axisNegPolynomial_X_of_ne k h]

/-- The reflection of one axis is an involution of the coordinate ring. -/
theorem axisNeg_involutive (k : Type u) [CommRing k] (i : ℕ) :
    Function.Involutive (axisNeg k i) := by
  intro a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [axisNeg_mk, axisNeg_mk, axisNegPolynomial_axisNegPolynomial]

/-- The reflection of one axis fixes the origin: evaluating all coordinates at zero does not
see a sign. -/
theorem axisAugmentation_axisNeg (k : Type u) [CommRing k] (i : ℕ)
    (a : puncturedAxisRing k) :
    axisAugmentation k (axisNeg k i a) = axisAugmentation k a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [axisNeg_mk, axisAugmentation_mk, axisAugmentation_mk, eval_zero_axisNegPolynomial]

/-- The reflection of one axis, as a ring automorphism. -/
noncomputable def axisNegEquiv (k : Type u) [CommRing k] (i : ℕ) :
    puncturedAxisRing k ≃+* puncturedAxisRing k :=
  RingEquiv.ofBijective (axisNeg k i) (axisNeg_involutive k i).bijective

/-- The ring automorphism `axisNegEquiv` acts as `axisNeg`. -/
@[simp]
theorem axisNegEquiv_apply (k : Type u) [CommRing k] (i : ℕ) (a : puncturedAxisRing k) :
    axisNegEquiv k i a = axisNeg k i a := rfl

/-! ### The union of the axes as a scheme -/

/-- The countable union of coordinate axes through a common origin, as an affine scheme. -/
noncomputable abbrev axesScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of (puncturedAxisRing k))

/-- The punctured `i`-th coordinate axis: the basic open of the `i`-th coordinate, which on
the union of the axes is the `i`-th axis with the origin removed. -/
noncomputable def axisOpen (k : Type u) [CommRing k] (i : ℕ) : (axesScheme k).Opens :=
  PrimeSpectrum.basicOpen (axisQuotientMap k (MvPolynomial.X i))

/-- The punctured `i`-th axis is quasi-compact, being a basic open of an affine scheme. -/
theorem compactSpace_axisOpen (k : Type u) [CommRing k] (i : ℕ) :
    CompactSpace (axisOpen k i).toScheme :=
  isCompact_iff_compactSpace.mp
    (PrimeSpectrum.isCompact_basicOpen (axisQuotientMap k (MvPolynomial.X i)))

/-- The reflection of the `i`-th axis in the origin, as an endomorphism of the union of the
axes. -/
noncomputable def axesReflection (k : Type u) [CommRing k] (i : ℕ) :
    axesScheme k ⟶ axesScheme k :=
  Spec.map (CommRingCat.ofHom (axisNegEquiv k i).toRingHom)

/-- The reflection of one axis is an involution of the union of the axes. -/
theorem axesReflection_comp_self (k : Type u) [CommRing k] (i : ℕ) :
    axesReflection k i ≫ axesReflection k i = 𝟙 (axesScheme k) := by
  rw [axesReflection, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact axisNeg_involutive k i a

/-- The reflection of one axis is an automorphism of the union of the axes. -/
noncomputable def axesReflectionIso (k : Type u) [CommRing k] (i : ℕ) :
    axesScheme k ≅ axesScheme k where
  hom := axesReflection k i
  inv := axesReflection k i
  hom_inv_id := axesReflection_comp_self k i
  inv_hom_id := axesReflection_comp_self k i

/-- The reflection of one axis is an isomorphism of schemes. -/
instance isIso_axesReflection (k : Type u) [CommRing k] (i : ℕ) :
    IsIso (axesReflection k i) :=
  (axesReflectionIso k i).isIso_hom

/-- The reflection of the `i`-th axis preserves the punctured `i`-th axis: it changes the
sign of the `i`-th coordinate, which does not change whether that coordinate vanishes. -/
theorem axesReflection_preimage_axisOpen (k : Type u) [CommRing k] (i : ℕ) :
    axesReflection k i ⁻¹ᵁ axisOpen k i = axisOpen k i := by
  ext p
  show axisNeg k i (axisQuotientMap k (MvPolynomial.X i)) ∉ p.asIdeal ↔
    axisQuotientMap k (MvPolynomial.X i) ∉ p.asIdeal
  rw [axisNeg_apply_X_self]
  simp

/-- The reflection of the `i`-th axis, restricted to the punctured `i`-th axis. -/
noncomputable def axisOpenReflection (k : Type u) [CommRing k] (i : ℕ) :
    (axisOpen k i).toScheme ⟶ (axisOpen k i).toScheme :=
  (axesReflection k i).resLE (axisOpen k i) (axisOpen k i)
    (by rw [axesReflection_preimage_axisOpen])

/-- Restricting the reflection to the punctured `i`-th axis commutes with the inclusion. -/
theorem axisOpenReflection_comp_ι (k : Type u) [CommRing k] (i : ℕ) :
    axisOpenReflection k i ≫ (axisOpen k i).ι =
      (axisOpen k i).ι ≫ axesReflection k i :=
  Scheme.Hom.resLE_comp_ι _ _

/-! ### The reflection is free on the punctured axis -/

/-- **The reflection of the `i`-th axis has no fixed point on the punctured `i`-th axis**,
away from characteristic two: a scheme mapping to the punctured axis and equalized by the
inclusion and by the inclusion followed by the reflection is empty.

On such a scheme `T` the pullback `r` of the `i`-th coordinate is invertible, because `T`
maps into the basic open of that coordinate, and satisfies `r = -r`; since `2` is a unit of
`Γ(T, ⊤)` this forces `r = 0`, so the basic open of `r` is at once the whole of `T` and
empty. -/
theorem isEmpty_of_eq_comp_axesReflection (k : Type u) [Field k] [NeZero (2 : k)] (i : ℕ)
    {T : Scheme.{u}} (f : T ⟶ (axisOpen k i).toScheme)
    (h : f ≫ (axisOpen k i).ι = f ≫ (axisOpen k i).ι ≫ axesReflection k i) :
    IsEmpty T := by
  set e := Scheme.ΓSpecIso (.of (puncturedAxisRing k)) with he
  set r := e.inv (axisQuotientMap k (MvPolynomial.X i)) with hr
  set g := f ≫ (axisOpen k i).ι with hg
  have hneg : (axesReflection k i).appTop r = -r := by
    have hnat := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (axisNegEquiv k i).toRingHom)
    have hh := congrArg (fun t => t (axisQuotientMap k (MvPolynomial.X i))) hnat
    change e.inv (axisNeg k i (axisQuotientMap k (MvPolynomial.X i))) =
      (axesReflection k i).appTop r at hh
    rw [axisNeg_apply_X_self, map_neg] at hh
    exact hh.symm
  have hself : g.appTop r = -g.appTop r := by
    have hh := congrArg (fun t : T ⟶ axesScheme k => t.appTop r) h
    simpa only [hg, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hneg, map_neg] using hh
  have htwo : IsUnit (2 : Γ(T, ⊤)) := by
    have hc : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (NeZero.ne (2 : k))
    simpa only [map_ofNat] using
      hc.map (g.appTop.hom.comp (e.inv.hom.comp ((axisQuotientMap k).comp MvPolynomial.C)))
  have hzero : g.appTop r = 0 := by
    refine (htwo.mul_right_eq_zero).mp ?_
    calc (2 : Γ(T, ⊤)) * g.appTop r = g.appTop r + g.appTop r := two_mul _
      _ = 0 := add_eq_zero_iff_eq_neg.mpr hself
  have hpre : g ⁻¹ᵁ axisOpen k i = ⊤ := by
    ext x
    exact iff_true_intro (f x).property
  have htop : T.basicOpen (g.appTop r) = ⊤ := by
    rw [← Scheme.preimage_basicOpen_top]
    show g ⁻¹ᵁ (axesScheme k).basicOpen
      (e.inv (axisQuotientMap k (MvPolynomial.X i))) = ⊤
    rw [basicOpen_eq_of_affine]
    exact hpre
  rw [hzero, Scheme.basicOpen_zero] at htop
  refine ⟨fun x => ?_⟩
  have hx : x ∈ (⊥ : T.Opens) := by rw [htop]; trivial
  simp at hx

/-! ### The origin as a point of the union of the axes -/

/-- The origin of the union of the axes, as a `k`-point: the morphism `Spec k ⟶ Spec(A k)`
given by evaluating every coordinate at zero. -/
noncomputable def axesOriginPoint (k : Type u) [CommRing k] :
    Spec (.of k) ⟶ axesScheme k :=
  Spec.map (CommRingCat.ofHom (axisAugmentation k))

/-- The origin `k`-point hits the origin. -/
theorem axesOriginPoint_closedPoint (k : Type u) [Field k] :
    axesOriginPoint k (IsLocalRing.closedPoint k) = axisOrigin k := by
  refine PrimeSpectrum.ext ?_
  ext a
  show axisAugmentation k a ∈ IsLocalRing.maximalIdeal k ↔ axisAugmentation k a = 0
  simp [IsLocalRing.maximalIdeal_eq_bot]

/-- The reflection of any axis fixes the origin `k`-point. -/
theorem axesOriginPoint_comp_axesReflection (k : Type u) [CommRing k] (i : ℕ) :
    axesOriginPoint k ≫ axesReflection k i = axesOriginPoint k := by
  rw [axesOriginPoint, axesReflection, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact axisAugmentation_axisNeg k i a

/-- The origin is a closed point of the union of the axes. -/
theorem isClosed_axisOrigin (k : Type u) [Field k] :
    IsClosed ({axisOrigin k} : Set (PrimeSpectrum (puncturedAxisRing k))) := by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact axisAugmentation_ker_isMaximal k

end Stacks.Examples

end
