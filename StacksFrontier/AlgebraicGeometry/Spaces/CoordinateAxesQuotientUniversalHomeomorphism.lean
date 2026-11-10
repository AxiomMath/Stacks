module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.CoordinateAxesQuotientIsoAwayFromOrigin

/-!
# The coordinate-axes quotient is universally homeomorphic to the affine line

Let `k` be a field, `U = Spec (k[x, y]/(xy))`, `R = Δ(U) ⨿ Δ'(U ∖ {0_U})` and `X = U/R`.
**Stacks 0ENU** asserts that the morphism `X ⟶ 𝔸¹_k` descended from `(x, y) ↦ x + y` is a
universal homeomorphism. This file proves it, by the criterion
`AlgebraicGeometry.Space.universalHomeomorphism_of_universallyInjective_of_universallyClosed`.

## Main results

* `AlgebraicGeometry.CoordinateAxesQuotient.isIntegralHom_coordinateSumMap`: the sum map
  `U ⟶ 𝔸¹_k` is integral, since `x` and `y` are roots of `T² - (x + y) T`.
* `AlgebraicGeometry.CoordinateAxesQuotient.isSurjective_sumMap`,
  `AlgebraicGeometry.CoordinateAxesQuotient.universallyClosed_sumMap` and
  `AlgebraicGeometry.CoordinateAxesQuotient.universallyInjective_sumMap`: the three inputs of
  the criterion.
* `AlgebraicGeometry.CoordinateAxesQuotient.universalHomeomorphism_sumMap`: **Stacks 0ENU**,
  `X ⟶ 𝔸¹_k` is a universal homeomorphism.

## Implementation notes

Universal injectivity is tested on field-valued points by
`AlgebraicGeometry.Space.universallyInjective_of_fieldPoints`. Over a field two points of `U`
with the same coordinate sum `s` have the same image in `X`: if `s` is invertible both have the
image of `(s, 0)` by
`AlgebraicGeometry.CoordinateAxesQuotient.toQuotientSheaf_eq_axesPoint_sum`, and if `s = 0`
then both coordinates of each point vanish, as `x² = x (x + y) - xy`. No hypothesis on the
characteristic is used.

## References

* [Stacks Project, Tag 0ENU](https://stacks.math.columbia.edu/tag/0ENU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedChangeOfRings

universe u

namespace AlgebraicGeometry.CoordinateAxesQuotient

open AffineLineInvolution

/-! ### Integrality of the sum map -/

section Integral

variable (S : Setup.{u})

/-- The `k`-algebra map `k[t] → k[x, y]/(xy)`, `t ↦ x + y`. -/
noncomputable def sumAlgHom : MvPolynomial PUnit.{u + 1} S.k →ₐ[S.k] NodalRing S.k :=
  MvPolynomial.aeval (fun _ => xClass S.k + yClass S.k)

/-- `t ↦ x + y` makes `k[x, y]/(xy)` integral over `k[t]`: `x` and `y` are roots of the monic
polynomial `T² - t T`, because `xy = 0`, and they generate. -/
theorem sumAlgHom_isIntegral : (sumAlgHom S).toRingHom.IsIntegral := by
  let R := MvPolynomial PUnit.{u + 1} S.k
  let N := NodalRing S.k
  let φ : R →+* N := (sumAlgHom S).toRingHom
  let _ : Algebra R N := φ.toAlgebra
  have hφ : algebraMap R N = φ := rfl
  let t : R := MvPolynomial.X PUnit.unit
  have hφt : φ t = xClass S.k + yClass S.k := MvPolynomial.aeval_X _ _
  have hxy : xClass S.k * yClass S.k = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hmonic : (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X : Polynomial R).Monic :=
    (Polynomial.monic_X_pow 2).sub_of_left (by
      refine (Polynomial.degree_C_mul_X_le t).trans_lt ?_
      rw [Polynomial.degree_X_pow]
      exact_mod_cast one_lt_two)
  have hroot (z : N) (hz : z * z = z * φ t) : _root_.IsIntegral R z := by
    refine ⟨_, hmonic, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, sub_eq_zero, pow_two, hz, mul_comm]
    rfl
  have hx : _root_.IsIntegral R (xClass S.k) :=
    hroot _ (by rw [hφt, mul_add, hxy, add_zero])
  have hy : _root_.IsIntegral R (yClass S.k) :=
    hroot _ (by rw [hφt, mul_add, mul_comm (yClass S.k) (xClass S.k), hxy, zero_add])
  let A : Subalgebra R N := Algebra.adjoin R {xClass S.k, yClass S.k}
  have htop : A = ⊤ := by
    refine top_unique fun z hz => ?_
    clear hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C r =>
        have hC : Ideal.Quotient.mk (nodalRelationIdeal S.k) (MvPolynomial.C r) =
            algebraMap R N (MvPolynomial.C r) := by
          rw [hφ]
          change _ = MvPolynomial.aeval _ (MvPolynomial.C r)
          rw [MvPolynomial.aeval_C]
          rfl
        rw [hC]
        exact A.algebraMap_mem _
    | add p q hp hq =>
        rw [map_add]
        exact A.add_mem hp hq
    | mul_X p i hp =>
        rw [map_mul]
        refine A.mul_mem hp (Algebra.subset_adjoin ?_)
        cases i
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hA : Algebra.IsIntegral R A :=
    Algebra.IsIntegral.adjoin (fun z hz => by
      rcases hz with rfl | hz
      · exact hx
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hy)
  have htopI : Algebra.IsIntegral R (⊤ : Subalgebra R N) := htop ▸ hA
  have hAI : Algebra.IsIntegral R N :=
    (Subalgebra.topEquiv (R := R) (A := N)).isIntegral_iff.mp htopI
  exact algebraMap_isIntegral_iff.mpr hAI

/-- The sum map `U ⟶ 𝔸¹_k` is the spectrum of `t ↦ x + y`, read through the identification of
`𝔸¹_k` with the spectrum of the polynomial ring. -/
theorem coordinateSumMap_left_eq :
    (coordinateSumMap S).left = Spec.map (CommRingCat.ofHom (sumAlgHom S).toRingHom) ≫
      (AffineSpace.SpecIso PUnit.{u + 1} (.of S.k)).inv := by
  refine (AffineSpace.hom_ext ?_ ?_).symm
  · rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    change _ = AffineSpace.homOfVector (baseMap S) _ ≫ _
    rw [AffineSpace.homOfVector_over, baseMap]
    refine congrArg Spec.map ?_
    ext r
    change sumAlgHom S (MvPolynomial.C r) = algebraMap S.k (NodalRing S.k) r
    exact MvPolynomial.aeval_C _ r
  · intro i
    cases i
    change (Spec.map (CommRingCat.ofHom (sumAlgHom S).toRingHom)).appTop
        ((AffineSpace.SpecIso PUnit.{u + 1} (.of S.k)).inv.appTop
          (AffineSpace.coord _ PUnit.unit)) =
      (AffineSpace.homOfVector (baseMap S) _).appTop (AffineSpace.coord _ PUnit.unit)
    rw [AffineSpace.SpecIso_inv_appTop_coord, AffineSpace.homOfVector_appTop_coord,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (sumAlgHom S (MvPolynomial.X _)) = _
    rw [sumAlgHom, MvPolynomial.aeval_X,
      RingHom.map_add (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv.hom]
    rfl

/-- The sum map `U ⟶ 𝔸¹_k` is an integral morphism of schemes. -/
instance isIntegralHom_coordinateSumMap : IsIntegralHom (coordinateSumMap S).left := by
  rw [coordinateSumMap_left_eq]
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (sumAlgHom S).toRingHom)) :=
    IsIntegralHom.SpecMap_iff.mpr (sumAlgHom_isIntegral S)
  infer_instance

end Integral

/-! ### The descended sum map -/

variable (B : BigFppfSite.{u}) (S : Setup.{u}) (hS : B.Contains (Spec (.of S.k)))

/-- The sum map as a morphism of charts in the site. -/
noncomputable def sumChart : axesChart S B hS ⟶ affineLineChart S.k B hS :=
  Over.homMk (ObjectProperty.homMk (coordinateSumMap S).left)
    (by apply ObjectProperty.hom_ext; exact (coordinateSumMap S).w)

/-- Pushing `sumChart` forward along the inclusion of the site into schemes over `B` recovers
the sum map `coordinateSumMap`. -/
theorem post_map_sumChart :
    (Over.post (X := B.obj hS) B.inclusion).map (sumChart B S hS) = coordinateSumMap S := by
  apply Over.OverMorphism.ext
  rfl

/-- The functor of points of the coordinate axes is an algebraic space, being represented by
the chart `AlgebraicGeometry.CoordinateAxesQuotient.axesChart`. -/
theorem isAlgebraicSpace_points_axes :
    IsAlgebraicSpace B (Spec (.of S.k)) hS
      (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (axesOver S)) :=
  AlgebraicGeometry.isAlgebraicSpace_of_iso B (Spec (.of S.k)) hS
    (Space.pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) (axesChart S B hS))
    (isAlgebraicSpace_yoneda B (Spec (.of S.k)) hS (axesChart S B hS))

variable [HasSheafify (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u)]

/-- The projection from the chart of the coordinate axes to the quotient sheaf is locally
surjective. -/
private theorem isLocallySurjective_toQuotientSheaf :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of S.k)) hS)
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)) :=
  Stacks.Groupoids.toQuotientSheaf_isLocallySurjective _ _ _

/-- The projection `U ⟶ X` is surjective on points: it is locally surjective by construction
of the quotient sheaf. -/
theorem isSurjective_quotientMap :
    Space.IsSurjective B (Spec (.of S.k)) hS (quotientMap S B hS) :=
  Space.surjective_pointsMap_of_isLocallySurjective B (Spec (.of S.k)) hS _
    (isLocallySurjective_toQuotientSheaf B S hS)

/-- The sum map `X ⟶ 𝔸¹_k` is surjective: already its composite with `U ⟶ X` is surjective on
`T`-points, through the first axis. -/
theorem isSurjective_sumMap :
    Space.IsSurjective B (Spec (.of S.k)) hS (sumMap S B hS) := by
  have hcomp : Function.Surjective (Space.pointsMap B (Spec (.of S.k)) hS _
      (quotientMap S B hS ≫ sumMap S B hS)) := by
    rw [quotientMap_comp_sumMap]
    exact Space.surjective_pointsMap_of_isLocallySurjective B (Spec (.of S.k)) hS _
      (Presheaf.isLocallySurjective_of_surjective _ _ (fun T t =>
        ⟨_, axesPoint_coord_zero_comp_coordinateSumMap S t⟩))
  rw [Space.pointsMap_comp] at hcomp
  exact hcomp.of_comp

/-- The composite `U ⟶ X ⟶ 𝔸¹_k` is universally closed: it is the morphism of represented
presheaves induced by the integral morphism `(x, y) ↦ x + y`. -/
theorem universallyClosed_quotientMap_comp_sumMap :
    Space.UniversallyClosed B (Spec (.of S.k)) hS (quotientMap S B hS ≫ sumMap S B hS) := by
  let F := Over.post (X := B.obj hS) B.inclusion
  have hU := isAlgebraicSpace_points_axes B S hS
  have hA := Space.isAlgebraicSpace_points_affineLine B S.k hS
  let eU : Stacks.Groupoids.points F (axesOver S) ≅ yoneda.obj (axesChart S B hS) :=
    Space.pointsYonedaIso F (axesChart S B hS)
  let eA : Stacks.Groupoids.points F (affineLine S.k) ≅ yoneda.obj (affineLineChart S.k B hS) :=
    Space.pointsYonedaIso F (affineLineChart S.k B hS)
  have hfac : quotientMap S B hS ≫ sumMap S B hS =
      eU.hom ≫ yoneda.map (sumChart B S hS) ≫ eA.inv := by
    rw [quotientMap_comp_sumMap]
    rw [← cancel_epi eU.inv, Iso.inv_hom_id_assoc]
    ext X y
    change F.map y ≫ coordinateSumMap S = F.map (y ≫ sumChart B S hS)
    rw [Functor.map_comp, post_map_sumChart]
    rfl
  rw [hfac]
  have hsq : AlgebraicGeometry.UniversallyClosed
      ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).map (sumChart B S hS)) := by
    change AlgebraicGeometry.UniversallyClosed (coordinateSumMap S).left
    infer_instance
  have hyon := (Space.presheaf_yoneda_map_iff B (Spec (.of S.k)) hS
    AlgebraicGeometry.universallyClosed_isStableUnderBaseChange (sumChart B S hS)).mpr hsq
  have hprop := MorphismProperty.RespectsIso.precomp _ eU.hom _
    (MorphismProperty.RespectsIso.postcomp _ eA.inv _ hyon)
  exact (Space.presheaf_universallyClosed_iff B (Spec (.of S.k)) hS hU hA hprop.rep).mp hprop

/-- The sum map `X ⟶ 𝔸¹_k` is universally closed, because its composite with the surjection
`U ⟶ X` is. -/
theorem universallyClosed_sumMap :
    Space.UniversallyClosed B (Spec (.of S.k)) hS (sumMap S B hS) :=
  Space.universallyClosed_of_comp_of_isSurjective B (Spec (.of S.k)) hS
    (isAlgebraicSpace_points_axes B S hS) (isAlgebraicSpace_quotientSpace S B hS)
    (Space.isAlgebraicSpace_points_affineLine B S.k hS) _ (sumMap S B hS)
    (isSurjective_quotientMap B S hS) (universallyClosed_quotientMap_comp_sumMap B S hS)

/-- Over a test object all of whose global functions are zero or units — the spectrum of a
field — two points of `U` with the same coordinate sum have the same image in `X`. -/
theorem quotientMap_eq_of_sum_eq (T : BigFppfOver B (Spec (.of S.k)) hS)
    (hT : ∀ z : Γ(((Over.post (X := B.obj hS) B.inclusion).obj T).left, ⊤), z = 0 ∨ IsUnit z)
    (a b : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ axesOver S)
    (h : a ≫ coordinateSumMap S = b ≫ coordinateSumMap S) :
    (quotientMap S B hS).app (Opposite.op T) a = (quotientMap S B hS).app (Opposite.op T) b := by
  have hsum : a.left.appTop (xSection S) + a.left.appTop (ySection S) =
      b.left.appTop (xSection S) + b.left.appTop (ySection S) := by
    rw [← comp_coordinateSumMap_coord, ← comp_coordinateSumMap_coord, h]
  have hzero : ∀ c : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ axesOver S,
      c.left.appTop (xSection S) + c.left.appTop (ySection S) = 0 →
      c.left.appTop (xSection S) = 0 ∧ c.left.appTop (ySection S) = 0 := by
    intro c hc
    have hp := appTop_xSection_mul_appTop_ySection S c
    have hx2 : c.left.appTop (xSection S) * c.left.appTop (xSection S) = 0 := by
      have e : c.left.appTop (xSection S) * c.left.appTop (xSection S) =
          c.left.appTop (xSection S) * (c.left.appTop (xSection S) + c.left.appTop (ySection S)) -
            c.left.appTop (xSection S) * c.left.appTop (ySection S) := by ring
      rw [e, hc, hp, mul_zero, sub_zero]
    have hx : c.left.appTop (xSection S) = 0 := by
      rcases hT (c.left.appTop (xSection S)) with h0 | hu
      · exact h0
      · have h0 : IsUnit (0 : Γ(((Over.post (X := B.obj hS) B.inclusion).obj T).left, ⊤)) :=
          hx2 ▸ hu.mul hu
        have := isUnit_zero_iff.mp h0
        exact (mul_one _).symm.trans (by rw [← this, mul_zero])
    exact ⟨hx, by rw [hx, zero_add] at hc; exact hc⟩
  rcases hT (a.left.appTop (xSection S) + a.left.appTop (ySection S)) with h0 | hu
  · obtain ⟨ha₁, ha₂⟩ := hzero a h0
    obtain ⟨hb₁, hb₂⟩ := hzero b (hsum ▸ h0)
    congr 1
    exact axes_hom_ext S (ha₁.trans hb₁.symm) (ha₂.trans hb₂.symm)
  · rw [toQuotientSheaf_eq_axesPoint_sum B S hS T a hu,
      toQuotientSheaf_eq_axesPoint_sum B S hS T b (hsum ▸ hu)]
    congr 1
    exact axes_hom_ext S (by rw [axesPoint_xSection, axesPoint_xSection, hsum])
      (by rw [axesPoint_ySection, axesPoint_ySection])

/-- The sum map `X ⟶ 𝔸¹_k` is universally injective.

Universal injectivity is tested on field-valued points: two field-valued points of `X` lift,
after one field extension each, to points of `U`, and two points of `U` over a field with the
same coordinate sum have the same image in `X`. -/
theorem universallyInjective_sumMap :
    Space.UniversallyInjective B (Spec (.of S.k)) hS (sumMap S B hS) := by
  refine Space.universallyInjective_of_fieldPoints B (Spec (.of S.k)) hS _ ?_
  intro p y h
  change (sumMap S B hS).app
      (Opposite.op (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS))) p.value =
    (sumMap S B hS).app
      (Opposite.op (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS))) y at h
  obtain ⟨L₁, hL₁f, hL₁, s₁, c₁, v₁, hv₁⟩ :=
    Space.exists_fieldSpec_lift_of_isLocallySurjective B (Spec (.of S.k)) hS _
      (isLocallySurjective_toQuotientSheaf B S hS)
      p.carrier p.contained p.toBase p.value
  obtain ⟨L₂, hL₂f, hL₂, s₂, c₂, v₂, hv₂⟩ :=
    Space.exists_fieldSpec_lift_of_isLocallySurjective B (Spec (.of S.k)) hS _
      (isLocallySurjective_toQuotientSheaf B S hS)
      L₁ hL₁ s₁ ((quotientSpace S B hS).obj.map c₁.op y)
  let T₂ : BigFppfOver B (Spec (.of S.k)) hS := Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hS)
  set t₁ : (Over.post (X := B.obj hS) B.inclusion).obj T₂ ⟶ axesOver S :=
    (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (axesOver S)).map
      c₂.op v₁ with ht₁
  have hp : (quotientSpace S B hS).obj.map (c₂ ≫ c₁).op p.value =
      (quotientMap S B hS).app (Opposite.op T₂) t₁ := by
    rw [ht₁, NatTrans.naturality_apply (quotientMap S B hS) c₂.op v₁, hv₁,
      op_comp, CategoryTheory.Functor.map_comp]
    rfl
  have hy : (quotientSpace S B hS).obj.map (c₂ ≫ c₁).op y =
      (quotientMap S B hS).app (Opposite.op T₂) v₂ := by
    rw [op_comp, CategoryTheory.Functor.map_comp]
    exact hv₂.symm
  have hsum : t₁ ≫ coordinateSumMap S = v₂ ≫ coordinateSumMap S := by
    rw [← sumMap_app_quotientMap S B hS T₂ t₁, ← sumMap_app_quotientMap S B hS T₂ v₂, ← hp, ← hy,
      NatTrans.naturality_apply (sumMap S B hS) (c₂ ≫ c₁).op p.value,
      NatTrans.naturality_apply (sumMap S B hS) (c₂ ≫ c₁).op y, h]
  have hfield : ∀ z : Γ(Spec (.of L₂), ⊤), z = 0 ∨ IsUnit z := by
    intro z
    rcases eq_or_ne z 0 with hz | hz
    · exact Or.inl hz
    · refine Or.inr ?_
      have hne : (Scheme.ΓSpecIso (.of L₂)).commRingCatIsoToRingEquiv z ≠ 0 := fun h0 ↦
        hz ((Scheme.ΓSpecIso (.of L₂)).commRingCatIsoToRingEquiv.injective
          (h0.trans (map_zero _).symm))
      simpa using (isUnit_iff_ne_zero.mpr hne).map
        (Scheme.ΓSpecIso (.of L₂)).commRingCatIsoToRingEquiv.symm
  have hclass := quotientMap_eq_of_sum_eq B S hS T₂ hfield t₁ v₂ hsum
  exact ⟨{ carrier := L₂
           field := hL₂f
           contained := hL₂
           toBase := s₂
           value := (quotientSpace S B hS).obj.map (c₂ ≫ c₁).op p.value }, c₂ ≫ c₁, rfl,
    hy.trans (hclass.symm.trans hp.symm)⟩

/-- **Stacks 0ENU.** The morphism `X ⟶ 𝔸¹_k` descended from `(x, y) ↦ x + y` is a universal
homeomorphism: it is universally injective, universally closed and surjective. No hypothesis
on the field is needed. -/
theorem universalHomeomorphism_sumMap :
    Space.UniversalHomeomorphism B (Spec (.of S.k)) hS (sumMap S B hS) :=
  Space.universalHomeomorphism_of_universallyInjective_of_universallyClosed B (Spec (.of S.k)) hS
    (isAlgebraicSpace_quotientSpace S B hS)
    (Space.isAlgebraicSpace_points_affineLine B S.k hS)
    (universallyInjective_sumMap B S hS) (universallyClosed_sumMap B S hS)
    (isSurjective_sumMap B S hS)

end AlgebraicGeometry.CoordinateAxesQuotient

end
