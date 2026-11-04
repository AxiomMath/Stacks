module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup
import all StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup

/-!
# The exceptional divisor on a chart of the blowup of a regular local surface

Let `R` be a regular local ring of dimension two with maximal ideal `𝔪 = (x, y)`. The presentation
`R[𝔪/x] ≅ R[T₀]/(x T₀ - y)` of the affine blowup chart also describes the exceptional divisor on
that chart, cut out by `x`.

## Main results

* `Stacks.Blowup.isDomain_quotient_affineBlowupAlgebraAway`: `R[𝔪/x]/x R[𝔪/x] ≅ κ[T₀]` is a
  domain, so the exceptional divisor is irreducible on the chart at `x`.
* `Stacks.Blowup.isRegularRing_quotient_affineBlowupAlgebraAway`: that quotient is a regular ring.
* `Stacks.Blowup.isPrime_span_algebraMap_affineBlowupAlgebraAway`: equivalently `x R[𝔪/x]` is
  prime.
* `Stacks.Blowup.notMem_span_algebraMap_of_algebraMap_mul_eq`: the fraction `y / x` is not in
  `x R[𝔪/x]`, so the generic point of the exceptional divisor on the chart at `x` lies on the chart
  at `y` as well.

## References

* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite IsLocalRing

universe u

namespace Stacks.Blowup

section Chart

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (x y : R)

/-- **The relation of the presentation, together with the denominator, generates the maximal
ideal.** Modulo `x T₀ - y` the two ideals `(x)` and `(x, y) = 𝔪` of `R[T₀]` agree, because `y`
is `x T₀` there. This is the computation that makes the chart's fibre over the closed point a
polynomial ring over the residue field. -/
private lemma relation_sup_span_C_eq_map_C
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    Ideal.span ({MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y} :
        Set (MvPolynomial (Fin 1) R)) ⊔
      Ideal.span {(MvPolynomial.C x : MvPolynomial (Fin 1) R)} =
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R) (maximalIdeal R) := by
  rw [← hxy, Ideal.map_span, ← Ideal.span_union]
  have himg : (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R) '' ({x, y} : Set R) =
      {MvPolynomial.C x, MvPolynomial.C y} := by simp
  rw [himg]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro p (hp | hp)
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact Ideal.mem_span_pair.mpr ⟨MvPolynomial.X 0, -1, by ring⟩
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
  · rintro p hp
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact Ideal.subset_span (Or.inr (Set.mem_singleton _))
    · exact Ideal.mem_span_pair.mpr ⟨-1, MvPolynomial.X 0, by ring⟩

omit [IsRegularLocalRing R] in
/-- **The denominator generates, on the presented chart, the image of `(x) ⊆ R[T₀]`.** -/
private lemma span_algebraMap_eq_map_mk :
    Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x} =
      Ideal.map (Ideal.Quotient.mk (Ideal.span
          {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}))
        (Ideal.span {(MvPolynomial.C x : MvPolynomial (Fin 1) R)}) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- **Modulo the denominator, the presented chart is a polynomial ring in one variable over the
residue field.** -/
private def presentedQuotientEquiv
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    ((MvPolynomial (Fin 1) R ⧸
          Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) ⧸
        Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
          Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x}) ≃+*
      MvPolynomial (Fin 1) (R ⧸ maximalIdeal R) :=
  (Ideal.quotEquivOfEq (span_algebraMap_eq_map_mk x y)).trans
    ((DoubleQuot.quotQuotEquivQuotSup
          (Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y})
          (Ideal.span {(MvPolynomial.C x : MvPolynomial (Fin 1) R)})).trans
      ((Ideal.quotEquivOfEq ((relation_sup_span_C_eq_map_C x y hxy).trans
            (ker_mvPolynomialMap (maximalIdeal R) (Fin 1)).symm)).trans
        (RingHom.quotientKerEquivOfSurjective
          (MvPolynomial.map_surjective (Ideal.Quotient.mk (maximalIdeal R))
            Ideal.Quotient.mk_surjective))))

/-- **Modulo the denominator, the presented chart is a domain** — a polynomial ring in one
variable over the residue field. -/
private lemma isDomain_quotient_presented
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    IsDomain ((MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) ⧸
      Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x}) := by
  have : (maximalIdeal R).IsMaximal := maximalIdeal.isMaximal R
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  exact MulEquiv.isDomain _ (presentedQuotientEquiv x y hxy).toMulEquiv

/-- **A two-element generating family of the maximal ideal of a two-dimensional regular local
ring is a regular sequence.** The maximal ideal needs two generators, so the family is minimal;
this is [Stacks, Tag 00NQ]. -/
private lemma isRegular_pair_of_span_eq (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    RingTheory.Sequence.IsRegular R [x, y] := by
  have hsf : (maximalIdeal R).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at h
    exact_mod_cast h
  have hofList : Ideal.ofList [x, y] = maximalIdeal R := by
    rw [← hxy, Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil]
    simp [Ideal.span_insert]
  exact ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    R).1 [x, y] hofList (by simp [hsf])).1

/-- The first member of a two-element regular sequence is nonzero. -/
private lemma ne_zero_of_isRegular_pair (hreg : RingTheory.Sequence.IsRegular R [x, y]) :
    x ≠ 0 := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  rintro rfl
  have h := hreg
  rw [RingTheory.Sequence.isRegular_cons_iff] at h
  exact one_ne_zero (h.1 (show (0 : R) • (1 : R) = (0 : R) • (0 : R) by simp))

/-! ### The exceptional equation on the chart -/

/-- The ideal of the presented chart generated by the denominator is the image of the ideal of
the chart generated by it. -/
private lemma map_span_algebraMap_chart_algEquiv
    (e : affineBlowupAlgebraAway (maximalIdeal R) x ≃ₐ[R]
      MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) :
    Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x} =
      Ideal.map (e.toRingEquiv : affineBlowupAlgebraAway (maximalIdeal R) x →+* _)
        (Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
          Set (affineBlowupAlgebraAway (maximalIdeal R) x))) := by
  have hcomm : (e.toRingEquiv : affineBlowupAlgebraAway (maximalIdeal R) x →+* _)
        (algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x) =
      algebraMap R (MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x :=
    e.commutes x
  rw [Ideal.map_span, Set.image_singleton, hcomm]

/-- The quotient of the chart by its denominator is isomorphic to the quotient of the presented
chart by its denominator. -/
private lemma nonempty_quotient_ringEquiv_presented (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    Nonempty (affineBlowupAlgebraAway (maximalIdeal R) x ⧸
      Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
        Set (affineBlowupAlgebraAway (maximalIdeal R) x)) ≃+*
      ((MvPolynomial (Fin 1) R ⧸
          Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) ⧸
        Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
          Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x})) := by
  obtain ⟨e⟩ := exists_chart_algEquiv x y (isRegular_pair_of_span_eq x y hdim hxy) hxy
  exact ⟨Ideal.quotientEquiv _ _ e.toRingEquiv (map_span_algebraMap_chart_algEquiv x y e)⟩

/-- **Modulo its denominator, the affine blowup chart of a two-dimensional regular local ring at
a minimal generator `x` of its maximal ideal is a domain.** A second generator `y` presents the
chart as `R[T₀]/(x T₀ - y)`, in which the denominator cuts out the polynomial ring `κ[T₀]` over
the residue field.

This is the ring-level statement that the exceptional divisor of the blowup of a regular surface
at its closed point is irreducible on each of the two standard charts: by
`AlgebraicGeometry.Stacks.BlowUpChartCover.ideal_exceptionalIdeal_eq_span_chartGenerator` the
exceptional ideal is generated on the chart at `x` by the pullback of `x`. -/
public theorem isDomain_quotient_affineBlowupAlgebraAway (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    IsDomain (affineBlowupAlgebraAway (maximalIdeal R) x ⧸
      Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
        Set (affineBlowupAlgebraAway (maximalIdeal R) x))) := by
  obtain ⟨f⟩ := nonempty_quotient_ringEquiv_presented x y hdim hxy
  have := isDomain_quotient_presented x y hxy
  exact MulEquiv.isDomain _ f.toMulEquiv

/-- **Modulo its denominator, the affine blowup chart of a two-dimensional regular local ring at
a minimal generator `x` of its maximal ideal is a regular ring.** A second generator `y` presents
the chart as `R[T₀]/(x T₀ - y)`, in which the denominator cuts out the polynomial ring `κ[T₀]`
over the residue field, and a polynomial ring over a field is regular.

This is the ring-level statement that the exceptional divisor of the blowup of a regular surface
at its closed point is *regular* on each of the two standard charts, which is strictly more than
the domain property `Stacks.Blowup.isDomain_quotient_affineBlowupAlgebraAway` reads off the same
presentation. -/
public theorem isRegularRing_quotient_affineBlowupAlgebraAway (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    IsRegularRing (affineBlowupAlgebraAway (maximalIdeal R) x ⧸
      Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
        Set (affineBlowupAlgebraAway (maximalIdeal R) x))) := by
  obtain ⟨f⟩ := nonempty_quotient_ringEquiv_presented x y hdim hxy
  have := isRegularRing_quotient_presented x y hxy
  exact IsRegularRing.of_ringEquiv f.symm

/-- **The denominator generates a prime ideal of the affine blowup chart.** The exceptional
divisor is therefore irreducible on the chart, with generic point that prime. -/
public theorem isPrime_span_algebraMap_affineBlowupAlgebraAway (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    (Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
      Set (affineBlowupAlgebraAway (maximalIdeal R) x))).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp
    (isDomain_quotient_affineBlowupAlgebraAway x y hdim hxy)

/-- **The ratio of the two generators is not in the exceptional ideal of the chart.** An element
`u` of `R[𝔪/x]` with `x u = y` — the fraction `y / x`, which is the inverse of the coordinate of
the *other* standard chart — does not lie in `x · R[𝔪/x]`.

On the presentation `R[T₀]/(x T₀ - y)` such a `u` is forced to be `T₀`, the denominator being a
nonzerodivisor; and `T₀` lies in `(x T₀ - y, x) = 𝔪 · R[T₀]` only if its coefficient `1` lies in
`𝔪`.

Together with `isPrime_span_algebraMap_affineBlowupAlgebraAway` this says that the prime
`x · R[𝔪/x]` — the generic point of the exceptional divisor on the chart at `x` — lies in the
chart at `y` as well: the two charts of the exceptional divisor meet. -/
public theorem notMem_span_algebraMap_of_algebraMap_mul_eq (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R)
    (u : affineBlowupAlgebraAway (maximalIdeal R) x)
    (hu : algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x * u =
      algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) y) :
    u ∉ Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
      Set (affineBlowupAlgebraAway (maximalIdeal R) x)) := by
  classical
  have hxne : x ≠ 0 := ne_zero_of_isRegular_pair x y (isRegular_pair_of_span_eq x y hdim hxy)
  have hdomB : IsDomain (affineBlowupAlgebraAway (maximalIdeal R) x) :=
    isDomain_affineBlowupAlgebraAway x hxne
  obtain ⟨e⟩ := exists_chart_algEquiv x y (isRegular_pair_of_span_eq x y hdim hxy) hxy
  -- the class of the variable in the presentation
  set T : MvPolynomial (Fin 1) R ⧸
      Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y} :=
    Ideal.Quotient.mk _ (MvPolynomial.X (0 : Fin 1)) with hTdef
  have hTrel : algebraMap R (MvPolynomial (Fin 1) R ⧸
      Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x * T =
      algebraMap R (MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) y := by
    rw [hTdef, show algebraMap R (MvPolynomial (Fin 1) R ⧸ Ideal.span
        {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x =
      Ideal.Quotient.mk _ (MvPolynomial.C x) from rfl,
      show algebraMap R (MvPolynomial (Fin 1) R ⧸ Ideal.span
        {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) y =
      Ideal.Quotient.mk _ (MvPolynomial.C y) from rfl, ← map_mul,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span rfl
  -- `u` is the variable: the denominator is a nonzerodivisor, and both satisfy `x · z = y`
  have heu : e u = T := by
    have h1 : algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x * e.symm T =
        algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) y := by
      rw [← e.symm.commutes x, ← map_mul, hTrel, e.symm.commutes y]
    have hxne' : algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x ≠ 0 := fun h =>
      hxne (injective_algebraMap_affineBlowupAlgebraAway x hxne (by rw [h, map_zero]))
    have : u = e.symm T := mul_left_cancel₀ hxne' (hu.trans h1.symm)
    rw [this, e.apply_symm_apply]
  -- the variable is not in `𝔪 · R[T₀]`
  intro hmem
  have hTmem : T ∈ Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
      Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x} := by
    rw [map_span_algebraMap_chart_algEquiv x y e, ← heu]
    exact Ideal.mem_map_of_mem _ hmem
  rw [span_algebraMap_eq_map_mk x y] at hTmem
  have hle : Ideal.span ({(MvPolynomial.C x : MvPolynomial (Fin 1) R)}) ≤
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R) (maximalIdeal R) :=
    (relation_sup_span_C_eq_map_C x y hxy) ▸ le_sup_right
  have hrel : Ideal.span ({MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y} :
      Set (MvPolynomial (Fin 1) R)) ≤
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R) (maximalIdeal R) :=
    (relation_sup_span_C_eq_map_C x y hxy) ▸ le_sup_left
  have hXmem : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) ∈
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R) (maximalIdeal R) := by
    have := Ideal.mem_quotient_iff_mem_sup.mp (Ideal.map_mono hle hTmem)
    rwa [sup_eq_left.mpr hrel] at this
  have hone : (1 : R) ∈ maximalIdeal R := by
    have := MvPolynomial.mem_map_C_iff.mp hXmem (Finsupp.single (0 : Fin 1) 1)
    simp at this
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr hone)

end Chart

end Stacks.Blowup

end
