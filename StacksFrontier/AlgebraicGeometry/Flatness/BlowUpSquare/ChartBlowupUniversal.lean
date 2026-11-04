module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBlowupAdmissible
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullbackUniqueness
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# The universal property of the blowup of an affine chart

Let `(X, D, M)` be a triple as in Situation 0F8S, let `(U, A, f, M^•)` be an affine chart for it,
and let `b_U : U' ⟶ U` be the blowing up of `U` in the product `I = ∏ᵢ I_i(M^•, f)` of the
determinantal ideals of the chart.  Stacks tag 0GTY asserts that `b_U` has clause (2) of the tag
over `U`: a morphism `h : Y ⟶ U` for which `h⁻¹(D ∩ U)` is defined and the pulled-back triple is
good factors uniquely through `b_U`.

This file proves that.  It is the paragraph of the tag's proof beginning "Finally, we claim that
`b_U : U' → U` has the universal property mentioned in part (2)".

The argument is that `I𝒪_Y` is invertible, after which the universal property of blowing up
(Stacks tag 0806) applies.  Invertibility is checked on the affine charts `(V, B, g, N^•)` of
`(Y, h⁻¹(D ∩ U), Lh^*M)` supplied by goodness: `g` and the image of `f` in `B` differ by a unit,
as both cut out `h⁻¹(D ∩ U) ∩ V`, so `I_i(N^•, g) = I_i(N^•, f|_V)` by Stacks tag 0GST; `N^•` and
`M^• ⊗_A B` are isomorphic in `D(B)` by part (1) of Stacks tag 0F8T, so `I_i(M^• ⊗_A B, f|_V)` is
principal too by Stacks tag 0GSS; and that ideal is `I_i(M^•, f)B` by part (2) of tag 0F8T.  The
product of the finitely many principal ideals `I_i(M^•, f)B` is principal, and it contains a power
of `f|_V`, which is a nonzerodivisor, so its generator is one as well.

## Main results

* `AlgebraicGeometry.existsUnique_lift_blowUpToBase`: the universal property of blowing up
  (Stacks tag 0806) in the form of a unique factorization, read off the terminality statement.
* `AffineChart.isPrincipal_pullback_determinantalIdeal_of_chart`: the determinantal ideals of
  the chart pulled back to the open of an arbitrary chart of the pulled-back triple are principal
  as soon as that chart's are.  This is where the unit discrepancy between the two equations is
  absorbed.
* `AffineChart.isEffectiveCartierDivisor_comap_blowupCentreIdealSheaf`: the inverse image of the
  centre `∏ᵢ I_i(M^•, f)` along a morphism good for the triple is an effective Cartier divisor.
* `AffineChart.existsUnique_lift_chartBlowup`: **Stacks tag 0GTY, clause (2) over an affine
  chart.**

## Implementation notes

`AffineChart.isPrincipal_determinantalIdeal_of_eq_appLE` in `ChartPullbackUniqueness.lean` runs
the transfer of principality in the other direction, from
the chart downstairs to a chart of the pulled-back triple, and requires the two equations to agree
on the nose.  Here the hypothesis is on the chart *upstairs* — it is what goodness hands over —
and the equations are only known to generate the same ideal, so
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.exists_unit_mul_of_span_singleton_eq`
first produces the unit relating them.

The affine-local criterion used for the effective Cartier divisor is
`Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_of_affineLocal`, which only asks for
a generator at the points of the support; that is what lets goodness, which only speaks about
points of the divisor, be applied — the support of the centre is contained in that of the divisor
because a power of the latter lies in the former.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0GSS](https://stacks.math.columbia.edu/tag/0GSS)
* [Stacks Project, Tag 0GST](https://stacks.math.columbia.edu/tag/0GST)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry

/-- **The universal property of blowing up, Stacks tag 0806, as a unique factorization.**  A
morphism `f : Y ⟶ X` along which the inverse image of the centre is an effective Cartier divisor
factors through the blowup in exactly one way.  This is the terminality statement
`Stacks.Blowup.isTerminal_blowUp` read as a `∃!`. -/
@[stacks 0806 "the terminality of the blowup read as a unique factorization: a morphism along \
which the inverse image of the centre is an effective Cartier divisor factors through the blowup \
in exactly one way"]
theorem existsUnique_lift_blowUpToBase {X : Scheme.{u}} (I : X.IdealSheafData) {Y : Scheme.{u}}
    (f : Y ⟶ X) (hf : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f)) :
    ∃! k : Y ⟶ blowUp I, k ≫ blowUpToBase I = f := by
  obtain ⟨hc, ⟨ht⟩⟩ := Stacks.Blowup.isTerminal_blowUp I
  let c : Stacks.Blowup.CartierOver I := ⟨Over.mk f, hf⟩
  refine ⟨(ht.from c).hom.left, Over.w (ht.from c).hom, fun k hk => ?_⟩
  exact congrArg (fun g => g.hom.left)
    (ht.hom_ext (ObjectProperty.homMk (Over.homMk k hk)) (ht.from c))

namespace ComplexAndDivisorSituation

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- **Two elements generating the same ideal, one of them a nonzerodivisor, differ by a unit.**
Each is a multiple of the other, so the product of the two multipliers acts as the identity on the
nonzerodivisor and is therefore `1`. -/
theorem exists_unit_mul_of_span_singleton_eq {A : Type*} [CommRing A] {a b : A}
    (hb : b ∈ nonZeroDivisors A)
    (h : Ideal.span ({a} : Set A) = Ideal.span ({b} : Set A)) :
    ∃ u : Aˣ, a = (u : A) * b := by
  obtain ⟨c, hc⟩ : ∃ c, c * b = a :=
    Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self a)
  obtain ⟨e, he⟩ : ∃ e, e * a = b :=
    Ideal.mem_span_singleton'.mp (h.symm ▸ Ideal.mem_span_singleton_self b)
  have hec : e * c = 1 := by
    have hb' : e * c * b = 1 * b := by rw [mul_assoc, hc, he, one_mul]
    exact (mul_cancel_right_mem_nonZeroDivisors hb).mp hb'
  exact ⟨⟨c, e, by rw [mul_comm]; exact hec, hec⟩, hc.symm⟩

/-- A finite product of principal ideals is principal. -/
theorem isPrincipal_finset_prod {A : Type*} [CommRing A] {ι : Type*} (s : Finset ι)
    (J : ι → Ideal A) (h : ∀ i ∈ s, (J i).IsPrincipal) : (∏ i ∈ s, J i).IsPrincipal := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_⟩
    rw [Finset.prod_empty, Ideal.one_eq_top]
    exact Ideal.span_singleton_one.symm
  | insert a t ha ih =>
    obtain ⟨x, hx⟩ := h a (Finset.mem_insert_self a t)
    obtain ⟨y, hy⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, hx, hy, Ideal.span_singleton_mul_span_singleton]
    exact ⟨_, rfl⟩

/-- **The equation of an arbitrary chart of the pulled-back triple and the equation of the
pulled-back chart over the same open generate the same ideal**, namely the ideal of `h⁻¹D` there:
the first by the chart's own defining property, the second by part (1) of Stacks tag 0F8T. -/
theorem span_singleton_eq_span_singleton_pullback (C : AffineChart S) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined h S.D)
    (C' : AffineChart (S.pullback h hD))
    (hV : ((C'.U : (S.pullback h hD).X.Opens) : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    Ideal.span {C'.f} = Ideal.span {(C.pullback h hD C'.U hV).f} :=
  C'.divisor_ideal.symm.trans (C.comap_ideal_eq_span h C'.U hV)

/-- **Principality of the determinantal ideals of an arbitrary chart of the pulled-back triple
passes to the pulled-back chart over the same open.**  The two equations generate the same ideal,
hence differ by a unit, which does not change the determinantal ideals by Stacks tag 0GST; the two
bounded complexes are isomorphic in `D(B)` by part (1) of Stacks tag 0F8T, and Stacks tag 0GSS
transports principality across such an isomorphism.

This is the direction opposite to `isPrincipal_determinantalIdeal_of_eq_appLE`, and the one the
universal property of Stacks tag 0GTY needs: the hypothesis is on the chart that
goodness of `h` supplies, and the conclusion is about the chart the tag's centre is built from. -/
theorem isPrincipal_pullback_determinantalIdeal_of_chart (C : AffineChart S)
    {Y : Scheme.{u}} (h : Y ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined h S.D)
    (C' : AffineChart (S.pullback h hD))
    (hV : ((C'.U : (S.pullback h hD).X.Opens) : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens))
    (i : ℤ) (hp : (C'.determinantalIdeal i).IsPrincipal) :
    ((C.pullback h hD C'.U hV).determinantalIdeal i).IsPrincipal := by
  obtain ⟨u, hu⟩ := exists_unit_mul_of_span_singleton_eq
    (A := Γ((S.pullback h hD).X, (C'.U : (S.pullback h hD).X.Opens)))
    (C.pullback h hD C'.U hV).regular.mem_nonZeroDivisors
    (C.span_singleton_eq_span_singleton_pullback h hD C' hV)
  have hC' : (idealI C'.complex (C.pullback h hD C'.U hV).f i).IsPrincipal := by
    rw [idealI_unit_mul_eq C'.complex (C.pullback h hD C'.U hV).f u i, ← hu]
    exact hp
  exact Stacks.Eta.DeterminantalIdeal.isPrincipal_idealI_of_derived_iso
    (C.pullback h hD C'.U hV).f
    (C.pullback h hD C'.U hV).regular.mem_nonZeroDivisors C'.complex _ i
    ((C.nonempty_derivedIso_pullback h hD C' hV).map Iso.symm) hC'

/-- **The inverse image of the centre of the blowup of an affine chart along a morphism good for
the triple is an effective Cartier divisor.**  This is the invertibility of `I𝒪_Y` asserted in the
proof of clause (2) of Stacks tag 0GTY.

A power of the inverse image of `D` lies in the inverse image of the centre, so only points of
the divisor have to be treated, and there goodness supplies a chart `(V, B, g, N^•)` whose
determinantal ideals are principal.  Principality passes to the pulled-back chart over `V` by
`AffineChart.isPrincipal_pullback_determinantalIdeal_of_chart`, and the determinantal ideals
of that chart are the extensions `I_i(M^•, f)B` by part (2) of Stacks tag 0F8T; their product,
which is the ideal of the inverse image of the centre on `V`, is therefore principal, and it
contains a power of the image of `f`, which is a nonzerodivisor, so its generator is one too. -/
theorem isEffectiveCartierDivisor_comap_blowupCentreIdealSheaf (C : AffineChart S)
    {Y : Scheme.{u}} (b : Y ⟶ (C.U : S.X.Opens).toScheme)
    (hgood : S.IsGoodOver (b ≫ (C.U : S.X.Opens).ι)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (C.blowupCentreIdealSheaf.comap b) := by
  classical
  have hVtop : ∀ W : Y.Opens, W ≤ (b ≫ (C.U : S.X.Opens).ι) ⁻¹ᵁ (C.U : S.X.Opens) := by
    intro W; simp
  -- a power of the inverse image of `D` lies in the inverse image of the centre
  have hle : S.D.comap (b ≫ (C.U : S.X.Opens).ι) ^
      ((∑ i ∈ C.complex.bounded.toFinset, C.complex.rank i) + 1) ≤
      C.blowupCentreIdealSheaf.comap b := by
    rw [Scheme.IdealSheafData.comap_comp, ← Stacks.IdealSheaf.comap_pow]
    exact Scheme.IdealSheafData.comap_mono b C.pow_comap_D_le_blowupCentreIdealSheaf
  -- so the support of the inverse image of the centre lies in that of the inverse image of `D`
  have hsupp : (C.blowupCentreIdealSheaf.comap b).support ≤
      (S.D.comap (b ≫ (C.U : S.X.Opens).ι)).support :=
    le_trans (Scheme.IdealSheafData.support_antitone hle)
      (le_of_eq (Scheme.IdealSheafData.support_pow_succ _ _))
  refine Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_of_affineLocal _
    fun y hy => ?_
  obtain ⟨C', hyC', hC'⟩ := hgood.isGoodTriple y
    (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr
      (hsupp (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hy)))
  set V : Y.affineOpens :=
    ⟨((C'.U : (S.pullback (b ≫ (C.U : S.X.Opens).ι) hgood.pullbackDefined).X.Opens) : Y.Opens),
      C'.U.2⟩ with hVdef
  refine ⟨V, hyC', ?_⟩
  -- every factor of the centre becomes principal on the chart's open
  have hfac : ∀ i : ℤ, (Ideal.map ((b ≫ (C.U : S.X.Opens).ι).appLE
      (C.U : S.X.Opens) (V : Y.Opens) (hVtop _)).hom
        (C.determinantalIdeal i)).IsPrincipal := by
    intro i
    rw [← C.pullback_determinantalIdeal (b ≫ (C.U : S.X.Opens).ι)
      hgood.pullbackDefined V (hVtop _) i]
    exact C.isPrincipal_pullback_determinantalIdeal_of_chart
      (b ≫ (C.U : S.X.Opens).ι) hgood.pullbackDefined C' (hVtop _) i (hC' i)
  -- hence so does their product, which is the ideal of the inverse image of the centre
  have hcentre := C.ideal_comap_blowupCentreIdealSheaf b V (hVtop _)
  obtain ⟨t, ht⟩ : ((C.blowupCentreIdealSheaf.comap b).ideal V).IsPrincipal := by
    rw [hcentre, blowupCentre, Ideal.map_finset_prod]
    exact isPrincipal_finset_prod _ _ fun i _ => hfac i
  -- its generator is a nonzerodivisor, a power of the image of `f` lying in the ideal
  set x := ((b ≫ (C.U : S.X.Opens).ι).appLE (C.U : S.X.Opens) (V : Y.Opens)
    (hVtop _)).hom (C.f ^ ((∑ i ∈ C.complex.bounded.toFinset, C.complex.rank i) + 1)) with hx
  have hmem : x ∈ (C.blowupCentreIdealSheaf.comap b).ideal V := by
    rw [hcentre]
    refine Ideal.mem_map_of_mem _ ?_
    rw [pow_succ']
    exact Ideal.mul_mem_left _ _ C.pow_mem_blowupCentre
  have hregpow : x ∈ nonZeroDivisors Γ(Y, (V : Y.Opens)) := by
    rw [hx, map_pow]
    exact pow_mem (C.isRegular_pullbackRingHom_f (b ≫ (C.U : S.X.Opens).ι)
      hgood.pullbackDefined V (hVtop _)).mem_nonZeroDivisors _
  rw [ht] at hmem
  exact ⟨t, Stacks.Divisors.mem_nonZeroDivisors_of_mem_span_singleton hregpow hmem, ht⟩

/-- **Stacks tag 0GTY, clause (2) over an affine chart.**  Let `(U, A, f, M^•)` be an affine chart
for the triple `(X, D, M)` and let `b_U : U' ⟶ U` be the blowing up of `U` in the product
`∏ᵢ I_i(M^•, f)` of its determinantal ideals.  Every morphism `h : Y ⟶ U` whose composite with
the inclusion of `U` is good for the triple factors through `b_U` in exactly one way.

The inverse image of the centre along `h` is an effective Cartier divisor by
`AffineChart.isEffectiveCartierDivisor_comap_blowupCentreIdealSheaf`, so the universal property of
blowing up, Stacks tag 0806, applies. -/
@[stacks 0GTY "clause (2) over an affine chart: a morphism to the chart whose composite with the \
inclusion of the chart is good for the triple factors uniquely through the blowing up of the \
chart in the product of its determinantal ideals, which is what `b` restricts to there"]
theorem existsUnique_lift_chartBlowup (C : AffineChart S) {Y : Scheme.{u}}
    (b : Y ⟶ (C.U : S.X.Opens).toScheme)
    (hgood : S.IsGoodOver (b ≫ (C.U : S.X.Opens).ι)) :
    ∃! k : Y ⟶ blowUp C.blowupCentreIdealSheaf,
      k ≫ blowUpToBase C.blowupCentreIdealSheaf = b :=
  existsUnique_lift_blowUpToBase C.blowupCentreIdealSheaf b
    (C.isEffectiveCartierDivisor_comap_blowupCentreIdealSheaf b hgood)

end AffineChart

end ComplexAndDivisorSituation

end AlgebraicGeometry

end
