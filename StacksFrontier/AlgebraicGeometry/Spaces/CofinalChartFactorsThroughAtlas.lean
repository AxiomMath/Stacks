module

public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartFamilyInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# The charts factoring through a surjective étale atlas are cofinal

The charts of an algebraic space `X` factoring through a fixed surjective étale scheme chart
`b : h_A ⟶ X` are cofinal among the affine étale charts of `X`, and the conjunction of two cofinal
classes of charts is cofinal as soon as one of them is stable under refinement.

## Main results

* `AlgebraicGeometry.Space.IsCofinalChartFamily.and` — the conjunction of two cofinal classes of
  charts is cofinal when one is stable under refinement.
* `AlgebraicGeometry.Space.isCofinalChartFamily_factorsThrough` — the charts factoring through a
  surjective étale chart are cofinal.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The conjunction of two cofinal classes of charts is cofinal**, provided one of them is
stable under refinement — that is, holds of `r ≫ c` whenever it holds of `c`. -/
theorem IsCofinalChartFamily.and {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {P Q : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ F) → Prop}
    (hP : IsCofinalChartFamily B S hS P) (hQ : IsCofinalChartFamily B S hS Q)
    (hQref : ∀ (T R : BigFppfOver B S hS) (r : T ⟶ R) (c : yoneda.obj R ⟶ F),
      Q R c → Q T (yoneda.map r ≫ c)) :
    IsCofinalChartFamily B S hS fun T c => P T c ∧ Q T c := by
  classical
  intro R hR c hc
  obtain ⟨I, V, π, hVaff, hπ, hcover, hQV⟩ := hQ R hR c hc
  choose J O ρ hOaff hρ hOcover hOP using fun i =>
    hP (V i) (hVaff i) (yoneda.map (π i) ≫ c) (isEtale_comp B S hS (hπ i) hc)
  refine ⟨Σ i, J i, fun p => O p.1 p.2, fun p => ρ p.1 p.2 ≫ π p.1,
    fun p => hOaff p.1 p.2, fun p => ?_, ?_, fun p => ⟨?_, ?_⟩⟩
  · simpa only [Functor.map_comp] using isEtale_comp B S hS (hρ p.1 p.2) (hπ p.1)
  · exact BigFppfOver.sieve_generate_ofArrows_comp_mem_topology B S hS V π hcover O ρ hOcover
  · simpa only [Functor.map_comp, Category.assoc] using hOP p.1 p.2
  · simpa only [Functor.map_comp, Category.assoc] using
      hQref (O p.1 p.2) (V p.1) (ρ p.1 p.2) (yoneda.map (π p.1) ≫ c) (hQV p.1)

variable (X : AlgebraicSpaces B S hS)

/-- **Factoring through a fixed chart is stable under refinement.** -/
theorem factorsThrough_comp {A T R : BigFppfOver B S hS} (b : yoneda.obj A ⟶ X.1)
    (r : T ⟶ R) (c : yoneda.obj R ⟶ X.1) (h : ∃ q : R ⟶ A, yoneda.map q ≫ b = c) :
    ∃ q : T ⟶ A, yoneda.map q ≫ b = yoneda.map r ≫ c := by
  obtain ⟨q, hq⟩ := h
  exact ⟨r ≫ q, by rw [← hq, Functor.map_comp, Category.assoc]⟩

/-- **The charts of `X` factoring through a surjective étale scheme chart `b : h_A ⟶ X` are
cofinal among the affine étale charts of `X`.** -/
theorem isCofinalChartFamily_factorsThrough (A : BigFppfOver B S hS)
    (b : yoneda.obj A ⟶ X.1) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    IsCofinalChartFamily B S hS (F := X.1)
      fun T c => ∃ r : T ⟶ A, yoneda.map r ≫ b = c := by
  have hcov : (SmallEtale.topology B S hS X.1).CoversTop
      (fun _ : PUnit.{u + 2} => etaleChartObj B S hS b hb) :=
    SmallEtale.coversTop_of_isSurjective B S hS X.1 X.property _
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.property A b).1 hsurj)
  have h := isCofinalChartFamily_hasSomeChartSection B S hS X.1
    (fun _ : PUnit.{u + 2} => smallEtaleChartSheaf B S hS X (etaleChartObj B S hS b hb))
    fun W => ⟨_, jointlyLocallyInhabited_smallEtaleChartSheaf B S hS
      (fun _ : PUnit.{u + 2} => etaleChartObj B S hS b hb) hcov W, fun _ _ hh => hh⟩
  intro R hR c hc
  obtain ⟨I, V, π, hVaff, hπ, hcover, hP⟩ := h R hR c hc
  refine ⟨I, V, π, hVaff, hπ, hcover, fun i => ?_⟩
  obtain ⟨_hch, _j, ⟨f⟩⟩ := hP i
  exact ⟨((SmallEtale.inclusion B S hS X.1).map f).left,
    CostructuredArrow.w ((SmallEtale.inclusion B S hS X.1).map f)⟩

end AlgebraicGeometry.Space

end
