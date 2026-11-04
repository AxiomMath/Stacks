module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ConnectedComponentSelfMap
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.CurveZetaRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurvePullbackTraces
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointCountMonotone
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionPoints

/-!
# Weil's formula on the components of a twisted Frobenius

Let `f : Y ⟶ Spec Ω` be proper and smooth of relative dimension one over an algebraically
closed field `Ω` of characteristic `p`, algebraic over `𝔽_p`, and let `φ : Y ⟶ Y` be an
endomorphism over `Ω` together with an automorphism `Ψ` of `Y` such that both `Ψ ≫ φ` and
`φ ≫ Ψ` are the `e`-fold absolute Frobenius (`e ≥ 1`). Each connected component `C_i` sent into
itself by `φ` is a smooth proper curve with the twisted Frobenius `φ_i`, so Weil's formula
(`Stacks.EtaleCohomology.WeilTraceInput`) applies to it; its fixed points are finitely many; and
the fixed points of `φ` are those of the `φ_i`.

## Main results

* `Stacks.EtaleCohomology.natCard_fixedSections_componentSelfMap_eq`: Weil on a component.
* `Stacks.EtaleCohomology.natCard_fixedSections_eq_sum`: the fixed points split.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of Ω))
  [IsProper f] [SmoothOfRelativeDimension 1 f] (φ : Y ⟶ Y) (w : φ ≫ f = f)
  (p : ℕ) [Fact p.Prime] (hY : IsInCharacteristic Y p) (e : ℕ) (Ψ : Y ≅ Y)
  (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow Y p hY e)
  (hΨ' : φ ≫ Ψ.hom = absoluteFrobeniusPow Y p hY e)

omit [IsAlgClosed Ω] [SmoothOfRelativeDimension 1 f] in
include w in
/-- The restriction `φ_i` of `φ` to a component sent into itself is a morphism over `Spec Ω`. -/
theorem componentSelfMap_comp_structure (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i) :
    componentSelfMap f φ i h ≫ (componentι f i ≫ f) = componentι f i ≫ f := by
  rw [componentSelfMap_comp_assoc, w]

omit [IsAlgClosed Ω] in
include hΨ' in
/-- The restriction of `φ` to a component sent into itself is not constant: it is injective on
points and a curve has infinitely many points. -/
theorem componentSelfMap_not_constant (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i) :
    ¬ ∃ y, ∀ x, (componentSelfMap f φ i h).base x = y := by
  rintro ⟨y, hy⟩
  obtain ⟨a, -, b, -, hab⟩ :=
    (infinite_closedPoints_of_isCurve (f := componentι f i ≫ f)).nontrivial
  apply hab
  apply (componentι f i).isOpenEmbedding.injective
  apply phi_base_injective φ p hY e Ψ hΨ'
  have ha := congrArg (fun g => g.base a) (componentSelfMap_comp f φ i h)
  have hb := congrArg (fun g => g.base b) (componentSelfMap_comp f φ i h)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at ha hb
  rw [← ha, ← hb, hy a, hy b]

omit [IsAlgClosed Ω] [SmoothOfRelativeDimension 1 f] in
include hΨ' in
/-- A point of a component fixed by `φ_i` is fixed by `Ψ_i`. -/
theorem componentPsi_base_of_fixed (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i)
    (x : (componentOpens f i).toScheme) (hx : (componentSelfMap f φ i h).base x = x) :
    (componentPsi f φ p hY e Ψ hΨ' i h).hom.base x = x := by
  apply (componentι f i).isOpenEmbedding.injective
  have h1 := congrArg (fun g => g.base x) (componentPsi_hom_comp f φ p hY e Ψ hΨ' i h)
  have h2 := congrArg (fun g => g.base x) (componentSelfMap_comp f φ i h)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1 h2
  rw [h1]
  rw [hx] at h2
  conv_lhs => rw [h2]
  exact psi_base_phi_base φ p hY e Ψ hΨ' _

variable [CharP Ω p] (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω)

include w hΨ hΨ' halg in
/-- **A component sent into itself has finitely many fixed points.** -/
theorem finite_fixedSections_componentSelfMap (he : 0 < e) (i : Fin (componentCount Y))
    (h : IsSelfComponent f φ i) :
    Finite (fixedSections (componentι f i ≫ f) (componentSelfMap f φ i h)) := by
  have : Smooth (componentι f i ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  have hfin := (Stacks.Zeta.exists_zeta_roots_of_twistedFrobenius p (componentι f i ≫ f) e he
    halg (componentSelfMap f φ i h) (componentSelfMap_comp_structure f φ w i h)
    (isInCharacteristic_of_hom (componentι f i) p hY) (componentPsi f φ p hY e Ψ hΨ' i h)
    (componentPsi_comp_componentSelfMap f φ p hY e Ψ hΨ hΨ' i h)).1 1 one_pos
  have := hfin.to_subtype
  have hcl : ∀ y : fixedSections (componentι f i ≫ f) (componentSelfMap f φ i h),
      IsClosed ({y.1.base default} : Set _) := fun y => by
    have := isClosedImmersion_of_comp_eq_id (componentι f i ≫ f) y.1 y.2.1
    have hr : Set.range y.1.base = {y.1.base default} := by
      ext z
      exact ⟨fun ⟨s, hs⟩ => hs ▸ congrArg y.1.base (Subsingleton.elim _ _),
        fun hz => ⟨default, hz.symm⟩⟩
    rw [← hr]
    exact y.1.isClosedEmbedding.isClosed_range
  refine Finite.of_injective (β := {x : (componentOpens f i).toScheme | IsClosed ({x} : Set _) ∧
    (componentPsi f φ p hY e Ψ hΨ' i h).hom.base^[1] x = x})
    (fun y => ⟨y.1.base default, ?_, ?_⟩) ?_
  · exact hcl y
  · rw [Function.iterate_one]
    refine componentPsi_base_of_fixed f φ p hY e Ψ hΨ' i h _ ?_
    exact congrArg (fun g : Spec (.of Ω) ⟶ _ => g.base default) y.2.2 |>.symm.trans rfl |>.symm
  · intro y y' hyy
    have hpt : y.1.base default = y'.1.base default := congrArg Subtype.val hyy
    apply Subtype.ext
    refine ext_of_apply_closedPoint_eq_of_comp_eq (componentι f i ≫ f)
      (x := y.1.base default) (hcl y) (congrArg y.1.base (Subsingleton.elim _ _))
      ((congrArg y'.1.base (Subsingleton.elim _ _)).trans hpt.symm) (y.2.1.trans y'.2.1.symm)

include w hΨ hΨ' halg in
/-- **Weil's formula on a component sent into itself.** -/
theorem natCard_fixedSections_componentSelfMap_eq (hW : WeilTraceInput.{u}) (he : 0 < e)
    (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : Ω) ≠ 0) (hn : 1 ≤ n) (i : Fin (componentCount Y))
    (h : IsSelfComponent f φ i) :
    ((Nat.card (fixedSections (componentι f i ≫ f) (componentSelfMap f φ i h)) : ℤ) :
        ZMod (ℓ ^ n)) =
      curvePullbackTraceValue (componentι f i ≫ f) ℓ n (componentSelfMap f φ i h)
          (componentSelfMap_comp_structure f φ w i h)
          (componentSelfMap_not_constant f φ p hY e Ψ hΨ' i h) 0 -
        curvePullbackTraceValue (componentι f i ≫ f) ℓ n (componentSelfMap f φ i h)
          (componentSelfMap_comp_structure f φ w i h)
          (componentSelfMap_not_constant f φ p hY e Ψ hΨ' i h) 1 +
        curvePullbackTraceValue (componentι f i ≫ f) ℓ n (componentSelfMap f φ i h)
          (componentSelfMap_comp_structure f φ w i h)
          (componentSelfMap_not_constant f φ p hY e Ψ hΨ' i h) 2 := by
  have : Smooth (componentι f i ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  exact hW Ω p halg (componentOpens f i).toScheme (componentι f i ≫ f) (componentSelfMap f φ i h)
    (componentSelfMap_comp_structure f φ w i h)
    (componentSelfMap_not_constant f φ p hY e Ψ hΨ' i h) e he
    (isInCharacteristic_of_hom (componentι f i) p hY) (componentPsi f φ p hY e Ψ hΨ' i h)
    (componentPsi_comp_componentSelfMap f φ p hY e Ψ hΨ hΨ' i h) ℓ n hℓ hn

open Classical in
include w hΨ hΨ' halg in
/-- **The fixed points of `φ` split over the components sent into themselves.** -/
theorem natCard_fixedSections_eq_sum (he : 0 < e) :
    Nat.card (fixedSections f φ) =
      ∑ i, if h : IsSelfComponent f φ i then
        Nat.card (fixedSections (componentι f i ≫ f) (componentSelfMap f φ i h)) else 0 := by
  classical
  have : ∀ i : {i // IsSelfComponent f φ i},
      Finite (fixedSections (componentι f i.1 ≫ f) (componentSelfMap f φ i.1 i.2)) := fun i =>
    finite_fixedSections_componentSelfMap f φ w p hY e Ψ hΨ hΨ' halg he i.1 i.2
  rw [Nat.card_congr (fixedSectionsEquivSigma f φ), Nat.card_sigma]
  set D := fun i => if h : IsSelfComponent f φ i then
    Nat.card (fixedSections (componentι f i ≫ f) (componentSelfMap f φ i h)) else 0
  calc ∑ i : {i // IsSelfComponent f φ i},
        Nat.card (fixedSections (componentι f i.1 ≫ f) (componentSelfMap f φ i.1 i.2))
      = ∑ i : {i // IsSelfComponent f φ i}, D i.1 :=
        Finset.sum_congr rfl fun i _ => by simp only [D, dite_eq_left i.2]
    _ = ∑ i ∈ Finset.univ.filter (IsSelfComponent f φ), D i :=
        (Finset.sum_subtype _ (by simp) _).symm
    _ = ∑ i, if IsSelfComponent f φ i then D i else 0 := Finset.sum_filter _ _
    _ = ∑ i, D i := Finset.sum_congr rfl fun i _ => by
        by_cases h : IsSelfComponent f φ i
        · rw [ite_eq_left h]
        · rw [ite_eq_right h]; simp only [D, dite_eq_right h]

end Stacks.EtaleCohomology

end
