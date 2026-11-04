module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic

/-!
# The scheme-level chart `D ∩ U ≅ Spec (A / I(U))`, and Tag 01WS with the chart as data

Let `X` be a scheme, `I : X.IdealSheafData` the ideal sheaf of a closed subscheme `D ⊆ X`, and
`U ⊆ X` an affine open with `A = Γ(X, U)`. This file produces the isomorphism
`D ×_X U ≅ Spec (A / I(U))`, together with the square making it compatible with the two closed
immersions into `Spec A`, and proves that the square determines the ideal. Consequently the
form of [Stacks, Tag 01WS] with the chart as data and the form with an ideal equation are
equivalent.

## Main results

* `Stacks.CartierQuotientChart.quotientChart` and
  `Stacks.CartierQuotientChart.quotientChart_hom_comp`: the chart and its compatibility square,
  for every ideal sheaf and every affine open.
* `Stacks.CartierQuotientChart.ideal_eq_of_quotientChart`: any closed-immersion square of that
  shape over `Spec A` has `K = I.ideal U`.
* `Stacks.CartierQuotientChart.ideal_eq_iff_exists_quotientChart`: the two forms are equivalent.
* `Stacks.CartierQuotientChart.isEffectiveCartierDivisor_iff_affineLocal`: [Stacks, Tag 01WS]
  with the isomorphism `D ×_X U ≅ Spec (A ⧸ (f))` and the compatibility square as data.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CartierQuotientChart

/-! ### Two quotient presentations of one closed subscheme of an affine scheme -/

section Affine

variable {R : Type u} [CommRing R] {J K : Ideal R}

/-- If the closed immersion `Spec (R / J) ⟶ Spec R` factors through `Spec (R / K) ⟶ Spec R`
by any morphism at all, then `K ≤ J`. -/
theorem le_of_spec_quotient_hom
    (ε : Spec (.of (R ⧸ J)) ⟶ Spec (.of (R ⧸ K)))
    (hε : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      ε ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :
    K ≤ J := by
  have key : (CommRingCat.ofHom (Ideal.Quotient.mk J) :
      CommRingCat.of R ⟶ CommRingCat.of (R ⧸ J)) =
      CommRingCat.ofHom (Ideal.Quotient.mk K) ≫ Spec.preimage ε :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage]; exact hε)
  intro x hx
  have hxJ := congrArg (fun φ : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ J) => φ.hom x) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hxJ
  rw [← Ideal.Quotient.eq_zero_iff_mem, hxJ, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

/-- **Two quotient presentations of the same closed subscheme of `Spec R` have the same ideal.**
If `Spec (R / J) ⟶ Spec R` and `Spec (R / K) ⟶ Spec R` are identified by an isomorphism over
`Spec R`, then `J = K`. -/
theorem ideal_eq_of_spec_quotient_iso
    (ε : Spec (.of (R ⧸ J)) ≅ Spec (.of (R ⧸ K)))
    (hε : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      ε.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :
    J = K :=
  le_antisymm
    (le_of_spec_quotient_hom ε.symm.hom (by rw [Iso.symm_hom, hε, Iso.inv_hom_id_assoc]))
    (le_of_spec_quotient_hom ε.hom hε)

end Affine

/-! ### The chart -/

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! #### The chart for an arbitrary open immersion onto the preimage of `U` -/

section Generic

variable (U : X.Opens) {Z : Scheme.{u}} (c : Z ⟶ I.subscheme) [IsOpenImmersion c]
  (hr : Set.range c = Set.range (I.subschemeι ⁻¹ᵁ U).ι)

/-- For an open immersion `c : Z ⟶ D` into the closed subscheme `D` with range the open
`I.subschemeι ⁻¹ᵁ U`, the isomorphism `D ×_X U ≅ Z`. -/
def chartOfCover : pullback I.subschemeι U.ι ≅ Z :=
  pullbackRestrictIsoRestrict I.subschemeι U ≪≫
    (IsOpenImmersion.isoOfRangeEq c (I.subschemeι ⁻¹ᵁ U).ι hr).symm

/-- The forward map of `chartOfCover`, as the composite through `I.subschemeι ⁻¹ᵁ U`. -/
theorem chartOfCover_hom :
    (chartOfCover I U c hr).hom = (pullbackRestrictIsoRestrict I.subschemeι U).hom ≫
      (IsOpenImmersion.isoOfRangeEq c (I.subschemeι ⁻¹ᵁ U).ι hr).inv :=
  rfl

/-- The induced isomorphism `Z ≅ I.subschemeι ⁻¹ᵁ U` carries any morphism `g : Z ⟶ U` lying over
`c` to the restriction `I.subschemeι ∣_ U`. -/
theorem isoOfRangeEq_inv_comp (g : Z ⟶ U.toScheme) (hg : g ≫ U.ι = c ≫ I.subschemeι) :
    (IsOpenImmersion.isoOfRangeEq c (I.subschemeι ⁻¹ᵁ U).ι hr).inv ≫ g =
      I.subschemeι ∣_ U := by
  rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, hg, morphismRestrict_ι,
    ← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac]

/-- The chart is compatible with the two morphisms down to `U`. -/
theorem chartOfCover_hom_comp (g : Z ⟶ U.toScheme) (hg : g ≫ U.ι = c ≫ I.subschemeι) :
    (chartOfCover I U c hr).hom ≫ g = pullback.snd I.subschemeι U.ι := by
  rw [chartOfCover_hom, Category.assoc, isoOfRangeEq_inv_comp I U c hr g hg,
    pullbackRestrictIsoRestrict_hom_morphismRestrict]

end Generic

variable (V : X.affineOpens)

/-- The affine chart of `I.subscheme` at `V` has as range the preimage of `V` under the closed
immersion `I.subschemeι`. -/
theorem range_subschemeCover_map :
    Set.range (I.subschemeCover.f V) = Set.range (I.subschemeι ⁻¹ᵁ V.1).ι :=
  (congrArg (fun W : I.subscheme.Opens => (W : Set I.subscheme))
    (I.opensRange_subschemeCover_map V)).trans (Scheme.Opens.range_ι _).symm

/-- The closed immersion `Spec (Γ(X, V) ⧸ I(V)) ⟶ V`. -/
def quotientImmersion :
    Spec (.of (Γ(X, V.1) ⧸ I.ideal V)) ⟶ V.1.toScheme :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal V))) ≫ V.2.isoSpec.inv

/-- The closed immersion `Spec (Γ(X, V) ⧸ I(V)) ⟶ V ⟶ X` factors as the affine chart of
`I.subscheme` at `V` followed by `I.subschemeι`. -/
theorem quotientImmersion_ι :
    quotientImmersion I V ≫ V.1.ι = I.subschemeCover.f V ≫ I.subschemeι :=
  (I.subschemeCover_map_subschemeι V).symm

/-- **The chart of [Stacks, Tag 01WS]: `D ×_X V ≅ Spec (Γ(X, V) / I(V))`**, for every ideal
sheaf `I` and every affine open `V`. -/
def quotientChart :
    pullback I.subschemeι V.1.ι ≅ Spec (.of (Γ(X, V.1) ⧸ I.ideal V)) :=
  @chartOfCover X I V.1 _ (I.subschemeCover.f V) (I.subschemeCover.map_prop V)
    (range_subschemeCover_map I V)

/-- The chart is compatible with the closed immersion into `V`: it carries the projection
`D ×_X V ⟶ V` to `Spec (Γ(X, V) / I(V)) ⟶ V`. -/
@[reassoc]
theorem quotientChart_hom_quotientImmersion :
    (quotientChart I V).hom ≫ quotientImmersion I V = pullback.snd I.subschemeι V.1.ι :=
  @chartOfCover_hom_comp X I V.1 _ (I.subschemeCover.f V) (I.subschemeCover.map_prop V)
    (range_subschemeCover_map I V) (quotientImmersion I V) (quotientImmersion_ι I V)

/-- **The compatibility square of [Stacks, Tag 01WS].** The chart `D ×_X V ≅ Spec (A / I(V))`
identifies the closed immersion `D ×_X V ⟶ V ≅ Spec A` with `Spec (A / I(V)) ⟶ Spec A`. -/
theorem quotientChart_hom_comp :
    pullback.snd I.subschemeι V.1.ι ≫ V.2.isoSpec.hom =
      (quotientChart I V).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal V))) := by
  rw [← quotientChart_hom_quotientImmersion I V, Category.assoc, quotientImmersion,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The two forms of the local description are interchangeable -/

/-- An ideal equation `I.ideal V = K` produces the scheme-level chart
`D ×_X V ≅ Spec (A ⧸ K)` with its compatibility square. -/
theorem exists_quotientChart_of_ideal_eq {K : Ideal Γ(X, V.1)} (hK : I.ideal V = K) :
    ∃ e : pullback I.subschemeι V.1.ι ≅ Spec (.of (Γ(X, V.1) ⧸ K)),
      pullback.snd I.subschemeι V.1.ι ≫ V.2.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) := by
  subst hK
  exact ⟨quotientChart I V, quotientChart_hom_comp I V⟩

/-- The chart determines the ideal: any isomorphism `D ×_X V ≅ Spec (A ⧸ K)` making the square
commute has `K = I.ideal V`. -/
theorem ideal_eq_of_quotientChart {K : Ideal Γ(X, V.1)}
    (e : pullback I.subschemeι V.1.ι ≅ Spec (.of (Γ(X, V.1) ⧸ K)))
    (he : pullback.snd I.subschemeι V.1.ι ≫ V.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :
    I.ideal V = K := by
  refine ideal_eq_of_spec_quotient_iso ((quotientChart I V).symm ≪≫ e) ?_
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he, quotientChart_hom_comp I V,
    Iso.inv_hom_id_assoc]

/-- **The ideal-equation form and the `Spec`-quotient form of the local description of a closed
subscheme are equivalent.** -/
theorem ideal_eq_iff_exists_quotientChart (K : Ideal Γ(X, V.1)) :
    I.ideal V = K ↔
      ∃ e : pullback I.subschemeι V.1.ι ≅ Spec (.of (Γ(X, V.1) ⧸ K)),
        pullback.snd I.subschemeι V.1.ι ≫ V.2.isoSpec.hom =
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) :=
  ⟨exists_quotientChart_of_ideal_eq I V, fun ⟨e, he⟩ => ideal_eq_of_quotientChart I V e he⟩

/-- `D ∩ V` is `Spec (A / fA)`, compatibly with the closed immersions, exactly when `f` generates
`I.ideal V`. -/
theorem ideal_eq_span_iff_exists_quotientChart (f : Γ(X, V.1)) :
    I.ideal V = Ideal.span {f} ↔
      ∃ e : pullback I.subschemeι V.1.ι ≅ Spec (.of (Γ(X, V.1) ⧸ Ideal.span {f})),
        pullback.snd I.subschemeι V.1.ι ≫ V.2.isoSpec.hom =
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) :=
  ideal_eq_iff_exists_quotientChart I V _

/-! ### Tag 01WS with the chart as data -/

/-- **[Stacks, Tag 01WS], with the chart as data.** A closed subscheme `D ⊆ X` is an
effective Cartier divisor if and only if every point of `D` has an affine open neighbourhood `U`
in `X` carrying a nonzerodivisor `f ∈ Γ(X, U)` and an isomorphism
`D ×_X U ≅ Spec (Γ(X, U) ⧸ (f))` compatible with the two closed immersions into
`U ≅ Spec Γ(X, U)`. -/
theorem isEffectiveCartierDivisor_iff_affineLocal (I : X.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor I ↔
      ∀ x ∈ I.supportSet,
        ∃ (U : X.Opens) (hU : IsAffineOpen U),
          x ∈ (U : Set X) ∧
            ∃ f : Γ(X, U), IsRegular f ∧
              ∃ e : pullback I.subschemeι U.ι ≅ Spec (.of (Γ(X, U) ⧸ Ideal.span {f})),
                pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom =
                  e.hom ≫ Spec.map
                    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) := by
  rw [Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_isRegular]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨W, hxW, f, hf, hgen⟩ := h x hx
    exact ⟨W.1, W.2, hxW, f, hf,
      (ideal_eq_span_iff_exists_quotientChart I W f).1 hgen⟩
  · obtain ⟨W, hW, hxW, f, hf, e, he⟩ := h x hx
    exact ⟨⟨W, hW⟩, hxW, f, hf,
      (ideal_eq_span_iff_exists_quotientChart I ⟨W, hW⟩ f).2 ⟨e, he⟩⟩

end Stacks.CartierQuotientChart

end
