module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartBiconditional

/-!
# The étale-chart biconditionals of Stacks 061K without the scheme-level 0D0F hypothesis

`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmoothChartBiconditional.lean` proves the two
biconditionals of [Stacks Project, Tag 061K] for a morphism `f : X ⟶ Y` of algebraic spaces,
carrying two hypotheses: `h0D0F`, the scheme-level implication (3) ⟹ (1) of
[Stacks Project, Tag 0D0F], used only for the forward implications, and `hGlue`, the triviality
of the pseudo-torsor of lifts, used only for the converse.

The first is no longer needed: `Stacks.Smooth.formallySmooth_of_formallySmooth_appLE` of
`StacksFrontier/AlgebraicGeometry/Smooth/FormallySmoothTFAE.lean` proves it unconditionally, and the
forward implications
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothScheme'` and
`AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothScheme'` of
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmoothChartCriterion.lean` go through it.  This
file restates the three biconditionals with `hGlue` as their only hypothesis.

## Main results

* `AlgebraicGeometry.Space.formallySmooth_iff_etaleCharts'`: the equivalence of (1) and (2).
* `AlgebraicGeometry.Space.formallySmooth_iff_surjectiveEtaleChart'`: the equivalence of (1)
  and (3).
* `AlgebraicGeometry.Space.formallySmooth_iff_holdsOnSurjectiveEtaleChart'`: the same
  equivalence with condition (3) read through
  `AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart` of [Stacks Project, Tag 03MJ].

## References

* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 061K, the equivalence of (1) and (2).** A morphism of algebraic spaces over `S` is
formally smooth exactly when the morphism of schemes underlying every commuting square of étale
scheme charts is formally smooth, granted the triviality of the pseudo-torsor of lifts.

The forward implication is unconditional. -/
theorem formallySmooth_iff_etaleCharts'
    (hGlue : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      FormallySmoothEtaleLocally B S hS g → FormallySmooth g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      HoldsOnEveryEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f := by
  refine ⟨holdsOnEveryEtaleChart_formallySmoothScheme', fun hall ↦ ?_⟩
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact formallySmooth_of_surjectiveEtaleChart B S hS hGlue hX hY a b ψ haEtale hbEtale haSurj
    hdiag (hall U V a b ψ haEtale hbEtale hdiag.symm)

/-- **Stacks 061K, the equivalence of (1) and (3).** A morphism of algebraic spaces over `S` is
formally smooth exactly when there is one commuting square of étale scheme charts, both chart
maps surjective, whose underlying morphism of schemes is formally smooth, granted the
triviality of the pseudo-torsor of lifts.

The forward implication is unconditional. -/
theorem formallySmooth_iff_surjectiveEtaleChart'
    (hGlue : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      FormallySmoothEtaleLocally B S hS g → FormallySmooth g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        yoneda.map ψ ≫ b = a ≫ f ∧
        Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ) := by
  constructor
  · intro hf
    obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
    obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
    exact ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, hbSurj, hdiag.symm,
      holdsOnEveryEtaleChart_formallySmoothScheme' hf U V a b ψ haEtale hbEtale hdiag.symm⟩
  · rintro ⟨U, V, a, b, ψ, ha, hb, haSurj, -, hdiag, hψ⟩
    exact formallySmooth_of_surjectiveEtaleChart B S hS hGlue hX hY a b ψ ha hb haSurj
      hdiag.symm hψ

/-- **Stacks 061K, the equivalence of (1) and (3) through Stacks 03MJ.** The same equivalence
with condition (3) read as `AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart`, the form in
which the forward implication is stated: only the chart of the source is required to be
surjective, which is all the converse uses. -/
theorem formallySmooth_iff_holdsOnSurjectiveEtaleChart'
    (hGlue : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      FormallySmoothEtaleLocally B S hS g → FormallySmooth g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      HoldsOnSurjectiveEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f := by
  refine ⟨holdsOnSurjectiveEtaleChart_formallySmoothScheme' hX hY, ?_⟩
  rintro ⟨U, V, a, b, ψ, ha, hb, haSurj, hdiag, hψ⟩
  exact formallySmooth_of_surjectiveEtaleChart B S hS hGlue hX hY a b ψ ha hb haSurj
    hdiag.symm hψ

end AlgebraicGeometry.Space

end
