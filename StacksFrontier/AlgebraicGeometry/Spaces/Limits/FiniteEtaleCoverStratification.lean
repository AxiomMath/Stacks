module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverStratificationCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeClosedInFiniteFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# A stratification of a qcqs algebraic space by finite étale covers

Stacks 0GUP: a quasi-compact and quasi-separated algebraic space `X` has a chain of closed
subspaces of finite presentation `Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t = ∅` with `Z₀ ⊆ X` a thickening, such that
each `Z_i` has a surjective, finite and finitely presented cover by a scheme which is finite
étale over `Z_i ∖ Z_{i+1}`.

The proof is by Noetherian-style induction on closed subsets of `|X|`
(`AlgebraicGeometry.Space.exists_isCoverStratified_univ_of_step`). For an irreducible closed
`C ⊆ |X|`, the reduced closed subspace `C₀` on `C` is qcqs with one irreducible component, so
Stacks 0GUN
(`AlgebraicGeometry.Space.exists_finiteSchemeCover_finiteEtaleOverDenseOpen_and_refining`)
gives a finite cover `Y ⟶ C₀` by a scheme, finite étale over a dense open, refining the étale
chart of `C₀` obtained from an affine étale chart `V ⟶ X`. Then `Y ⟶ X` is closed in a finite
and finitely presented scheme over `X`
(`exists_isClosedImmersion_isFinite_isFinitePresentation_of_factorsZariskiLocallyThrough`),
and `AlgebraicGeometry.Space.exists_isCoverStratified_of_closedImmersion` performs the step.

## Main results

* `AlgebraicGeometry.Space.exists_finiteEtaleCoverStratification`: Stacks 0GUP.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Stacks 0GUP.** Let `X` be a quasi-compact and quasi-separated algebraic space. There are
`t ≥ 0` and closed subspaces `X ⊇ Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t = ∅` with each `Z_i ⟶ X` of finite
presentation and `Z₀ ⊆ X` a thickening, such that for each `i < t` there is a scheme `Y_i` and a
surjective, finite and finitely presented morphism `Y_i ⟶ Z_i` which is finite étale over the
open subspace `Z_i ∖ Z_{i+1}` (`AlgebraicGeometry.Space.IsFiniteEtaleCoverStep`). -/
@[stacks 0GUP]
theorem exists_finiteEtaleCoverStratification (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ∃ (t : ℕ) (Z : ℕ → Subfunctor X),
      (∀ i, IsClosedSubspace B S hS (Z i)) ∧ (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
      (∀ i, Z (i + 1) ≤ Z i) ∧ IsThickening B S hS ⟨X, hX⟩ (Z 0) ∧
      IsEmpty (points B S hS (Z t).toFunctor) ∧
      ∀ i < t, IsFiniteEtaleCoverStep B S hS (Z i) (Z (i + 1)) := by
  obtain ⟨V, p, hV, hps, hpe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hXqc
  have := hV
  have hpe' : IsEtale B S hS p := hpe
  obtain ⟨W, -, -, hWs, hWpts⟩ := exists_isCoverStratified_univ_of_step hX hXqc
    (fun C hC hirr hsmall => by
      let C₀ := reducedClosedSubspace B S hS X hX C hC
      have hC₀ : IsClosedSubspace B S hS C₀ :=
        isClosedSubspace_reducedClosedSubspace B S hS X hX C hC
      have hC₀pts : subspacePointSet B S hS X C₀ = C :=
        range_pointsMap_ι_reducedClosedSubspace B S hS X hX C hC
      have hC₀qc : IsQuasiCompactSpace B S hS C₀.toFunctor :=
        isQuasiCompactSpace_of_isClosedImmersion B S hS hXqc C₀.ι hC₀.2
      have hC₀qs : IsAbsolutelyQuasiSeparated B S hS hZ C₀.toFunctor :=
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hC₀.1 hXqs
          (isQuasiSeparated_of_isClosedImmersion B S hS hC₀.2)
      have hcomp : (irreducibleComponents (points B S hS C₀.toFunctor)).Finite := by
        have hemb : Topology.IsEmbedding (pointsMap B S hS C₀.toFunctor C₀.ι) :=
          isEmbedding_pointsMap_of_isImmersion B S hS hX C₀.ι
            (isImmersion_of_isClosedImmersion B S hS hC₀.2)
        have hrange : Set.range (pointsMap B S hS C₀.toFunctor C₀.ι) = C := hC₀pts
        have : IrreducibleSpace C := (Subtype.irreducibleSpace hirr)
        let e := hemb.toHomeomorph
        have : IrreducibleSpace (points B S hS C₀.toFunctor) := by
          have h : IrreducibleSpace (Set.range (pointsMap B S hS C₀.toFunctor C₀.ι)) := by
            rw [hrange]; infer_instance
          exact Function.Surjective.irreducibleSpace e.symm.continuous e.symm.surjective
        rw [irreducibleComponents_eq_singleton]
        exact Set.finite_singleton _
      -- the chart of `C₀`
      have hrep := hC₀.2.1
      let ζ := hrep.fst p
      let z := hrep.snd p
      have sqZ : IsPullback ζ (yoneda.map z) C₀.ι p := hrep.isPullback p
      have hζs : IsSurjective B S hS ζ := surjective_pointsMap_of_isPullback B S hS sqZ.flip
        ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX V p).1 hps)
      have hζe : IsEtale B S hS ζ :=
        isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqZ
          (isAlgebraicSpace_yoneda B S hS _) hC₀.1 (isAlgebraicSpace_yoneda B S hS V) hX hpe'
      obtain ⟨Y, f, U, ⟨hfs, hff, hffp, hU, -, hUd, -, hUe⟩, hfac⟩ :=
        (exists_finiteSchemeCover_finiteEtaleOverDenseOpen_and_refining B S hS hZ _ hC₀.1 hC₀qc
          hC₀qs hcomp).2 _ (isAlgebraicSpace_yoneda B S hS _) ζ hζs hζe
      have hfac' : FactorsZariskiLocallyThrough B S hS p Y (f ≫ C₀.ι) := by
        intro y
        obtain ⟨W, hW, hWrep, hy, c, hc⟩ := hfac y
        refine ⟨W, hW, hWrep, hy, c ≫ yoneda.map z, ?_⟩
        rw [← Category.assoc, hc, Category.assoc, sqZ.w, Category.assoc]
      obtain ⟨T, g, i, hg, hgfp, hi, hig⟩ :=
        exists_isClosedImmersion_isFinite_isFinitePresentation_of_factorsZariskiLocallyThrough
          B S hS hZ X hX hXqc hXqs V p hpe' Y (f ≫ C₀.ι)
          (isFinite_comp B S hS hff (isFinite_of_isClosedImmersion B S hS _ hC₀.2)) hfac'
      have hsmall' : ∀ C' : Set (points B S hS X), IsClosed C' → C' ⊂ subspacePointSet B S hS X C₀ →
          ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
            IsCoverStratified B S hS W ∧ C' ⊆ subspacePointSet B S hS X W := by
        rw [hC₀pts]; exact hsmall
      have hne : (subspacePointSet B S hS X C₀).Nonempty := hC₀pts ▸ hirr.nonempty
      obtain ⟨W, hW, hWfp, hWs, hsub⟩ := exists_isCoverStratified_of_closedImmersion hZ hX hXqc hXqs
        hC₀ hsmall' hne hfs hffp hU hUd hUe hg hgfp hi hig
      exact ⟨W, hW, hWfp, hWs, hC₀pts ▸ hsub⟩)
  exact exists_finiteEtaleCoverStratification_of_isCoverStratified hX hWs hWpts

end AlgebraicGeometry.Space

end
