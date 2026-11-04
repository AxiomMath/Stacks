module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.HigherGenus
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.GenusOne
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.LocalizationDVR
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.GenusZeroSplitting
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.Characterization
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RationalPointHyperplane

/-!
# The semistable reduction theorem

[Stacks, Tag 0CDN]: let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth
projective curve over `K` with `H⁰(C, 𝒪_C) = K`. Then there is an extension of discrete valuation
rings `R ⊆ R'` inducing a finite separable extension `K'/K` of fraction fields such that `C_{K'}`
has semistable reduction; more precisely

1. in genus `0`, a separable `K'/K` of degree `2` with `C_{K'} ≅ 𝐏¹_{K'}`, the generic fibre of
   the smooth projective `𝐏¹_{R'}` over the integral closure `R'` of `R` in `K'`;
2. in genus `1`, a finite separable `K'/K` with `C_{K'}` semistable over every `R'_𝔪`, the special
   fibre of every minimal model being a smooth genus one curve or a cycle of rational curves;
3. in genus `g ≥ 2`, a finite separable `K'/K` of degree at most `B_g` ([Stacks, Tag 0CEJ]) with
   `C_{K'}` semistable over every `R'_𝔪`.

## Main results

* `Stacks.Models.semistableReduction_of_statements` — the whole statement, untagged, from the
  statements of [Stacks, Tags 0CDU, 0CE6 and 0C20] ([Stacks, Tags 0CA6 and 0CE9] instantiated);
  clause (1) is `AlgebraicGeometry.SemistableReduction.genusZero_splitting` and [Stacks, Tag 0C6U]
  is instantiated
  (`AlgebraicGeometry.ProjectiveLineCriterion.nonempty_iso_projectiveLine_of_section`).

## References

* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] AddSubgroup.torsionBy.zmodModule

namespace Stacks.Models

/-- [Stacks, Tag 0C6U] in the form used by section 0CEG: a smooth proper curve of genus `0` with
`H⁰ = k` and a rational point is the projective line. -/
theorem nonempty_iso_projectiveLine_of_isRationalPoint (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    (hgenus : genus f = 0) (hx : ∃ x, IsRationalPoint f x) :
    Nonempty (Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) := by
  obtain ⟨x, hx⟩ := hx
  exact ProjectiveLineCriterion.nonempty_iso_projectiveLine_of_section k f hgenus
    (ptOfIsRationalPoint f x hx) (ptOfIsRationalPoint_comp f x hx)

/-- **[Stacks, Tag 0CDN], from the statements of its inputs.** The whole semistable reduction
theorem; the premises are the statements of [Stacks, Tags 0CDU (1) and (2),
0CE6 and 0C20] in the forms used. -/
theorem semistableReduction_of_statements
    (h0CDU₁ : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
      [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (n : ℕ),
      IsUnit (n : k) → genus f = 1 →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
        Algebra.IsSeparable k k' ∧
        (∃ x : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
          x ≫ pullback.snd _ _ = 𝟙 _) ∧
        Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
          (Fin 2 → ZMod n)))
    (h0CDU₂ : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
      [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (n : ℕ),
      IsUnit (n : k) → 2 ≤ genus f →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
        Algebra.IsSeparable k k' ∧
        Module.finrank k k' ≤ (2 * genus f - 2) * (n ^ (2 * genus f)).factorial ∧
        (∃ x : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
          x ≫ pullback.snd _ _ = 𝟙 _) ∧
        Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
          (Fin (2 * genus f) → ZMod n)))
    (h0CE6 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
      (_ : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (_ : IsUnit (ℓ : k)),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus g + geometricGenus k g)
    (h0C20 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [IsReduced X] (_hdim : topologicalKrullDim (X : Type u) = 1)
      (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)))
    (h0C20eq : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
      (_hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
            genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) ↔
          ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
            Stacks.Curves.IsMulticrossSingularity k X x))
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] :
    haveI : IsProper c := hproj.isProper
    (∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
        (_ : Algebra R' K') (_ : IsFractionRing R' K') (_ : Algebra R R')
        (_ : IsScalarTower R R' K'), IsLocalHom (algebraMap R R') ∧
        HasSemistableReduction R'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (hproj.pullback_snd _)) ∧
    (genus c = 0 →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
        (_ : IsScalarTower R K K'),
        FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧ Module.finrank K K' = 2 ∧
        Nonempty (Over.mk (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≅
          Over.mk (projectiveSpaceOver 1 (Spec (.of K')) ↘ Spec (.of K'))) ∧
        IsFractionRing (integralClosure R K') K' ∧
        Smooth (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
          Spec (.of (integralClosure R K'))) ∧
        IsProjective (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
          Spec (.of (integralClosure R K'))) ∧
        Nonempty (Over.mk (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≅
          Over.mk (pullback.snd (C := Scheme.{u})
            (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
              Spec (.of (integralClosure R K')))
            (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K')))))) ∧
    (genus c = 1 →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
        (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
        HasSemistableReductionAtMaximalIdeals R K'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (hproj.pullback_snd _) ∧
        HasGenusOneMinimalFibresAtMaximalIdeals R K'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) ∧
    (2 ≤ genus c →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
        (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
        Module.finrank K K' ≤
          AlgebraicGeometry.SemistableReduction.semistableReductionDegreeBound (genus c) ∧
        HasSemistableReductionAtMaximalIdeals R K'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (hproj.pullback_snd _)) := by
  have : IsProper c := hproj.isProper
  have h1 := fun hg : genus c = 0 =>
    AlgebraicGeometry.SemistableReduction.genusZero_splitting R K c hproj hg
  have h2 := fun hg : genus c = 1 =>
    exists_genusOne_semistableReduction_of_statements
      (fun S hexc n e =>
        S.isMinimal_associatedNumericalType_of_not_hasExceptionalCurveOfFirstKind hexc n e)
      h0CDU₁ h0CE6 h0C20 h0C20eq
      (fun k _ X f _ _ _ _ => nonempty_iso_projectiveLine_of_isRationalPoint k X f) R K c hproj hg
  have h3 := fun hg : 2 ≤ genus c =>
    exists_hasSemistableReductionAtMaximalIdeals_of_two_le_genus_of_statements
      h0CDU₂ h0CE6 h0C20 h0C20eq R K c hproj hg
  refine ⟨?_, h1, h2, h3⟩
  -- the main assertion, from whichever clause applies
  have hmain : ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      HasSemistableReductionAtMaximalIdeals R K'
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (hproj.pullback_snd _) := by
    rcases Nat.lt_or_ge (genus c) 2 with hlt | hge
    · obtain hgc | hgc : genus c = 0 ∨ genus c = 1 := by omega
      · obtain ⟨K', iF, iA, iRK, iT, hfin, hsep, -, ⟨eC⟩, -⟩ := h1 hgc
        open AlgebraicGeometry.SemistableReduction in
        exact ⟨K', iF, iA, iRK, iT, hfin, hsep,
          hasSemistableReductionAtMaximalIdeals_of_iso_projectiveLine
            R K' _ _ eC⟩
      · obtain ⟨K', iF, iA, iRK, iT, hfin, hsep, hss, -⟩ := h2 hgc
        exact ⟨K', iF, iA, iRK, iT, hfin, hsep, hss⟩
    · obtain ⟨K', iF, iA, iRK, iT, hfin, hsep, -, hss⟩ := h3 hge
      exact ⟨K', iF, iA, iRK, iT, hfin, hsep, hss⟩
  obtain ⟨K', iF, iA, iRK, iT, hfin, hsep, hss⟩ := hmain
  exact ⟨K', iF, iA, iRK, iT, hfin, hsep,
    exists_hasSemistableReduction_of_hasSemistableReductionAtMaximalIdeals R K K' _ _ hss⟩

end Stacks.Models

end
