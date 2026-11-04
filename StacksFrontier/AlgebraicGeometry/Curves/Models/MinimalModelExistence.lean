module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractionStep
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModel
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContraction
public import StacksFrontier.AlgebraicGeometry.Models.RegularProperModelExists
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuasiProjectiveRegularSurface
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Contracting a regular proper model down to a minimal model

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth projective curve
over `K` with `H⁰(C, 𝒪_C) = K`. A regular proper model of `C` is obtained from a minimal model by
a finite sequence of blowups at closed points; read the other way, a regular proper model is
contracted to a minimal model by finitely many contractions of exceptional curves of the first
kind ([Stacks, Tag 0CD9]), and consequently a minimal model exists ([Stacks, Tag 0C2W]).

## Main definitions

* `Stacks.Models.ExceptionalContractionSequence` — a sequence `X = Xₘ → ⋯ → X₀` of regular proper
  models of `C`, each morphism the contraction of an exceptional curve of the first kind.

## Main results

* `Stacks.Models.exists_exceptionalContractionSequence_of_step` — the induction of the proof of
  Tag 0CD9, from a single contraction step which strictly decreases a natural number.
* `Stacks.Models.isProjective_of_isModel_of_isRegular` — a regular proper model is projective
  over `R` ([Stacks, Tag 0C5P]).
* `Stacks.Models.exists_exceptionalContractionSequence_isMinimalModel` — [Stacks, Tag 0CD9].
* `Stacks.Models.exists_isMinimalModel` — [Stacks, Tag 0C2W].

## References

* [Stacks Project, Tag 0CD9](https://stacks.math.columbia.edu/tag/0CD9)
* [Stacks Project, Tag 0C2W](https://stacks.math.columbia.edu/tag/0C2W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A sequence of contractions of exceptional curves of the first kind between regular proper
models of `C`: `ExceptionalContractionSequence c p q g` says that `g : X ⟶ Y` is a composite
`X = Xₘ → Xₘ₋₁ → ⋯ → X₀ = Y` of morphisms over `Spec R`, from the structure morphism `p` of `X`
to the structure morphism `q` of `Y`, each of which is the contraction of an exceptional curve of
the first kind, and each of whose targets is a regular proper model of `C`. The source `X` is not
required to be a model by the predicate itself: that is a hypothesis of every statement using
it. -/
inductive ExceptionalContractionSequence {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) :
    ∀ {X Y : Scheme.{u}}, (X ⟶ Spec (.of R)) → (Y ⟶ Spec (.of R)) → (X ⟶ Y) → Prop
  /-- The empty sequence. -/
  | refl {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) : ExceptionalContractionSequence c p p (𝟙 X)
  /-- A contraction `b : X ⟶ X'` of an exceptional curve of the first kind, onto a regular proper
  model `X'` of `C`, followed by a sequence of contractions starting at `X'`. -/
  | step {X X' Y : Scheme.{u}} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
      {q : Y ⟶ Spec (.of R)} {g : X' ⟶ Y} (b : X ⟶ X') (D : X.IdealSheafData) (k : Type u)
      [Field k] (eE : projectiveLineProj k ≅ D.subscheme)
      (hE : D.IsExceptionalCurveOfFirstKind k eE) (hb : IsContractionOfExceptionalCurve D b)
      (hbp : b ≫ p' = p)
      (e' : C ≅ pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (hmod : IsModel c p' e') (hproper : IsProper p') (hreg : IsRegular X')
      (rest : ExceptionalContractionSequence c p' q g) :
      ExceptionalContractionSequence c p q (b ≫ g)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **The induction of the proof of [Stacks, Tag 0CD9].** Suppose that every regular proper model
`X` of `C` containing an exceptional curve of the first kind `E` admits a contraction of `E` onto a
regular proper model `X'` of `C`, with `μ X' < μ X` for some natural number `μ` (the hypothesis
`step`; in the source, `μ` is the number of irreducible components of the special fibre). Then
every regular proper model of `C` is contracted to a minimal model by a sequence of contractions
of exceptional curves of the first kind. -/
theorem exists_exceptionalContractionSequence_of_step {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop))
    (μ : ∀ {X : Scheme.{u}}, (X ⟶ Spec (.of R)) → ℕ)
    (step : ∀ {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsModel c p e → IsProper p → IsRegular X →
      ∀ (D : X.IdealSheafData) (k : Type u) [Field k] (eE : projectiveLineProj k ≅ D.subscheme),
        D.IsExceptionalCurveOfFirstKind k eE →
        ∃ (X' : Scheme.{u}) (b : X ⟶ X') (p' : X' ⟶ Spec (.of R))
          (e' : C ≅ pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
          IsContractionOfExceptionalCurve D b ∧ b ≫ p' = p ∧ IsModel c p' e' ∧ IsProper p' ∧
            IsRegular X' ∧ μ p' < μ p)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) [IsProper p] (hreg : IsRegular X) :
    ∃ (X₀ : Scheme.{u}) (p₀ : X₀ ⟶ Spec (.of R))
      (e₀ : C ≅ pullback p₀ (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (g : X ⟶ X₀),
      ExceptionalContractionSequence c p p₀ g ∧ IsMinimalModel c p₀ e₀ := by
  -- strong induction on `μ p`
  suffices H : ∀ (n : ℕ) {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      μ p = n → IsModel c p e → IsProper p → IsRegular X →
      ∃ (X₀ : Scheme.{u}) (p₀ : X₀ ⟶ Spec (.of R))
        (e₀ : C ≅ pullback p₀ (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (g : X ⟶ X₀),
        ExceptionalContractionSequence c p p₀ g ∧ IsMinimalModel c p₀ e₀ from
    H _ p e rfl hmod inferInstance hreg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X p e hn hmod hprop hreg
    by_cases hX : X.HasExceptionalCurveOfFirstKind
    · obtain ⟨k, hk, D, eE, hE⟩ := hX
      let := hk
      obtain ⟨X', b, p', e', hb, hbp, hmod', hprop', hreg', hlt⟩ :=
        step p e hmod hprop hreg D k eE hE
      obtain ⟨X₀, p₀, e₀, g, hseq, hmin⟩ := ih (μ p') (hn ▸ hlt) p' e' rfl hmod' hprop' hreg'
      exact ⟨X₀, p₀, e₀, b ≫ g, .step b D k eE hE hb hbp e' hmod' hprop' hreg' hseq, hmin⟩
    · exact ⟨X, p, e, 𝟙 X, .refl p, ⟨hproj, hH0, hmod, hprop, hreg, hX⟩⟩

/-- **A regular proper model is projective over `R`.** Its total space has dimension at most two
(`Stacks.Models.topologicalKrullDim_le_two_of_isModel`), so this is [Stacks, Tag 0C5P]. -/
theorem isProjective_of_isModel_of_isRegular {C X : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) [IsProper p] (hreg : IsRegular X) : IsProjective p :=
  isProjective_of_isRegular_of_topologicalKrullDim_le_two p hreg
    (topologicalKrullDim_le_two_of_isModel c p e hmod)

/-- **Stacks Project, Tag 0CD9.** Let `C` be a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K`. If `X` is a regular proper model for `C`, then there is a sequence of morphisms
`X = Xₘ → Xₘ₋₁ → ⋯ → X₁ → X₀` of regular proper models of `C`, each the contraction of an
exceptional curve of the first kind, such that `X₀` is a minimal model.

The proof is the source's: `X` is projective over `R` ([Stacks, Tag 0C5P]), so an exceptional
curve of the first kind on it can be contracted onto a regular projective model
([Stacks, Tag 0C2N]), and the number of points of the special fibre with one-dimensional local
ring — the generic points of the irreducible components of the special fibre — drops by one. -/
@[stacks 0CD9]
theorem exists_exceptionalContractionSequence_isMinimalModel {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)) (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) [IsProper p] (hreg : IsRegular X) :
    ∃ (X₀ : Scheme.{u}) (p₀ : X₀ ⟶ Spec (.of R))
      (e₀ : C ≅ pullback p₀ (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (g : X ⟶ X₀),
      ExceptionalContractionSequence c p p₀ g ∧ IsMinimalModel c p₀ e₀ :=
  exists_exceptionalContractionSequence_of_step c hproj hH0
    (fun {_} q => codimOneSpecialFibreCard q)
    (fun q eq hq hqp hqreg D k _ eE hE => by
      have := hqp
      obtain ⟨X', b, p', e', hb, hbp, hmod', hprop', -, hreg', hlt⟩ :=
        exists_isContractionOfExceptionalCurve_isModel c q eq hq
          (isProjective_of_isModel_of_isRegular c q eq hq hqreg) hqreg hE
      exact ⟨X', b, p', e', hb, hbp, hmod', hprop', hreg', hlt⟩)
    p e hmod hreg

/-- **Stacks Project, Tag 0C2W.** Let `C` be a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K`. A minimal model of `C` exists.

The proof is the source's: the scheme-theoretic image of `C` in a projective space over `R` is a
projective model, a resolution of its singularities is a regular proper model
(`Stacks.Models.exists_isModel_isProper_isRegular`, through [Stacks, Tag 0C2S] and
[Stacks, Tag 0C2U]), and [Stacks, Tag 0CD9] contracts it to a minimal model. -/
@[stacks 0C2W, sga "7 I 3.5" "partial"]
theorem exists_isMinimalModel {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : Stacks.HProjective.IsHProjective c)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)) :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p e := by
  obtain ⟨X, p, e, hmod, hprop, hreg, -⟩ := exists_isModel_isProper_isRegular (R := R) c hproj
  have := hprop
  obtain ⟨X₀, p₀, e₀, -, -, hmin⟩ :=
    exists_exceptionalContractionSequence_isMinimalModel c hproj hH0 p e hmod hreg
  exact ⟨X₀, p₀, e₀, hmin⟩

end Stacks.Models

end
