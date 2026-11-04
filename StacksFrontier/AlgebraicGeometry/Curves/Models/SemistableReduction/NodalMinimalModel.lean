module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.RegularNodalModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelUniqueness
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Nodal
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase

/-!
# Semistable reduction and minimal models

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K`. This file proves the implications of [Stacks, Tag 0CDG]
that do not use the uniqueness of minimal models:

* (1) ⇒ (2): if `C` has a proper at-worst-nodal model, it has an at-worst-nodal minimal model. A
  proper nodal model is resolved by blowups at its singular points into a regular one
  ([Stacks, Tag 0CDE]), a regular proper model contracts to a minimal model by a sequence of
  contractions of exceptional curves of the first kind ([Stacks, Tag 0CD9]), and each contraction
  keeps the family at-worst-nodal ([Stacks, Tag 0CDF]).
* (2) ⇒ (1): a minimal model is a proper model.
* (3) ⇒ (2): a minimal model exists ([Stacks, Tag 0C2W]).

## Main results

* `Stacks.Models.ExceptionalContractionSequence.isAtWorstNodalOfRelativeDimensionOne` — the
  target of a sequence of contractions of exceptional curves of an at-worst-nodal model is
  at-worst-nodal.
* `Stacks.Models.exists_isMinimalModel_isAtWorstNodal_of_hasSemistableReduction` — (1) ⇒ (2).
* `Stacks.Models.hasSemistableReduction_of_isMinimalModel_of_isAtWorstNodal` — (2) ⇒ (1).
* `Stacks.Models.exists_isMinimalModel_isAtWorstNodal_of_forall` — (3) ⇒ (2).

## References

* [Stacks Project, Tag 0CDG](https://stacks.math.columbia.edu/tag/0CDG)
* [Stacks Project, Tag 0CDE](https://stacks.math.columbia.edu/tag/0CDE)
* [Stacks Project, Tag 0CD9](https://stacks.math.columbia.edu/tag/0CD9)
* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
* [Stacks Project, Tag 0C2W](https://stacks.math.columbia.edu/tag/0C2W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsFractionRing R K] in
/-- **Contracting exceptional curves keeps a model at-worst-nodal** ([Stacks, Tag 0CDF] along a
sequence): if the source of a sequence of contractions of exceptional curves of the first kind is
at-worst-nodal of relative dimension one over `R`, so is its target. The structure morphism of
each intermediate model is the unique factorization through the contraction, so it is the one
[Stacks, Tag 0CDF] provides. -/
public theorem ExceptionalContractionSequence.isAtWorstNodalOfRelativeDimensionOne
    {C : Scheme.{u}} {c : C ⟶ Spec (.of K)} {X Y : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    {q : Y ⟶ Spec (.of R)} {g : X ⟶ Y} (hs : ExceptionalContractionSequence c p q g)
    (hp : IsAtWorstNodalOfRelativeDimensionOne p) :
    IsAtWorstNodalOfRelativeDimensionOne q := by
  induction hs with
  | refl p => exact hp
  | step b D k eE hE hb hbp e' hmod hproper hreg rest ih =>
    apply ih
    obtain ⟨f', hf', hn⟩ :=
      isAtWorstNodalOfRelativeDimensionOne_of_isContractionOfExceptionalCurve D k eE hE b hb _ hp
    obtain ⟨_, -, huniq⟩ := exists_factor_of_contraction D k eE b hb (A := R) _
    rw [← (huniq _ hf').trans (huniq _ hbp).symm]
    exact hn

/-- **[Stacks, Tag 0CDG], (1) ⇒ (2).** A curve with a proper model which is at-worst-nodal of
relative dimension one has a minimal model which is at-worst-nodal of relative dimension one. -/
public theorem exists_isMinimalModel_isAtWorstNodal_of_hasSemistableReduction {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (h : HasSemistableReduction R c hc) :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p e ∧ IsAtWorstNodalOfRelativeDimensionOne p := by
  obtain ⟨X, p, e, hmod, hprop, hreg, hnod⟩ :=
    exists_isModel_isProper_isRegular_isAtWorstNodal c hc h
  have := hprop
  obtain ⟨X₀, p₀, e₀, g, hseq, hmin⟩ := exists_exceptionalContractionSequence_isMinimalModel c
    ((isProjective_iff_isProjectiveMorphism_of_isAffine c).mp hc) inferInstance p e hmod hreg
  exact ⟨X₀, p₀, e₀, hmin, hseq.isAtWorstNodalOfRelativeDimensionOne hnod⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **[Stacks, Tag 0CDG], (2) ⇒ (1).** A minimal model is a proper model. -/
public theorem hasSemistableReduction_of_isMinimalModel_of_isAtWorstNodal {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmin : IsMinimalModel c p e) (hnod : IsAtWorstNodalOfRelativeDimensionOne p) :
    HasSemistableReduction R c hc :=
  ⟨X, p, e, hmin.isModel, hmin.isProper, hnod⟩

/-- **[Stacks, Tag 0CDG], (3) ⇒ (2).** If every minimal model is at-worst-nodal of relative
dimension one, there is one, a minimal model existing by [Stacks, Tag 0C2W]. -/
public theorem exists_isMinimalModel_isAtWorstNodal_of_forall {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (h : ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p e → IsAtWorstNodalOfRelativeDimensionOne p) :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p e ∧ IsAtWorstNodalOfRelativeDimensionOne p := by
  obtain ⟨X, p, e, hmin⟩ := exists_isMinimalModel (R := R) c
    ((isProjective_iff_isProjectiveMorphism_of_isAffine c).mp hc) inferInstance
  exact ⟨X, p, e, hmin, h X p e hmin⟩

/-- **Two minimal models of a curve of positive genus are isomorphic over `R`**
([Stacks, Tag 0C6B]), so a property of the structure morphism preserved by composing with
isomorphisms passes from one to the other. -/
public theorem exists_iso_comp_eq_of_isMinimalModel_of_pos_genus {C X Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 0 < genus c)
    (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R))
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsMinimalModel c p eX) (hY : IsMinimalModel c q eY) :
    ∃ φ : Y ≅ X, φ.hom ≫ p = q := by
  obtain ⟨φ, ⟨hφ, -⟩, -⟩ := (exists_isMinimalModel_and_existsUnique_iso c
    ((isProjective_iff_isProjectiveMorphism_of_isAffine c).mp hc) inferInstance hg).2
      p q eX eY hX hY
  exact ⟨φ.symm, by rw [Iso.symm_hom, ← hφ, Iso.inv_hom_id_assoc]⟩

end Stacks.Models

end
