module

public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibreRankSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods

/-!
# The fibre-degree stratification with its fpqc-locality hypotheses discharged

Finiteness and finite local freeness of a given rank are fpqc local on the target. With these
inputs supplied, the fibre-degree stratification of a flat, locally finitely presented,
separated, locally quasi-finite morphism from a scheme to an algebraic space, and the
stratification clause of [Stacks, Tag 0BBN], hold as soon as the corresponding stratification
exists for morphisms of schemes (the hypothesis `h086R`). That hypothesis is proved here for
quasi-compact morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.exists_antitone_opens_factors_iff_fibreDegree_ge_of_quasiCompact`:
  the fibre-degree stratification of a flat, locally finitely presented, separated, locally
  quasi-finite and quasi-compact morphism of schemes, in terms of factorisations of
  field-valued points.
* `AlgebraicGeometry.Space.exists_antitone_openSubspaces_iff_fibreDegree_ge_of_h086R`: the
  fibre-degree stratification for a morphism from a scheme to an algebraic space, given
  `h086R`.
* `AlgebraicGeometry.Space.exists_openFiltration_quasiCompactPoint_mem_stratum_of_h086R`: the
  stratification clause of [Stacks, Tag 0BBN], given `h086R`.

## References

* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 086R](https://stacks.math.columbia.edu/tag/086R)
* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 0BBN](https://stacks.math.columbia.edu/tag/0BBN)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Let `g : Z ⟶ Y` be a flat, locally finitely presented, separated, locally quasi-finite and
quasi-compact morphism of schemes. Then there is a decreasing chain of opens
`Y = V 0 ⊇ V 1 ⊇ V 2 ⊇ …` of `Y` such that a morphism from the spectrum of a field factors
through `V d` exactly when the base change of `g` along it either fails to be finite or is
finite locally free of some rank at least `d`. -/
theorem exists_antitone_opens_factors_iff_fibreDegree_ge_of_quasiCompact
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [Flat g] [LocallyOfFinitePresentation g]
    [_root_.AlgebraicGeometry.IsSeparated g] [LocallyQuasiFinite g] [QuasiCompact g] :
    ∃ V : ℕ → Y.Opens, V 0 = ⊤ ∧ Antitone V ∧
      ∀ (d : ℕ) (k : Type u) (_ : Field k) (c : Spec (.of k) ⟶ Y),
        (∃ h : Spec (.of k) ⟶ (V d).toScheme, h ≫ (V d).ι = c) ↔
          (¬ _root_.AlgebraicGeometry.IsFinite (pullback.fst c g) ∨
            ∃ r : ℕ, d ≤ r ∧
              Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst c g) r) := by
  obtain ⟨V, h0, hanti, hiff⟩ := exists_antitone_opens_iff_fibreDegree_ge_of_quasiCompact g
  refine ⟨V, h0, hanti, fun d k hk c => ?_⟩
  refine (factors_through_open_iff_mem k c (V d)).trans ?_
  rw [Subsingleton.elim (default : Spec (.of k)) (IsLocalRing.closedPoint k)]
  exact hiff d k hk c

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : h_V ⟶ X` be a flat, locally finitely presented, separated, locally quasi-finite
morphism from a scheme to an algebraic space `X` over `S`, and assume `h086R`, the same
stratification for morphisms of schemes. Then there is a decreasing chain of open subspaces
`X = X₀ ⊇ X₁ ⊇ X₂ ⊇ …` of `X` such that a field-valued point of `X` factors through `X_d`
exactly when the fibre of `f` over it has degree at least `d`, a nonfinite fibre counting as
having infinite degree. -/
theorem exists_antitone_openSubspaces_iff_fibreDegree_ge_of_h086R
    (h086R : ∀ {Z Y : Scheme.{u}} (g : Z ⟶ Y), Flat g → LocallyOfFinitePresentation g →
      _root_.AlgebraicGeometry.IsSeparated g → LocallyQuasiFinite g →
      ∃ V : ℕ → Y.Opens, V 0 = ⊤ ∧ Antitone V ∧
        ∀ (d : ℕ) (k : Type u) (_ : Field k) (c : Spec (.of k) ⟶ Y),
          (∃ h : Spec (.of k) ⟶ (V d).toScheme, h ≫ (V d).ι = c) ↔
            (¬ _root_.AlgebraicGeometry.IsFinite (pullback.fst c g) ∨
              ∃ r : ℕ, d ≤ r ∧
                Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst c g) r))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : BigFppfOver B S hS) (f : yoneda.obj V ⟶ X)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hsep : IsSeparated B S hS f) (hlqf : IsLocallyQuasiFinite B S hS f) :
    ∃ U : ℕ → Subfunctor X,
      (∀ d, IsOpenSubspace B S hS (U d)) ∧ U 0 = ⊤ ∧ Antitone U ∧
      ∀ (d : ℕ) (p : FieldValuedPoint B S hS X),
        (∃ g : yoneda.obj (FieldValuedPoint.siteObject B S hS X p) ⟶ (U d).toFunctor,
          g ≫ (U d).ι = yonedaEquiv.symm p.value) ↔
        (¬ (MorphismProperty.inverseImage
              (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) f) ∨
          ∃ r : ℕ, d ≤ r ∧
            (MorphismProperty.inverseImage
              (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) f)) :=
  exists_antitone_openSubspaces_iff_fibreDegree_ge B S hS
    Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc h086R hX V f hflat hfp hsep
    hlqf

/-- Assume `h086R`, the fibre-degree stratification for morphisms of schemes. A quasi-compact
algebraic space `X` has a surjective étale morphism `φ` from an affine scheme and a decreasing
chain of open subspaces `X = U 0 ⊇ U 1 ⊇ …`, a field-valued point lying in `U d` exactly when the
fibre of `φ` over it has degree at least `d`, such that every point represented by a
quasi-compact field-valued point lies in some stratum `U p \ U (p + 1)`. -/
theorem exists_openFiltration_quasiCompactPoint_mem_stratum_of_h086R
    (h086R : ∀ {Z Y : Scheme.{u}} (g : Z ⟶ Y), Flat g → LocallyOfFinitePresentation g →
      _root_.AlgebraicGeometry.IsSeparated g → LocallyQuasiFinite g →
      ∃ V : ℕ → Y.Opens, V 0 = ⊤ ∧ Antitone V ∧
        ∀ (d : ℕ) (k : Type u) (_ : Field k) (c : Spec (.of k) ⟶ Y),
          (∃ h : Spec (.of k) ⟶ (V d).toScheme, h ≫ (V d).ι = c) ↔
            (¬ _root_.AlgebraicGeometry.IsFinite (pullback.fst c g) ∨
              ∃ r : ℕ, d ≤ r ∧
                Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst c g) r))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) :
    ∃ (A : BigFppfOver B S hS) (φ : yoneda.obj A ⟶ X) (U : ℕ → Subfunctor X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf φ ∧
      IsEtale B S hS φ ∧
      (∀ p, IsOpenSubspace B S hS (U p)) ∧ U 0 = ⊤ ∧ Antitone U ∧
      (∀ (d : ℕ) (q : FieldValuedPoint B S hS X),
        q.class B S hS X ∈ Set.range (pointsMap B S hS (U d).toFunctor (U d).ι) ↔
          (¬ (MorphismProperty.inverseImage
                (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
                (BigFppfOver.toScheme B S hS)).presheaf
                  (pullback.fst (yonedaEquiv.symm q.value) φ) ∨
            ∃ r : ℕ, d ≤ r ∧
              (MorphismProperty.inverseImage
                (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
                (BigFppfOver.toScheme B S hS)).presheaf
                  (pullback.fst (yonedaEquiv.symm q.value) φ))) ∧
      (∀ (x : points B S hS X) (q : FieldValuedPoint B S hS X),
        q.class B S hS X = x → IsQuasiCompact B S hS (fieldMorphism B S hS X q) →
        ∃ p : ℕ,
          x ∈ Set.range (pointsMap B S hS (U p).toFunctor (U p).ι) ∧
          x ∉ Set.range (pointsMap B S hS (U (p + 1)).toFunctor (U (p + 1)).ι)) :=
  exists_openFiltration_quasiCompactPoint_mem_stratum B S hS
    Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc h086R hX hqc

end AlgebraicGeometry.Space

end
