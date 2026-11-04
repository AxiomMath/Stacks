module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.FiberCriterion

/-!
# Universally injective unramified morphisms

For a morphism of schemes, being unramified and a monomorphism is equivalent to being unramified
and universally injective. These conditions also admit characterizations in terms of local finite
type and formal unramifiedness, or in terms of the scheme-theoretic fibres.

## Main results

* `AlgebraicGeometry.universallyInjective_unramified_tfae` gives the five equivalent
  characterizations.

## Implementation notes

The five entries of the `List.TFAE` are the five numbered conditions of the source, in order.
A fibre being empty is expressed by `IsEmpty`; when it is nonempty, the canonical morphism from
the fibre to the spectrum of the residue field is required to be an isomorphism.

## References

* [Stacks Project, Tag 05VH](https://stacks.math.columbia.edu/tag/05VH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private theorem isEmpty_or_isIso_of_mono_to_spec_field {K : Type u} [Field K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of K)) [Mono g] : IsEmpty X ∨ IsIso g := by
  rcases isEmpty_or_nonempty X with h | h
  · exact Or.inl h
  · exact Or.inr (isIso_of_mono_to_spec_field g)

private noncomputable def unitSigmaSpecIso (K : Type u) [Field K] :
    (∐ fun _ : ULift.{u} PUnit => Spec (.of K)) ≅ Spec (.of K) := by
  let i : ULift.{u} PUnit := ⟨PUnit.unit⟩
  refine ⟨Sigma.desc (fun _ => 𝟙 (Spec (.of K))),
    Sigma.ι (fun _ : ULift.{u} PUnit => Spec (.of K)) i, ?_, ?_⟩
  · exact Sigma.hom_ext _ _ fun _ ↦ by simp [i]
  · simp [i]

private theorem universallyInjective_of_fibers {X S : Scheme.{u}} (f : X ⟶ S)
    (hfib : ∀ s : S, IsEmpty (f.fiber s) ∨ IsIso (f.fiberToSpecResidueField s)) :
    UniversallyInjective f := by
  apply ((AlgebraicGeometry.tfae_universallyInjective f).out 2 1).mp
  intro K _ g₁ g₂ heq
  let x : X := g₁ (IsLocalRing.closedPoint K)
  let s : S := f x
  let φ : CommRingCat.of (S.residueField s) ⟶ CommRingCat.of K :=
    (Scheme.SpecToEquivOfField K S (g₁ ≫ f)).2
  have h₁ : Spec.map φ ≫ S.fromSpecResidueField s = g₁ ≫ f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S (g₁ ≫ f)
  have key : ∀ g : Spec (.of K) ⟶ X, g ≫ f = Spec.map φ ≫ S.fromSpecResidueField s →
      ∃ q : Spec (.of K) ⟶ f.fiber s,
        q ≫ f.fiberι s = g ∧ q ≫ f.fiberToSpecResidueField s = Spec.map φ :=
    fun g h ↦ ⟨pullback.lift g (Spec.map φ) h, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  obtain ⟨q₁, hg₁, hq₁⟩ := key g₁ h₁.symm
  obtain ⟨q₂, hg₂, hq₂⟩ := key g₂ (heq.symm.trans h₁.symm)
  have hq' : q₁ = q₂ := by
    rcases hfib s with hempty | hiso
    · exact (hempty.false (q₁ (IsLocalRing.closedPoint K))).elim
    · exact ((asIso (f.fiberToSpecResidueField s)).cancel_iso_hom_right q₁ q₂).mp
        (hq₁.trans hq₂.symm)
  rw [← hg₁, ← hg₂, hq']

/-- The equivalent characterizations of an unramified universally injective morphism of
schemes. -/
@[stacks 05VH, ega "IV 17.2.6", ega "IV 8.11.5.1" "loc. finite type case"]
public theorem universallyInjective_unramified_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE
      [ Unramified f ∧ Mono f,
        Unramified f ∧ UniversallyInjective f,
        LocallyOfFiniteType f ∧ Mono f,
        UniversallyInjective f ∧
          (LocallyOfFiniteType f ∧ FormallyUnramified f),
        LocallyOfFiniteType f ∧
          ∀ s : S, IsEmpty (f.fiber s) ∨ IsIso (f.fiberToSpecResidueField s) ] := by
  tfae_have 1 → 3 := by
    rintro ⟨hunr, hmono⟩
    exact ⟨(unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp hunr |>.1, hmono⟩
  tfae_have 3 → 4 := by
    rintro ⟨hft, hmono⟩
    exact ⟨inferInstance, hft, inferInstance⟩
  tfae_have 4 → 2 := by
    rintro ⟨hui, hft, hformal⟩
    exact ⟨(unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr ⟨hft, hformal⟩, hui⟩
  tfae_have 2 → 1 := by
    rintro ⟨hunr, hui⟩
    have : IsIso (pullback.diagonal f) :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr
        ⟨inferInstance, (UniversallyInjective.iff_diagonal f).mp hui⟩
    exact ⟨hunr, (pullback.isIso_diagonal_iff f).mp this⟩
  tfae_have 3 → 5 := by
    rintro ⟨hft, hmono⟩
    refine ⟨hft, fun s ↦ ?_⟩
    have hmonoFiber : Mono (f.fiberToSpecResidueField s) := by
      change Mono (pullback.snd f (S.fromSpecResidueField s))
      infer_instance
    exact @isEmpty_or_isIso_of_mono_to_spec_field (S.residueField s) inferInstance
      (f.fiber s) (f.fiberToSpecResidueField s) hmonoFiber
  tfae_have 5 → 4 := by
    rintro ⟨hft, hfib⟩
    have hunr : Unramified f :=
      unramified_of_fibres f fun s ↦ by
        rcases hfib s with hempty | hiso
        · let : IsEmpty (ULift.{u} PEmpty) := ⟨fun i => PEmpty.elim i.down⟩
          let K : ULift.{u} PEmpty → Type u := fun _ => S.residueField s
          let hK : ∀ i, Field (K i) := fun i => PEmpty.elim i.down
          let F : ULift.{u} PEmpty → Scheme := fun i =>
            Spec (@CommRingCat.of (K i) (hK i).toCommRing)
          let : IsEmpty (↑(∐ F)) :=
            ⟨fun z => ‹IsEmpty (ULift.{u} PEmpty)›.false ((AlgebraicGeometry.sigmaMk F).symm z).1⟩
          refine ⟨ULift.{u} PEmpty, K, hK, ?_, ?_, ?_, ?_, ?_⟩
          all_goals try (intro i; exact PEmpty.elim i.down)
          · exact (isInitialOfIsEmpty : IsInitial (f.fiber s)).uniqueUpToIso
              (isInitialOfIsEmpty : IsInitial (∐ F))
          · exact (isInitialOfIsEmpty : IsInitial (f.fiber s)).hom_ext _ _
        · refine ⟨ULift.{u} PUnit, fun _ => S.residueField s, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals try (intro i; infer_instance)
          · exact asIso (f.fiberToSpecResidueField s) ≪≫
              (unitSigmaSpecIso (S.residueField s)).symm
          · change (asIso (f.fiberToSpecResidueField s) ≪≫
              (unitSigmaSpecIso (S.residueField s)).symm).hom ≫
              Sigma.desc (fun _ => Spec.map (CommRingCat.ofHom
                (algebraMap (S.residueField s) (S.residueField s)))) =
              f.fiberToSpecResidueField s
            have hdesc : Sigma.desc (fun _ => Spec.map (CommRingCat.ofHom
                (algebraMap (S.residueField s) (S.residueField s)))) =
                (unitSigmaSpecIso (S.residueField s)).hom := by
              apply Sigma.hom_ext
              intro i
              simp [unitSigmaSpecIso]
            rw [hdesc]
            simp
    exact ⟨universallyInjective_of_fibers f hfib, hft,
      ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp hunr).2⟩
  tfae_finish

end AlgebraicGeometry

end
