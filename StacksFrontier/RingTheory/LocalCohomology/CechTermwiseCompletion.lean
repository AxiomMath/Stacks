module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DegreewiseInvertedMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import StacksFrontier.Homology.DerivedComplete.CechReflectionTriangulated
public import StacksFrontier.RingTheory.Cech.Tensor
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletionUnitAdicCompletion
public import StacksFrontier.RingTheory.LocalCohomology.CechAdicQuotient
public import StacksFrontier.RingTheory.LocalCohomology.CechModel.BoundedTerms

/-!
# The termwise completion of a Čech complex is its derived completion

Let `A` be a Noetherian ring, `I` an ideal, `g₁, …, g_r` elements of `A` and `M` a finite
`A`-module. The termwise `I`-adic completion `C^•(g; M)^∧` of the extended Čech complex is a
model of its derived completion. More precisely:

* derived `I`-adic completion inverts the map `C^•(g; M) ⟶ C^•(g; M)^∧`;
* the termwise completion is derived `I`-complete.

Every term of `C^•(g; M)` is `M ⊗_A F` for a flat module `F`, a finite sum of localizations of
`A`. Derived completion of such a module, placed in one degree, is its adic completion
(Stacks 0EEU). An exact functor that inverts a map of bounded complexes in every degree inverts
the map itself. Applied to a triangulated model of derived completion, this gives the first
statement. The second holds because adic completions are complete and derived complete objects
form a triangulated subcategory.

This is the input from which the proof of Stacks 0EIF reads the conclusion of Stacks 0EFL on
the Čech complex in degrees `0` and `1`. An isomorphism on `Hⁱ` in `D(A)` of the image of the
completion map is one on `Hⁱ` of the complexes by
`NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ i)`, which is the form
`Stacks.LocalCohomology.exists_cycles_lift_of_isIso_homologyMap` consumes.

## Main results

* `Stacks.LocalCohomology.isIso_adicCompletionFunctor_map_toTermwiseAdicCompletion`: derived
  completion inverts `C^•(g; M) ⟶ C^•(g; M)^∧`.
* `Stacks.LocalCohomology.isDerivedComplete_termwiseAdicCompletion`: `C^•(g; M)^∧` is derived
  `I`-complete.

## References

* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (I : Ideal A) {r : ℕ} (g : Fin r → A) (M : ModuleCat.{u} A)

/-- **The terms of the termwise completion of the Čech complex vanish outside degrees
`0, …, r`.** -/
theorem isZero_termwiseAdicCompletion_extendedCechComplex_X (i : ℤ)
    (hi : i < 0 ∨ (r : ℤ) + 1 ≤ i) :
    IsZero ((HomologicalComplex.termwiseAdicCompletion I (extendedCechComplex.{0} g M)).X i) :=
  (AdicCompletion.moduleCatFunctor I).map_isZero (isZero_extendedCechComplex_X g M i hi)

/-- **The termwise completion of the Čech complex is derived `I`-complete.** Its terms are adic
completions, which are complete, so each of them placed in any degree is derived complete; the
complex is bounded, and derived complete objects are closed under extensions. -/
theorem isDerivedComplete_termwiseAdicCompletion (hI : I.FG) :
    IsDerivedComplete I (DerivedCategory.Q.obj
      (HomologicalComplex.termwiseAdicCompletion I (extendedCechComplex.{0} g M))) := by
  refine prop_Q_obj_of_bounded_terms (Dualizing.derivedCompleteProperty A I) (r + 1) 0 _
    (fun i hi => isZero_termwiseAdicCompletion_extendedCechComplex_X I g M i
      (by rcases hi with hi | hi <;> [left; right] <;> push_cast at hi ⊢ <;> omega))
    (fun i q => ?_)
  have h0 : Dualizing.derivedCompleteProperty A I
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I ((extendedCechComplex.{0} g M).X i)))) :=
    (isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective A I _).1
      (AdicCompletion.isAdicComplete (I := I) hI)
  have e := ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-q) q 0
    (by omega)).app (ModuleCat.of A (AdicCompletion I ((extendedCechComplex.{0} g M).X i)))
  exact (Dualizing.derivedCompleteProperty A I).prop_of_iso e
    ((Dualizing.derivedCompleteProperty A I).le_shift (-q) _ h0)

/-- **A term of the Čech complex, placed in degree `0`, has derived completion its adic
completion**, in the form consumed by `Dualizing.isIso_derivedCompletion_map_adicCompletionOf`:
an abstract isomorphism. The term in degree `p ≥ 0` is `M ⊗_A C^p(g; A)`, with `C^p(g; A)` a
finite sum of localizations of `A`, hence flat. -/
theorem nonempty_derivedCompletion_iso_extendedCechComplex_X [IsNoetherianRing A]
    [Module.Finite A M] (hI : I.FG) (p : ℕ) :
    Nonempty ((Dualizing.derivedCompleteProperty A I).ι.obj
        ((Dualizing.derivedCompletion A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A ((extendedCechComplex.{0} g M).X (p : ℤ))))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I ((extendedCechComplex.{0} g M).X (p : ℤ))))) := by
  have hp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := by simp
  have hflat : Module.Flat A (_root_.Cech.cechTerm g A p) := by
    unfold _root_.Cech.cechTerm _root_.Cech.cechMod
    infer_instance
  let l : ((extendedCechComplex.{0} g M).X (p : ℤ)) ≃ₗ[A]
      TensorProduct A M (_root_.Cech.cechTerm g A p) :=
    (HomologicalComplex.extendXIso (_root_.Cech.cechComplex g M) ComplexShape.embeddingUpNat
      hp).toLinearEquiv ≪≫ₗ ExtendedCech.termTensorEquiv g M p
  exact Dualizing.nonempty_derivedCompletion_iso_adicCompletion_of_linearEquiv I hI l
    (Dualizing.nonempty_derivedCompletion_iso_adicCompletion_of_tensor_flat I hI M
      (_root_.Cech.cechTerm g A p))

/-- **Derived completion inverts the termwise completion map of the Čech complex.** For `A`
Noetherian and `M` finite, derived `I`-adic completion inverts the image in `D(A)` of
`C^•(g; M) ⟶ C^•(g; M)^∧`.

Derived completion is computed by the triangulated Čech model
`DerivedCompletion.derivedCompletionFunctor` on generators of `I`, which agrees with it by
uniqueness of left adjoints. That exact functor inverts the map in every degree, the degree-`n`
component being the shift of the completion map of a term placed in degree `0`, which derived
completion inverts by Stacks 0EEU. -/
theorem isIso_adicCompletionFunctor_map_toTermwiseAdicCompletion [IsNoetherianRing A]
    [Module.Finite A M] (hI : I.FG) :
    IsIso ((Stacks.Algebraization.adicCompletionFunctor A I hI).map (DerivedCategory.Q.map
      (HomologicalComplex.toTermwiseAdicCompletion I (extendedCechComplex.{0} g M)))) := by
  obtain ⟨k, f, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  let P := Dualizing.derivedCompleteProperty.{u, u} A (Ideal.span (Set.range f))
  let G := DerivedCompletion.derivedCompletionFunctor A f
  -- the triangulated Čech model of derived completion agrees with the reflection
  let eL : P.lift G (DerivedCompletion.derivedCompleteProperty_derivedCompletionFunctor_obj A f) ≅
      Dualizing.derivedCompletion A (Ideal.span (Set.range f)) hI :=
    (DerivedCompletion.derivedCompletionAdjunction A f).leftAdjointUniq
      (Dualizing.derivedCompletionReflection A (Ideal.span (Set.range f)) hI).2
  let eG : G ≅ Stacks.Algebraization.adicCompletionFunctor A (Ideal.span (Set.range f)) hI :=
    Functor.isoWhiskerRight eL P.ι
  rw [← NatIso.isIso_map_iff eG]
  let K := extendedCechComplex.{0} g M
  have hsupp : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ i : ℤ, i < 0 ∨ (r : ℤ) + 1 ≤ i → IsZero (L.X i)) → {i : ℤ | ¬ IsZero (L.X i)}.Finite :=
    fun L hL => (Set.finite_Icc (0 : ℤ) r).subset fun i hi => by
      simp only [Set.mem_ofPred_eq] at hi
      simp only [Set.mem_Icc]
      by_contra hc
      exact hi (hL i (by omega))
  refine Stacks.DerivedCategory.BoundedInduction.isIso_map_Q_map_of_isIso_map_singleFunctor_map
    G _ (hsupp K (isZero_extendedCechComplex_X g M))
    (hsupp _ (isZero_termwiseAdicCompletion_extendedCechComplex_X _ g M)) fun n => ?_
  -- reduce the degree-`n` component to the degree-`0` one
  let S0 := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let e₁ : DerivedCategory.singleFunctor (ModuleCat.{u} A) n ⋙ G ≅
      S0 ⋙ G ⋙ shiftFunctor _ (-n) :=
    Functor.isoWhiskerRight
        ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-n) n 0 (by omega)).symm G ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft S0 (G.commShiftIso (-n))
  have hG0 : IsIso (G.map (S0.map
      (ModuleCat.ofHom (AdicCompletion.of (Ideal.span (Set.range f)) (K.X n))))) := by
    by_cases hn : 0 ≤ n
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = (p : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
      have h0 : IsIso ((Dualizing.derivedCompletion A (Ideal.span (Set.range f)) hI).map
          (S0.map (ModuleCat.ofHom (AdicCompletion.of (Ideal.span (Set.range f)) (K.X p))))) :=
        Dualizing.isIso_derivedCompletion_map_adicCompletionOf _ hI (K.X p)
          (nonempty_derivedCompletion_iso_extendedCechComplex_X _ g M hI p).some
      rw [NatIso.isIso_map_iff eG]
      change IsIso (P.ι.map ((Dualizing.derivedCompletion A (Ideal.span (Set.range f)) hI).map _))
      infer_instance
    · have hz : IsZero (K.X n) := isZero_extendedCechComplex_X g M n (Or.inl (by omega))
      have hz' : IsZero ((AdicCompletion.moduleCatFunctor (Ideal.span (Set.range f))).obj
          (K.X n)) := (AdicCompletion.moduleCatFunctor _).map_isZero hz
      have : IsIso (S0.map
          (ModuleCat.ofHom (AdicCompletion.of (Ideal.span (Set.range f)) (K.X n)))) :=
        ⟨0, (S0.map_isZero hz).eq_of_src _ _, (S0.map_isZero hz').eq_of_src _ _⟩
      infer_instance
  have : IsIso ((S0 ⋙ G ⋙ shiftFunctor _ (-n)).map
      (ModuleCat.ofHom (AdicCompletion.of (Ideal.span (Set.range f)) (K.X n)))) := by
    change IsIso ((shiftFunctor _ (-n)).map (G.map (S0.map _)))
    infer_instance
  exact (NatIso.isIso_map_iff e₁ _).2 this

end Stacks.LocalCohomology

end
