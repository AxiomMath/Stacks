module

public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Algebra.Homology.PseudoCoherentNoetherianModels
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# A bounded complex of projective modules with finite cohomology is perfect

Let `R` be a (left) Noetherian ring, not necessarily commutative, and `E` a bounded complex of
projective `R`-modules, not necessarily finite, whose cohomology modules are finite. Then `E` is
a perfect object of `D(R)`.

Over a Noetherian ring `E` is pseudo-coherent ([Stacks, Tag 066E]): it is quasi-isomorphic to a
bounded above complex `P` of finite free modules. Both `P` and `E` are bounded above complexes of
projectives, hence K-projective, so the quasi-isomorphism is a homotopy equivalence and the
identity of `P` is homotopic to a map factoring through `E`, which vanishes in degrees below the
lower bound `a` of `E`. In degree `a - 1` the homotopy `h` gives `1 = -(d h + h d)`, so
`1 + h d` on `P^a` kills the boundaries and splits the projection `P^a → P^a / d(P^{a-1})`. The
canonical truncation `τ_{≥ a} P` is therefore a bounded complex of finite projective modules, and
it is quasi-isomorphic to `P`.

This is the last step of the perfectness criterion over a quasi-Frobenius ring used for
`RΓ_c(U_k̄, D(A[H]))` in Step 7 of the proof of [Stacks, Tag 03UG].

## Main results

* `StacksDraft.Perfect.isPerfect_of_projective_of_finite_homology`

## References

* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace StacksDraft.Perfect

variable {R : Type u} [Ring R]

/-- In a complex `P` whose identity is homotopic, through `h`, to a map vanishing in degree
`a - 1`, the projection `P^a → P^a / d(P^{a-1})` is split. -/
theorem retract_opcycles_of_homotopy {C : Type*} [Category* C] [Preadditive C]
    [CategoryWithHomology C] (P : CochainComplex C ℤ) (φ : P ⟶ P) (h : Homotopy φ (𝟙 P)) (a : ℤ)
    (hφ : φ.f (a - 1) = 0) :
    ∃ s : P.opcycles a ⟶ P.X a, s ≫ P.pOpcycles a = 𝟙 _ := by
  have hc := h.comm (a - 1)
  rw [hφ, dNext_eq h.hom (show (ComplexShape.up ℤ).Rel (a - 1) a by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (a - 1 - 1) (a - 1) by simp),
    HomologicalComplex.id_f] at hc
  let σ : P.X a ⟶ P.X a := 𝟙 _ + h.hom a (a - 1) ≫ P.d (a - 1) a
  have hσ : P.d (a - 1) a ≫ σ = 0 := by
    have hc' : P.d (a - 1) a ≫ h.hom a (a - 1) =
        -(h.hom (a - 1) (a - 1 - 1) ≫ P.d (a - 1 - 1) (a - 1) + 𝟙 _) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]
      exact hc.symm
    simp only [σ, Preadditive.comp_add, Category.comp_id]
    rw [← Category.assoc, hc', Preadditive.neg_comp, Preadditive.add_comp, Category.assoc,
      P.d_comp_d, comp_zero, zero_add, Category.id_comp, add_neg_cancel]
  refine ⟨P.descOpcycles σ (a - 1) (by simp) hσ, ?_⟩
  rw [← cancel_epi (P.pOpcycles a), HomologicalComplex.p_descOpcycles_assoc, Category.comp_id]
  simp only [σ, Preadditive.add_comp, Category.id_comp, Category.assoc,
    HomologicalComplex.d_pOpcycles, comp_zero, add_zero]

/-- A zero module is finite and projective. -/
private theorem finite_projective_of_isZero {M : ModuleCat.{v} R} (hM : IsZero M) :
    Module.Finite R M ∧ Module.Projective R M := by
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  exact ⟨inferInstance, inferInstance⟩

/-- **A bounded complex of projective modules with finite cohomology over a Noetherian ring is
perfect.** -/
theorem isPerfect_of_projective_of_finite_homology [IsNoetherianRing R] [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ) [E.IsStrictlyGE a] [E.IsStrictlyLE b]
    (hE : ∀ i, Projective (E.X i)) (hf : ∀ i, Module.Finite R (E.homology i)) :
    IsPerfect (DerivedCategory.Q.obj E) := by
  let eH : ∀ i, (DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj E) ≅
      E.homology i := fun i => (DerivedCategory.homologyFunctorFactors _ i).app E
  obtain ⟨P, hP, ⟨e⟩⟩ :=
    StacksDraft.PseudoCoherence.isPseudoCoherentIn_of_boundedAbove_finite_homology
      (DerivedCategory.Q.obj E)
      ⟨b, fun i hi => ((E.exactAt_of_isLE b i hi).isZero_homology).of_iso (eH i)⟩
      (fun i => Module.Finite.equiv (eH i).toLinearEquiv.symm)
  obtain ⟨d, hd⟩ := hP.upperBound
  have : ∀ i, Projective (P.X i) := fun i => by
    have := (hP.finiteFree i).2
    infer_instance
  have := CochainComplex.isKProjective_of_projective P d
  have := CochainComplex.isKProjective_of_projective E b
  let eQ : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj E) :=
    (DerivedCategory.quotientCompQhIso _).app P ≪≫ e ≪≫
      ((DerivedCategory.quotientCompQhIso _).app E).symm
  obtain ⟨φ, hφ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P _).2 eQ.hom
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective E _).2 eQ.inv
  have hφψ : φ ≫ ψ = 𝟙 _ := (CochainComplex.IsKProjective.Qh_map_bijective P _).1 (by
    rw [Functor.map_comp, hφ, hψ, Iso.hom_inv_id, CategoryTheory.Functor.map_id])
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
  have hfg : Homotopy (f ≫ g) (𝟙 P) := HomotopyCategory.homotopyOfEq _ _ (by
    rw [Functor.map_comp, hφψ, CategoryTheory.Functor.map_id])
  obtain ⟨s, hs⟩ := retract_opcycles_of_homotopy P (f ≫ g) hfg a (by
    rw [HomologicalComplex.comp_f,
      (E.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_tgt (f.f (a - 1)) 0, zero_comp])
  have hPge : P.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((E.exactAt_of_isGE a i hi).isZero_homology).of_iso
      (((DerivedCategory.homologyFunctorFactors _ i).app P).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫ eH i)
  have : IsIso (DerivedCategory.Q.map (P.πTruncGE a)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hX : ∀ i, Module.Finite R ((P.truncGE a).X i) ∧ Module.Projective R ((P.truncGE a).X i) := by
    intro i
    rcases lt_trichotomy i a with hi | rfl | hi
    · exact finite_projective_of_isZero ((P.truncGE a).isZero_of_isStrictlyGE a i hi)
    · let r : Retract (P.opcycles i) (P.X i) := ⟨s, P.pOpcycles i, hs⟩
      have : Projective (P.opcycles i) := r.projective
      have : Projective ((P.truncGE i).X i) :=
        Projective.of_iso (P.truncGEXIsoOpcycles i).symm inferInstance
      have := (hP.finiteFree i).1
      have hsurj : Function.Surjective (P.pOpcycles i ≫ (P.truncGEXIsoOpcycles i).inv).hom := by
        rw [← ModuleCat.epi_iff_surjective]
        infer_instance
      exact ⟨Module.Finite.of_surjective _ hsurj, inferInstance⟩
    · have := (hP.finiteFree i).1
      have := (hP.finiteFree i).2
      exact ⟨Module.Finite.equiv (P.truncGEXIso a i hi).toLinearEquiv.symm,
        Module.Projective.of_equiv (P.truncGEXIso a i hi).toLinearEquiv.symm⟩
  refine ⟨P.truncGE a, a, max a d, inferInstance, ?_, fun i => (hX i).1, fun i => (hX i).2,
    ⟨e.symm ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE a))⟩⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (P.isZero_of_isStrictlyLE d i (by omega)).of_iso (P.truncGEXIso a i (by omega))

end StacksDraft.Perfect
