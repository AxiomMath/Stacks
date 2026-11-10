module

public import StacksFrontier.Homology.Perfect.BettiConstructible
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Derived-fibre Betti numbers read over an arbitrary field

Let `C` be a bounded above complex of projective `A`-modules and let `g : A →+* Ω` be a ring
homomorphism to a field, with kernel the prime `p`. Then the `i`-th derived-fibre Betti number of
`C` at `p` is the dimension over `Ω` of the `i`-th cohomology of `C ⊗_A Ω`.

## Main results

* `StacksDraft.Perfect.fibreBetti_eq_finrank_homology_extendScalars`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- **Derived-fibre Betti numbers over an arbitrary field.** For a strictly bounded above complex
`C` of projective `A`-modules and a ring homomorphism `g : A →+* Ω` to a field whose kernel is the
prime `p`, the `i`-th derived-fibre Betti number of `C` at `p` is the dimension over `Ω` of the
`i`-th cohomology of the degreewise base change `C ⊗_A Ω`. -/
theorem fibreBetti_eq_finrank_homology_extendScalars {A : Type u} [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [C.IsStrictlyLE b]
    [∀ j, Projective (C.X j)] {Ω : Type u} [Field Ω] (g : A →+* Ω) (p : PrimeSpectrum A)
    (hp : RingHom.ker g = p.asIdeal) (i : ℤ) :
    fibreBetti.{u, u} (DerivedCategory.Q.obj C) i p =
      Module.finrank Ω
        ((((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C).homology i) := by
  let κ := p.asIdeal.ResidueField
  -- `g` factors through the residue field at `p`
  have h₁ : p.asIdeal ≤ RingHom.ker g := hp.ge
  have h₂ : p.asIdeal.primeCompl ≤ (IsUnit.submonoid Ω).comap g := fun a ha =>
    isUnit_iff_ne_zero.2 fun h => ha (hp ▸ RingHom.mem_ker.2 h)
  let ι : κ →+* Ω := Ideal.ResidueField.lift p.asIdeal g h₁ h₂
  have hι : ι.comp (algebraMap A κ) = g :=
    RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p.asIdeal g h₁ h₂ a
  -- the derived fibre at `p` is computed degreewise
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A κ)
  have hiso : IsIso (D.comparison.app C) := D.comparison_isIso_of_projective C b
  let Cκ := ((ModuleCat.extendScalars.{u, u, u} (algebraMap A κ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj C
  let e : D.functor.obj (DerivedCategory.Q.obj C) ≅ DerivedCategory.Q.obj Cκ :=
    asIso (D.comparison.app C) ≪≫ Iso.refl _
  have hfib : fibreBetti.{u, u} (DerivedCategory.Q.obj C) i p =
      Module.finrank κ (Cκ.homology i) := by
    change Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
      (D.functor.obj (DerivedCategory.Q.obj C))) = _
    rw [finrank_homologyFunctor_eq_of_iso.{u, u} e i, finrank_homologyFunctor_Q_obj.{u, u}]
  -- base change along the field extension `κ → Ω` is exact
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} ι) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by
      let := ι.toAlgebra
      exact (inferInstance : Module.Flat κ Ω))
  let eC : ((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C ≅
      ((ModuleCat.extendScalars.{u, u, u} ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Cκ :=
    eqToIso (by rw [← hι]) ≪≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp (algebraMap A κ) ι)
        (ComplexShape.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm.app C
  rw [hfib, (HomologicalComplex.homologyMapIso eC i).toLinearEquiv.finrank_eq]
  exact (finrank_extendScalars ι (Cκ.homology i) (Module.Free.of_divisionRing _ _)).symm.trans
    ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (ModuleCat.extendScalars.{u, u, u} ι) (ComplexShape.up ℤ) i).app
        Cκ).toLinearEquiv.finrank_eq.symm

end StacksDraft.Perfect
