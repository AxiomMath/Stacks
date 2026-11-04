module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.FibreFunctions
public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.BaseChangeSplitting
public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.FiniteEtaleSpreading
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsArbitraryBase
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections

/-!
# The affine case of the splitting at a geometrically reduced fibre

Let `g : Y ⟶ Spec R` be proper, flat and of finite presentation and let `p` be a prime of `R` at
which `g` has geometrically reduced fibre (`FibreGeometricallyReducedAt`). Then there are
`a ∉ p` and `h ∉ p` divisible by `a` such that

* over `Spec R_a`, the derived direct image of the structure sheaf of the base change splits as
  `X₁ ⊕ P` with `X₁` of Tor amplitude in `[0, 0]` and `P` perfect of Tor amplitude in `[1, b]`;
* for every localization `B` of `R` away from `h`, the `B`-algebra `B ⊗_R Γ(Y, 𝒪_Y)` is finite
  and etale.

This is the proof of [Stacks, Tag 0G7Y] over an affine base, with the Čech model of `RΓ(Y, 𝒪_Y)`
standing for `Rf_*𝒪_X` restricted to the affine open.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
open scoped TensorProduct

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- Let `g : Y ⟶ Spec R` be proper, flat and of finite presentation, with geometrically reduced
fibre at the prime `p`. Then there are `a ∉ p` and `b` such that, for every base change `g'` of `g`
to `Spec R_a`, the derived pushforward of the structure sheaf along `g'` splits as `X₁ ⊞ P'` with
`X₁` of Tor amplitude in `[0, 0]` and `P'` perfect of Tor amplitude in `[1, b]`; and there is
`h ∉ p` divisible by `a` such that `B ⊗_R Γ(Y, 𝒪_Y)` is finite and étale over every localization
`B` of `R` away from `h`. -/
theorem exists_away_splitting_and_finiteEtale {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of R)) (hfp : FinitePresentation g) [IsProper g] [Flat g]
    (p : Ideal R) [p.IsPrime] (hred : FibreGeometricallyReducedAt g p) :
    ∃ a : R, a ∉ p ∧
      (∃ b : ℤ, ∀ {Y' : Scheme.{u}} {g' : Y' ⟶ Spec (.of (Localization.Away a))} {q : Y' ⟶ Y}
        (_ : IsPullback q g' g
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a))))),
        letI := HasDerivedCategory.standard Y'.Modules
        letI := HasDerivedCategory.standard (Spec (.of (Localization.Away a))).Modules
        ∃ X₁ P' : DerivedCategory (Spec (.of (Localization.Away a))).Modules,
          Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g'
            (Scheme.unitModule Y') ≅ X₁ ⊞ P') ∧
          HasTorAmplitudeStd (Spec (.of (Localization.Away a))) X₁ 0 0 ∧
          Stacks.Duality.CompactBoundedness.IsPerfectStd P' ∧
          HasTorAmplitudeStd (Spec (.of (Localization.Away a))) P' 1 b) ∧
      ∃ h : R, h ∉ p ∧ a ∣ h ∧
        (letI := (Stacks.Cech.globalRingHom g).hom.toAlgebra
        ∀ (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away h B],
          Module.Finite B (B ⊗[R] Γ(Y, ⊤)) ∧ Algebra.Etale B (B ⊗[R] Γ(Y, ⊤))) := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  have : LocallyOfFinitePresentation g := hfp.1
  obtain ⟨I, hI, hlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper g
  have : (Scheme.unitModule Y).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit Y
  have hflat : IsFlatOver g.toLRSHom.toShHom (Scheme.unitModule Y) := fun x =>
    (AlgebraicGeometry.MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit g x).1
      (Flat.stalkMap g x)
  let D := baseAlternatingCechComplex g U hU (Scheme.unitModule Y)
  have hDflat : ∀ i, Module.Flat R (D.X i) :=
    flat_baseAlternatingCechComplex_X g U hU (Scheme.unitModule Y) hUaff hflat
  have : D.IsStrictlyLE (Fintype.card I : ℤ) :=
    isStrictlyLE_baseAlternatingCechComplex g U hU (Scheme.unitModule Y)
  have hD : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj D) :=
    StacksDraft.Perfect.isPerfect_of_iso
      (alternatingCechIsoDerivedGlobalSectionsOverBase g U hU (Scheme.unitModule Y) haff)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper g (Scheme.unitModule Y) hflat)
  have hS := degreeZeroCyclesSurjective_residueField g p hred U hU hUaff
  obtain ⟨a, ha, P, b, hPge, hPle, hPfin, hPproj, ⟨hfin, hfree, ⟨e⟩⟩, hinj⟩ :=
    exists_away_splitting p D (Fintype.card I) hS hD
  refine ⟨a, ha, ⟨b, fun {Y'} {g'} {q} hsq => ?_⟩, ?_⟩
  · exact exists_derivedPushforward_splitting_of_away g U hU hUaff haff a P b hPfin hPproj
      hfree ⟨e⟩ hsq
  have hsqp := IsPullback.of_hasPullback g
    (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))
  let fp := pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))
  have : GeometricallyReduced fp := geometricallyReduced_of_fibreGeometricallyReducedAt hred hsqp
  have : IsProper fp := inferInstance
  let : Algebra R Γ(Y, ⊤) := (Stacks.Cech.globalRingHom g).hom.toAlgebra
  have hét : let := (Stacks.Cech.globalRingHom fp).hom.toAlgebra
      Algebra.Etale p.ResidueField (p.Fiber Γ(Y, ⊤)) :=
    etale_fiber_globalSections p hsqp U hU hUaff hS hinj
      (Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_globalSections_of_geometricallyReduced
        p.ResidueField fp).1
  have hfib : Algebra.FormallyUnramified p.ResidueField (p.Fiber Γ(Y, ⊤)) := inferInstance
  let e₀ : Γ(Y, ⊤) ≃ₗ[R]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj (DerivedCategory.Q.obj D)) :=
    (globalSectionsCyclesEquiv (g := g) U hU).trans
      (D.isoHomologyπ (-1) 0 (by simp) (d_neg_one_zero_eq_zero D) ≪≫
        ((DerivedCategory.homologyFunctorFactors _ 0).app D).symm).toLinearEquiv
  let e₁ : Localization.Away a ⊗[R] Γ(Y, ⊤) ≃ₗ[Localization.Away a]
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away a))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj (DerivedCategory.Q.obj D)) :=
    (e₀.baseChange R (Localization.Away a)).trans
      (PseudoCoherence.extendScalarsTensorIso (S := Localization.Away a) _).symm.toLinearEquiv
  have : Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] Γ(Y, ⊤)) :=
    Module.Finite.equiv e₁.symm
  have : Module.Free (Localization.Away a) (Localization.Away a ⊗[R] Γ(Y, ⊤)) :=
    Module.Free.of_equiv e₁.symm
  exact exists_away_finite_etale_of_formallyUnramified p a ha hfib

end StacksDraft.Perfect.GeomReducedFibre

end
