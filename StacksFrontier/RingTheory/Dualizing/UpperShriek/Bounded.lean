module

public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison.A72
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PerfectCoextension
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialExtension
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectAnyPresentation

/-!
# Boundedness and coherence under algebraic upper shriek

For a finite type homomorphism `f : R →+* A` of Noetherian rings, the algebraic upper shriek
functor of a polynomial presentation maps `D⁺(R)` into `D⁺(A)` and `D⁺_Coh(R)` into `D⁺_Coh(A)`;
when `f` is perfect it also maps `D⁻(R)` into `D⁻(A)`, `D⁻_Coh(R)` into `D⁻_Coh(A)` and
`Dᵇ_Coh(R)` into `Dᵇ_Coh(A)`.

## Main results

* `Dualizing.PolynomialPresentation.upperShriekFunctor_isBoundedBelow` and
  `Dualizing.PolynomialPresentation.upperShriekFunctor_derivedCategoryBPlus` — [stacks 0BZK] (1).
* `Dualizing.upperShriekFunctor_isBoundedAbove_of_isPerfectRingMap`,
  `Dualizing.upperShriekFunctor_derivedCategoryBMinus_of_isPerfectRingMap` and
  `Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_isPerfectRingMap` —
  [stacks 0BZK] (2), with `φ` a perfect ring map.
* `Dualizing.PolynomialPresentation.upperShriekFunctor_isBoundedAbove`,
  `Dualizing.PolynomialPresentation.upperShriekFunctor_derivedCategoryBMinus` and
  `Dualizing.PolynomialPresentation.upperShriekFunctor_derivedCategoryBBounded` — the same,
  assuming instead that the target is perfect over the polynomial algebra of the presentation.

## Implementation notes

Upper shriek is only defined up to isomorphism, so every statement is made for an arbitrary
polynomial presentation; all the properties involved are invariant under isomorphism, so this is
the strongest reading and it does not depend on [stacks 0BZJ].

Coherent modules over a Noetherian ring are the finite ones, so `D^?_Coh` is
`DerivedCategoryB.derivedCategoryB?` taken at the object property `Module.Finite`.

Perfectness of `f` enters through its target being a perfect module over the polynomial algebra
of the presentation, which is [stacks 068Y]; the two formulations are related by
`RingHom.isPerfectModule_of_isPerfectRingMap`.

## References

* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

section BoundedBelow

/-- Derived coextension of scalars along a ring homomorphism carries complexes concentrated in
degrees `≥ n` to complexes concentrated in degrees `≥ n`. -/
theorem isGE_derivedHom_obj (g : R →+* A)
    (X : DerivedCategory (ModuleCat.{max v u} R)) (n : ℤ) (hX : X.IsGE n) :
    ((derivedHom.{u, v, u} g).obj X).IsGE n := by
  let F := ModuleCat.restrictScalars.{max v u} g
  let : Limits.PreservesFiniteLimits F := by
    constructor; intro J _ _; constructor; intro G; infer_instance
  let : Limits.PreservesFiniteColimits F := by
    constructor; intro J _ _; constructor; intro G; infer_instance
  let adj : F.mapDerivedCategory ⊣ derivedHom.{u, v, u} g :=
    Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, v, u} g)
  let : X.IsGE n := hX
  change DerivedCategory.TStructure.t.IsGE ((derivedHom.{u, v, u} g).obj X) n
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro Y hom hY
  let : Y.IsLE (n - 1) := hY
  let : (F.mapDerivedCategory.obj Y).IsLE (n - 1) := mapDerivedCategory_isLE F Y (n - 1)
  apply (adj.homEquiv Y X).symm.injective
  simpa using DerivedCategory.TStructure.t.zero
    ((adj.homEquiv Y X).symm hom) (n - 1) n (by omega)

namespace PolynomialPresentation

/-- Algebraic upper shriek carries cohomologically bounded-below complexes to cohomologically
bounded-below complexes. -/
@[stacks 0BZK "(1), the statement that φ^! maps D⁺(R) into D⁺(A)"]
theorem upperShriekFunctor_isBoundedBelow (p : PolynomialPresentation f)
    {K : DerivedCategory (ModuleCat.{max v u} R)} (hK : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow (p.upperShriekFunctor.{u, v}.obj K) := by
  obtain ⟨a, ha⟩ := p.derivedExtension_isBoundedBelow hK
  have hHom : ((derivedHom.{u, v, u} p.toRingHom).obj (p.derivedExtension.{u, v}.obj K)).IsGE a :=
    isGE_derivedHom_obj p.toRingHom _ a ((DerivedCategory.isGE_iff _ a).2 ha)
  rw [p.upperShriekFunctor_obj K]
  exact DerivedCategoryB.isBoundedBelow_shift (p.variableCount : ℤ)
    ⟨a, (DerivedCategory.isGE_iff _ a).1 hHom⟩

end PolynomialPresentation

end BoundedBelow

section Coherent

/-- Shifting reindexes the cohomology modules, so finiteness of all of them is preserved. -/
private theorem finiteCohomology_shift {B : Type u} [CommRing B]
    {X : DerivedCategory (ModuleCat.{max v u} B)}
    (hX : ∀ i : ℤ, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) i).obj X)) (a : ℤ) :
    ∀ i : ℤ, Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) i).obj
      ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) a).obj X)) := by
  intro i
  let F := DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) 0
  have e : (F.shift i).obj ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) a).obj X) ≅
      (F.shift (a + i)).obj X := (F.shiftIso a i (a + i) rfl).app X
  have : Module.Finite B ((F.shift (a + i)).obj X) := by
    rw [DerivedCategory.shift_homologyFunctor]; exact hX (a + i)
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Derived coextension of scalars along a finite homomorphism of Noetherian rings carries
bounded-below complexes with coherent cohomology to bounded-below complexes with coherent
cohomology. -/
private theorem derivedCategoryBPlus_derivedHom_obj [IsNoetherianRing R] [IsNoetherianRing A]
    (g : R →+* A) (hg : g.Finite) {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M) ((derivedHom.{u, v, u} g).obj K) :=
  isBoundedBelowCoherent_obj_rightDerivedCoextendScalars g hg (derivedHom.{u, v, u} g)
    ((coextendScalarsToDerivedCategory g).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} R) (.up ℤ))) hK

namespace PolynomialPresentation

/-- Algebraic upper shriek along a finite type homomorphism of Noetherian rings carries
bounded-below complexes with coherent cohomology to bounded-below complexes with coherent
cohomology. -/
@[stacks 0BZK "(1), the statement that φ^! maps D⁺_Coh(R) into D⁺_Coh(A)"]
theorem upperShriekFunctor_derivedCategoryBPlus [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation f) {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M)
      (p.upperShriekFunctor.{u, v}.obj K) := by
  have hP : IsNoetherianRing p.Poly := inferInstance
  have hHom := derivedCategoryBPlus_derivedHom_obj p.toRingHom p.finite_toRingHom
    (p.derivedExtension_derivedCategoryBPlus hK)
  rw [p.upperShriekFunctor_obj K]
  exact ⟨DerivedCategoryB.isBoundedBelow_shift _ hHom.1,
    finiteCohomology_shift hHom.2 (p.variableCount : ℤ)⟩

end PolynomialPresentation

end Coherent

section Perfect

/-- A perfect module stays perfect after a universe lift. -/
private theorem isPerfectModule_uLift {P : Type u} [CommRing P] (M : Type u) [AddCommGroup M]
    [Module P M] (hM : StacksDraft.Perfect.IsPerfectModule (R := P) M) :
    StacksDraft.Perfect.IsPerfectModule (R := P) (ULift.{v} M) := by
  change StacksDraft.Perfect.IsPerfect
    ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P M)) at hM
  obtain ⟨C, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hM
  let U := ModuleCat.uliftFunctor.{v} P
  let : U.Additive := inferInstance
  let : Limits.PreservesFiniteLimits U := inferInstance
  refine ⟨(U.mapHomologicalComplex (ComplexShape.up ℤ)).obj C, a, b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ U.map_isZero (C.isZero_of_isStrictlyGE a i hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ U.map_isZero (C.isZero_of_isStrictlyLE b i hi)
  · intro i
    let : Module.Finite P (C.X i) := hfinite i
    exact Module.Finite.equiv (ULift.moduleEquiv : ULift.{v} (C.X i) ≃ₗ[P] C.X i).symm
  · intro i
    let : Module.Projective P (C.X i) := hprojective i
    exact Module.Projective.of_equiv (ULift.moduleEquiv : ULift.{v} (C.X i) ≃ₗ[P] C.X i).symm
  · exact ⟨((U.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of P M)).symm ≪≫
      U.mapDerivedCategory.mapIso e ≪≫ U.mapDerivedCategoryFactors.app C⟩

namespace PolynomialPresentation

/-- If the target is perfect over the polynomial algebra of a presentation, then so is its
universe lift, viewed in degree `0` of the derived category of the polynomial algebra. -/
private theorem isPerfect_singleFunctor_uLift (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} p.Poly) 0).obj
        ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{v} A))))) := by
  let : Module p.Poly A := Module.compHom A p.toRingHom
  change StacksDraft.Perfect.IsPerfectModule (R := p.Poly) (ULift.{v} A)
  exact isPerfectModule_uLift.{u, v} A hperf

/-- The polynomial extension of a bounded-above complex lies in the `t`-structure's `minus`. -/
private theorem minus_derivedExtension [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation f) {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.IsBoundedAbove K) :
    haveI : IsNoetherianRing p.Poly := inferInstance
    (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} p.Poly)).minus
      (p.derivedExtension.{u, v}.obj K) := by
  obtain ⟨b, hb⟩ := p.derivedExtension_isBoundedAbove.{u, v} hK
  exact ⟨b, (DerivedCategory.isLE_iff _ b).2 hb⟩

/-- When the target is perfect over the polynomial algebra of the presentation, algebraic upper
shriek carries cohomologically bounded-above complexes to cohomologically bounded-above
complexes. -/
theorem upperShriekFunctor_isBoundedAbove [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A)
    {K : DerivedCategory (ModuleCat.{max v u} R)} (hK : DerivedCategoryB.IsBoundedAbove K) :
    DerivedCategoryB.IsBoundedAbove (p.upperShriekFunctor.{u, v}.obj K) := by
  have hP : IsNoetherianRing p.Poly := inferInstance
  have hminus := p.minus_derivedExtension.{u, v} hK
  obtain ⟨b, hb⟩ := derivedCoextendScalars_mem_minus.{u, v} p.toRingHom p.surjective
    (p.isPerfect_singleFunctor_uLift.{u, v} hperf) _ hminus
  rw [p.upperShriekFunctor_obj K]
  exact DerivedCategoryB.isBoundedAbove_shift (p.variableCount : ℤ)
    ⟨b, fun i hi ↦ (DerivedCategory.isLE_iff _ b).mp hb i hi⟩

/-- When the target is perfect over the polynomial algebra of the presentation, algebraic upper
shriek carries bounded-above complexes with coherent cohomology to bounded-above complexes with
coherent cohomology. -/
theorem upperShriekFunctor_derivedCategoryBMinus [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M)
      (p.upperShriekFunctor.{u, v}.obj K) := by
  have hP : IsNoetherianRing p.Poly := inferInstance
  have hHom := derivedCoextendScalars_finiteCohomology.{u, v} p.toRingHom p.surjective
    (p.isPerfect_singleFunctor_uLift.{u, v} hperf) _ (p.minus_derivedExtension.{u, v} hK.1)
    (p.derivedExtension_derivedCategoryBMinus.{u, v} hK).2
  refine ⟨p.upperShriekFunctor_isBoundedAbove.{u, v} hperf hK.1, ?_⟩
  rw [p.upperShriekFunctor_obj K]
  exact finiteCohomology_shift hHom (p.variableCount : ℤ)

/-- When the target is perfect over the polynomial algebra of the presentation, algebraic upper
shriek carries bounded complexes with coherent cohomology to bounded complexes with coherent
cohomology. -/
theorem upperShriekFunctor_derivedCategoryBBounded [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M)
      (p.upperShriekFunctor.{u, v}.obj K) :=
  ⟨⟨p.upperShriekFunctor_isBoundedBelow.{u, v} hK.1.1,
      (p.upperShriekFunctor_derivedCategoryBMinus.{u, v} hperf ⟨hK.1.2, hK.2⟩).1⟩,
    (p.upperShriekFunctor_derivedCategoryBPlus.{u, v} ⟨hK.1.1, hK.2⟩).2⟩

end PolynomialPresentation

/-- The target of a perfect ring map is perfect over the polynomial algebra of any of its
presentations ([stacks 068Y]). -/
private theorem isPerfectModule_poly_of_isPerfectRingMap (p : PolynomialPresentation f)
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hf : letI : Algebra R A := f.toAlgebra
      RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived) :
    letI : Module p.Poly A := Module.compHom A p.toRingHom
    StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A := by
  let : Algebra R A := f.toAlgebra
  exact RingHom.isPerfectModule_of_isPerfectRingMap derivedTensor comparison isLeftDerived hf
    p.variableCount (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes) p.surjective

/-- Algebraic upper shriek along a perfect homomorphism of Noetherian rings carries cohomologically
bounded-above complexes to cohomologically bounded-above complexes. -/
@[stacks 0BZK "(2), the statement that φ^! maps D⁻(R) into D⁻(A)"]
theorem upperShriekFunctor_isBoundedAbove_of_isPerfectRingMap
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f)
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hf : letI : Algebra R A := f.toAlgebra
      RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived)
    {K : DerivedCategory (ModuleCat.{max v u} R)} (hK : DerivedCategoryB.IsBoundedAbove K) :
    DerivedCategoryB.IsBoundedAbove (p.upperShriekFunctor.{u, v}.obj K) :=
  p.upperShriekFunctor_isBoundedAbove.{u, v}
    (isPerfectModule_poly_of_isPerfectRingMap p derivedTensor comparison isLeftDerived hf) hK

/-- Algebraic upper shriek along a perfect homomorphism of Noetherian rings carries bounded-above
complexes with coherent cohomology to bounded-above complexes with coherent cohomology. -/
@[stacks 0BZK "(2), the statement that φ^! maps D⁻_Coh(R) into D⁻_Coh(A)"]
theorem upperShriekFunctor_derivedCategoryBMinus_of_isPerfectRingMap
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f)
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hf : letI : Algebra R A := f.toAlgebra
      RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M)
      (p.upperShriekFunctor.{u, v}.obj K) :=
  p.upperShriekFunctor_derivedCategoryBMinus.{u, v}
    (isPerfectModule_poly_of_isPerfectRingMap p derivedTensor comparison isLeftDerived hf) hK

/-- Algebraic upper shriek along a perfect homomorphism of Noetherian rings carries bounded
complexes with coherent cohomology to bounded complexes with coherent cohomology. -/
@[stacks 0BZK "(2), the statement that φ^! maps Dᵇ_Coh(R) into Dᵇ_Coh(A)"]
theorem upperShriekFunctor_derivedCategoryBBounded_of_isPerfectRingMap
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f)
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hf : letI : Algebra R A := f.toAlgebra
      RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M)
      (p.upperShriekFunctor.{u, v}.obj K) :=
  p.upperShriekFunctor_derivedCategoryBBounded.{u, v}
    (isPerfectModule_poly_of_isPerfectRingMap p derivedTensor comparison isLeftDerived hf) hK

end Perfect

end Dualizing

end
