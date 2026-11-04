module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Homothety
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFinite
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.CoextendDual
public import StacksFrontier.RingTheory.Dualizing.FiniteMapDualizing
public import StacksFrontier.RingTheory.Dualizing.LocalizationCriterion

/-!
# Derived coextension of scalars is the derived dual of the target ring

Let `f : A →+* B` be a homomorphism of commutative rings. There are two constructions in the
library of the object `RHom_A(B, K)`: the total right derived functor `Dualizing.derivedHom` of
coextension of scalars of [stacks 0A70], which lands in `D(B)`, and the internal derived Hom
bifunctor of [stacks 0A63] evaluated at `B[0]`, which lands in `D(A)`. This file identifies the
first, after restriction of scalars, with the second.

## Main results

* `Dualizing.restrictScalarsDerivedHomIso` — `RHom_A(B, ω)` read in `D(A)` is the internal
  derived Hom `RHom_A(B[0], ω)`, for `ω` presented by a bounded-below complex of injectives.
* `Dualizing.dualRestrictScalarsDerivedHomIso` — the derived `ω`-dual of `RHom_A(B, ω)` is
  `B[0]`, by the biduality theorem of [stacks 0A7C] at `B[0]`.
* `Dualizing.subsingleton_hom_derivedHom_shift` — the nonzero degrees of the Hom computation of
  [stacks 0AX0]: `Hom_{D(B)}(RHom_A(B, ω), RHom_A(B, ω)[n]) = 0` for `n ≠ 0`.
* `Dualizing.isDualizingComplex_derivedHom_of_finite_of_endLinearEquiv` — [stacks 0AX0] with
  only the degree-zero half of the Hom computation left as a hypothesis.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {A B : Type u} [CommRing A] [CommRing B]

/-- A K-injective complex computes the canonical derived coextension-of-scalars functor
`Dualizing.derivedHom` of [stacks 0A70]: its value at `I` is the degreewise coextension
`Hom_A(B, I)`. This is `Dualizing.rightDerivedCoextendObjIso` at that functor. -/
noncomputable def derivedHomObjIsoCoextend (f : A →+* B)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (hI : I.IsKInjective) :
    (derivedHom.{u, v, u} f).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((coextendComplex.{u, u, v} f).obj I) := by
  have := coextendScalars_hasPointwiseRightDerivedFunctor.{u, v, u} f
  exact rightDerivedCoextendObjIso f _
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))) I hI

/-- The target ring `B`, universe-lifted and placed in degree zero as an object of `D(A)`. This
is the object whose derived `ω`-dual is `RHom_A(B, ω)`. -/
noncomputable abbrev targetSingle (f : A →+* B) : DerivedCategory (ModuleCat.{max v u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (targetAsModule.{u, v} f)

/-- A bounded-below complex of injectives representing `ω` gives a cochain model for
`RHom_A(B, ω)` read in `D(A)`, namely the degreewise coextension `Hom_A(B, I)`. -/
noncomputable def restrictScalarsDerivedHomModelIso (f : A →+* B)
    {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hinj : ∀ i, Injective (I.X i))
    (e : ω ≅ DerivedCategory.Q.obj I) :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
        ((derivedHom.{u, v, u} f).obj ω) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((coextendComplex.{u, u, v} f).obj I)) :=
  have hI : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have := hGE
  have := hinj
  (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.mapIso
      ((derivedHom.{u, v, u} f).mapIso e ≪≫ derivedHomObjIsoCoextend.{u, v} f I hI) ≪≫
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.app
      ((coextendComplex.{u, u, v} f).obj I)

/-- **Derived coextension of scalars is the derived dual of the target ring.** For a
homomorphism of commutative rings `f : A →+* B` and an object `ω` of `D(A)` presented by a
bounded-below complex `I` of injective `A`-modules, the object `RHom_A(B, ω)` of [stacks 0A70],
read in `D(A)` by restriction of scalars, is the internal derived Hom `RHom_A(B[0], ω)` of
[stacks 0A63].

The two sides are computed on the same model: `RHom_A(B, ω)` by the degreewise coextension
`Hom_A(B, I)` and `RHom_A(B[0], ω)` by the Hom complex `Hom^•_A(B[0], I)`, and those two
complexes agree by `Dualizing.coextendComplexIsoHomComplexSingle`. -/
noncomputable def restrictScalarsDerivedHomIso (f : A →+* B)
    {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hinj : ∀ i, Injective (I.X i))
    (e : ω ≅ DerivedCategory.Q.obj I) :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
        ((derivedHom.{u, v, u} f).obj ω) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.obj
        (Opposite.op (targetSingle.{u, v} f), ω) :=
  restrictScalarsDerivedHomModelIso.{u, v} f I a hGE hinj e ≪≫
    DerivedCategory.Q.mapIso (coextendComplexIsoHomComplexSingle.{u, v} f I) ≪≫
    (derivedInternalHomModelIso₂.{u, max v u}
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj (targetAsModule.{u, v} f))
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0).app
        (targetAsModule.{u, v} f))
      I a hGE hinj).symm ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.mapIso
      ((Iso.refl _).prod e.symm)

/-! ### The dual of the derived dual -/

/-- The cohomology of `B[0]` vanishes in every nonzero degree. -/
private theorem isZero_homology_targetSingle (f : A →+* B) {i : ℤ} (hi : i ≠ 0) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      (targetSingle.{u, v} f)) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 i h
  · exact DerivedCategory.isZero_of_isLE _ 0 i h

/-- For a finite homomorphism, the cohomology modules of `B[0]` are finite over `A`: the one in
degree zero is `B` itself, and the others vanish. -/
theorem finite_homology_targetSingle (f : A →+* B) (hf : f.Finite) (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      (targetSingle.{u, v} f)) := by
  by_cases hi : i = 0
  · subst hi
    have hfin : Module.Finite A (targetAsModule.{u, v} f) := by
      change (let _ : Algebra A B := f.toAlgebra; Module.Finite A (ULift.{max v u} B))
      let _ : Algebra A B := f.toAlgebra
      have : Module.Finite A B := hf
      exact Module.Finite.ulift
    have hfin' : Module.Finite A
      ((𝟭 (ModuleCat.{max v u} A)).obj (targetAsModule.{u, v} f)) := hfin
    exact Module.Finite.equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) 0).app (targetAsModule.{u, v} f)).symm.toLinearEquiv
  · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
        (targetSingle.{u, v} f)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_homology_targetSingle.{u, v} f hi)
    infer_instance

/-- **The derived `ω`-dual of `RHom_A(B, ω)` is `B[0]`.** This is the biduality theorem of
[stacks 0A7C] at the object `B[0]`, which has finite cohomology because `f` is finite, combined
with `Dualizing.restrictScalarsDerivedHomIso`. -/
noncomputable def dualRestrictScalarsDerivedHomIso [IsNoetherianRing A] (f : A →+* B)
    (hf : f.Finite) {ω : DerivedCategory (ModuleCat.{max v u} A)} (hω : IsDualizingComplex ω)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hinj : ∀ i, Injective (I.X i))
    (e : ω ≅ DerivedCategory.Q.obj I) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.obj
        (Opposite.op ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
          ((derivedHom.{u, v, u} f).obj ω)), ω) ≅
      targetSingle.{u, v} f :=
  have := isIso_dualizingBidualityMor_of_finiteCohomology.{u, max v u} A ω
    (targetSingle.{u, v} f) hω (finite_homology_targetSingle.{u, v} f hf)
  (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.mapIso
      ((restrictScalarsDerivedHomIso.{u, v} f I a hGE hinj e).symm.op.prod (Iso.refl ω)) ≪≫
    (asIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f))).symm

/-! ### The higher self-extensions of `RHom_A(B, ω)` vanish -/

/-- **The nonzero degrees of the Hom computation of [stacks 0AX0].** For a finite homomorphism
of commutative rings and a dualizing complex `ω` over the source, there is no nonzero morphism
`RHom_A(B, ω) ⟶ RHom_A(B, ω)[n]` in `D(B)` for `n ≠ 0`.

The adjunction of [stacks 0A70] turns `Hom_{D(B)}(RHom_A(B, ω), RHom_A(B, ω)[n])` into
`Hom_{D(A)}(RHom_A(B, ω), ω[n])` — the shift passes through the right adjoint because
restriction of scalars commutes with it — and that is the degree-`n` cohomology of
`RHom_A(RHom_A(B, ω), ω)`, which is `B[0]` by `Dualizing.dualRestrictScalarsDerivedHomIso`. -/
theorem subsingleton_hom_derivedHom_shift [IsNoetherianRing A] (f : A →+* B) (hf : f.Finite)
    {ω : DerivedCategory (ModuleCat.{max v u} A)} (hω : IsDualizingComplex ω)
    (n : ℤ) (hn : n ≠ 0) :
    Subsingleton ((derivedHom.{u, v, u} f).obj ω ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj
        ((derivedHom.{u, v, u} f).obj ω)) := by
  obtain ⟨a, b, I, hGE, hLE, hinj, ⟨e⟩⟩ := hω.finiteInjectiveDimension
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v, u} f
  have hcs : (derivedHom.{u, v, u} f).CommShift ℤ := adj.rightAdjointCommShift ℤ
  have hsubH : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) n).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max v u} A).obj
        (Opposite.op ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
          ((derivedHom.{u, v, u} f).obj ω)), ω))) :=
    ModuleCat.isZero_iff_subsingleton.mp ((isZero_homology_targetSingle.{u, v} f hn).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) n).mapIso
        (dualRestrictScalarsDerivedHomIso.{u, v} f hf hω I a hGE hinj e)))
  have hsubHom : Subsingleton
      ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
          ((derivedHom.{u, v, u} f).obj ω) ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n).obj ω) :=
    Equiv.subsingleton (extAddEquivHomologyDerivedInternalHom.{u, max v u}
      (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((coextendComplex.{u, u, v} f).obj I))
      (restrictScalarsDerivedHomModelIso.{u, v} f I a hGE hinj e) I a hGE hinj e n).symm.toEquiv
  exact Equiv.subsingleton
    ((Iso.homCongr (Iso.refl ((derivedHom.{u, v, u} f).obj ω))
        ((((derivedHom.{u, v, u} f).commShiftIso n).app ω).symm)).trans
      (adj.homEquiv ((derivedHom.{u, v, u} f).obj ω)
        ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n).obj ω)).symm)

/-- **Tag 0AX0 modulo the degree-zero half of its Hom computation.** For a finite homomorphism
of Noetherian commutative rings and a dualizing complex `ω` over the source, `RHom_A(B, ω)` is a
dualizing complex over `B` as soon as its derived endomorphism module is `B`-linearly `B`.

Compared with `Dualizing.isDualizingComplex_derivedHom_of_finite_of_end` this discharges the
vanishing hypothesis in the nonzero degrees, by
`Dualizing.subsingleton_hom_derivedHom_shift`. What remains is the degree-zero statement, and
only its `B`-linearity: the chain of identifications used here produces an `A`-linear
isomorphism `End_{D(B)}(RHom_A(B, ω)) ≃ₗ[A] B` with no `B`-module structure attached, and an
`A`-linear isomorphism is genuinely insufficient — a `B`-algebra `E` with `E ≃ₗ[A] B` need not
have `B ≃ E`, as `A = k`, `B = k[x]/(x²)`, `E = k[y]/(y²)` with `x ↦ 0` shows. -/
theorem isDualizingComplex_derivedHom_of_finite_of_endLinearEquiv [IsNoetherianRing A]
    [IsNoetherianRing B] (f : A →+* B) (hf : f.Finite)
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (hω : IsDualizingComplex ω)
    (e₀ : End ((derivedHom.{u, v, u} f).obj ω) ≃ₗ[B] B) :
    IsDualizingComplex ((derivedHom.{u, v, u} f).obj ω) :=
  isDualizingComplex_derivedHom_of_finite_of_end.{u, v} f hf ω hω e₀
    fun n hn => subsingleton_hom_derivedHom_shift.{u, v} f hf hω n hn

end Dualizing

end
