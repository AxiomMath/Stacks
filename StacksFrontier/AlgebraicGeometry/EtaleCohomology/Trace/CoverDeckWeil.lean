module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckStepEight
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusCurveWeil
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison

/-!
# Steps 8 and 9 of the trace formula for a Galois cover, with Weil's formula

For `Λ = ℤ/ℓⁿ` and `N = Λ` placed in degree zero, the Frobenius of
`RΓ(Y_k̄, j_!(f_* j'^{-1} Λ_{V̄}))` composed with a deck transformation of a Galois cover has trace
zero, given only the perfectness of the complexes involved: the hypothesis of
`perfectDerivedTrace_openDeck_coverCompactification_eq_zero` on the twisted Frobenius of the
compactification is Weil's formula
`perfectDerivedTrace_selfMapCohomologyEndo_twistedGeometricFrobenius_eq_card_smul`, for the
constant complex `(ℤ/ℓⁿ)_{k̄}` identified with
`Stacks.Cohomology.GlobalSections.constantModuleSheaf`.

## Main definitions

* `Stacks.EtaleCohomology.zmodSingleComplex`: the complex `ℤ/ℓⁿ` in degree zero.
* `Stacks.EtaleCohomology.etaleModuleConstantComplexZModIso`: the constant complex `(ℤ/ℓⁿ)_{k̄}`
  in degree zero is the constant module sheaf in degree zero.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_openDeck_coverCompactification_eq_zero_of_zmod`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 8 and 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` (imported through Weil's formula) has a
-- free universe `w`; with it in scope the instance problems `EnoughInjectives (EtaleModules Λ X)`
-- of the statements below get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

universe u

namespace Stacks.EtaleCohomology

section CoverWeil

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U V : Scheme.{u}}
  {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU] (Y : Over (Spec (.of k))) [IsProper Y.hom]
  {jU : U ⟶ Y.left} [IsOpenImmersion jU] (hjU : jU ≫ Y.hom = pU) {f : V ⟶ U} [IsFinite f]
  [Etale f] [ConnectedSpace V] (C : CoverCompactification k Y.hom jU f) (a : V ≅ V)
  (ha : a.hom ≫ f = f) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- The complex `ℤ/ℓⁿ` placed in degree zero. -/
abbrev zmodSingleComplex (ℓ n : ℕ) : CochainComplex.Plus (ModuleCat.{u + 1} (ZMod (ℓ ^ n))) :=
  (Stacks.DerivedIndexing.singlePlusFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ n))) 0).obj
    (ModuleCat.of (ZMod (ℓ ^ n)) (ULift.{u + 1} (ZMod (ℓ ^ n))))

/-- The constant complex `(ℤ/ℓⁿ)_{k̄}` in degree zero is the constant module sheaf in degree
zero. -/
def etaleModuleConstantComplexZModIso (ℓ n : ℕ) :
    etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n) ≅
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
          (Spec (.of kbar)).smallEtaleTopology) :=
  (singlePlusFunctorCompMapCochainComplexPlusIso
    (constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod (ℓ ^ n))))).app
      (ModuleCat.of (ZMod (ℓ ^ n)) (ULift.{u + 1} (ZMod (ℓ ^ n))))

omit [IsCurve k pU] [Smooth pU] in
include hjU in
/-- **Steps 8 and 9 of [Stacks, Tag 03UG] for a Galois cover, with `Λ = ℤ/ℓⁿ`**: the Frobenius of
`RΓ(Y_k̄, j_!(f_* j'^{-1} Λ_{V̄}))` composed with the deck transformation `a` has trace zero,
granted the perfectness of the complexes involved. -/
theorem perfectDerivedTrace_openDeck_coverCompactification_eq_zero_of_zmod
    [Algebra.IsAlgebraic k kbar] (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hn : 1 ≤ n)
    [IsEmpty (rationalPoints pU)]
    (hY : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
          (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
            (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
                (openComplex (ZMod (ℓ ^ n)) (Z := C.toOver) C.j f
                  (zmodSingleComplex.{u} ℓ n)))))))))
        (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
          (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex (ZMod (ℓ ^ n)) C.toOver C.j
                (zmodSingleComplex.{u} ℓ n))))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod (ℓ ^ n))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)).obj))) :
    perfectDerivedTrace (ZMod (ℓ ^ n)) ⟨_, hY⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n)) (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n)) (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} (ZMod (ℓ ^ n))
          (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
            (openComplex (ZMod (ℓ ^ n)) (Z := C.toOver) C.j f (zmodSingleComplex.{u} ℓ n))))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
              (openComplex (ZMod (ℓ ^ n)) (Z := C.toOver) C.j f (zmodSingleComplex.{u} ℓ n))))
          (Y := (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
                (openComplex (ZMod (ℓ ^ n)) (Z := C.toOver) C.j f (zmodSingleComplex.{u} ℓ n)))))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} (ZMod (ℓ ^ n)) Y kbar p q hcard) (ComplexShape.up ℤ)).app
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
              (openComplex (ZMod (ℓ ^ n)) (Z := C.toOver) C.j f
                (zmodSingleComplex.{u} ℓ n))).obj) ≫
          (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
              (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.map
                (openDeck (ZMod (ℓ ^ n)) (C.extendOver hjU a ha) C.j f a.hom ha
                (C.isPullback_extend pU hjU a ha) (zmodSingleComplex.{u} ℓ n))))))) = 0 := by
  have : IsProper C.toOver.hom := inferInstanceAs (IsProper C.q)
  have : SmoothOfRelativeDimension 1 C.toOver.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.q)
  have e := etaleModuleConstantComplexZModIso.{u} kbar ℓ n
  have hp₂' := (isPerfect_selfMapCohomology_iff_of_iso (ZMod (ℓ ^ n))
    (pullback.snd C.toOver.hom (specAlgebraMap k kbar)) e).1 hp₂
  have hΓ' := (isPerfect_baseSectionsComplex_iff_of_iso (ZMod (ℓ ^ n))
    ((CochainComplex.Plus.ι _).mapIso e)).1 hΓ
  refine perfectDerivedTrace_openDeck_coverCompactification_eq_zero Y hjU C a ha kbar p q hcard
    (ZMod (ℓ ^ n)) (zmodSingleComplex.{u} ℓ n) hY hZ hp₂ hp₃ hΓ ?_
  rw [perfectDerivedTrace_selfMapCohomologyEndo_eq_of_iso (ZMod (ℓ ^ n))
      (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
      (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard)
      (twistedGeometricFrobenius_comp_toBase C.toOver (C.extendOver hjU a ha) kbar p q hcard)
      e hp₂ hp₂',
    perfectDerivedTrace_selfMapCohomologyEndo_twistedGeometricFrobenius_eq_card_smul C.toOver
      (C.extendOver hjU a ha) kbar p q hcard ℓ n hℓ hn hp₂' hΓ']
  exact congrArg _ (perfectDerivedTrace_id_baseSectionsComplex_eq_of_iso (ZMod (ℓ ^ n))
    ((CochainComplex.Plus.ι _).mapIso e) hΓ hΓ').symm

end CoverWeil

end Stacks.EtaleCohomology
