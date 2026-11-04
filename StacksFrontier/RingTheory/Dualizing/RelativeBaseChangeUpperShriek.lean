module

public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian

/-!
# Base change of the relative dualizing complex `φ^!(R)` over a Noetherian base

For a flat map of finite type `R → A` with a polynomial presentation, the derived base change of
`ω^•_{A/R} = φ^!(R)` along `R → R'` is a relative dualizing complex for `R' → A ⊗_R R'`: this is
clause (2) of [stacks 0E2F] at `ω^•_{A/R}`.

## Main results

* `Dualizing.isRelativeDualizingComplex_baseChange_relativeDualizingComplex`: the case where `R`
  and `R'` are Noetherian.
* `Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_relativeDualizingComplex`: for
  `R` Noetherian, the cohomology of `RHom(A_𝔭, ω_𝔭 ⊗ᴸ B_𝔭)` over the residue field at a prime `𝔭`
  vanishes outside degree zero.
* `Dualizing.isRelativeDualizingComplex_baseChange_relativeDualizingComplex_of_representation`:
  the case of an arbitrary `R'`, given the representation data of [stacks 0E1U].

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local implicit_reducible] extensionOfScalarsComplexGeneral

universe u

namespace Dualizing

noncomputable section

/-- An object of a derived category of modules which is a single module in degree zero has no
cohomology outside degree zero. -/
private theorem isZero_homology_singleFunctor {S : Type u} [CommRing S] (M : ModuleCat.{u} S)
    (j : ℤ) (hj : j ≠ 0) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) j).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M)) := by
  rcases lt_or_gt_of_ne hj with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 j h
  · exact DerivedCategory.isZero_of_isLE _ 0 j h

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- **The Noetherian case of [stacks 0E2F] (2), at the upper shriek complex.** For `R` and `R'`
Noetherian and `R → A` flat of finite type with a polynomial presentation `p`, the derived base
change along `R → R'` of `ω^•_{A/R} = φ^!(R)` is a relative dualizing complex for
`R' → A ⊗_R R'`. -/
theorem isRelativeDualizingComplex_baseChange_relativeDualizingComplex [IsNoetherianRing R]
    [IsNoetherianRing R'] (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R A).Flat) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    letI : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  let : Algebra.FinitePresentation R' (A ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R A R')
  let : Module.Flat R' (TensorProduct R R' A) := Module.Flat.baseChange R R' A
  let ω := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let f : A →+* TensorProduct R R' A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom
  let D := totalDerivedExtensionScalars.{u, u, u} f
  obtain ⟨e₀⟩ := relativeDualizingComplexBaseChange_of_flatAlgebra p hflat
    D.functor D.comparison D.isLeftDerived
  let q := PolynomialPresentation.baseChangeStructureMap R A R' p
  have : Algebra.FiniteType R' (TensorProduct R R' A) :=
    RingHom.finiteType_algebraMap.mp q.finiteType
  have : IsNoetherianRing (TensorProduct R R' A) :=
    Algebra.FiniteType.isNoetherianRing R' (TensorProduct R R' A)
  have : Algebra.FinitePresentation R' (TensorProduct R R' A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hflatq : (algebraMap R' (TensorProduct R R' A)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hqRDC := q.relativeDualizingComplex_isRelativeDualizingComplex hflatq
  have hDω : IsRelativeDualizingComplex R' (TensorProduct R R' A) (D.functor.obj ω) :=
    isRelativeDualizingComplex_of_iso R' (TensorProduct R R' A) hqRDC e₀.symm
  have hC := RelativeExistence.isRelativeDualizingComplex_of_algEquiv
    (baseChangeComm R A R') (D.functor.obj ω) hDω
  let eC : (A ⊗[R] R') ≃+* TensorProduct R R' A :=
    (baseChangeComm R A R').symm.toRingEquiv
  let g : A →+* A ⊗[R] R' :=
    eC.symm.toRingHom.comp (f.comp (RingEquiv.refl A).toRingHom)
  have hgeq : g = (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R') :=
    baseChangeComm_comp_includeRight R A R'
  let G := totalDerivedExtensionScalars.{u, u, u} g
  have : D.functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ D.functor ⟶
        (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from D.comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    D.isLeftDerived
  have : G.functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ G.functor ⟶
        (ModuleCat.extendScalars.{u, u, u}
            (eC.symm.toRingHom.comp (f.comp (RingEquiv.refl A).toRingHom))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from G.comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    G.isLeftDerived
  have eG := StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight.{u}
    eC f D.functor D.comparison G.functor G.comparison
  exact isRelativeDualizingComplex_of_iso R' (A ⊗[R] R') hC ((eG.app ω).symm ≪≫ eqToIso (congrArg
    (fun h : A →+* A ⊗[R] R' ↦ (totalDerivedExtensionScalars.{u, u, u} h).functor.obj ω) hgeq))

/-- **The residue-field vanishing.** For `R` Noetherian and `R → A` flat of finite type with a
polynomial presentation `p`, the cohomology of `RHom_{B_𝔭}(A_𝔭, ω_𝔭 ⊗ᴸ_{A_𝔭} B_𝔭)` vanishes
outside degree zero at every prime `𝔭` of `R`, where the subscript is base change along
`R → κ(𝔭)` and `ω = φ^!(R)`. -/
theorem isZero_homology_derivedHom_diagonalBaseChangeTarget_relativeDualizingComplex
    [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (t : Ideal R) [t.IsPrime] (j : ℤ) (hj : j ≠ 0) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    letI : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
    Limits.IsZero
      ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)) j).obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul'
              (StacksDraft.DegreewiseChase.ResidueFieldAt R t) :
              (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)
                  ⊗[StacksDraft.DegreewiseChase.ResidueFieldAt R t]
                (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)
                →ₐ[StacksDraft.DegreewiseChase.ResidueFieldAt R t]
                (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)).toRingHom).obj
          (diagonalBaseChangeTarget R A (StacksDraft.DegreewiseChase.ResidueFieldAt R t)
            (p.upperShriekFunctor.{u, 0}.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                (ModuleCat.of R R)))))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  let : Field (StacksDraft.DegreewiseChase.ResidueFieldAt R t) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (Localization.AtPrime t))
  let : Algebra.FinitePresentation (StacksDraft.DegreewiseChase.ResidueFieldAt R t)
      (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t) :=
    Algebra.FinitePresentation.equiv
      (baseChangeComm R A (StacksDraft.DegreewiseChase.ResidueFieldAt R t))
  have h := isRelativeDualizingComplex_baseChange_relativeDualizingComplex R A
    (StacksDraft.DegreewiseChase.ResidueFieldAt R t) p hflat
  exact (isZero_homology_singleFunctor
      (ModuleCat.of (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)
        (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)) j hj).of_iso
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)) j).mapIso
        h.diagonalDerivedHom.some)

/-- **Clause (2) of [stacks 0E2F] at the upper shriek complex over a Noetherian base.** Given
the representation data of [stacks 0E1U] for the diagonal, the derived base change of
`ω^•_{A/R} = φ^!(R)` along any `R → R'` is a relative dualizing complex for `R' → A ⊗_R R'`. -/
theorem isRelativeDualizingComplex_baseChange_relativeDualizingComplex_of_representation
    [Module.Flat R A] [Algebra.FinitePresentation R A] [IsNoetherianRing R] [IsNoetherianRing A]
    [IsNoetherianRing (A ⊗[R] A)] (pres : PolynomialPresentation (algebraMap R A))
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i : ℤ, Projective (P.X i)] (hP : CochainComplex.KFlat.{u, u} P)
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    (hflatF : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj
      (pres.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hE : ∀ (S' : Type u) [CommRing S'] [Algebra R S'],
      Nonempty ((diagonalIncludeLeftExtend R A S').obj E ≅
        CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] S')
          ((diagonalIncludeLeftExtend R A S').obj P)
          ((diagonalIncludeLeftExtend R A S').obj F)))
    (hEflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (E.X i)))
    (hEfin : ∀ i : ℤ, Module.Finite (A ⊗[R] A) (E.X i)) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj
        (pres.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  have hflat : (algebraMap R A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  exact isRelativeDualizingComplex_baseChange_of_residueFieldVanishing R A R' _
    (pres.relativeDualizingComplex_isRelativeDualizingComplex hflat)
    P dP hP eP F d hflatF eF E hE hEflat hEfin
    (fun t _ j hj ↦
      isZero_homology_derivedHom_diagonalBaseChangeTarget_relativeDualizingComplex
        R A pres hflat t j hj)

end

end Dualizing

end
