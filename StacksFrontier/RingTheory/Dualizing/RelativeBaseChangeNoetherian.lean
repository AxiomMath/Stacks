module

public import StacksFrontier.RingTheory.Dualizing.RelativeAlgEquivTransport
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero
public import StacksFrontier.RingTheory.Dualizing.RelativePerfectionTransitivity
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingDiagonal
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso
public import StacksFrontier.RingTheory.Flat.DegreewiseChase

/-!
# The Noetherian case of [stacks 0E2F] (2), and the residue-field vanishing it supplies

Let `R` be Noetherian, let `R → A` be flat of finite type with a polynomial presentation `p`, and
write `ω^•_{A/R} = φ^!(R)` for the upper shriek complex of `p` at the base ring.  For a
*Noetherian* `R'` the derived base change `ω^•_{A/R} ⊗ᴸ_A A'` is a relative dualizing complex for
`R' → A'`, and this file proves it: that is the case of clause (2) of [stacks 0E2F] which the
source does **not** obtain from the degreewise chase but from [stacks 0BZV] and [stacks 0E2E].

The point of having it is the residue fields.  The chase that proves clause (2) for an arbitrary
`R'` consumes, at every prime `𝔭` of `R`, the vanishing of the cohomology of
`RHom_{B_𝔭}(A_𝔭, K_𝔭 ⊗ᴸ_{A_𝔭} B_𝔭)` outside degree zero, where the subscript is base change along
`R → κ(𝔭)`.  Each `κ(𝔭)` is Noetherian, so the statement below applies at `R' = κ(𝔭)` and the
vanishing follows, with nothing carried.

## Main results

* `Dualizing.isRelativeDualizingComplex_of_iso` — being a relative dualizing complex depends only
  on the isomorphism class of the object.
* `Dualizing.isRelativeDualizingComplex_baseChange_upperShriek` — **the Noetherian case of
  [stacks 0E2F] (2), at the upper shriek complex.**
* `Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek` — **the
  residue-field vanishing**, in the shape the chase consumes it.

## The proof

[stacks 0BZV], `Dualizing.relativeDualizingComplexBaseChange_of_flatAlgebra`, gives
`ω^•_{A/R} ⊗ᴸ_A (R' ⊗_R A) ≅ ω^•_{(R' ⊗_R A)/R'}` at the base-changed presentation `p'`, for `R`
and `R'` Noetherian and `R → A` flat.  [stacks 0E2E],
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex_of_flat`,
says that the right-hand side *is* a relative dualizing complex for `R' → R' ⊗_R A`, `R' ⊗_R A`
being Noetherian because it is of finite type over `R'`.  Transporting along that isomorphism and
then along the `R'`-algebra isomorphism `R' ⊗_R A ≅ A ⊗_R R'` of `Dualizing.baseChangeComm` lands
the conclusion on the object clause (2) is stated at.

Two bookkeeping steps are needed and are both local.  [stacks 0BZV] states the base change as a
presentation of `Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗_R A` rather than of the
structure map `algebraMap R' (R' ⊗_R A)`, which [stacks 0E2E] reads; since the upper shriek
functor of a presentation uses only its variable count and its surjection, and those two ring maps
are equal, `Dualizing.PolynomialPresentation.baseChangeStructureMap` repackages it with no change
to the functor.  And [stacks 0BZV] lands on `R' ⊗_R A` while clause (2) lands on `A ⊗_R R'`; the
two derived extensions of scalars are identified by
`StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight`, uniqueness of left adjoints,
because the left coprojection `A → A ⊗_R R'` is the right coprojection `A → R' ⊗_R A` followed by
the commutation isomorphism.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
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

/-- **Being a relative dualizing complex depends only on the isomorphism class of the object.**
Relative perfection does, by `Dualizing.isRelativelyPerfect_of_iso`, and the diagonal condition of
[stacks 0E2C] is a `Nonempty` of isomorphisms, so it transports by functoriality of the derived
extension along the left coprojection and of derived Hom from the diagonal. -/
theorem isRelativeDualizingComplex_of_iso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K L : DerivedCategory (ModuleCat.{u} A)} (hK : IsRelativeDualizingComplex R A K)
    (e : K ≅ L) :
    IsRelativeDualizingComplex R A L :=
  ⟨isRelativelyPerfect_of_iso
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) e hK.relativelyPerfect,
    ⟨(derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
        ((diagonalDerivedExtension R A).mapIso e).symm ≪≫ hK.diagonalDerivedHom.some⟩⟩

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

/-- **The base-changed presentation of [stacks 0BZV], read at the structure map.**
`Dualizing.PolynomialPresentation.baseChange` presents
`Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗_R A`, while [stacks 0E2E] reads a presentation
of the structure map `algebraMap R' (R' ⊗_R A)`.  The two ring maps are equal, and the upper
shriek functor of a presentation uses only its variable count and its surjection, so this
repackaging changes neither the functor nor the projection-formula compatibility. -/
def PolynomialPresentation.baseChangeStructureMap
    (p : PolynomialPresentation (algebraMap R A)) :
    PolynomialPresentation (algebraMap R' (TensorProduct R R' A)) where
  variableCount := (p.baseChange (R' := R')).variableCount
  toRingHom := (p.baseChange (R' := R')).toRingHom
  commutes := by
    rw [(p.baseChange (R' := R')).commutes]
    ext r
    simp
  surjective := (p.baseChange (R' := R')).surjective

/-- The commutation of the two coprojections `A → R' ⊗_R A` and `A → A ⊗_R R'`: the second is the
first followed by `Dualizing.baseChangeComm`. -/
theorem baseChangeComm_comp_includeRight :
    ((baseChangeComm R A R').symm.toRingEquiv.symm.toRingHom.comp
        (((Algebra.TensorProduct.includeRight :
              A →ₐ[R] TensorProduct R R' A).toRingHom).comp
          (RingEquiv.refl A).toRingHom)) =
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R') := by
  ext a
  change (baseChangeComm R A R') ((1 : R') ⊗ₜ[R] a) = a ⊗ₜ[R] (1 : R')
  change (Algebra.TensorProduct.comm R R' A) ((1 : R') ⊗ₜ[R] a) = a ⊗ₜ[R] (1 : R')
  rw [Algebra.TensorProduct.comm_tmul]

/-- **The Noetherian case of [stacks 0E2F] (2), at the upper shriek complex.**  For `R` and `R'`
Noetherian and `R → A` flat of finite type with a polynomial presentation `p`, the derived base
change along `R → R'` of `ω^•_{A/R} = φ^!(R)` is a relative dualizing complex for
`R' → A ⊗_R R'`.

This is the case of clause (2) the source settles by [stacks 0BZV] and [stacks 0E2E] rather than
by the degreewise chase; like those two in this library, it carries no further hypothesis. -/
theorem isRelativeDualizingComplex_baseChange_upperShriek [IsNoetherianRing R]
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
  have hqRDC := q.relativeDualizingComplex_isRelativeDualizingComplex_of_flat hflatq
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
  -- The bundles spell the target of `comparison` as `extensionOfScalarsComplexGeneral`, and
  -- `derivedExtensionRingEquivIsoRight` spells it as the underlying `mapHomologicalComplex`; the
  -- two are definitionally equal but instance search is syntactic, so each universal property is
  -- restated at the spelling the consumer uses.
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
  refine isRelativeDualizingComplex_of_iso R' (A ⊗[R] R') hC ?_
  refine (eG.app ω).symm ≪≫ ?_
  exact eqToIso (congrArg
    (fun h : A →+* A ⊗[R] R' => (totalDerivedExtensionScalars.{u, u, u} h).functor.obj ω) hgeq)

/-- **The residue-field vanishing, from the Noetherian case of the clause.**  For `R`
Noetherian and `R → A` flat of finite type with a polynomial presentation `p`, the cohomology of
`RHom_{B_𝔭}(A_𝔭, ω_𝔭 ⊗ᴸ_{A_𝔭} B_𝔭)` vanishes outside degree zero at every prime `𝔭` of `R`, where
the subscript is base change along `R → κ(𝔭)` and `ω = φ^!(R)`.

The residue field `κ(𝔭)` is Noetherian, so
`Dualizing.isRelativeDualizingComplex_baseChange_upperShriek` applies at `R' = κ(𝔭)`; its diagonal
condition identifies the object with `A_𝔭[0]`, whose cohomology is concentrated in degree zero.
This is the hypothesis `hres` of
`Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldVanishing`. -/
theorem isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek [IsNoetherianRing R]
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
  have h := isRelativeDualizingComplex_baseChange_upperShriek R A
    (StacksDraft.DegreewiseChase.ResidueFieldAt R t) p hflat
  exact (isZero_homology_singleFunctor
      (ModuleCat.of (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)
        (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)) j hj).of_iso
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R t)) j).mapIso
        h.diagonalDerivedHom.some)

/-- **Clause (2) of [stacks 0E2F] at the upper shriek complex, with the residue-field vanishing
discharged.**  This is `Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldVanishing`
read at `K = ω^•_{A/R} = φ^!(R)` over a Noetherian base: both of its hypotheses about the complex
itself are supplied here, `hK` by [stacks 0E2E] and `hres` by
`Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek`, so what is left is
the representation data of [stacks 0E1U]. -/
theorem isRelativeDualizingComplex_baseChange_upperShriek_of_representation
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
    (pres.relativeDualizingComplex_isRelativeDualizingComplex_of_flat hflat)
    P dP hP eP F d hflatF eF E hE hEflat hEfin
    (fun t _ j hj =>
      isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek R A pres hflat t j hj)

end

end Dualizing

end
