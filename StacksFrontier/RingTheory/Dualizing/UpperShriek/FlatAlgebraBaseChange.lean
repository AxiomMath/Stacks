module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.TorIndependentBaseChange
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectAnyPresentation

/-!
# Base change for the upper shriek of a flat finite-type homomorphism

Let `R → R'` be an arbitrary homomorphism, let `φ : R → A` be flat and of finite type and let
`φ' : R' → A' = R' ⊗_R A` be obtained from `φ` by base change. Flatness of `φ` makes `A` and `R'`
Tor independent over `R`, so the Tor-independent base-change map of [stacks 0BZR] gives the map
of [stacks 0BZS]: `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')`, natural in `K` in `D(R)`. Over a
Noetherian base `A` is a perfect module over the polynomial algebra of every presentation of
`φ`, and this map is an isomorphism, given the projection-formula compatibility of
[stacks 0E2A].

## Main results

* `RingTheory.TorIndependence.torIndependent_of_flat_left` — a flat `R`-algebra is Tor
  independent over `R` from every `R`-algebra.
* `Dualizing.PolynomialPresentation.upperShriekFlatAlgebraBaseChange` — the base-change map for a
  flat `φ`, read at arbitrary left-derived models of the two extensions of scalars.
* `Dualizing.PolynomialPresentation.upperShriekFlatAlgebraBaseChangeCanonical` — the same map at
  the canonical models, where the two derived tensor products need not be supplied.
* `Dualizing.PolynomialPresentation.isPerfectModule_of_flat` — for `R` Noetherian and `φ` flat,
  `A` is a perfect module over the polynomial algebra of the presentation.
* `Dualizing.PolynomialPresentation.isPerfectModule_uLift_of_flat` — the same for the universe
  lift of `A`.
* `Dualizing.PolynomialPresentation.isIso_upperShriekFlatAlgebraBaseChange` — that map is an
  isomorphism of functors over a Noetherian base, given the projection-formula compatibility
  `Dualizing.KFlatAlgebraActionEq` of [stacks 0E2A].

## References

* [Stacks Project, Tag 0BZS](https://stacks.math.columbia.edu/tag/0BZS)
* [Stacks Project, Tag 0BZR](https://stacks.math.columbia.edu/tag/0BZR)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 067J](https://stacks.math.columbia.edu/tag/067J)
* [Stacks Project, Tag 068Y](https://stacks.math.columbia.edu/tag/068Y)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingTheory.TorIndependence

/-- A flat `R`-algebra `A` is Tor independent over `R` from every `R`-algebra `S`. -/
@[sga "6 VIII 1.4" "partial", sga "7 VIII 1.2" "special case"]
theorem torIndependent_of_flat_left {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Module.Flat R A] :
    TorIndependent R A S := by
  rw [torIndependent_iff_isZero_tor]
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact isZero_Tor_succ_of_flat (ModuleCat.of R A) (ModuleCat.of R S) k

end RingTheory.TorIndependence

namespace Dualizing

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- For a flat `φ : R → A` of finite type over a Noetherian ring `R`, the target is a perfect
module over the polynomial algebra `P` of every polynomial presentation of `φ`. -/
theorem PolynomialPresentation.isPerfectModule_of_flat [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : Module p.Poly A := Module.compHom A p.toRingHom
    StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let D := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R
  let α : p.Poly →ₐ[R] A := p.toAlgHom
  exact RingHom.isPerfectModule_of_isPerfectRingMap D.tensor D.comparison D.isLeftDerived
    ((RingHom.isPerfectRingMap_of_flat_of_finitePresentation R A).2
      D.tensor D.comparison D.isLeftDerived)
    p.variableCount α p.surjective

/-- For a flat `φ : R → A` of finite type over a Noetherian ring `R`, the universe lift
`ULift.{v} A` is a perfect module over the polynomial algebra of every polynomial presentation
of `φ`. -/
theorem PolynomialPresentation.isPerfectModule_uLift_of_flat [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : Module p.Poly (ULift.{v} A) := Module.compHom (ULift.{v} A) p.toRingHom
    StacksDraft.Perfect.IsPerfectModule (R := p.Poly) (ULift.{v} A) := by
  let : Module p.Poly A := Module.compHom A p.toRingHom
  exact StacksDraft.Perfect.isPerfectModule_ulift.{u, v} A (p.isPerfectModule_of_flat hflat)

/-- Let `φ : R → A` be flat and admit the polynomial presentation `p`, and let `R → R'` be
arbitrary. The base-change map
`φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')`, natural in `K` in `D(R)`, for
`φ' : R' → A' = R' ⊗_R A`; here `φ^!` is read at `p` and `(φ')^!` at the base-changed
presentation, and the two derived tensor products are read at the given left-derived models of
extension of scalars. -/
@[no_expose]
def PolynomialPresentation.upperShriekFlatAlgebraBaseChange
    (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R A).Flat)
    (bcR : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    p.upperShriekFunctor.{u, 0} ⋙ bcT ⟶
      bcR ⋙ (p.baseChange (R' := R')).upperShriekFunctor.{u, 0} :=
  letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  p.upperShriekTorIndependentBaseChange
    RingTheory.TorIndependence.torIndependent_of_flat_left bcR cmpR ldR bcT cmpT ldT

attribute [local implicit_reducible] extensionOfScalarsComplexGeneral
  extensionOfScalarsComplex

/-- The map of `Dualizing.PolynomialPresentation.upperShriekFlatAlgebraBaseChange` at the
canonical unbounded derived extensions of scalars. -/
def PolynomialPresentation.upperShriekFlatAlgebraBaseChangeCanonical
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    p.upperShriekFunctor.{u, 0} ⋙
        (derivedExtensionScalarsGeneral.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).functor ⟶
      (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R R')).functor ⋙
        (p.baseChange (R' := R')).upperShriekFunctor.{u, 0} :=
  p.upperShriekFlatAlgebraBaseChange hflat
    (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R R')).functor
    (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R R')).comparison
    (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R R')).isLeftDerived
    (derivedExtensionScalarsGeneral.{u, u, u}
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] TensorProduct R R' A).toRingHom).functor
    (derivedExtensionScalarsGeneral.{u, u, u}
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] TensorProduct R R' A).toRingHom).comparison
    (derivedExtensionScalarsGeneral.{u, u, u}
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] TensorProduct R R' A).toRingHom).isLeftDerived

/-- Let `R` be Noetherian, let `φ : R → A` be flat and admit the polynomial presentation `p`,
and let `R → R'` be arbitrary.
The base-change map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')` of
`Dualizing.PolynomialPresentation.upperShriekFlatAlgebraBaseChange` is an isomorphism of
functors, given the projection-formula compatibility `hAct : Dualizing.KFlatAlgebraActionEq` of
[stacks 0E2A]. -/
theorem PolynomialPresentation.isIso_upperShriekFlatAlgebraBaseChange [IsNoetherianRing R]
    (hAct : KFlatAlgebraActionEq.{u})
    (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R A).Flat)
    (bcR : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    IsIso (p.upperShriekFlatAlgebraBaseChange hflat bcR cmpR ldR bcT cmpT ldT) :=
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  p.isIso_upperShriekTorIndependentBaseChange hAct
    RingTheory.TorIndependence.torIndependent_of_flat_left (p.isPerfectModule_of_flat hflat)
    bcR cmpR ldR bcT cmpT ldT

end Dualizing

end
