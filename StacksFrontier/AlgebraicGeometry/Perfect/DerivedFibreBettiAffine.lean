module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.Homology.Perfect.BettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived-fibre Betti function on an affine scheme

Let `R` be a commutative ring and let `E` be a pseudo-coherent object of `D(𝒪_{Spec R})`.  This
module identifies the derived-fibre Betti function of `E`, the function
`x ↦ dim_{κ(x)} H^i(Li_x^* E)` of
`AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti`, with the module-theoretic derived-fibre
Betti function `StacksDraft.Perfect.fibreBetti` of an object of `D(R)` on `PrimeSpectrum R`, and
deduces from the affine case of part (2) of [Stacks, Tag 0BDI] that it is upper semi-continuous
on `Spec R`.

## Main results

* `AlgebraicGeometry.DerivedFibreBetti.finrank_derivedFibre_of_fac`: the dimension of the
  degree-`i` cohomology of the derived fibre of `M̃` at a point `x` of `Spec R`, computed through
  a factorisation of `i_x : Spec κ(x) ⟶ Spec R` through the spectrum of a field over `R`.
* `AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_eq_fibreBetti`: an object of
  `D(𝒪_{Spec R})` isomorphic to `M̃` has `StacksDraft.Perfect.fibreBetti M i` for its
  derived-fibre Betti function.
* `AlgebraicGeometry.DerivedFibreBetti.exists_isPseudoCoherent_derivedFiberBetti_eq`: a
  pseudo-coherent object of `D(𝒪_{Spec R})` has the derived-fibre Betti function of a
  pseudo-coherent object of `D(R)`.
* `AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti_spec`: **the affine
  case of part (2) of [Stacks, Tag 0BDI].**  The derived-fibre Betti function of a
  pseudo-coherent object of `D(𝒪_{Spec R})` is upper semi-continuous.

## Implementation notes

*The two steps of the bridge.*  The points of `Spec R` are the primes of `R` and the two
topologies agree definitionally, so what has to be compared is the two recipes for the fibre.
The sheaf-level one derives the pullback along `i_x : Spec κ(x) ⟶ Spec R` and then takes global
sections on `Spec κ(x)`; the module-level one extends scalars along `R ⟶ κ(x)` in `D(R)`.  Three
results identify them.
`AlgebraicGeometry.Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` factors `i_x` as
`Spec` of the canonical map `R ⟶ κ(x)` followed by `Spec` of an isomorphism of fields, and
`AlgebraicGeometry.SpecField.finrank_derivedPullback` says the second step does not
change dimensions; the affine comparison square of [Stacks, Tag 08DW] part (2),
`AlgebraicGeometry.StandardModel.affinePullbackComparison`, turns the first step into derived
extension of scalars; and over a field `AlgebraicGeometry.tilde.toTildeΓNatIso` together with the
exactness of `~` reads off the global sections.

*Where the object of `D(R)` comes from.*  A pseudo-coherent object of `D(𝒪_{Spec R})` has
quasi-coherent cohomology by [Stacks, Tag 08E5]
(`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`), so it is `M̃` for an object `M`
of `D(R)` by [Stacks, Tag 06Z0]
(`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`), and [Stacks, Tag 08E7]
(`Stacks.Thickenings.isPseudoCoherent_mapDerivedCategory_tilde_iff`) makes `M` pseudo-coherent.
That is exactly the hypothesis of
`StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent`, the affine case of
part (2) of [Stacks, Tag 0BDI].

*The model of the derived category.*  Everything is at
`CategoryTheory.HasDerivedCategory.standard`, and the local attribute carries priority `10000`: the
import closure reaches `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose
`HasDerivedCategory` instances are global, and a default-priority local attribute would not beat
them.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DerivedFibreBetti

/-! ### The derived fibre of a sheafified object -/

/-- Isomorphic objects of `D(𝒪_{Spec K})` have degree-`i` cohomology of the same dimension over
`K`. -/
private theorem finrank_homology_eq_of_iso (K : CommRingCat.{u}) (i : ℤ)
    {A B : DerivedCategory (Spec K).Modules} (e : A ≅ B) :
    Module.finrank K ((moduleSpecΓFunctor (R := K)).obj
        ((DerivedCategory.homologyFunctor (Spec K).Modules i).obj A)) =
      Module.finrank K ((moduleSpecΓFunctor (R := K)).obj
        ((DerivedCategory.homologyFunctor (Spec K).Modules i).obj B)) :=
  (((moduleSpecΓFunctor (R := K)).mapIso
    ((DerivedCategory.homologyFunctor (Spec K).Modules i).mapIso e)).toLinearEquiv).finrank_eq

/-- **The derived fibre of `M̃` through a factorisation of `i_x`.**  Let `R` be a commutative
ring, `x` a point of `Spec R` and `ψ : R ⟶ κ` a homomorphism into a field through whose spectrum
the canonical morphism `i_x : Spec κ(x) ⟶ Spec R` factors, the remaining step being `Spec` of an
isomorphism `κ(x) ≅ κ`.  Then the dimension over `κ(x)` of the degree-`i` cohomology of the
derived fibre of `M̃` at `x` is the dimension over `κ` of the degree-`i` cohomology of
`κ ⊗ᴸ_R M`. -/
public theorem finrank_derivedFibre_of_fac (R κ : CommRingCat.{u}) (hκ : IsField (κ : Type u))
    (x : ↥(Spec R)) (ψ : R ⟶ κ) (ι : (Spec R).residueField x ≅ κ)
    (hfac : Spec.map ι.inv ≫ Spec.map ψ = (Spec R).fromSpecResidueField x)
    (M : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    Module.finrank ((Spec R).residueField x)
      ((moduleSpecΓFunctor (R := (Spec R).residueField x)).obj
        ((DerivedCategory.homologyFunctor (Spec ((Spec R).residueField x)).Modules i).obj
          ((derivedPullback ((Spec R).fromSpecResidueField x).toLRSHom.toShHom).obj
            ((tilde.functor R).mapDerivedCategory.obj M)))) =
      Module.finrank (κ : Type u)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (κ : Type u)) i).obj
          ((totalDerivedExtensionScalars.{u, u, u} ψ.hom).functor.obj M)) := by
  have hLfield : IsField ((Spec R).residueField x : Type u) := Field.toIsField _
  have := SpecField.isEquivalence_tildeFunctor hκ
  have := SpecField.hasLeftDerivedFunctor_pullbackOnHomotopy_SpecMap hκ hLfield ι.inv
  have hshfac : (Spec.map ι.inv).toLRSHom.toShHom ≫ (Spec.map ψ).toLRSHom.toShHom =
      ((Spec R).fromSpecResidueField x).toLRSHom.toShHom := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : Spec ((Spec R).residueField x) ⟶ Spec R => k.toLRSHom.toShHom) hfac
  have e1 : (derivedPullback ((Spec R).fromSpecResidueField x).toLRSHom.toShHom).obj
        ((tilde.functor R).mapDerivedCategory.obj M) ≅
      (derivedPullback (Spec.map ι.inv).toLRSHom.toShHom).obj
        ((derivedPullback (Spec.map ψ).toLRSHom.toShHom).obj
          ((tilde.functor R).mapDerivedCategory.obj M)) :=
    (((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (Spec.map ι.inv).toLRSHom.toShHom (Spec.map ψ).toLRSHom.toShHom).app
          ((tilde.functor R).mapDerivedCategory.obj M)) ≪≫
      eqToIso (congrArg (fun k => (derivedPullback k).obj
        ((tilde.functor R).mapDerivedCategory.obj M)) hshfac)).symm
  have e2 : (derivedPullback (Spec.map ψ).toLRSHom.toShHom).obj
        ((tilde.functor R).mapDerivedCategory.obj M) ≅
      (tilde.functor κ).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} ψ.hom).functor.obj M) :=
    (AlgebraicGeometry.StandardModel.affinePullbackComparison R κ ψ).app M
  have e3 : (DerivedCategory.homologyFunctor (ModuleCat.{u} (κ : Type u)) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} ψ.hom).functor.obj M) ≅
      (moduleSpecΓFunctor (R := κ)).obj
        ((DerivedCategory.homologyFunctor (Spec κ).Modules i).obj
          ((tilde.functor κ).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u} ψ.hom).functor.obj M))) :=
    (tilde.toTildeΓNatIso (R := κ)).app _ ≪≫
      (moduleSpecΓFunctor (R := κ)).mapIso
        (derivedHomologyMapIso (tilde.functor κ) _ i)
  exact (finrank_homology_eq_of_iso _ i e1).trans
    ((SpecField.finrank_derivedPullback hκ hLfield ι.inv _ i).trans
      ((finrank_homology_eq_of_iso κ i e2).trans e3.toLinearEquiv.finrank_eq.symm))

/-! ### The derived-fibre Betti function on `Spec R` -/

/-- **An object of `D(𝒪_{Spec R})` isomorphic to `M̃` has the derived-fibre Betti function of
`M`.**  The derived-fibre Betti function of `E` is `StacksDraft.Perfect.fibreBetti M i`, read on
`Spec R` through the identification of its points with the primes of `R`. -/
public theorem derivedFiberBetti_eq_fibreBetti (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E) (i : ℤ)
    (M : DerivedCategory (ModuleCat.{u} R))
    (e : (tilde.functor R).mapDerivedCategory.obj M ≅ E) :
    derivedFiberBetti (Spec R) E hE i = StacksDraft.Perfect.fibreBetti.{u, u} M i := by
  funext x
  have hprime : x.asIdeal.IsPrime := x.isPrime
  refine (finrank_homology_eq_of_iso _ i
    ((derivedPullback ((Spec R).fromSpecResidueField x).toLRSHom.toShHom).mapIso e).symm).trans ?_
  exact finrank_derivedFibre_of_fac R (CommRingCat.of x.asIdeal.ResidueField)
    (Field.toIsField _) x (CommRingCat.ofHom (algebraMap (R : Type u) x.asIdeal.ResidueField))
    (Scheme.Spec.residueFieldIso R x)
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R x) M i

/-- **A pseudo-coherent object of `D(𝒪_{Spec R})` has the derived-fibre Betti function of a
pseudo-coherent object of `D(R)`.** -/
public theorem exists_isPseudoCoherent_derivedFiberBetti_eq (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} R),
      StacksDraft.PseudoCoherence.IsPseudoCoherent M ∧
        ∀ i : ℤ, derivedFiberBetti (Spec R) E hE i = StacksDraft.Perfect.fibreBetti.{u, u} M i := by
  obtain ⟨M, ⟨e⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R E
    (isQuasicoherentDerived_of_isPseudoCoherent (Spec R) E hE)
  refine ⟨M, ?_, fun i => derivedFiberBetti_eq_fibreBetti R E hE i M e⟩
  exact (Stacks.Thickenings.isPseudoCoherent_mapDerivedCategory_tilde_iff R M).1
    (hE.of_iso e.symm)

/-- **The affine case of part (2) of [Stacks, Tag 0BDI].**  The derived-fibre Betti function of a
pseudo-coherent object of `D(𝒪_{Spec R})` is upper semi-continuous on `Spec R`. -/
@[ega "III 7.6.9" "more general"]
public theorem upperSemicontinuous_derivedFiberBetti_spec (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E) (i : ℤ) :
    UpperSemicontinuous (derivedFiberBetti (Spec R) E hE i) := by
  obtain ⟨M, hM, hbetti⟩ := exists_isPseudoCoherent_derivedFiberBetti_eq R E hE
  rw [hbetti i]
  exact StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent.{u, u} M hM i

end AlgebraicGeometry.DerivedFibreBetti

end
