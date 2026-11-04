module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AbelianRestrictionCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StandardCoverAcyclicity

/-!
# Quasi-coherent modules are acyclic on affine objects of the big crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` and a sheaf `N` of `𝒪_{X/S}`-modules on
the big crystalline site `CRIS(X/S)` which is quasi-coherent, in the sense of
`SheafOfModules.IsQuasicoherentOnSite` (the form in which `Crystalline.FCrystal` carries it).  This
file proves that for every object `T = (U, T, δ)` of `CRIS(X/S)` whose map `U ⟶ X` is an open
immersion and whose ambient scheme is affine, the higher cohomology of `N` over `T` vanishes:

`R^q Γ(T, -) (N) = 0` for `q > 0`,

where `Γ(T, -)` is the sections functor of abelian sheaves on `CRIS(X/S)` at the coefficient
universe `u + 1`, applied to the abelian sheaf underlying the universe lift of `N`.  This is the
form in which the acyclicity hypothesis of the Čech theorem [Stacks, Tag 03F7]
(`Stacks.CechSite.Acyclic.isIso_cechCohomologyToCohomology_app`) is stated.

The objects in question are exactly those of the small crystalline site `Cris(X/S)`, and the proof
transports the small-site statement [Stacks, Tag 07JJ]
(`...SmallSite.vanishing07JJ_of_hasStandardCechVanishing`) along the inclusion
`i : Cris(X/S) ⥤ CRIS(X/S)`:

* the sections of an abelian sheaf on `CRIS(X/S)` over `i(A)` are the sections of its
  restriction `i^{-1}` over `A`, on the nose;
* restriction to the small site is exact and preserves injective objects
  (`...SmallSite.preservesInjectiveObjects_smallRestriction`), so it comes out of the right
  derived functors of the sections functor
  (`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`);
* the restriction of a quasi-coherent module on `CRIS(X/S)` is locally quasi-coherent on
  `Cris(X/S)` ([Stacks, Tag 07IT] on the big site,
  `Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`), so
  its Čech cohomology vanishes on the standard restriction covers and [Stacks, Tag 07JJ] applies.

## Main results

* `SmallSite.bigRightDerivedSectionsIso` — `R^q Γ(i(A), -) ≅ i^{-1} ⋙ R^q Γ(A, -)`.
* `SmallSite.isZero_bigRightDerivedSections_of_isAffine` — **the vanishing of the higher
  cohomology of a quasi-coherent module over an object of `CRIS(X/S)` lying in `Cris(X/S)` with
  affine ambient scheme.**

## References

* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- The restriction to `Cris(X/S)` of the abelian sheaf underlying a locally quasi-coherent module
on `CRIS(X/S)` has vanishing positive-degree Čech cohomology on the standard restriction covers:
it is the abelian sheaf of the restricted module, on the nose. -/
theorem hasStandardCechVanishing_smallRestriction
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hN : GlobalCrystallineSituation.IsLocallyQuasiCoherent N) :
    HasStandardCechVanishing
      ((smallRestriction S).obj ((bigToAbelianSheaf S).obj ((bigModuleULift S).obj N))) :=
  hasStandardCechVanishing_abelianSheaf (restrictSheafOfModules N)
    (fun A ↦ hN A.obj)

/-- The sections over `i(A)` of an abelian sheaf on `CRIS(X/S)` are the sections over `A` of its
restriction to `Cris(X/S)`. -/
def bigSectionsIsoSmallRestriction (A : CrystallineThickening S) :
    (sheafSections (topology S) AddCommGrpCat.{u + 1}).obj (op A.obj) ≅
      smallRestriction S ⋙ sectionsFunctorOver S A :=
  Iso.refl _

/-- **`R^q Γ(i(A), -) ≅ i^{-1} ⋙ R^q Γ(A, -)`**: restriction to the small site is exact and
preserves injective objects, so it comes out of the right derived functors of the sections
functor. -/
def bigRightDerivedSectionsIso (A : CrystallineThickening S) (q : ℕ) :
    ((sheafSections (topology S) AddCommGrpCat.{u + 1}).obj (op A.obj)).rightDerived q ≅
      smallRestriction S ⋙ (sectionsFunctorOver S A).rightDerived q :=
  Functor.rightDerivedIsoOfNatIso (bigSectionsIsoSmallRestriction A) q ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (smallRestriction S) (sectionsFunctorOver S A) q

/-- **A quasi-coherent module on `CRIS(X/S)` has no higher cohomology over an object whose map to
`X` is an open immersion and whose ambient scheme is affine**: `R^q Γ(T, -)` vanishes for `q > 0`
on the abelian sheaf underlying the universe lift of the module.  This is [Stacks, Tag 07JJ] on the
small site transported along `bigRightDerivedSectionsIso`. -/
theorem isZero_bigRightDerivedSections_of_isAffine
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (T : Thickening S) [IsOpenImmersion T.toX] [IsAffine T.thickening.target.scheme]
    (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (topology S) AddCommGrpCat.{u + 1}).obj (op T)).rightDerived q).obj
      ((bigToAbelianSheaf S).obj ((bigModuleULift S).obj N))) := by
  let A : CrystallineThickening S := ⟨T, inferInstanceAs (IsOpenImmersion T.toX)⟩
  refine IsZero.of_iso ?_ ((bigRightDerivedSectionsIso A q).app _)
  refine IsZero.of_iso ?_ (overCohomologyIsoRightDerivedSections S A _ q).symm
  exact vanishing07JJ_of_hasStandardCechVanishing _
    (hasStandardCechVanishing_smallRestriction
      (GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite N hN))
    A (inferInstanceAs (IsAffine T.thickening.target.scheme)) q hq

end Crystalline.GlobalCrystallineSituation.SmallSite
