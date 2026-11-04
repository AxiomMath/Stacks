module

public import StacksFrontier.AlgebraicGeometry.Etale.ModuleSheafDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.TorsionDirectImageAcyclicComplexes
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact

/-!
# Complexes of acyclic sheaves of modules compute `Rh_*`, on the small étale sites of a big site

Let `B` be a big étale site, `h : Y ⟶ Z` a proper morphism of it and `Λ` a torsion ring. A complex
`P` of sheaves of `Λ`-modules on `Y_étale` whose terms are acyclic for the direct image `h_*`
computes `Rh_*` on the unbounded derived category: `h_*` carries every quasi-isomorphism from `P`
to a K-injective complex to a quasi-isomorphism. This is
`Stacks.EtaleCohomology.quasiIso_etaleModuleDirectImage_map_of_rightAcyclic` (the core of case (b)
of [Stacks, Tag 0F7G]) carried to the size-bounded small étale sites of `B` along
`AlgebraicGeometry.SmallEtale.sheafEquiv`, which commutes with direct images
(`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`), preserves K-injective
complexes and quasi-isomorphisms, and identifies the higher direct images.

## Main definitions

* `AlgebraicGeometry.SmallEtale.etalePushforwardModSheafEquivIso`: the comparison of direct
  images of sheaves of `Λ`-modules across `AlgebraicGeometry.SmallEtale.sheafEquiv`.

## Main results

* `AlgebraicGeometry.SmallEtale.quasiIso_etalePushforwardMod_map_of_rightAcyclic`: the statement
  above.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {Y Z : B.Scheme}

/-- Modules over `Λ : Type u` in `Type (u + 1)` have limits indexed by `Type (u + 1)`, stated at
these universes so that instance search does not have to solve `max (u + 1) ?r = u + 1`. -/
private instance hasLimitsOfSize_moduleCat_succ_succ :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, u}

/-- The comparison `AlgebraicGeometry.SmallEtale.sheafEquiv` of the two small étale sites, for
sheaves of `Λ`-modules, with the limits it needs supplied at the universes at hand so that
instance search does not have to solve `max u ?r = u + 1`. -/
abbrev moduleSheafEquiv (S : B.Scheme) :
    ModuleSheaf.{u, u, u} B S Λ ≌ Stacks.EtaleCohomology.EtaleModules.{u, u} Λ S.obj :=
  @sheafEquiv B S.obj S.property (ModuleCat.{u + 1} Λ) _
    (ModuleCat.hasLimitsOfSize.{u, u, u + 1, u})

/-- **Direct images of sheaves of `Λ`-modules commute with the comparison of the two small étale
sites**: `h_* ⋙ E_Z ≅ E_Y ⋙ h_*`, for `E` the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`
from the bounded small étale sites to Mathlib's. -/
def etalePushforwardModSheafEquivIso (h : Y ⟶ Z) :
    etalePushforwardMod B Λ h ⋙ (moduleSheafEquiv B Λ Z).functor ≅
      (moduleSheafEquiv B Λ Y).functor ⋙
        Stacks.EtaleCohomology.etaleModuleDirectImage.{u, u} Λ (B.inclusion.map h) :=
  let EY := moduleSheafEquiv B Λ Y
  let EZ := moduleSheafEquiv B Λ Z
  let Hm := Stacks.EtaleCohomology.etaleModuleDirectImage.{u, u} Λ (B.inclusion.map h)
  let e₀ : Hm ⋙ EZ.inverse ≅ EY.inverse ⋙ etalePushforwardMod B Λ h :=
    toEtaleSitePushforwardBaseChangeIso B h (ModuleCat.{u + 1} Λ)
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight EY.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft EY.functor
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₀.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Hm EZ.counitIso ≪≫
        Functor.rightUnitor _)

/-- **Complexes of `h_*`-acyclic sheaves of `Λ`-modules compute `Rh_*`, for `h` proper and `Λ`
torsion**, on the small étale sites of a big étale site: `h_*` carries every quasi-isomorphism
from such a complex to a K-injective complex to a quasi-isomorphism. -/
theorem quasiIso_etalePushforwardMod_map_of_rightAcyclic (h : Y ⟶ Z)
    [IsProper (B.inclusion.map h)] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    {P J : CochainComplex (ModuleSheaf.{u, u, u} B Y Λ) ℤ}
    (hP : ∀ (i : ℤ) (p : ℕ), 0 < p →
      IsZero (((etalePushforwardMod B Λ h).rightDerived p).obj (P.X i)))
    (s : P ⟶ J) [QuasiIso s] (hJ : J.IsKInjective) :
    QuasiIso (((etalePushforwardMod B Λ h).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  let EY := moduleSheafEquiv B Λ Y
  let EZ := moduleSheafEquiv B Λ Z
  let Hb := etalePushforwardMod B Λ h
  let Hm := Stacks.EtaleCohomology.etaleModuleDirectImage.{u, u} Λ (B.inclusion.map h)
  let Φ := etalePushforwardModSheafEquivIso B Λ h
  have : EY.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EZ.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EY.functor.PreservesHomology := Functor.preservesHomologyOfExact _
  have : EZ.functor.PreservesHomology := Functor.preservesHomologyOfExact _
  have : EY.functor.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms EY.symm.toAdjunction
  -- the transported data
  have hJ' : CochainComplex.IsKInjective ((EY.functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J) :=
    have := hJ
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence EY.functor J
  have hP' : ∀ (i : ℤ) (p : ℕ), 0 < p → IsZero ((Hm.rightDerived p).obj
      (((EY.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i)) :=
    fun i p hp ↦ (EZ.functor.map_isZero (hP i p hp)).of_iso
      ((Functor.rightDerivedSquareIsoOfExact Hb EZ.functor EY.functor Hm Φ p).app (P.X i)).symm
  have hm' : QuasiIso (((EY.functor ⋙ Hm).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
    Stacks.EtaleCohomology.quasiIso_etaleModuleDirectImage_map_of_rightAcyclic Λ
      (B.inclusion.map h) m hm hΛ hP'
      ((EY.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map s) hJ'
  have hb : QuasiIso (((Hb ⋙ EZ.functor).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
      ((NatIso.mapHomologicalComplex Φ (ComplexShape.up ℤ)).app P)
      ((NatIso.mapHomologicalComplex Φ (ComplexShape.up ℤ)).app J)
      ((NatIso.mapHomologicalComplex Φ (ComplexShape.up ℤ)).hom.naturality s).symm)).2 hm'
  have hb' : QuasiIso ((EZ.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((Hb.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) := hb
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ EZ.functor).1 hb'

end AlgebraicGeometry.SmallEtale

end
