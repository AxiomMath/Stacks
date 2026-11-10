module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.CoherentBaseCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# Perfect derived direct image over an affine base gives perfect derived global sections

Let `f : X ⟶ Spec R` be quasi-compact and quasi-separated and let `G` be a quasi-coherent
`𝒪_X`-module. If the derived direct image `Rf_*G` is a perfect object of `D(𝒪_{Spec R})`, then the
derived global sections `RΓ(X, G)` form a perfect object of `D(R)`.

## Main results

* `AlgebraicGeometry.isPerfect_derivedGlobalSectionsOverBase_of_isPerfect_derivedPushforward`:
  for `G` quasi-coherent and `f` quasi-compact and quasi-separated, if `Rf_*G` is perfect then
  `RΓ(X, G)` is perfect.
* `AlgebraicGeometry.isPerfect_derivedGlobalSectionsOver_id_of_isPerfect`: over `Spec R`, a
  perfect object of `D(𝒪_{Spec R})` with quasi-coherent cohomology has perfect derived global
  sections.
* `AlgebraicGeometry.nonempty_derivedGlobalSectionsOver_iso_derivedGlobalSectionsOverBase`: the
  unbounded `A`-linear `RΓ(X, G)` (`derivedGlobalSectionsOver f`) and the bounded below one
  (`ProperFlatGlobalSections.derivedGlobalSectionsOverBase f G`) agree on a module in degree `0`.

## References

* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- Over an affine base, a perfect object of `D(𝒪_{Spec R})` with quasi-coherent cohomology has
perfect derived global sections. -/
theorem isPerfect_derivedGlobalSectionsOver_id_of_isPerfect (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPerfect (X := (Spec R).toRingedSpace) E)
    (hQ : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj E) := by
  obtain ⟨M, ⟨e⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E hQ
  have hM : StacksDraft.Perfect.IsPerfect M :=
    (isPerfect_tilde_iff M).1 (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec R).toRingedSpace) e.symm hE)
  have := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit R
  let eu : M ≅ (derivedGlobalSectionsOver (𝟙 (Spec R))).obj
      ((derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).obj M) :=
    asIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M)
  exact StacksDraft.Perfect.isPerfect_of_iso
    (eu ≪≫ (derivedGlobalSectionsOver (𝟙 (Spec R))).mapIso ((derivedTildeCompι R).app M ≪≫ e)).symm
    hM

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- `Γ(X, 𝒪_X)`-linear global sections on the homotopy category of `𝒪_X`-modules, with values
in `D(Γ(X, 𝒪_X))`. -/
abbrev homotopyTopSections :
    HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)) :=
  (moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `homotopyTopSections` has a right derived functor with respect to the quasi-isomorphisms of
complexes of `𝒪_X`-modules. -/
instance homotopyTopSections_hasRightDerivedFunctor :
    (homotopyTopSections (X := X)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Scheme.Modules.hasRightDerivedFunctor X _

/-- The unbounded `Γ(X, 𝒪_X)`-linear derived global sections. -/
abbrev derivedTopSections : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)) :=
  (homotopyTopSections (X := X)).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The `A`-linear unbounded derived global sections are the `Γ(X, 𝒪_X)`-linear ones with the
scalars restricted along `A ⟶ Γ(X, 𝒪_X)`. -/
def derivedTopSectionsRestrictIso :
    derivedTopSections (X := X) ⋙
        (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory ≅
      derivedGlobalSectionsOver f := by
  haveI : (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).Additive :=
    inferInstance
  haveI := Stacks.Cohomology.SiteCohomologyPresheaf.isRightDerivedFunctor_totalRightDerived_comp
    (homotopyTopSections (X := X))
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory
  exact Functor.rightDerivedNatIso _ _
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedCompUnit
      (homotopyTopSections (X := X))
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory)
    (derivedGlobalSectionsOverUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (homotopyCompBaseIso (moduleGlobalSections X)
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom)
      (globalSectionsOver f) (Iso.refl _))

/-- For a module `G` in degree `0`, the unbounded derived global sections
`derivedGlobalSectionsOver f` and the bounded below
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsOverBase` agree on `G`. -/
theorem nonempty_derivedGlobalSectionsOver_iso_derivedGlobalSectionsOverBase (G : X.Modules) :
    Nonempty ((derivedGlobalSectionsOver f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
      Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsOverBase f G) := by
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (moduleGlobalSections X) (derivedTopSections (X := X))
    ((homotopyTopSections (X := X)).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (fun I hI => isIso_app_isKInjective_of_isRightDerivedFunctor X (moduleGlobalSections X)
      (derivedTopSections (X := X))
      ((homotopyTopSections (X := X)).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))) I hI)
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj G) 0 (by
      change ((DerivedCategory.singleFunctor X.Modules 0).obj G).IsGE 0
      infer_instance)
  exact ⟨((derivedTopSectionsRestrictIso f).app _).symm ≪≫
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory.mapIso e⟩

/-- For `f : X ⟶ Spec R` quasi-compact and quasi-separated and `G` a quasi-coherent
`𝒪_X`-module, if the derived direct image `Rf_*G` is perfect in `D(𝒪_{Spec R})` then
`RΓ(X, G)`, in the form `derivedGlobalSectionsOverBase`, is perfect in `D(R)`. -/
theorem isPerfect_derivedGlobalSectionsOverBase_of_isPerfect_derivedPushforward
    [QuasiCompact f] [QuasiSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (h : RingedSpace.IsPerfect (X := (Spec (CommRingCat.of A)).toRingedSpace)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          f.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex G)))) :
    StacksDraft.Perfect.IsPerfect
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsOverBase f G) := by
  let s : (DerivedCategory.singleFunctor X.Modules 0).obj G ≅
      DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex G) :=
    (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app G
  let E := (derivedPushforwardModules f).obj
    (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex G))
  have hQ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules
      n).obj E).IsQuasicoherent :=
    fun n => isQuasicoherent_of_iso _ _ _
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules n).mapIso
        ((derivedPushforwardModules f).mapIso s))
      (isQuasicoherent_homology_derivedPushforward_single_zero f G ‹_› n)
  obtain ⟨eB⟩ := nonempty_derivedGlobalSectionsOver_iso_derivedGlobalSectionsOverBase f G
  exact StacksDraft.Perfect.isPerfect_of_iso
    (eB.symm ≪≫ (derivedGlobalSectionsOver f).mapIso s ≪≫
      (derivedGlobalSectionsOverPushforwardIso f).app _)
    (isPerfect_derivedGlobalSectionsOver_id_of_isPerfect (CommRingCat.of A) E h hQ)

end AlgebraicGeometry

end
