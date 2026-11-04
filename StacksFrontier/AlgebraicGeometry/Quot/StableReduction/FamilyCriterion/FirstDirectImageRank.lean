module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyStructureSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.FirstDirectImageRankCech
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.FirstDirectImageRankGenus
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.FirstDirectImageRankSite

/-!
# The rank of `R¹f_*𝒪_X` for a family of nodal curves

Let `f : X ⟶ S` be proper and at-worst-nodal of relative dimension one, with geometrically
connected fibres. By [Stacks, Tag 0GKA] (b), `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module
whose formation commutes with base change; its fibre at `s ∈ S` is therefore `H¹(X_s, 𝒪_{X_s})`,
of dimension the genus of `X_s`. So if every fibre has genus `r`, then `R¹f_*𝒪_X` is finite
locally free of rank `r` on the small Zariski site of `S`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.NodalFamilyCohomology`.

* `isFiniteLocallyFreeOfRank_cohomology_one_of_specTarget`: over `Spec A`, `H¹(X, 𝒪_X)` is a
  finite locally free `A`-module of rank `r`.
* `isFiniteLocallyFreeOfRank_rightDerived_one_of_specTarget`: over `Spec A`, `R¹f_*𝒪_X` is
  finite locally free of rank `r`.
* `isFiniteLocallyFreeOfRank_rightDerived_one`: `R¹f_*𝒪_X` is finite locally free of rank `r`,
  pointwise on `S`.
* `isFiniteLocallyFreeOfRank_rightDerived_one_of_forall_genus`: the same on the small Zariski
  ringed site of `S`.

## Implementation notes

The rank is computed on the Čech model of `isFiniteLocallyFree_cohomology_one_of_specTarget`:
near a prime `p` of `A`, `H¹` of the model is free of rank `dim_{κ(p)} H¹(X_p, 𝒪)`, see
`StacksFrontier/AlgebraicGeometry/Quot/StableReduction/FamilyCriterion/FirstDirectImageRankCech.lean`.
The genus of the fibre over the field-valued point `Spec κ(p) ⟶ Spec A` is the genus of the
scheme-theoretic fibre at the image point, by invariance of the genus under extension of the
ground field (`genus_eq_of_isPullback_of_forall_genus`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.AlgebraicGeometry.NodalFamilyCohomology

variable {X S : Scheme.{u}}

/-- **Over an affine base, `H¹(X, 𝒪_X)` is finite locally free of rank the genus of the
fibres.** Let `f : X ⟶ Spec A` be proper and at-worst-nodal of relative dimension one, with
geometrically connected fibres, all of genus `r`. Then `H¹(X, 𝒪_X)` is a finite locally free
`A`-module of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_cohomology_one_of_specTarget {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f] [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (r : ℕ)
    (hr : ∀ s : Spec (.of A), genus (f.fiberToSpecResidueField s) = r) :
    Module.IsFiniteLocallyFreeOfRank A
      ((ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).obj
        (((moduleGlobalSections X).rightDerived 1).obj
          (SheafOfModules.unit X.ringCatSheaf))) r := by
  classical
  obtain ⟨hflat, hlfp, -⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := hlfp
  have : GeometricallyReduced f := geometricallyReduced_of_isAtWorstNodal f hf
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  obtain ⟨I, hI, hlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  have hfib : ∀ (p : Ideal A) [p.IsPrime], Function.Bijective (Stacks.Cech.globalRingHom
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).hom :=
    fun p _ => (ConcreteCategory.isIso_iff_bijective _).mp
      (Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper
        p.ResidueField _)
  have hvan : ∀ (p : Ideal A) [p.IsPrime] (j : ℕ), 2 ≤ j → Subsingleton
      (((moduleGlobalSections
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).rightDerived
          j).obj ((Scheme.Modules.pullback
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).obj
              O)) := by
    intro p _ j hj
    set g := Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))
    have hnod : IsAtWorstNodalOfRelativeDimensionOne (pullback.snd f g) :=
      IsAtWorstNodalOfRelativeDimensionOne.of_isPullback (IsPullback.of_hasPullback f g) hf
    have hdim := topologicalKrullDim_fiber_le_one (pullback.snd f g) hnod
    have : ((Scheme.Modules.pullback (pullback.fst f g)).obj O).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ O
    let := HasDerivedCategory.standard (pullback f g).Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(pullback f g, ⊤))
    have hz := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_cohomology_of_affine_base
      (d := 1) (pullback.snd f g) hdim ((Scheme.Modules.pullback (pullback.fst f g)).obj O)
      (j : ℤ) (by omega)
    exact ModuleCat.subsingleton_of_isZero
      ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ j _).mpr hz)
  have hgenus : ∀ (p : Ideal A) [p.IsPrime],
      genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))) = r :=
    fun p _ => genus_eq_of_isPullback_of_forall_genus (IsPullback.of_hasPullback f _) r hr
  exact (isFiniteLocallyFreeOfRank_homology_one f U hU hUaff haff hfib hvan r hgenus).of_linearEquiv
    (homologyBaseAlternatingCechComplexIso f U hU O haff 1).toLinearEquiv

/-- **Over an affine base, `R¹f_*𝒪_X` is finite locally free of rank the genus of the
fibres.** It is quasi-coherent, hence the sheaf associated with its module of global sections,
which is `H¹(X, 𝒪_X)`; that module is finite locally free of rank `r` by
`isFiniteLocallyFreeOfRank_cohomology_one_of_specTarget`, and so is the associated sheaf. -/
theorem isFiniteLocallyFreeOfRank_rightDerived_one_of_specTarget {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f] [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (r : ℕ)
    (hr : ∀ s : Spec (.of A), genus (f.fiberToSpecResidueField s) = r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank
      (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) r := by
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  set G := ((Scheme.Modules.pushforward f).rightDerived 1).obj O
  have : G.IsQuasicoherent := inferInstance
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (Spec (.of A)).Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Spec (.of A), ⊤))
  let Q : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := ⟨O, inferInstance⟩
  let H := ((moduleGlobalSections X).rightDerived 1).obj O
  let e2 : (ModuleCat.restrictScalars f.appTop.hom).obj H ≅
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (Spec (.of A))).obj G :=
    (ModuleCat.restrictScalars f.appTop.hom).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Stacks.Cohomology.AffineBase.moduleGlobalSections X) 1).app O) ≪≫
    (Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward f
      ((1 : ℕ) : ℤ)).app Q ≪≫
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (Spec (.of A))).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) 1).app O).symm
  let E : (ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).obj H ≅
      moduleSpecΓFunctor.obj G :=
    ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso (.of A)).inv.hom f.appTop.hom
        (Stacks.Cech.globalRingHom f).hom rfl H ≪≫
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).mapIso e2
  exact Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso (asIso (Scheme.Modules.fromTildeΓ G))
    ((tilde_isFiniteLocallyFreeOfRank_iff A (moduleSpecΓFunctor.obj G) r).mpr
      ((isFiniteLocallyFreeOfRank_cohomology_one_of_specTarget f hf r hr).of_linearEquiv
        E.toLinearEquiv))

/-- **`R¹f_*𝒪_X` is finite locally free of rank the genus of the fibres.** For `f : X ⟶ S`
proper and at-worst-nodal of relative dimension one with geometrically connected fibres, all of
genus `r`, the module `R¹f_*𝒪_X` is free of rank `r` on an open neighbourhood of every point of
`S`. Over an affine open `V` of `S` its restriction is `R¹(f ∣_ V)_*𝒪`, transported along
`V ≅ Spec Γ(V, 𝒪_V)` to `isFiniteLocallyFreeOfRank_rightDerived_one_of_specTarget`; the fibres of
`f ∣_ V` are base changes of fibres of `f`, of the same genus. -/
theorem isFiniteLocallyFreeOfRank_rightDerived_one (f : X ⟶ S) [IsProper f]
    [GeometricallyConnected f] (hf : IsAtWorstNodalOfRelativeDimensionOne f) (r : ℕ)
    (hr : ∀ s : S, genus (f.fiberToSpecResidueField s) = r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank
      (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) r := by
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top (fun V : S.affineOpens => V.1)
    (iSup_affineOpens_eq_top S) fun V => ?_
  have : IsAffine V.1.toScheme := V.2
  set g := f ∣_ V.1
  set e := V.1.toScheme.isoSpec
  set h : (f ⁻¹ᵁ V.1).toScheme ⟶ Spec (.of Γ(V.1.toScheme, ⊤)) := g ≫ e.hom
  have hg : IsAtWorstNodalOfRelativeDimensionOne g :=
    hf.of_isPullback (isPullback_morphismRestrict f V.1).flip
  have hsq : IsPullback (𝟙 _) h g e.inv := IsPullback.of_horiz_isIso ⟨by simp [h]⟩
  have : IsProper h := MorphismProperty.of_isPullback (P := @IsProper) hsq
    (inferInstanceAs (IsProper (f ∣_ V.1)))
  have : GeometricallyConnected h :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq
      (inferInstanceAs (GeometricallyConnected (f ∣_ V.1)))
  have hbig : IsPullback (f ⁻¹ᵁ V.1).ι h f (e.inv ≫ V.1.ι) := by
    simpa using hsq.paste_horiz (isPullback_morphismRestrict f V.1).flip
  have hrh : ∀ t : Spec (.of Γ(V.1.toScheme, ⊤)), genus (h.fiberToSpecResidueField t) = r :=
    fun t => genus_eq_of_isPullback_of_forall_genus
      ((IsPullback.of_hasPullback h (Scheme.fromSpecResidueField _ t)).paste_horiz hbig) r hr
  have hR :=
    isFiniteLocallyFreeOfRank_rightDerived_one_of_specTarget h (hg.of_isPullback hsq) r hrh
  set O' : (f ⁻¹ᵁ V.1).toScheme.Modules := SheafOfModules.unit (f ⁻¹ᵁ V.1).toScheme.ringCatSheaf
  set N := ((Scheme.Modules.pushforward g).rightDerived 1).obj O'
  -- transport along `e`
  let eh : (Scheme.Modules.pushforward e.hom).obj N ≅
      ((Scheme.Modules.pushforward h).rightDerived 1).obj O' :=
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (Scheme.Modules.pushforward g)
      (Scheme.Modules.pushforward e.hom) (Scheme.Modules.pushforward h)
      (Scheme.Modules.pushforwardComp g e.hom) 1).app O'
  have h2 : Scheme.Modules.IsFiniteLocallyFreeOfRank N r :=
    ((hR.of_iso eh.symm).pushforward_of_iso e.symm).of_iso
      ((Scheme.Modules.pushforwardComp e.hom e.inv).app N ≪≫
        (Scheme.Modules.pushforwardCongr e.hom_inv_id).app N ≪≫
        (Scheme.Modules.pushforwardId _).app N)
  -- restriction to `V`
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard S.Modules
  let := HasDerivedCategory.standard (f ⁻¹ᵁ V.1).toScheme.Modules
  let := HasDerivedCategory.standard V.1.toScheme.Modules
  let eV : N ≅ (Scheme.Modules.restrictFunctor V.1.ι).obj
      (((Scheme.Modules.pushforward f).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward g) 1).app O' ≪≫
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageRestrictIso f V.1 ≪≫
      (Scheme.Modules.restrictFunctor V.1.ι).mapIso
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) 1).app
          (SheafOfModules.unit X.ringCatSheaf)).symm
  exact h2.of_iso eV

/-- **`R¹f_*𝒪_X` has rank the genus of the fibres.** Let `f : X ⟶ S` be proper and
at-worst-nodal of relative dimension one, with geometrically connected fibres, all of genus `r`.
Then `R¹f_*𝒪_X` is finite locally free of rank `r` on the small Zariski site of `S`. -/
theorem isFiniteLocallyFreeOfRank_rightDerived_one_of_forall_genus (f : X ⟶ S) [IsProper f]
    [GeometricallyConnected f] (hf : IsAtWorstNodalOfRelativeDimensionOne f) (r : ℕ)
    (hr : ∀ s : S, genus (f.fiberToSpecResidueField s) = r) :
    RingedSite.IsFiniteLocallyFreeOfRank S.zariskiRingedSite
      (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) r :=
  (isFiniteLocallyFreeOfRank_rightDerived_one f hf r
    hr).isFiniteLocallyFreeOfRank_zariskiRingedSite

end Stacks.AlgebraicGeometry.NodalFamilyCohomology

end
