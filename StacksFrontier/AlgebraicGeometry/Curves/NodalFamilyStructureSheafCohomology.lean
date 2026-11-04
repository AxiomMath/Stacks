module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.FirstCohomologyLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.GeometricFibresDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyBaseChange
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimensionOneCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeTopDegreeConclusion

/-!
# The cohomology of the structure sheaf of a family of nodal curves

Let `f : X ⟶ S` be proper and at-worst-nodal of relative dimension one, with geometrically
connected fibres. [Stacks, Tag 0GKA] asserts that

* (a) `f_*𝒪_X = 𝒪_S`, and this holds after any base change;
* (b) `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module whose formation commutes with any base
  change;
* (c) `Rᵠf_*𝒪_X = 0` for `q ≥ 2`.

Part (a) is [Stacks, Tag 0E0L], to which the source refers, applied to `f`: an at-worst-nodal
family is flat and locally of finite presentation, and its fibres are geometrically reduced
([Stacks, Tags 0C59, 0E37]).

## Main results

All in the namespace `Stacks.AlgebraicGeometry.NodalFamilyCohomology`.

* `topologicalKrullDim_fiber_le_one`, `geometricallyReduced_of_isAtWorstNodal`: the fibres of
  such a family are curves, and they are geometrically reduced ([Stacks, Tags 0C59, 0E37]).
* `isFiniteLocallyFree_cohomology_one_of_specTarget`: over an affine base, `H¹(X, 𝒪_X)` is a
  finite locally free module.
* `isFiniteLocallyFree_rightDerived_one`: `R¹f_*𝒪_X` is finite locally free.
* `topDegreeSituation`: `f` over a quasi-compact quasi-separated open of `S`, as a situation of
  [Stacks, Tag 0EX3] in degree one.
* `isFiniteLocallyFree_rightDerived_one_and_isIso_baseChange`: **part (b)**.
* `isIso_c_and_isIso_c_of_isPullback_of_isAtWorstNodal`: **part (a)**.
* `isZero_rightDerived_of_two_le`: **part (c)**.

## Implementation notes

The source's proof of (b) splits `Rf_*𝒪_X = 𝒪_S ⊕ P` locally ([Stacks, Tag 0E62]). Here the
same information is read off the mapping cone of the unit `𝒪_S ⟶ Rf_*𝒪_X` on a Čech model,
whose derived fibres are concentrated in degree one; see
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFamily/FirstCohomologyLocallyFree.lean`. The
base-change half of (b) is [Stacks, Tag 0EX3] (c) at `d = 1`, whose vanishing hypothesis is
[Stacks, Tag 0E7D]; the base-change map of this library is defined over a quasi-compact
quasi-separated base, so the clause is stated over every quasi-compact quasi-separated open of
`S`, which is what commutation with base change means locally on the base. Higher direct images
are Mathlib's `ℕ`-indexed right derived functors, which do not depend on a choice of model of the
derived category.

## References

* [Stacks Project, Tag 0GKA](https://stacks.math.columbia.edu/tag/0GKA)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.AlgebraicGeometry.NodalFamilyCohomology

variable {X S : Scheme.{u}}

/-- **The fibres of an at-worst-nodal family with geometrically connected fibres have dimension
one.** They are nonempty, being connected, and a nonempty fibre is equidimensional of dimension
one ([Stacks, Tag 0C59]). -/
theorem topologicalKrullDim_fiber_le_one (f : X ⟶ S) [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (s : S) :
    topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, -, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  rw [(h s inferInstance).2.1]
  rfl

/-- **An at-worst-nodal family with geometrically connected fibres is geometrically reduced.**
Every fibre is a curve over its residue field with at-worst-nodal singularities, hence
geometrically reduced ([Stacks, Tag 0E37]). -/
theorem geometricallyReduced_of_isAtWorstNodal (f : X ⟶ S) [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) : GeometricallyReduced f := by
  obtain ⟨-, hlfp, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  have : LocallyOfFinitePresentation f := hlfp
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun s => ?_⟩
  let : (f.fiber s).Over (Spec (.of (S.residueField s))) := ⟨f.fiberToSpecResidueField s⟩
  have : LocallyOfFiniteType (f.fiber s ↘ Spec (.of (S.residueField s))) :=
    inferInstanceAs (LocallyOfFiniteType (f.fiberToSpecResidueField s))
  obtain ⟨heq, hdim, hnodal⟩ := h s inferInstance
  exact (Stacks.Curves.geometricallyReduced_of_hasAtWorstNodalSingularities _ _ heq hdim
    hnodal).geometrically_isReduced

/-- An at-worst-nodal family is flat, locally of finite presentation and geometrically reduced. -/
private theorem flat_and_lfp_and_geometricallyReduced_of_isAtWorstNodal (f : X ⟶ S)
    [GeometricallyConnected f] (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    Flat f ∧ LocallyOfFinitePresentation f ∧ GeometricallyReduced f := by
  obtain ⟨hflat, hlfp, -⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  exact ⟨hflat, hlfp, geometricallyReduced_of_isAtWorstNodal f hf⟩

/-- Finite local freeness is invariant under linear equivalence. -/
private theorem isFiniteLocallyFree_of_linearEquiv {A M N : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (h : Module.IsFiniteLocallyFree A M) : Module.IsFiniteLocallyFree A N := by
  rw [Module.isFiniteLocallyFree_iff_finite_projective] at h ⊢
  obtain ⟨_, _⟩ := h
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

/-- **Over an affine base, `H¹(X, 𝒪_X)` is a finite locally free module.** Let
`f : X ⟶ Spec A` be proper and at-worst-nodal of relative dimension one, with geometrically
connected fibres. Every fibre `X_p` is a proper, geometrically reduced and geometrically connected
curve over `κ(p)`, so it has only constant functions ([Stacks, Tag 0BUG]) and no cohomology above
degree one ([Stacks, Tag 0E7D]); the Čech computation of
`isFiniteLocallyFree_homology_one` then applies. -/
theorem isFiniteLocallyFree_cohomology_one_of_specTarget {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f] [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    Module.IsFiniteLocallyFree A ((ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).obj
      (((moduleGlobalSections X).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf))) := by
  classical
  obtain ⟨_, _, _⟩ := flat_and_lfp_and_geometricallyReduced_of_isAtWorstNodal f hf
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : O.IsFinitePresentation := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have : O.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation O
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
  have h := isFiniteLocallyFree_homology_one f U hU hUaff haff hfib hvan
  have e := (homologyBaseAlternatingCechComplexIso f U hU O haff 1).toLinearEquiv
  exact isFiniteLocallyFree_of_linearEquiv e h

/-- **Over an affine base, `R¹f_*𝒪_X` is finite locally free.** It is quasi-coherent, hence the
sheaf associated with its module of global sections, which is `H¹(X, 𝒪_X)`
([Stacks, Tag 01XK]); that module is finite locally free by
`isFiniteLocallyFree_cohomology_one_of_specTarget`, and so is the associated sheaf
([Stacks, Tag 05JM]). -/
theorem isFiniteLocallyFree_rightDerived_one_of_specTarget {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f] [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : O.IsFinitePresentation := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have : O.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation O
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
  let e3 := ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso (.of A)).inv.hom f.appTop.hom
    (Stacks.Cech.globalRingHom f).hom rfl H
  let E : (ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).obj H ≅
      moduleSpecΓFunctor.obj G :=
    e3 ≪≫ (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).mapIso e2
  have hM := isFiniteLocallyFree_cohomology_one_of_specTarget f hf
  have hM' : Module.IsFiniteLocallyFree A (moduleSpecΓFunctor.obj G) := by
    exact isFiniteLocallyFree_of_linearEquiv E.toLinearEquiv hM
  have ht := (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module A
    (moduleSpecΓFunctor.obj G)).mpr hM'
  exact SheafOfModules.IsFiniteLocallyFree.of_iso (asIso (Scheme.Modules.fromTildeΓ G)) (h := ht)

/-- **`R¹f_*𝒪_X` is finite locally free.** For `f : X ⟶ S` proper and at-worst-nodal of
relative dimension one with geometrically connected fibres, `R¹f_*𝒪_X` is a finite locally free
`𝒪_S`-module. Finite local freeness is local on `S`, and over an affine open `V` of `S` the
restriction of `R¹f_*𝒪_X` is `R¹(f ∣_ V)_*𝒪` ([Stacks, Tag 01E5]), which is transported along
`V ≅ Spec Γ(V, 𝒪_V)` to `isFiniteLocallyFree_rightDerived_one_of_specTarget`. -/
theorem isFiniteLocallyFree_rightDerived_one (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  rw [← Scheme.Modules.isFiniteLocallyFree_iff]
  refine Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top (fun V : S.affineOpens => V.1)
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
  have hR := isFiniteLocallyFree_rightDerived_one_of_specTarget h (hg.of_isPullback hsq)
  set O' : (f ⁻¹ᵁ V.1).toScheme.Modules := SheafOfModules.unit (f ⁻¹ᵁ V.1).toScheme.ringCatSheaf
  set N := ((Scheme.Modules.pushforward g).rightDerived 1).obj O'
  -- transport along `e`
  let eh : (Scheme.Modules.pushforward e.hom).obj N ≅
      ((Scheme.Modules.pushforward h).rightDerived 1).obj O' :=
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (Scheme.Modules.pushforward g)
      (Scheme.Modules.pushforward e.hom) (Scheme.Modules.pushforward h)
      (Scheme.Modules.pushforwardComp g e.hom) 1).app O'
  have h1 : Scheme.Modules.IsFiniteLocallyFree ((Scheme.Modules.pushforward e.hom).obj N) :=
    ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr hR).of_iso eh.symm
  have h2 : Scheme.Modules.IsFiniteLocallyFree N :=
    (h1.pushforward_of_iso e.symm).of_iso
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

/-- **[Stacks, Tag 0GKA], part (a).** Let `f : X ⟶ S` be proper and at-worst-nodal of relative
dimension one, with geometrically connected fibres. Then `f_*𝒪_X = 𝒪_S`, i.e. the comparison
`f.c : 𝒪_S ⟶ f_*𝒪_X` is invertible, and this holds after any base change: for every cartesian
square `X' ⟶ X`, `f' : X' ⟶ S'`, `S' ⟶ S`, the comparison `f'.c` is invertible.

This is [Stacks, Tag 0E0L]: `f` is flat and locally of finite presentation, being syntomic, and
geometrically reduced by `geometricallyReduced_of_isAtWorstNodal`. -/
@[stacks 0GKA "(a): `f_*𝒪_X = 𝒪_S`, as invertibility of `f.c`, and the same for every base \
change, stated for every cartesian square over `S`"]
theorem isIso_c_and_isIso_c_of_isPullback_of_isAtWorstNodal (f : X ⟶ S) [IsProper f]
    [GeometricallyConnected f] (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    IsIso f.c ∧ ∀ {X' S' : Scheme.{u}} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'},
      IsPullback g' f' f g → IsIso f'.c := by
  obtain ⟨_, _, _⟩ := flat_and_lfp_and_geometricallyReduced_of_isAtWorstNodal f hf
  exact Stacks.AlgebraicGeometry.ProperFlatStructureSheaf.isIso_c_and_isIso_c_of_isPullback f

/-- **The top-degree base-change situation of a nodal family over a quasi-compact and
quasi-separated open of the base.** For `f : X ⟶ S` proper and at-worst-nodal of relative
dimension one with geometrically connected fibres and `V ⊆ S` a quasi-compact quasi-separated
open, the restriction `f ∣_ V` has fibres of dimension at most one, so its higher direct images of
quasi-coherent modules vanish above degree one ([Stacks, Tag 0E7D]); together with the identity
square this is a `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` in degree `d = 1`, the
setting in which this library defines the base-change map `γ` of [Stacks, Tag 0EX3]. -/
def topDegreeSituation (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (V : S.Opens) [CompactSpace V]
    [QuasiSeparatedSpace V] : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u} where
  X := f ⁻¹ᵁ V
  Y := V
  f := f ∣_ V
  d := 1
  isCompact_X := QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  isQuasiSeparated_X := quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  isCompact_Y := inferInstance
  isQuasiSeparated_Y := inferInstance
  vanishes_above i hi F hF := by
    have : F.IsQuasicoherent := hF
    exact
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_higherDirectImage_of_one_lt_of_isProper
      (f ∣_ V) (topologicalKrullDim_fiber_le_one (f ∣_ V)
        (hf.of_isPullback (isPullback_morphismRestrict f V).flip)) F i hi
  X' := f ⁻¹ᵁ V
  Y' := V
  g' := 𝟙 _
  f' := f ∣_ V
  g := 𝟙 _
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **[Stacks, Tag 0GKA], part (b).** Let `f : X ⟶ S` be proper and at-worst-nodal of relative
dimension one, with geometrically connected fibres. Then `R¹f_*𝒪_X` is a finite locally free
`𝒪_S`-module, and its formation commutes with any base change: over every quasi-compact and
quasi-separated open `V ⊆ S` (for instance every affine open, or `S` itself when `S` is
quasi-compact and quasi-separated), for every cartesian square `X'' ⟶ f⁻¹(V)`, `X'' ⟶ Y''`,
`Y'' ⟶ V`, the canonical map `h^* R¹(f ∣_ V)_*𝒪 ⟶ R¹f''_* (h')^*𝒪` of [Stacks, Tag 0EX3] is an
isomorphism.

The base-change map of this library,
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMap`, is defined over a
quasi-compact quasi-separated base; commutation with base change is local on
the base, so asking it over every such open of `S` is the source's assertion. -/
@[stacks 0GKA "(b): `R¹f_*𝒪_X` is finite locally free, and its formation commutes with any base \
change, read over every quasi-compact quasi-separated open of the base, where the base-change map \
of Tag 0EX3 is defined"]
theorem isFiniteLocallyFree_rightDerived_one_and_isIso_baseChange (f : X ⟶ S) [IsProper f]
    [GeometricallyConnected f] (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (((Scheme.Modules.pushforward f).rightDerived 1).obj
          (SheafOfModules.unit X.ringCatSheaf)) ∧
      ∀ (V : S.Opens) [CompactSpace V] [QuasiSeparatedSpace V] {X'' Y'' : Scheme.{u}}
        (h' : X'' ⟶ f ⁻¹ᵁ V) (f'' : X'' ⟶ Y'') (h : Y'' ⟶ V)
        (sq : IsPullback h' f'' (f ∣_ V) h),
        IsIso (@Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMap _ _
          (topDegreeSituation f hf V) (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)
          (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _) h' f'' h
          (Stacks.AlgebraicGeometry.TopDegreeBaseChange.toShHom_comm_of_isPullback
            (S := topDegreeSituation f hf V) h' f'' h sq)) :=
  ⟨isFiniteLocallyFree_rightDerived_one f hf, fun V _ _ _ _ h' f'' h sq =>
    @Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap _ _
      (topDegreeSituation f hf V) (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _) h' f'' h sq⟩

/-- **[Stacks, Tag 0GKA], part (c).** Let `f : X ⟶ S` be proper and at-worst-nodal of relative
dimension one, with geometrically connected fibres. Then `Rᵠf_*𝒪_X = 0` for every `q ≥ 2`.

The fibres have dimension one, so this is [Stacks, Tag 0E7D] at `d = 1`. -/
@[stacks 0GKA "(c): `Rᵠf_*𝒪_X = 0` for `q ≥ 2`"]
theorem isZero_rightDerived_of_two_le (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard S.Modules
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).mpr
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_higherDirectImage_of_one_lt_of_isProper f
      (topologicalKrullDim_fiber_le_one f hf) _ (q : ℤ) (by omega))

end Stacks.AlgebraicGeometry.NodalFamilyCohomology

end
