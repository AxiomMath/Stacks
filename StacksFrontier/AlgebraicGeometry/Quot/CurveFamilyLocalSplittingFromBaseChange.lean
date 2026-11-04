module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardSplitting
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyDerivedFibreVanishing
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyLocalSplitting
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyFromInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.Homology.Perfect.SingleDegreeFibre
public import StacksFrontier.Homology.Perfect.MinimalComplexFreeCohomology
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Cotangent.KoszulRegularQuotient
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# The étale-local splitting `Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕ r}[-1]` from Stacks 0E6B (b) and 0CTM (1)

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z) for which the base change map of Stacks 0CTM,
part (1), at `𝒪_X` is an isomorphism for every morphism of families. Let `V = Spec A` be an
affine étale chart of `S` on which `(Rf_*𝒪_X)|_V ≅ 𝒪_V ⊕ P` with `P` strictly perfect in degrees
`≥ 1` (Stacks 0E6B, part (b)). Then every prime `𝔭` of `A` has a principal neighbourhood `D(a)`
on which `(Rf_*𝒪_X)|_{D(a)} ≅ 𝒪 ⊕ 𝒪^{⊕ r}[-1]`.

This is the sharpening of the source's proof of Stacks 0E1J: `P = M^~` for a bounded complex `M`
of finite projective `A`-modules in degrees `≥ 1`; its derived fibre at `𝔭` vanishes in degrees
`≤ 0` because `M` does, and in degrees `≥ 2` by base change to `Spec κ(𝔭)`
(`AlgebraicGeometry.CurveFamily.isZero_homology_derivedExtension_primeResidueMap_of_splitting`);
More on Algebra, Lemma 0BCD
    (`StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated`)
then makes `M ⊗_A A_a` a finite free module in degree `1`, and affine base change along
`D(a) ⟶ V` carries this back to the sheaves.

## Main results

* `StacksDraft.Perfect.exists_away_iso_singleFunctor_one_free_of_isStrictlyGE_one`: the algebra.
* `AlgebraicGeometry.CurveFamily.exists_notMem_iso_basicOpen_of_splitting`: the splitting on a
  principal neighbourhood.

## Implementation notes

No declaration here carries a `stacks` attribute: these are steps of the proof of Stacks 0E1J.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### The algebra -/

namespace StacksDraft.Perfect

/-- **A bounded complex of finite projective modules in degrees `≥ 1` whose derived fibre at
`𝔭` vanishes above degree one is, near `𝔭`, a finite free module in degree one.** The derived
fibre at `𝔭` is computed termwise, so it vanishes in degrees `≤ 0`; above degree one it is
given through any ring `A'` isomorphic to `κ(𝔭)` over `A`. Then 0BCD applies. -/
theorem exists_away_iso_singleFunctor_one_free_of_isStrictlyGE_one {A A' : Type u} [CommRing A]
    [CommRing A'] (p : Ideal A) [p.IsPrime] (N : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    [N.IsStrictlyGE 1] [N.IsStrictlyLE b] (hfin : ∀ j, Module.Finite A (N.X j))
    (hproj : ∀ j, Module.Projective A (N.X j)) (φ : A →+* A') (e : A' ≃+* p.ResidueField)
    (he : (e : A' →+* p.ResidueField).comp φ = algebraMap A p.ResidueField)
    (hvan :
      letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      letI := HasDerivedCategory.standard (ModuleCat.{u} A')
      ∀ j : ℤ, 2 ≤ j → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') j).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            φ).functor.obj
          (DerivedCategory.Q.obj N)))) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    ∃ f : A, f ∉ p ∧ ∃ r : ℕ,
      letI := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away f))
      Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A (Localization.Away f))).functor.obj (DerivedCategory.Q.obj N) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) 1).obj
          (ModuleCat.of (Localization.Away f) (ULift.{u} (Fin r → Localization.Away f)))) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (ModuleCat.{u} A')
  let := HasDerivedCategory.standard (ModuleCat.{u} p.ResidueField)
  have : ∀ j, Projective (N.X j) := fun j => (IsProjective.iff_projective (N.X j)).mp (hproj j)
  have hK : IsPerfect (DerivedCategory.Q.obj N) :=
    ⟨N, 1, b, inferInstance, inferInstance, hfin, hproj, ⟨Iso.refl _⟩⟩
  have hvan' : ∀ j : ℤ, j ≠ 1 →
      Module.finrank p.ResidueField (derivedFibreHomology.{u, u} p (DerivedCategory.Q.obj N) j) =
        0 := by
    intro j hj
    have hZ : IsZero (derivedFibreHomology.{u, u} p (DerivedCategory.Q.obj N) j) := by
      refine IsZero.of_iso ?_ (homologyTotalDerivedExtensionScalarsQIso (algebraMap A
          p.ResidueField)
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A p.ResidueField)) N b j)
      rcases le_or_gt j 0 with hj0 | hj0
      · exact ShortComplex.isZero_homology_of_isZero_X₂ _
          ((ModuleCat.extendScalars _).map_isZero (N.isZero_of_isStrictlyGE 1 j (by omega)))
      · have h2 : 2 ≤ j := by omega
        have h := isZero_homology_fibreComplex_comp_ringEquiv φ e N j
          ((hvan j h2).of_iso (homologyTotalDerivedExtensionScalarsQIso φ
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ)
              N b j).symm)
        rwa [he] at h
    have : Subsingleton (derivedFibreHomology.{u, u} p (DerivedCategory.Q.obj N) j) :=
      ModuleCat.isZero_iff_subsingleton.mp hZ
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨f, hf, ⟨iso⟩⟩ :=
    exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, u} p (DerivedCategory.Q.obj N) hK 1
      hvan'
  exact ⟨f, hf, _, ⟨iso⟩⟩

end StacksDraft.Perfect


namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] Space.etaleModulePullback_additive
  Space.preservesFiniteLimits_etaleModulePullback Space.preservesFiniteColimits_etaleModulePullback

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A strictly perfect complex on an affine represented space in degrees `≥ n` is `M^~` for a
bounded complex `M` of finite projective modules in degrees `≥ n`**: `M` is the complex of
sections. -/
theorem exists_isStrictlyGE_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) P) (n : ℤ) [hn : P.IsStrictlyGE n] :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    ∃ (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (b : ℤ),
      N.IsStrictlyGE n ∧ N.IsStrictlyLE b ∧
      (∀ j, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X j)) ∧
      (∀ j, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X j)) ∧
      Nonempty ((representedAffineDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N) ≅
        DerivedCategory.Q.obj P) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U))
  let adj₀ := representedAffineAssociatedAdjunction B S hS U
  let Φ₀ := representedAffineAssociated B S hS U
  let Γ₀ := representedAffineSections B S hS U
  have h := fun j => isIso_counit_app_and_finite_projective_of_isDirectSummandOfFiniteFree
    (P.X j) (hP.termDirectSummand j)
  let N := (Γ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let c : (Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun j => @asIso _ _ _ _ (adj₀.counit.app (P.X j)) (h j).1)
      (fun i j _ => (adj₀.counit.naturality (P.d i j)).symm)
  obtain ⟨-, b, -, hLE⟩ := exists_isStrictlyGE_isStrictlyLE_of_isStrictlyPerfect B S hS U P hP
  refine ⟨N, b, ?_, ?_, fun j => (h j).2.1, fun j => (h j).2.2,
    ⟨Φ₀.mapDerivedCategoryFactors.app N ≪≫ DerivedCategory.Q.mapIso c⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff N n).2 fun j hj =>
      Γ₀.map_isZero (P.isZero_of_isStrictlyGE n j hj)
  · exact (CochainComplex.isStrictlyLE_iff N b).2 fun j hj =>
      Γ₀.map_isZero (P.isZero_of_isStrictlyLE b j hj)

end Space

/-- **A finite free module over a localization stays finite free after an isomorphism of rings**:
`A' ⊗_{A_f} A_f^{⊕ r} ≅ A'^{⊕ r}`, as a coproduct of copies of `A'`. -/
def _root_.ModuleCat.extendScalarsULiftFunIsoSigma {R R' : Type u} [CommRing R] [CommRing R']
    (ψ : R →+* R') (r : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} ψ).obj (ModuleCat.of R (ULift.{u} (Fin r → R))) ≅
      ∐ (fun _ : ULift.{u} (Fin r) => ModuleCat.of R' R') :=
  letI := ψ.toAlgebra
  (((ULift.moduleEquiv (R := R) (M := Fin r → R)).baseChange R R' _ _).trans
      ((TensorProduct.piScalarRight R R' R' (Fin r)).trans
        ((LinearEquiv.funCongrLeft R' R' (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)).trans
          (DirectSum.linearEquivFunOnFintype R' (ULift.{u} (Fin r)) (fun _ =>
              R')).symm))).toModuleIso ≪≫
    (ModuleCat.coprodIsoDirectSum (fun _ : ULift.{u} (Fin r) => ModuleCat.of R' R')).symm

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **The splitting `Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕ r}[-1]` on a principal neighbourhood**, from the base
change clause of Stacks 0CTM, part (1), at `𝒪_X` and a splitting `(Rf_*𝒪_X)|_V ≅ 𝒪 ⊕ P` with `P`
strictly perfect in degrees `≥ 1` on an affine chart `V = Spec A` (Stacks 0E6B, part (b)): every
prime `𝔭` of `A` lies in a basic open `D(a)` on whose chart
`(Rf_*𝒪_X)|_{D(a)} ≅ 𝒪[0] ⊕ 𝒪^{⊕ I}[-1]` with `I` finite. -/
theorem exists_notMem_iso_basicOpen_of_splitting {X : CurveFamily B hZ}
    (hbc : X.HasDerivedStructureSheafBaseChange)
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1)
    [IsAffine (Space.chartScheme V)]
    (P : CochainComplex (Space.Modules.{u, u} B integerBase hZ
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2).O)) P)
    (hP1 : P.IsStrictlyGE 1)
    (e :
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
      (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
              0).obj (Space.structureSheafModule B integerBase hZ (schemeSpace X.base))) ⊞
          DerivedCategory.Q.obj P)
    (p : Ideal Γ(Space.chartScheme V, ⊤)) [p.IsPrime] :
    ∃ a : Γ(Space.chartScheme V, ⊤), a ∉ p ∧
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a))).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a))).2)
      ∃ I : Type u, Finite I ∧
        Nonempty ((Space.etaleModulePullback.{u, u} B integerBase hZ
            (Space.chartToSpace B integerBase hZ (schemeSpace X.base)
              (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a)))
            (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              (Space.openChart B integerBase hZ _ V
                ((Space.chartScheme V).basicOpen a)))).mapDerivedCategory.obj
            ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
              ((DerivedCategory.singleFunctor
                (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
                (Space.structureSheafModule B integerBase hZ X.total))) ≅
          (DerivedCategory.singleFunctor
            (Space.Modules.{u, u} B integerBase hZ
              (Space.chartSpace B integerBase hZ (schemeSpace X.base)
                (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a))).1
              (Space.chartSpace B integerBase hZ (schemeSpace X.base)
                (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a))).2)
                    0).obj
              (SheafOfModules.unit _) ⊞
            (DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ
                (Space.chartSpace B integerBase hZ (schemeSpace X.base)
                  (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a))).1
                (Space.chartSpace B integerBase hZ (schemeSpace X.base)
                  (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a))).2)
                      1).obj
              (SheafOfModules.free (R := Space.ringStructureSheaf B integerBase hZ
                (Space.chartSpace B integerBase hZ (schemeSpace X.base)
                  (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen a))).1)
                      I)) := by
  classical
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (X.total)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (X.total).1 (X.total).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ ((schemeSpace
        X.base))))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ ((schemeSpace X.base)).1 ((schemeSpace X.base)).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (Space.chartSpace B
        integerBase hZ (schemeSpace X.base) V)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (Space.chartSpace B integerBase hZ (schemeSpace X.base)
        V).1 (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (yoneda.obj (X.chartObject V))
      (isAlgebraicSpace_yoneda B integerBase hZ (X.chartObject V)))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (⟨yoneda.obj (X.chartObject V), isAlgebraicSpace_yoneda B integerBase hZ (X.chartObject V)⟩
          : AlgebraicSpaces B integerBase hZ)))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
      (X.chartObject V), ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
    (Space.primeResidueObject B integerBase hZ (X.chartObject V) p), ⊤))
  -- the complex of `A`-modules underlying `P`
  obtain ⟨N, b, hN1, hNb, hfin, hproj, ⟨eM⟩⟩ :=
    Space.exists_isStrictlyGE_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect B
      integerBase hZ (X.chartObject V) P hP 1 (hn := hP1)
  have := hN1
  have := hNb
  -- its derived fibres are concentrated in degree one, so it is free in degree one near `𝔭`
  have hvan := fun j hj => isZero_homology_derivedExtension_primeResidueMap_of_splitting hbc V P e
    (DerivedCategory.Q.obj N) eM p j hj
  obtain ⟨f, hf, r, ⟨iso₀⟩⟩ :=
      StacksDraft.Perfect.exists_away_iso_singleFunctor_one_free_of_isStrictlyGE_one
    p N b hfin hproj
    (Space.representedAffineCommRingCatHom B integerBase hZ
      (Space.primeResidueMap B integerBase hZ (X.chartObject V) p)).hom
    (Space.primeResidueRingEquiv B integerBase hZ (X.chartObject V) p)
    (Space.primeResidueRingEquiv_comp B integerBase hZ (X.chartObject V) p) hvan
  refine ⟨f, hf, ULift.{u} (Fin r), inferInstance, ⟨?_⟩⟩
  -- the basic-open chart
  have : IsAffine (Space.chartScheme (Space.openChart B integerBase hZ _ V ((Space.chartScheme
      V).basicOpen f))) :=
    Space.isAffine_chartScheme_openChart_basicOpen B integerBase hZ _ V inferInstance f
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (Space.chartSpace B
        integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ _ V
            ((Space.chartScheme V).basicOpen f)))))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (Space.chartSpace B integerBase hZ (schemeSpace X.base)
        (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).1
            (Space.chartSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase
                hZ _ V ((Space.chartScheme V).basicOpen f))).2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (yoneda.obj ((Space.SmallEtale.toOver B integerBase hZ
        (schemeSpace X.base).1).obj (Space.openChart B integerBase hZ _ V ((Space.chartScheme
            V).basicOpen f))))
      (isAlgebraicSpace_yoneda B integerBase hZ ((Space.SmallEtale.toOver B integerBase hZ
          (schemeSpace X.base).1).obj (Space.openChart B integerBase hZ _ V ((Space.chartScheme
              V).basicOpen f)))))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (⟨yoneda.obj ((Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).obj
          (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))),
              isAlgebraicSpace_yoneda B integerBase hZ ((Space.SmallEtale.toOver B integerBase hZ
                  (schemeSpace X.base).1).obj (Space.openChart B integerBase hZ _ V
                      ((Space.chartScheme V).basicOpen f)))⟩ : AlgebraicSpaces B integerBase hZ)))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
      ((Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).obj (Space.openChart B
          integerBase hZ _ V ((Space.chartScheme V).basicOpen f))), ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away f))
  let ι := Space.openChartInclusion B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)
  let g := (Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).map ι
  let := (Space.representedAffineCommRingCatHom B integerBase hZ g).hom.toAlgebra
  have : IsLocalization.Away f Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
      ((Space.chartScheme V).basicOpen f)), ⊤) :=
    Space.isLocalization_away_representedAffineRingHom_openChartInclusion B integerBase hZ
        V f
  let ψ := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
    Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen
        f)), ⊤)
  have hψ : (ψ : Localization.Away f →+* Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
      ((Space.chartScheme V).basicOpen f)), ⊤)).comp
      (algebraMap _ (Localization.Away f)) =
      (Space.representedAffineCommRingCatHom B integerBase hZ g).hom :=
    ψ.toAlgHom.comp_algebraMap
  have : Projective (ModuleCat.of (Localization.Away f) (ULift.{u} (Fin r → Localization.Away
      f))) :=
    (IsProjective.iff_projective _).mp inferInstance
  -- `M ⊗^L_A Γ(D(f))` is free in degree one
  let iso₁ : (Space.representedAffineDerivedExtension B integerBase hZ g).functor.obj
      (DerivedCategory.Q.obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Space.chartScheme (Space.openChart B
          integerBase hZ _ V ((Space.chartScheme V).basicOpen f)), ⊤)) 1).obj
        (∐ (fun _ : ULift.{u} (Fin r) => ModuleCat.of Γ(Space.chartScheme (Space.openChart B
            integerBase hZ _ V ((Space.chartScheme V).basicOpen f)), ⊤)
          Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V ((Space.chartScheme
              V).basicOpen f)), ⊤))) :=
    eqToIso (congrArg (fun φ =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        φ).functor.obj (DerivedCategory.Q.obj N)) hψ.symm) ≪≫
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (algebraMap _ (Localization.Away f))
        (ψ : Localization.Away f →+* Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
            ((Space.chartScheme V).basicOpen f)), ⊤))).app _).symm ≪≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (ψ : Localization.Away f →+* Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
            ((Space.chartScheme V).basicOpen f)), ⊤))).functor.mapIso iso₀ ≪≫
      CommAlgCat.totalDerivedExtensionScalarsSingleIsoOfProjective _
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (ψ : Localization.Away f →+* Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
              ((Space.chartScheme V).basicOpen f)), ⊤))) _ 1 ≪≫
      (DerivedCategory.singleFunctor _ 1).mapIso (ModuleCat.extendScalarsULiftFunIsoSigma _ r)
  let iso₂ := (Space.representedAffineDerivedAssociated B integerBase hZ ((Space.SmallEtale.toOver
      B integerBase hZ (schemeSpace X.base).1).obj (Space.openChart B integerBase hZ _ V
          ((Space.chartScheme V).basicOpen f)))).mapIso iso₁ ≪≫
    ((Space.representedAffineAssociated B integerBase hZ ((Space.SmallEtale.toOver B integerBase
        hZ (schemeSpace X.base).1).obj (Space.openChart B integerBase hZ _ V ((Space.chartScheme
            V).basicOpen f)))).mapDerivedCategorySingleFunctor 1).app _ ≪≫
    (DerivedCategory.singleFunctor _ 1).mapIso
      (Space.representedAffineAssociatedSigmaUnitIso (B := B) (S := integerBase) (hS := hZ)
        (U := ((Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).obj
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)))) r)
  -- restriction to `D(f)` is restriction to `V` followed by restriction along `D(f) ⟶ V`
  let Lι := Space.smallEtaleDerivedModulePullback B integerBase hZ
    (Space.chartMap B integerBase hZ (schemeSpace X.base) ι)
  let cres := fun E => ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ
          _ V ((Space.chartScheme V).basicOpen f)))
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B
          integerBase hZ _ V ((Space.chartScheme V).basicOpen f)))).app E).symm ≪≫
    (Space.smallEtaleDerivedModulePullbackCongr B integerBase hZ
      (Space.chartMap_comp_chartToSpace B integerBase hZ (schemeSpace X.base) ι).symm).app E ≪≫
    ((Space.smallEtaleDerivedModulePullbackCompIso B integerBase hZ
      (Space.chartMap B integerBase hZ (schemeSpace X.base) ι) (Space.chartToSpace B integerBase
          hZ (schemeSpace X.base) V)).app E).symm ≪≫
    Lι.mapIso ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V)).app E)
  let first := (cres _).symm ≪≫ ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ
          _ V ((Space.chartScheme V).basicOpen f)))
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B
          integerBase hZ _ V ((Space.chartScheme V).basicOpen f)))).app _).symm ≪≫
    Space.smallEtaleDerivedModulePullbackUnitIso (B := B) (S := integerBase) (hS := hZ)
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ
          _ V ((Space.chartScheme V).basicOpen f)))
  let second := Lι.mapIso eM.symm ≪≫
    (Space.representedAffineDerivedBaseChangeIso B integerBase hZ g).app _ ≪≫ iso₂
  let eι := Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
    (Space.chartMap B integerBase hZ (schemeSpace X.base) ι)
    (Space.isEtale_chartMap B integerBase hZ (schemeSpace X.base) ι)
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (Space.etaleModulePullback.{u, u} B integerBase hZ
      (Space.chartMap B integerBase hZ (schemeSpace X.base) ι)
      (Space.isEtale_chartMap B integerBase hZ (schemeSpace X.base) ι)).mapDerivedCategory
  exact cres _ ≪≫ Lι.mapIso e ≪≫ eι.app _ ≪≫
    (Space.etaleModulePullback.{u, u} B integerBase hZ
      (Space.chartMap B integerBase hZ (schemeSpace X.base) ι)
      (Space.isEtale_chartMap B integerBase hZ (schemeSpace X.base)
          ι)).mapDerivedCategory.mapBiprod _ _ ≪≫
    biprod.mapIso ((eι.app _).symm ≪≫ first) ((eι.app _).symm ≪≫ second)


/-- **An affine strictly perfect splitting `Rf_*𝒪_X ≅ 𝒪 ⊕ P`**, for a family of curves
`f : X → S`: a family of étale charts `V_k` of `S` with affine schemes, covering `S`, on each of
which `(Rf_*𝒪_X)|_{V_k} ≅ 𝒪|_{V_k} ⊕ P_k` with `P_k` a strictly perfect complex in degrees `≥ 1`.
This is Stacks 0E6B, part (b), for `f`, in the form its proof produces (the strictly perfect
models of the summand live on basic opens of affine charts). -/
def HasAffineStrictlyPerfectLocalSplitting (X : CurveFamily B hZ) : Prop :=
  ∃ (κ : Type (u + 1)) (V : κ → Space.SmallEtale B integerBase hZ (schemeSpace X.base).1),
  (Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).CoversTop V ∧
  ∀ k : κ, IsAffine (Space.chartScheme (V k)) ∧
  ∃ P : CochainComplex (Space.Modules.{u, u} B integerBase hZ
    (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
    (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2) ℤ,
    IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2).O)) P ∧
    P.IsStrictlyGE 1 ∧
    letI := HasDerivedCategory.standard
      (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    letI := HasDerivedCategory.standard
      (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
    letI := HasDerivedCategory.standard
      (Space.Modules.{u, u} B integerBase hZ
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2)
    Nonempty ((Space.etaleModulePullback.{u, u} B integerBase hZ
        (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
        (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
          (V k))).mapDerivedCategory.obj
        ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
          ((DerivedCategory.singleFunctor
            (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
            (Space.structureSheafModule B integerBase hZ X.total))) ≅
      (Space.etaleModulePullback.{u, u} B integerBase hZ
        (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
        (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
          (V k))).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor
          (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1
            (schemeSpace X.base).2) 0).obj
          (Space.structureSheafModule B integerBase hZ (schemeSpace X.base))) ⊞
        DerivedCategory.Q.obj P)

/-- **The étale-local splitting `Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕ r}[-1]` of a family of curves from Stacks 0CTM,
part (1), and Stacks 0E6B, part (b).** If the base change map of Stacks 0CTM, part (1), at `𝒪_X`
is an isomorphism for every morphism of families into `X`, and the base is covered by affine
étale charts `V_k` on which `(Rf_*𝒪_X)|_{V_k} ≅ 𝒪|_{V_k} ⊕ P_k` with `P_k` strictly perfect in
degrees `≥ 1` (Stacks 0E6B, part (b), in the form of its proof), then `X` has an étale-local
splitting `Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕ I}[-1]` with `I` finite: the basic opens of the `V_k` given by
`exists_notMem_iso_basicOpen_of_splitting` at the points of the `V_k` cover the base. -/
theorem hasLocalDerivedPushforwardSplitting_of_baseChange_of_affineSplitting
    {X : CurveFamily B hZ} (hbc : X.HasDerivedStructureSheafBaseChange)
    (hsplit : X.HasAffineStrictlyPerfectLocalSplitting) :
    X.HasLocalDerivedPushforwardSplitting := by
  obtain ⟨κ, V, hV, hk⟩ := hsplit
  choose hAff P hP hP1 he using hk
  have hloc := fun (k : κ) (x : Space.chartScheme (V k)) =>
    haveI := hAff k
    exists_notMem_iso_basicOpen_of_splitting hbc (V k) (P k) (hP k) (hP1 k) (he k).some
      ((Space.chartScheme (V k)).toSpecΓ x).asIdeal
  choose a ha hiso using hloc
  have hxa : ∀ (k : κ) (x : Space.chartScheme (V k)),
      x ∈ (Space.chartScheme (V k)).basicOpen (a k x) := fun k x => by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact ha k x
  let W : (Σ k : κ, Space.chartScheme (V k)) → Space.SmallEtale B integerBase hZ (schemeSpace
      X.base).1 :=
    fun kx => Space.openChart B integerBase hZ _ (V kx.1)
      ((Space.chartScheme (V kx.1)).basicOpen (a kx.1 kx.2))
  refine ⟨Σ k : κ, Space.chartScheme (V k), W, ?_, fun kx => hiso kx.1 kx.2⟩
  -- the basic opens of the charts cover the charts, and the charts cover the base
  intro T
  refine (Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).transitive (hV T) _ ?_
  intro T' f hf
  obtain ⟨k, ⟨g⟩⟩ := hf
  have hcov : Sieve.ofArrows (fun x : Space.chartScheme (V k) => W ⟨k, x⟩)
      (fun x => Space.openChartInclusion B integerBase hZ _ (V k)
        ((Space.chartScheme (V k)).basicOpen (a k x))) ∈
      Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1 (V k) := by
    refine Space.SmallEtale.ofArrows_mem_topology B integerBase hZ _ _ _ ?_
    rw [ofArrows_mem_etalePrecoverage_iff]
    refine ⟨fun x => ⟨x, ?_⟩, fun x => ?_⟩
    · rw [Space.toScheme_map_toOver_map_openChartInclusion]
      exact ⟨⟨x, hxa k x⟩, rfl⟩
    · rw [Space.toScheme_map_toOver_map_openChartInclusion]
      exact (inferInstance : Etale ((Space.chartScheme (V k)).basicOpen (a k x)).ι)
  refine (Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).superset_covering ?_
    ((Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).pullback_stable g hcov)
  intro T'' h hh
  obtain ⟨_, h', _, ⟨x⟩, -⟩ := hh
  exact ⟨⟨k, x⟩, ⟨h'⟩⟩

/-- **Parts (2) and (3) of Stacks 0E1J from Stacks 0CTM, part (1), and Stacks 0E6B, part (b)**,
in the form of the hypotheses `h2` and `h3` of the consumers of Stacks 0E1J: if every family in
`Curves^{h0,1}` satisfies the base change clause of Stacks 0CTM, part (1), at `𝒪_X` and has an
affine strictly perfect splitting `Rf_*𝒪_X ≅ 𝒪 ⊕ P` (Stacks 0E6B, part (b)), then for every such
family `R¹f_*𝒪_X` is finite locally free and its formation commutes with arbitrary base change.
The sharpening of the splitting to `𝒪 ⊕ 𝒪^{⊕ r}[-1]` is
`hasLocalDerivedPushforwardSplitting_of_baseChange_of_affineSplitting`. -/
theorem firstHigherDirectImage_of_baseChange_of_affineSplitting
    (hbc : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasDerivedStructureSheafBaseChange)
    (hsplit : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasAffineStrictlyPerfectLocalSplitting) :
    (∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage) ∧
    (∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :=
  firstHigherDirectImage_of_inputs
    (fun X hX => hasLocalDerivedPushforwardSplitting_of_baseChange_of_affineSplitting (hbc X hX)
      (hsplit X hX)) hbc

end CurveFamily

end AlgebraicGeometry

end
