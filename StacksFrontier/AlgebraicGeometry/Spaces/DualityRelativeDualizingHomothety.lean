module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPushforwardTraceCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRelativeDualizingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualExactPairing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedHomothety
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomDinaturality
public import StacksFrontier.CategoryTheory.Adjunction.InternalHomTraceHomothety
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Braiding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatGeneral
public import StacksFrontier.CategoryTheory.Adjunction.TransportAdjunctionDinaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomDinaturality

/-!
# The homothety map of `a(𝒪_Y)` and its transpose

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of quasi-compact and
quasi-separated algebraic spaces and `ω = a(𝒪_Y)` for the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55). The proof of Stacks 0E5V (3) identifies, for
every perfect `E`, `Hom(E, R𝓗om(ω, ω))` with `Hom(E, 𝒪_X)` through the chain of bijections

`Hom(E, R𝓗om(ω, ω)) = Hom(E ⊗ ω, ω) = Hom(Rf_*(E ⊗ ω), 𝒪_Y) = Hom(Rf_*R𝓗om(E^∨, ω), 𝒪_Y)`
`= Hom(R𝓗om(Rf_*E^∨, 𝒪_Y), 𝒪_Y) = Hom(𝒪_Y, Rf_*E^∨) = Hom(E, 𝒪_X)`,

carried out abstractly in `StacksFrontier/CategoryTheory/Adjunction/InternalHomTraceHomothety.lean`.
This file provides the space-level inputs that are not yet in the library: the braiding of
`D(𝒪_X)`, and the invertibility of the transpose `𝒪_X ⊗^L K ⟶ K` of the homothety map
`𝒪_X ⟶ R𝓗om(K, K)`, which lets the abstract chain be read at the homothety map itself.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedBraided`: the braiding of `D(𝒪_X)` (Stacks 0FPT).

## Main results

* `AlgebraicGeometry.Space.isIso_homEquiv_symm_smallEtaleDerivedHomothety`: the transpose of the
  homothety map is invertible.
* `AlgebraicGeometry.Space.bijective_comp_smallEtaleDerivedHomothety_rightAdjoint`,
  `AlgebraicGeometry.Space.bijective_comp_smallEtaleDerivedHomothety_affineRightAdjoint`: for
  every perfect `E`, `φ ↦ φ ≫ h` is a bijection `Hom(E, 𝒪_X) ⟶ Hom(E, R𝓗om(ω, ω))`.

## References

* [Stacks Project, Tag 0E5V](https://stacks.math.columbia.edu/tag/0E5V)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The braiding of `D(𝒪_X)`** (Stacks 0FPT): the Koszul symmetry of the derived monoidal
structure re-seated onto the derived tensor product of `X`. -/
@[instance_reducible]
def smallEtaleDerivedBraided (X : AlgebraicSpaces B S hS) :
    @BraidedCategory (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) _
      (smallEtaleDerivedMonoidal X) :=
  @reseatBraided _ _
    (Stacks.SheafOfModules.DerivedMonoidalGeneral.derivedMonoidal
      (smallEtaleRingedSite B S hS X.1 X.2).O) _ _
    (Stacks.SheafOfModules.DerivedMonoidalGeneral.derivedSymmetric
      (smallEtaleRingedSite B S hS X.1 X.2).O).toBraidedCategory
    (smallEtaleDerivedTensorProduct B S hS X).monoidalTensorIso
    (Stacks.SheafOfModules.DerivedMonoidalGeneral.canonicalUnitIso
      (smallEtaleRingedSite B S hS X.1 X.2).O)

section Generic

variable {C D : Type*} [Category C] [Category D]

omit hS in
/-- For an equivalence `e`, `e(η_a ≫ e⁻¹ x) ≫ ε_b = x`. -/
lemma functor_map_unitIso_comp_inverse_map_comp_counit (e : C ≌ D) {a : C} {b : D}
    (x : e.functor.obj a ⟶ b) :
    e.functor.map (e.unitIso.hom.app a ≫ e.inverse.map x) ≫ e.counit.app b = x := by
  simp

omit hS in
/-- **A transpose under a transported tensor–Hom adjunction is invertible** as soon as the
transpose, under the adjunction of `D`, of `e g` followed by the counit of `e` is. -/
lemma isIso_transportAdjunction_homEquiv_symm (e : C ≌ D) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (μ : Functor.uncurry.obj TC ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj TD)
    (HD : Dᵒᵖ ⥤ D ⥤ D) (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P)) (M : C)
    (ρ : TC.flip.obj M ≅ e.functor ⋙ TD.flip.obj (e.functor.obj M) ⋙ e.inverse)
    (hρ : ∀ A : C, ρ.hom.app A = e.unit.app ((TC.obj A).obj M) ≫ e.inverse.map (μ.hom.app (A, M)))
    (adjC : TC.flip.obj M ⊣ (e.functor.op ⋙ HD ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
      (Functor.whiskeringRight _ _ _).obj e.inverse).obj (op M))
    (hadj : adjC =
      ((e.toAdjunction.comp (adjD (e.functor.obj M))).comp e.symm.toAdjunction).ofNatIsoLeft ρ.symm)
    (A Z : C) (g : A ⟶ e.inverse.obj ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj Z)))
    (hg : IsIso (((adjD (e.functor.obj M)).homEquiv (e.functor.obj A) (e.functor.obj Z)).symm
      (e.functor.map g ≫ e.counit.app ((HD.obj (op (e.functor.obj M))).obj (e.functor.obj Z))))) :
    IsIso ((adjC.homEquiv A Z).symm g) := by
  subst hadj
  rw [CategoryTheory.PullbackInternalHom.transportAdjunction_homEquiv_symm e TC TD μ HD adjD M ρ
    hρ A Z g]
  infer_instance

omit hS in
/-- If `w` is invertible and `h` has invertible transpose, the transpose of
`e(η_a ≫ e⁻¹(w ≫ h)) ≫ ε` is invertible. -/
lemma isIso_homEquiv_symm_functor_map_comp_counit (e : C ≌ D) {TD : D ⥤ D ⥤ D}
    {HD : Dᵒᵖ ⥤ D ⥤ D} (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P)) (Q : D) {a : C} {U b : D}
    (w : e.functor.obj a ≅ U) (h : U ⟶ (HD.obj (op Q)).obj b)
    (hh : IsIso (((adjD Q).homEquiv U b).symm h)) :
    IsIso (((adjD Q).homEquiv (e.functor.obj a) b).symm
      (e.functor.map (e.unitIso.hom.app a ≫ e.inverse.map (w.hom ≫ h)) ≫ e.counit.app _)) := by
  rw [functor_map_unitIso_comp_inverse_map_comp_counit, Adjunction.homEquiv_naturality_left_symm]
  infer_instance

end Generic

/-- **The transpose of the homothety map of `K` is invertible**: under `- ⊗^L K ⊣ R𝓗om(K, -)`
the homothety `𝒪_X ⟶ R𝓗om(K, K)` corresponds to an isomorphism `𝒪_X ⊗^L K ≅ K`, the left unit
constraint of the equi-universe model read through the derived equivalence. -/
theorem isIso_homEquiv_symm_smallEtaleDerivedHomothety (X : AlgebraicSpaces B S hS)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (((smallEtaleDerivedTensorSheafHomAdjunction B S hS X K).homEquiv _ K).symm
      (smallEtaleDerivedHomothety B S hS X K)) := by
  refine isIso_transportAdjunction_homEquiv_symm (smallEtaleModelDerivedEquivalence B S hS X)
    (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedTensorIso B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2)) K
    (smallEtaleDerivedTensorRightIso B S hS X K) (smallEtaleDerivedTensorRightIso_hom_app X K)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X K)
    (smallEtaleDerivedTensorSheafHomAdjunction_eq X K) _ K
    (smallEtaleDerivedHomothety B S hS X K) ?_
  have hM : IsIso (((RingedSite.derivedTensorSheafHomAdjunction
      (smallEtaleModelRingedSite B S hS X.1 X.2)
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K)).homEquiv _ _).symm
        (RingedSite.derivedHomothety (smallEtaleModelRingedSite B S hS X.1 X.2)
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K))) := by
    rw [RingedSite.derivedTensorSheafHomAdjunction_homEquiv_symm_apply,
      RingedSite.derivedCurryHomEquiv_derivedHomothety]
    infer_instance
  exact isIso_homEquiv_symm_functor_map_comp_counit (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2)) _
    (((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategorySingleFunctor
      0).app (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) _ hM

variable (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Postcomposition with the homothety of `a(𝒪_Y)` is bijective on morphisms out of a perfect
object** (the chain of bijections of the proof of Stacks 0E5V (3)). Let `f : X ⟶ Y` be proper,
flat and of finite presentation, with `X` and `Y` quasi-compact and quasi-separated, and let
`ω = a(𝒪_Y)`. For every perfect `E` in `D(𝒪_X)`, `φ ↦ φ ≫ h` is a bijection
`Hom(E, 𝒪_X) ⟶ Hom(E, R𝓗om(ω, ω))`, for the homothety map `h : 𝒪_X ⟶ R𝓗om(ω, ω)`. -/
theorem bijective_comp_smallEtaleDerivedHomothety_rightAdjoint
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    Function.Bijective fun φ : E ⟶ (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) =>
      φ ≫ smallEtaleDerivedHomothety B S hS X ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs
          hYqs).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj := by
  let : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS X))) := smallEtaleDerivedMonoidal X
  let : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y))) := smallEtaleDerivedMonoidal Y
  let : BraidedCategory (DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS X))) := smallEtaleDerivedBraided X
  set a := quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs hfp.2.1 hfp.2.2
  set ω := ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
    (derivedStructureSheaf B S hS Y.1 Y.2)).obj with hω
  have hN : ∀ (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
      (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E),
      Function.Bijective (InternalHomTrace.dualityChainMap
        (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedPullbackTensorIso f).hom
        (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS Y)
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y)
        (smallEtaleDerivedModulePullbackUnitIso f).hom
        (a.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)).hom E) :=
    fun E hE => by
      have hD := isPerfect_smallEtaleDerivedDual B S hS X E hE
      have hfD := (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp
        _ hD).1
      exact InternalHomTrace.bijective_dualityChainMap _ _ _ _ _ _ _ _
        (Iso.isIso_hom (smallEtaleDerivedModulePullbackUnitIso f)) E
        (isIso_smallEtaleLeftTensorHomDiagonal_of_isPerfect X E E _ hE)
        (isIso_smallEtalePushforwardTrace_of_isPerfect hZ f hXqc hXqs hYqs
          (quasicoherentDerivedDual X ⟨E, derivedCategoryB_of_isPerfect B S hS X E hE⟩ hE)
          (derivedStructureSheaf B S hS Y.1 Y.2) hYqc hD hfD)
        (isIso_smallEtaleLeftTensorHomDiagonal_of_isPerfect Y _ _ _ hfD)
  have hε : ∀ (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
      (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E),
      Function.Bijective fun v : E ⊗ ω ⟶ ω => (derivedModulePushforward B S hS f).map v ≫
        (a.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)).hom := fun E hE => by
    let Z : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
      ⟨_, qcohDerived_smallEtaleDerivedTensor X _ _ (derivedCategoryB_of_isPerfect B S hS X E hE)
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
          (derivedStructureSheaf B S hS Y.1 Y.2)).property⟩
    have key : (fun v : Z.obj ⟶ ω => (derivedModulePushforward B S hS f).map v ≫
          (a.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)).hom) =
        (fun w => w.hom) ∘ (a.homEquiv Z (derivedStructureSheaf B S hS Y.1 Y.2)).symm ∘
          ((ObjectProperty.fullyFaithfulι (QcohDerived B S hS X)).homEquiv (X := Z)
            (Y := (quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj (derivedStructureSheaf
                B S hS Y.1 Y.2))).symm := by
      funext v
      simp only [Function.comp_apply, Adjunction.homEquiv_counit]
      rfl
    change Function.Bijective (fun v : Z.obj ⟶ ω => (derivedModulePushforward B S hS f).map v ≫
      (a.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)).hom)
    rw [key]
    exact (ObjectProperty.fullyFaithfulι (QcohDerived B S hS Y)).homEquiv.bijective.comp
      ((a.homEquiv Z (derivedStructureSheaf B S hS Y.1 Y.2)).symm.bijective.comp
        (ObjectProperty.fullyFaithfulι (QcohDerived B S hS X)).homEquiv.symm.bijective)
  have hO : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
      (𝟙_ (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))) :=
    isPerfect_unit X
  exact InternalHomTrace.bijective_comp_of_isIso_homEquiv_symm
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedPullbackTensorIso f).hom
    (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS Y)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y)
    (smallEtaleDerivedModulePullbackUnitIso f).hom
    (a.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)).hom
    (fun {_ _} u {_ _} θ =>
      smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural B S hS X _ _ u θ)
    (fun {_ _} u {_ _} θ =>
      smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural B S hS Y _ _ u θ)
    (ω := ω) (isIso_homEquiv_symm_smallEtaleDerivedHomothety X ω) E (hN E hE) (hN _ hO)
    (hε E hE) (hε _ hO)

/-- **Postcomposition with the homothety of `a(𝒪_Y)` is bijective on morphisms out of a perfect
object, over an affine base** (the chain of bijections of the proof of Stacks 0E5V (3)). Let `Y`
be affine and `f : X ⟶ Y` proper, flat and of finite presentation, and `ω = a(𝒪_Y)`. For every
perfect `E` in `D(𝒪_X)`, `φ ↦ φ ≫ h` is a bijection `Hom(E, 𝒪_X) ⟶ Hom(E, R𝓗om(ω, ω))`, for
the homothety map `h : 𝒪_X ⟶ R𝓗om(ω, ω)`. -/
theorem bijective_comp_smallEtaleDerivedHomothety_affineRightAdjoint (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    Function.Bijective fun φ : E ⟶ (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) =>
      φ ≫ smallEtaleDerivedHomothety B S hS X
        ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj :=
  bijective_comp_smallEtaleDerivedHomothety_rightAdjoint hZ f
    (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY.isQuasiCompactSpace hf hfl hfp
    E hE

end AlgebraicGeometry.Space

end
