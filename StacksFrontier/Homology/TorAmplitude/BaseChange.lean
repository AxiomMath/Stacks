module

public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude and derived base change

Let `A → B` be a map of commutative rings. Derived extension of scalars along it preserves a
Tor-amplitude bound: if `K` is an object of `D(A)` with Tor amplitude in `[a, b]`, then
`K ⊗_A^L B` has Tor amplitude in `[a, b]` as an object of `D(B)`. This is Stacks 066L.

The derived tensor products on `D(A)` and `D(B)` and the derived extension of scalars
`D(A) ⥤ D(B)` are universally quantified certified data, as in
`StacksFrontier.Homology.TorAmplitude.Defs` (Stacks 0652).

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitude_derivedExtendScalars`: Stacks 066L.

## References

* [Stacks Project, Tag 066L](https://stacks.math.columbia.edu/tag/066L)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.MonoidalCategory HomologicalComplex

namespace StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-! ### Generic left derived functors of termwise functors -/

section Generic

section Acyclic

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- An additive functor turns a bounded above acyclic complex of projective objects into an
acyclic complex. -/
private lemma acyclic_mapHomologicalComplex_of_projective (a : ℤ) (L : CochainComplex C ℤ)
    (hLE : L.IsStrictlyLE a) (hproj : ∀ n : ℤ, Projective (L.X n)) (hac : L.Acyclic) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := by
  have := hLE
  have := hproj
  have : L.IsKProjective := CochainComplex.isKProjective_of_projective L a
  have hz : IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) := by
    rw [IsZero.iff_id_eq_zero]
    exact CochainComplex.IsKProjective.leftOrthogonal L (𝟙 _)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hac)
  have hz2 := (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_isZero hz
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic D).prop_of_isZero hz2

end Acyclic

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

variable (F : C ⥤ D) [F.Additive]

/-- `F` read on the homotopy category and followed by the localization to the derived
category. -/
private noncomputable abbrev mapHomotopyDerived :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory D :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

variable [(mapHomotopyDerived F).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- The total left derived functor of `F` on the derived category. -/
private noncomputable def mapDerived : DerivedCategory C ⥤ DerivedCategory D :=
  (mapHomotopyDerived F).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- Its counit, on the homotopy category. -/
private noncomputable def mapDerivedCounitHomotopy :
    DerivedCategory.Qh ⋙ mapDerived F ⟶ mapHomotopyDerived F :=
  (mapHomotopyDerived F).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

private instance isLeftDerivedFunctor_mapDerivedCounitHomotopy :
    (mapDerived F).IsLeftDerivedFunctor (mapDerivedCounitHomotopy F)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [mapDerived, mapDerivedCounitHomotopy]
  infer_instance

/-- `F` read on the homotopy category, precomposed with the homotopy quotient, is `F` applied
termwise followed by the localization. -/
private noncomputable def quotientCompMapHomotopyDerivedIso :
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ mapHomotopyDerived F ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso D)

/-- The counit of `mapDerived F`, on complexes. -/
private noncomputable def mapDerivedCounit :
    DerivedCategory.Q ⋙ mapDerived F ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso C).inv (mapDerived F) ≫
    whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (mapDerivedCounitHomotopy F) ≫ (quotientCompMapHomotopyDerivedIso F).hom

private instance isLeftDerivedFunctor_mapDerivedCounit :
    (mapDerived F).IsLeftDerivedFunctor (mapDerivedCounit F)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_of_homotopyCategory _ (mapHomotopyDerived F)
    (quotientCompMapHomotopyDerivedIso F) (mapDerived F) (mapDerivedCounitHomotopy F)
    (mapDerivedCounit F) (by
      ext X
      dsimp only [mapDerivedCounit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
      rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      simp)

/-- The counit of the total left derived functor of `F` is invertible at a K-projective complex. -/
private lemma isIso_mapDerivedCounitHomotopy_app (P : CochainComplex C ℤ) [P.IsKProjective] :
    IsIso ((mapDerivedCounitHomotopy F).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) := by
  have hptw : (RightExtension.mk (mapDerived F)
      (mapDerivedCounitHomotopy F)).IsPointwiseRightKanExtension :=
    Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
      (mapDerived F) (mapDerivedCounitHomotopy F)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  have hat := hptw (DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P))
  have h := hat.isIso_π_app_of_isInitial _ (isInitialStructuredArrowMkId P)
  simpa using h

/-- The same statement on complexes. -/
private lemma isIso_mapDerivedCounit_app (P : CochainComplex C ℤ) [P.IsKProjective] :
    IsIso ((mapDerivedCounit F).app P) := by
  have := isIso_mapDerivedCounitHomotopy_app F P
  dsimp only [mapDerivedCounit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  infer_instance

/-- **The K-projective comparison.** For an additive functor `F` whose left derived functor
along `Qh` exists pointwise, the counit of *any* total left derived functor of `F` applied
termwise is invertible at a K-projective complex. -/
private lemma isIso_counit_app_of_isKProjective
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : DerivedCategory.Q ⋙ G ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))]
    (P : CochainComplex C ℤ) [P.IsKProjective] :
    IsIso (β.app P) := by
  have hβ : IsIso ((mapDerivedCounit F).app P) := isIso_mapDerivedCounit_app F P
  set τ := Functor.leftDerivedNatTrans (mapDerived F) G (mapDerivedCounit F) β
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (𝟙 _) with hτ
  have hiso : IsIso (τ.app (DerivedCategory.Q.obj P)) := by
    have h : IsIso ((Functor.leftDerivedNatIso (mapDerived F) G
        (mapDerivedCounit F) β
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
        (Iso.refl _)).hom.app (DerivedCategory.Q.obj P)) := inferInstance
    simpa using h
  have hkey : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ β.app P) := by
    rw [hτ, Functor.leftDerivedNatTrans_app]
    simpa using hβ
  exact IsIso.of_isIso_comp_left (τ.app (DerivedCategory.Q.obj P)) (β.app P)

end Generic

universe u

/-! ### A Tor-amplitude bound bounds the cohomology -/

section Unitor

variable {R : Type u} [CommRing R]

/-- Tensoring on the right by the ring itself is the identity functor of `ModuleCat R`: the
monoidal right unitor. -/
private noncomputable def tensorModuleRightUnitIso (R : Type u) [CommRing R] :
    tensorModuleRight (ModuleCat.of R R) ≅ 𝟭 (ModuleCat.{u} R) :=
  MonoidalCategory.rightUnitorNatIso (ModuleCat.{u} R)

/-- Termwise tensoring by the ring itself, followed by the localization, is the localization. -/
private noncomputable def unitTensorComplexIso (R : Type u) [CommRing R] :
    (tensorModuleRight (ModuleCat.of R R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q (C := ModuleCat.{u} R) :=
  Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (tensorModuleRightUnitIso R)
      (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ DerivedCategory.Q.leftUnitor

variable
  {derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)}
  {comparison : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q}

/-- The certificate of a derived tensor product, evaluated at the ring itself, identifies
`- ⊗^L R[0]` with the identity functor of `D(R)`. -/
private noncomputable def derivedTensorUnitIso
    (isLeftDerived : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))) :
    derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R)) :=
  letI := isLeftDerived (ModuleCat.of R R)
  letI e : DerivedCategory.Q (C := ModuleCat.{u} R) ⋙ 𝟭 _ ≅
      (tensorModuleRight (ModuleCat.of R R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
    DerivedCategory.Q.rightUnitor ≪≫ (unitTensorComplexIso R).symm
  letI := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (𝟭 _) e
  Functor.leftDerivedNatIso _ (𝟭 _) (comparison (ModuleCat.of R R)) e.hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (Iso.refl _)

/-- An object of `D(R)` with Tor amplitude in `[a, b]` has vanishing cohomology outside
`[a, b]`. -/
private lemma isZero_homology_of_hasTorAmplitude
    (isLeftDerived : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hK : HasTorAmplitude derivedTensor comparison isLeftDerived K a b) (i : ℤ)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
  (hK (ModuleCat.of R R) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((derivedTensorUnitIso isLeftDerived).app K).symm)

end Unitor

/-! ### Representing a cohomologically bounded above object by a K-projective complex -/

/-- An object of `D(R)` whose cohomology vanishes in degrees `> b` is the image of a bounded
above complex of projective modules. -/
private lemma exists_projective_representative {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (b : ℤ)
    (hK : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ), P.IsStrictlyLE m ∧
      (∀ i : ℤ, Projective (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  set E := DerivedCategory.Q.objPreimage K with hE
  have eE : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hLE : E.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hK i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app E).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso eE)
  have := hLE
  obtain ⟨P, m, π, hPLE, hPproj, hπ⟩ := exists_projective_resolution (E.truncLE b) b
  have := hπ
  refine ⟨P, m, hPLE, hPproj, ⟨?_⟩⟩
  exact asIso (DerivedCategory.Q.map π) ≪≫ asIso (DerivedCategory.Q.map (E.ιTruncLE b)) ≪≫ eE

/-! ### Extension of scalars -/

section ExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Extension of scalars is a left adjoint. -/
private instance extendScalars_isLeftAdjoint (f : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint

set_option maxHeartbeats 2000000 in
-- Instance search for `Projective (X ⊞ Y)` unfolds the `ModuleCat` biproduct, which is slow.

/-- Stacks 0794 applies to extension of scalars: its left derived functor along
`Qh : K(A) ⥤ D(A)` is defined at every object. -/
private instance hasPointwiseLeftDerivedFunctor_extendScalars (f : A →+* B) :
    (mapHomotopyDerived (ModuleCat.extendScalars.{u, u, u} f)).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
  CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    _ (projectiveObjects A) projectiveObjects_biprod projectiveObjects_cover
    (fun a L hLE hP hac =>
      acyclic_mapHomologicalComplex_of_projective (ModuleCat.extendScalars.{u, u, u} f) a L
        hLE hP hac)

variable [Algebra A B]

/-- Extension of scalars carries a flat module to a flat module over the target ring. -/
@[ega "0 6.2.1"]
private lemma flat_extendScalars (N : ModuleCat.{u} A) (hN : Module.Flat A (N : Type u)) :
    Module.Flat B (((ModuleCat.extendScalars (algebraMap A B)).obj N : ModuleCat.{u} B) :
      Type u) := by
  have := hN
  have : Module.Flat B (TensorProduct A B (N : Type u)) := Module.Flat.baseChange A B (N : Type u)
  exact Module.Flat.of_linearEquiv
    (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A B N)

/-- Termwise tensoring is tensoring by the module placed in cohomological degree zero, after
the braiding. -/
private noncomputable def tensorModuleRightSingleIso {S : Type u} [CommRing S]
    (N : ModuleCat.{u} S) (Z : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ≅
      (tensorLeft ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N)).obj Z :=
  (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight N)
      (ComplexShape.up ℤ)).symm.app Z ≪≫
    (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso N Z).symm

/-- **The projection formula.** The termwise tensor product over `B` of the base change of `P`
with a `B`-module `M`, restricted to `A`, is the termwise tensor product over `A` of `P` with
`M`. -/
private noncomputable def restrictTensorExtendIso (M : ModuleCat.{u} B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≅
      (((tensorModuleRight
        ((ModuleCat.restrictScalars (algebraMap A B)).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (tensorModuleRightSingleIso M _) ≪≫
    StacksDraft.TorAmplitude.FaithfullyFlat.restrictTensorLeftExtendIso A B
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj M) P ≪≫
    ((tensoringLeft (CochainComplex (ModuleCat.{u} A) ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars (algebraMap A B)) (ComplexShape.up ℤ) 0).app M)).app P ≪≫
    (tensorModuleRightSingleIso ((ModuleCat.restrictScalars (algebraMap A B)).obj M) P).symm

/-- The termwise tensor product over `A` detects the termwise tensor product over `B` of the base
change: a vanishing cohomology module of the former forces the vanishing of the corresponding
one of the latter. -/
private lemma isZero_homology_tensor_extendScalars (M : ModuleCat.{u} B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (h : IsZero ((((tensorModuleRight
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i)) :
    IsZero ((((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).homology i) := by
  set X := ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) with hX
  rw [← StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff (algebraMap A B)
    (X.homology i)]
  exact h.of_iso
    ((ShortComplex.mapHomologyIso (X.sc i)
        (ModuleCat.restrictScalars (algebraMap A B))).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i).mapIso
        (restrictTensorExtendIso M P))

/-! ### Stacks 066L -/

/-- **Stacks 066L.** Let `A → B` be a map of commutative rings and let `K` be an object of
`D(A)` with Tor amplitude in `[a, b]`. Then `K ⊗_A^L B` has Tor amplitude in `[a, b]` as an
object of `D(B)`.

The derived tensor products over `A` and over `B` are certified as in Stacks 0652, and derived
extension of scalars is certified in the same style: `extendDerived` is equipped with a
comparison map `extendComparison` to termwise extension of scalars making it the total left
derived functor of the latter. -/
@[stacks 066L]
public theorem hasTorAmplitude_derivedExtendScalars {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B]
    (extendDerived : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
    (extendComparison : DerivedCategory.Q ⋙ extendDerived ⟶
      (ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (extendIsLeftDerived : extendDerived.IsLeftDerivedFunctor extendComparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (derivedTensorA : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparisonA : ∀ M : ModuleCat.{u} A,
      DerivedCategory.Q ⋙ derivedTensorA.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedA : ∀ M : ModuleCat.{u} A,
      (derivedTensorA.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).IsLeftDerivedFunctor
        (comparisonA M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (derivedTensorB : DerivedCategory (ModuleCat.{u} B) ⥤
      DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B))
    (comparisonB : ∀ M : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ derivedTensorB.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedB : ∀ M : ModuleCat.{u} B,
      (derivedTensorB.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).IsLeftDerivedFunctor
        (comparisonB M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (hK : HasTorAmplitude derivedTensorA comparisonA isLeftDerivedA K a b) :
    HasTorAmplitude derivedTensorB comparisonB isLeftDerivedB (extendDerived.obj K) a b := by
  obtain ⟨P, m, hPLE, hPproj, ⟨eP⟩⟩ := exists_projective_representative K b (fun i hi =>
    isZero_homology_of_hasTorAmplitude isLeftDerivedA K a b hK i (by
      simp only [Set.mem_Icc, not_and_or, not_le]
      exact Or.inr hi))
  have := hPLE
  have hproj : ∀ i : ℤ, Projective (P.X i) := hPproj
  have := hproj
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P m
  have hflatA : ∀ i : ℤ, Module.Flat A (P.X i) := fun i => by
    have := hPproj i
    infer_instance
  have hboundedA : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨m, fun i hi => P.isZero_of_isStrictlyLE m i hi⟩
  set extP := ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P with hextP
  have hflatB : ∀ i : ℤ, Module.Flat B (extP.X i) :=
    fun i => flat_extendScalars (P.X i) (hflatA i)
  have hboundedB : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (extP.X i) :=
    ⟨m, fun i hi => Functor.map_isZero (ModuleCat.extendScalars (algebraMap A B))
      (P.isZero_of_isStrictlyLE m i hi)⟩
  have := extendIsLeftDerived
  have hIso : IsIso (extendComparison.app P) :=
    isIso_counit_app_of_isKProjective (ModuleCat.extendScalars (algebraMap A B))
      extendDerived extendComparison P
  have eL : extendDerived.obj K ≅ DerivedCategory.Q.obj extP :=
    extendDerived.mapIso eP.symm ≪≫ asIso (extendComparison.app P)
  intro M i hi
  have hA : IsZero ((((tensorModuleRight
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i) :=
    (hK ((ModuleCat.restrictScalars (algebraMap A B)).obj M) i hi).of_iso
      ((certifiedTensorHomologyIsoOfFlat comparisonA isLeftDerivedA P hboundedA hflatA
          ((ModuleCat.restrictScalars (algebraMap A B)).obj M) i).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
          ((derivedTensorA.mapIso eP).app _))
  have hB : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      ((derivedTensorB.obj (DerivedCategory.Q.obj extP)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M))) :=
    (isZero_homology_tensor_extendScalars M P i hA).of_iso
      (certifiedTensorHomologyIsoOfFlat comparisonB isLeftDerivedB extP hboundedB hflatB M i)
  exact hB.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso
    ((derivedTensorB.mapIso eL).app _))

end ExtendScalars

end StacksDraft.TorAmplitude
