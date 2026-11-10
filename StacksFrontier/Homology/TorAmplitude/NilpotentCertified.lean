module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.Homology.TorAmplitude.Nilpotent

/-!
# Stacks 0H75 at the three-field certificate of Stacks 0652

Let `R' → R` be a surjective map of commutative rings whose kernel is a nilpotent ideal, let `K`
be an object of `D(R')` and let `L` be derived extension of scalars along `R' → R`. Then `L.obj K`
has Tor amplitude in `[a, b]` if and only if `K` does. This is Stacks 0H75, and it is proved here
with both Tor amplitudes read off a `StacksDraft.TorAmplitude.CertifiedDerivedTensoring` — the
bifunctor, its comparison with termwise tensoring, and the `IsLeftDerivedFunctor` certificate,
which is exactly the datum Stacks 0652 reads Tor amplitude off and nothing more.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_certified_iff`: Stacks 0H75,
  with the universe of `R'`, the universe of `R` and the universe of the module carriers
  independent, as in the source statement, and both derived tensor products quantified as
  three-field certificates.

## Implementation notes

`StacksFrontier.Homology.TorAmplitude.Nilpotent` proves the same equivalence over
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, an eight-field datum that carries in
addition the comparison at pairs of K-flat complexes, its naturality, and the commutation with
the shift and the exactness in *each* variable. A richer hypothesis makes a weaker theorem, so
that form does not state Stacks 0H75: the source reads Tor amplitude off the three fields of
Stacks 0652 only. This file removes that gap.

The three fields suffice because they already pin the bifunctor down. For each module `M`, the
functor `- ⊗ᴸ M[0]` is the *total left derived functor* of termwise tensoring by `M`, and a total
left derived functor is unique up to a unique natural isomorphism
(`CategoryTheory.Functor.leftDerivedNatIso`). So any two certificates on one ring compute the same
cohomology modules, and the Tor-amplitude predicate cannot tell them apart. The proof exploits
this twice:

* `derivedTensorScalarLiftIso` transports an arbitrary certificate along the change of coefficient
  ring `scalarLift` of `StacksFrontier.Homology.TorAmplitude.DerivedComparison`, identifying it with
  the *canonical* certificate over the lifted ring. `hasTorAmplitude_iff_scalarLift` reads that off
  as an equivalence of Tor-amplitude predicates.
* over the lifted rings the ring universe and the module universe coincide, so the canonical
  derived tensor product of Stacks 0BYI is available there and carries all eight fields. The
  same-universe form `hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse` therefore
  applies to it, and the eight-field theorem is never reproved.

Transporting the derived base change to the lifted rings is `derivedExtensionLiftSquare`, and it
is uniqueness of left derived functors again. On modules, extension of scalars commutes with the
coefficient changes (`extensionLiftSquare`) because both composites are left adjoint to the same
functor, by `restrictionLiftSquare` and `Adjunction.leftAdjointUniq`. On derived categories, `L`
followed by the coefficient change is a total left derived functor because postcomposing with an
equivalence preserves the universal property, and the coefficient change followed by the derived
extension of scalars along the lifted map is one by
`CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp`; the two termwise functors are
identified by `extensionLiftSquare`, so `Functor.leftDerivedNatIso` identifies the composites. The
derived extension of scalars along the lifted map is not assumed but constructed, by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral`.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 0H75](https://stacks.math.columbia.edu/tag/0H75)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace StacksDraft.TorAmplitude

universe u v w q₁ q₂

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-! ### Moving a ring map into the common module universe -/

/-- A ring map, read between the `ULift`s of its two rings into one common universe. `ULift`
changes nothing about a ring except the universe its carrier lives in, and this is the map of
lifted rings induced by the original one. -/
public def liftedRingHom {R' : Type u} {R : Type v} [CommRing R'] [CommRing R] (f : R' →+* R) :
    ULift.{max u v w} R' →+* ULift.{max u v w} R :=
  (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom

/-- The lifted map is surjective when the original one is. -/
public lemma liftedRingHom_surjective {R' : Type u} {R : Type v} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f) :
    Function.Surjective (liftedRingHom.{u, v, w} f) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.down
  exact ⟨ULift.up x, ULift.down_injective hx⟩

/-- The kernel of the lifted map is nilpotent when the kernel of the original one is: it is the
image of the original kernel under the ring isomorphism `R' ≃+* ULift R'`. -/
public lemma liftedRingHom_isNilpotent_ker {R' : Type u} {R : Type v} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : IsNilpotent (RingHom.ker f)) :
    IsNilpotent (RingHom.ker (liftedRingHom.{u, v, w} f)) := by
  let e : R' →+* ULift.{max u v w} R' := ULift.ringEquiv.symm.toRingHom
  have hker : RingHom.ker (liftedRingHom.{u, v, w} f) = Ideal.map e (RingHom.ker f) := by
    apply le_antisymm
    · intro x hx
      rw [show x = e x.down from rfl]
      exact Ideal.mem_map_of_mem e (congrArg ULift.down hx)
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      change ULift.up (f y) = 0
      rw [hy]
      rfl
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [hker, ← Ideal.map_pow, hn]; exact Ideal.map_bot⟩

/-- Restriction of scalars along `S ≃+* ULift S`: the inverse of the coefficient change
`StacksDraft.TorAmplitude.scalarLift`. -/
public noncomputable abbrev scalarUnlift (S : Type q₁) [CommRing S] :
    ModuleCat.{max q₁ q₂} (ULift.{q₂} S) ⥤ ModuleCat.{max q₁ q₂} S :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{q₂} S ≃+* S)).inverse

/-- `scalarLift` is left adjoint to `scalarUnlift`: the two are the halves of the equivalence of
module categories induced by the ring isomorphism `ULift S ≃+* S`. -/
public noncomputable def scalarLiftAdjunction (S : Type q₁) [CommRing S] :
    scalarLift.{q₁, q₂} (R := S) ⊣ scalarUnlift.{q₁, q₂} S :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{q₂} S ≃+* S)).toAdjunction

/-- Extension of scalars along a map of rings in two independent universes is additive: it is a
left adjoint of restriction of scalars, which is additive. The instance is what lets termwise
extension of scalars be read on cochain complexes at the free module universe of the source
statement. -/
public instance additive_extendScalars_free {R' : Type u} {R : Type v} [CommRing R'] [CommRing R]
    (f : R' →+* R) : (ModuleCat.extendScalars.{u, v, max u v w} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} f).left_adjoint_additive

/-! ### Transporting a certificate to the lifted ring -/

section ScalarLift

variable {R : Type u} [CommRing R]

/-- Uniqueness of total left derived functors transports a certified derived tensor product along
the change of coefficient ring `scalarLift`: the functor `- ⊗ᴸ M[0]` of an arbitrary certificate,
followed by the coefficient change, is the coefficient change followed by `- ⊗ᴸ (M lifted)[0]` for
the *canonical* derived tensor product of the lifted ring.

Both composites are total left derived functors of the same termwise functor, one directly and one
through `LocalizerMorphism.isLeftDerivedFunctor_iff_precomp` for the localizer morphism of the
coefficient change, so `Functor.leftDerivedNatIso` identifies them. -/
private noncomputable def derivedTensorScalarLiftIso
    (T : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
    (M : ModuleCat.{max u v} R)
    (α : DerivedCategory.Q ⋙ T ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))] :
    T ⋙ (scalarLift.{u, v} (R := R)).mapDerivedCategory ≅
      (scalarLift.{u, v} (R := R)).mapDerivedCategory ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            (ULift.{v} R)).tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
            ((scalarLift.{u, v} (R := R)).obj M)) := by
  let G := scalarLift.{u, v} (R := R)
  let C := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{v} R)
  let L' := C.tensor.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj (G.obj M))
  let α' := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α G.mapDerivedCategory
  let β : DerivedCategory.Q ⋙ (G.mapDerivedCategory ⋙ L') ⟶
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight (G.obj M)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight G.mapDerivedCategoryFactors.hom L' ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (canonicalTensorComparison (ULift.{v} R) (G.obj M))
  haveI : (G.mapDerivedCategory ⋙ L').IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := by
    apply (LocalizerMorphism.isLeftDerivedFunctor_iff_precomp
      (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory G.mapDerivedCategoryFactors.symm
      β (canonicalTensorComparison (ULift.{v} R) (G.obj M)) (Iso.refl _) (Iso.refl _) ?_).1
      inferInstance
    ext X
    dsimp [β, L', C, Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism]
    simp only [Category.id_comp, Category.comp_id]
  let τ :
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ G.mapDerivedCategory ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight (G.obj M)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (tensorScalarLiftIso M) (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (G ⋙ tensorModuleRight (G.obj M))) (ComplexShape.up ℤ)).symm) _ ≪≫
      Functor.associator _ _ _
  exact Functor.leftDerivedNatIso _ _ α' β
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) τ

/-- Tor amplitude does not see which certificate it is read off, nor the change of coefficient
ring: an arbitrary certified derived tensor product on `R`, with modules in `ModuleCat.{max u v}`,
gives the same Tor-amplitude predicate as the canonical derived tensor product of the lifted ring
`ULift.{v} R`, whose ring universe agrees with its module universe. -/
private theorem hasTorAmplitude_iff_scalarLift
    (derivedTensor : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
    (comparison : ∀ M : ModuleCat.{max u v} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{max u v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))
    (X : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) :
    HasTorAmplitude derivedTensor comparison isLeftDerived X a b ↔
      HasTorAmplitude
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{v} R)).tensor
        (canonicalTensorComparison (ULift.{v} R)) (canonicalTensorIsLeftDerived (ULift.{v} R))
        ((scalarLift.{u, v} (R := R)).mapDerivedCategory.obj X) a b := by
  let G := scalarLift.{u, v} (R := R)
  let C := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{v} R)
  have hM : ∀ (M : ModuleCat.{max u v} R) (i : ℤ),
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
          ((derivedTensor.obj X).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M))) ↔
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).obj
          ((C.tensor.obj (G.mapDerivedCategory.obj X)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
              (G.obj M)))) := by
    intro M i
    let TM := derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
    have := isLeftDerived M
    let e := derivedTensorScalarLiftIso TM M (comparison M)
    exact (scalarLift_map_isZero_homology_iff (TM.obj X) i).symm.trans
      (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).mapIso
        (e.app X)).isZero_iff)
  refine ⟨fun h N i hi ↦ ((hM (G.objPreimage N) i).1 (h (G.objPreimage N) i hi)).of_iso ?_,
    fun h M i hi ↦ (hM M i).2 (h (G.obj M) i hi)⟩
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).mapIso
    ((C.tensor.obj (G.mapDerivedCategory.obj X)).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).mapIso
        (G.objObjPreimageIso N)))).symm

end ScalarLift

/-! ### Transporting derived extension of scalars to the lifted rings -/

section ExtensionSquare

variable {R' : Type u} {R : Type v} [CommRing R'] [CommRing R] (f : R' →+* R)

/-- Extension of scalars along the lifted map is additive: it is a left adjoint of restriction
of scalars, which is additive. -/
public instance liftedExtendScalars_additive :
    (ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
      (liftedRingHom.{u, v, w} f)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{max u v w, max u v w, max u v w}
    (liftedRingHom.{u, v, w} f)).left_adjoint_additive

/-- Restriction of scalars commutes with the coefficient changes: restricting along `f` and then
lowering the coefficients agrees with lowering them first and restricting along the lifted map.
Both sides are restriction of scalars along one composite `R' →+* ULift R`, and the two composites
agree. -/
public noncomputable def restrictionLiftSquare :
    scalarUnlift.{v, max u v w} R ⋙ ModuleCat.restrictScalars.{max u v w, u, v} f ≅
      ModuleCat.restrictScalars.{max u v w, max u v w, max u v w} (liftedRingHom.{u, v, w} f) ⋙
        scalarUnlift.{u, max u v w} R' := by
  let sourceUp : R' →+* ULift.{max u v w} R' := ULift.ringEquiv.symm.toRingHom
  let targetUp : R →+* ULift.{max u v w} R := ULift.ringEquiv.symm.toRingHom
  change ModuleCat.restrictScalars.{max u v w} targetUp ⋙ ModuleCat.restrictScalars f ≅
    ModuleCat.restrictScalars (liftedRingHom.{u, v, w} f) ⋙
      ModuleCat.restrictScalars.{max u v w} sourceUp
  have hcomm : targetUp.comp f = (liftedRingHom.{u, v, w} f).comp sourceUp :=
    RingHom.ext fun _ ↦ rfl
  exact (ModuleCat.restrictScalarsComp' f targetUp (targetUp.comp f) rfl).symm ≪≫
    ModuleCat.restrictScalarsCongr hcomm ≪≫
    ModuleCat.restrictScalarsComp' sourceUp (liftedRingHom.{u, v, w} f)
      ((liftedRingHom.{u, v, w} f).comp sourceUp) rfl

/-- Extension of scalars commutes with the coefficient changes. Both composites are left adjoint
to the same functor, by `restrictionLiftSquare`, so `Adjunction.leftAdjointUniq` identifies
them. -/
public noncomputable def extensionLiftSquare :
    ModuleCat.extendScalars.{u, v, max u v w} f ⋙ scalarLift.{v, max u v w} (R := R) ≅
      scalarLift.{u, max u v w} (R := R') ⋙
        ModuleCat.extendScalars.{max u v w, max u v w, max u v w} (liftedRingHom.{u, v, w} f) :=
  Adjunction.leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} f).comp
      (scalarLiftAdjunction.{v, max u v w} R))
    (((scalarLiftAdjunction.{u, max u v w} R').comp
        (ModuleCat.extendRestrictScalarsAdj.{max u v w, max u v w, max u v w}
          (liftedRingHom.{u, v, w} f))).ofNatIsoRight (restrictionLiftSquare f).symm)

/-- A total derived extension of scalars along the lifted map. Both lifted rings live in the
common module universe, so this is the same-universe construction. -/
public noncomputable abbrev liftedDerivedExtension :
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{max u v w, max u v w,
      max u v w} (liftedRingHom.{u, v, w} f) :=
  CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{max u v w, max u v w,
    max u v w} (liftedRingHom.{u, v, w} f)

/-- Its comparison with termwise extension of scalars along the lifted map, in the shape the
same-universe form of Stacks 0H75 takes it. -/
public noncomputable def liftedComparison :
    DerivedCategory.Q ⋙ (liftedDerivedExtension.{u, v, w} f).functor ⟶
      (ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
          (liftedRingHom.{u, v, w} f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (liftedDerivedExtension.{u, v, w} f).comparison

/-- The derived extension of scalars along the lifted map is the total left derived functor of
termwise extension of scalars along it, with `liftedComparison` as its comparison. -/
public instance liftedComparison_isLeftDerived :
    (liftedDerivedExtension.{u, v, w} f).functor.IsLeftDerivedFunctor
      (liftedComparison.{u, v, w} f)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} (ULift.{max u v w} R'))
        (ComplexShape.up ℤ)) :=
  (liftedDerivedExtension.{u, v, w} f).isLeftDerived

/-- **The derived base change, transported to the lifted rings.** The derived extension of scalars
along `f` followed by the coefficient change is the coefficient change followed by the derived
extension of scalars along the lifted map.

Both composites are total left derived functors of the termwise functors identified by
`extensionLiftSquare`: the first because postcomposition with an equivalence of derived categories
preserves the universal property, the second by
`LocalizerMorphism.isLeftDerivedFunctor_iff_precomp` for the localizer morphism of the coefficient
change. `Functor.leftDerivedNatIso` then identifies them. -/
public noncomputable def derivedExtensionLiftSquare
    (L : DerivedCategory (ModuleCat.{max u v w} R') ⥤ DerivedCategory (ModuleCat.{max u v w} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{max u v w} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := ModuleCat.{max u v w} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R') (ComplexShape.up ℤ))] :
    L ⋙ (scalarLift.{v, max u v w} (R := R)).mapDerivedCategory ≅
      (scalarLift.{u, max u v w} (R := R')).mapDerivedCategory ⋙
        (liftedDerivedExtension.{u, v, w} f).functor := by
  let G' := scalarLift.{u, max u v w} (R := R')
  let G := scalarLift.{v, max u v w} (R := R)
  let LL := (liftedDerivedExtension.{u, v, w} f).functor
  let EL := ModuleCat.extendScalars.{max u v w, max u v w, max u v w} (liftedRingHom.{u, v, w} f)
  let α' := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight comparison G.mapDerivedCategory
  let β : DerivedCategory.Q ⋙ (G'.mapDerivedCategory ⋙ LL) ⟶
      G'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        EL.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight G'.mapDerivedCategoryFactors.hom LL ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (liftedComparison.{u, v, w} f)
  haveI : (G'.mapDerivedCategory ⋙ LL).IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R') (ComplexShape.up ℤ)) := by
    apply (LocalizerMorphism.isLeftDerivedFunctor_iff_precomp
      (G'.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G'.mapDerivedCategory
      G'.mapDerivedCategoryFactors.symm β (liftedComparison.{u, v, w} f) (Iso.refl _)
      (Iso.refl _) ?_).1 inferInstance
    ext X
    dsimp [β, LL, Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism]
    simp only [Category.id_comp, Category.comp_id]
  let τ :
      ((ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ G.mapDerivedCategory ≅
      G'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        EL.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (extensionLiftSquare f) (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ EL))
            (ComplexShape.up ℤ)).symm) _ ≪≫
      Functor.associator _ _ _
  exact Functor.leftDerivedNatIso _ _ α' β
    (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R') (ComplexShape.up ℤ)) τ

end ExtensionSquare

/-! ### Stacks 0H75 -/

section Endpoint

variable {R' : Type u} {R : Type v} [CommRing R'] [CommRing R] (f : R' →+* R)

/-- **Stacks 0H75.** Let `f : R' → R` be a surjective map of commutative rings whose kernel is a
nilpotent ideal, and let `L` be the derived base change along `f`. For every object `K` of `D(R')`
and every finite interval `[a, b]`, the object `L.obj K` has Tor amplitude in `[a, b]` if and only
if `K` does.

`L` is quantified over together with its comparison to termwise extension of scalars and the
`Functor.IsLeftDerivedFunctor` certificate, which pins it down as *the* derived base change rather
than an arbitrary functor. Each of the two derived tensor products is quantified as a
`StacksDraft.TorAmplitude.CertifiedDerivedTensoring`: the bifunctor, its comparison with termwise
tensoring by a module placed in degree zero, and the universal property making each `- ⊗ᴸ M[0]` the
total left derived functor of `- ⊗ M`. That is exactly the datum Stacks 0652 reads Tor amplitude
off, and no more; in particular neither the comparison at pairs of K-flat complexes nor exactness
in the second variable is assumed.

The universe of `R'`, the universe of `R` and the universe of the module carriers are independent:
`R' : Type u`, `R : Type v`, and both rings' modules are read in `ModuleCat.{max u v w}`, as in the
source statement. Neither ring is `ULift`ed in the statement.

The proof moves both sides into the lifted rings, where the ring universe and the module universe
coincide, by `hasTorAmplitude_iff_scalarLift` for the Tor amplitudes and
`derivedExtensionLiftSquare` for the base change, and there applies
`hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse` to the canonical derived tensor
product of Stacks 0BYI. -/
@[stacks 0H75]
public theorem hasTorAmplitudeIn_derivedExtensionScalars_certified_iff
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (L : DerivedCategory (ModuleCat.{max u v w} R') ⥤ DerivedCategory (ModuleCat.{max u v w} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{max u v w} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := ModuleCat.{max u v w} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R') (ComplexShape.up ℤ))]
    (D' : CertifiedDerivedTensoring.{u, max u v w} R')
    (D : CertifiedDerivedTensoring.{v, max u v w} R)
    (K : DerivedCategory (ModuleCat.{max u v w} R')) (a b : ℤ) :
    D.HasTorAmplitudeIn (L.obj K) a b ↔ D'.HasTorAmplitudeIn K a b := by
  let G' := scalarLift.{u, max u v w} (R := R')
  let G := scalarLift.{v, max u v w} (R := R)
  let LL := (liftedDerivedExtension.{u, v, w} f).functor
  let C' := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
    (ULift.{max u v w} R')
  let C := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{max u v w} R)
  have h1 : D.HasTorAmplitudeIn (L.obj K) a b ↔
      HasTorAmplitude C.tensor (canonicalTensorComparison (ULift.{max u v w} R))
        (canonicalTensorIsLeftDerived (ULift.{max u v w} R))
        (G.mapDerivedCategory.obj (L.obj K)) a b :=
    (D.hasTorAmplitudeIn_iff (L.obj K) a b).trans
      (hasTorAmplitude_iff_scalarLift D.tensor D.comparison D.isLeftDerived (L.obj K) a b)
  have h2 : D'.HasTorAmplitudeIn K a b ↔
      HasTorAmplitude C'.tensor (canonicalTensorComparison (ULift.{max u v w} R'))
        (canonicalTensorIsLeftDerived (ULift.{max u v w} R'))
        (G'.mapDerivedCategory.obj K) a b :=
    (D'.hasTorAmplitudeIn_iff K a b).trans
      (hasTorAmplitude_iff_scalarLift D'.tensor D'.comparison D'.isLeftDerived K a b)
  have e := (derivedExtensionLiftSquare f L comparison).app K
  have h3 : HasTorAmplitude C.tensor (canonicalTensorComparison (ULift.{max u v w} R))
        (canonicalTensorIsLeftDerived (ULift.{max u v w} R))
        (G.mapDerivedCategory.obj (L.obj K)) a b ↔
      HasTorAmplitude C.tensor (canonicalTensorComparison (ULift.{max u v w} R))
        (canonicalTensorIsLeftDerived (ULift.{max u v w} R))
        (LL.obj (G'.mapDerivedCategory.obj K)) a b :=
    hasTorAmplitude_of_iso e a b
  have h4 : HasTorAmplitude C.tensor (canonicalTensorComparison (ULift.{max u v w} R))
        (canonicalTensorIsLeftDerived (ULift.{max u v w} R))
        (LL.obj (G'.mapDerivedCategory.obj K)) a b ↔
      HasTorAmplitude C'.tensor (canonicalTensorComparison (ULift.{max u v w} R'))
        (canonicalTensorIsLeftDerived (ULift.{max u v w} R'))
        (G'.mapDerivedCategory.obj K) a b := by
    refine (hasTorAmplitudeIn_iff_hasTorAmplitude C (canonicalTensorComparison _)
      (canonicalTensorIsLeftDerived _) (LL.obj (G'.mapDerivedCategory.obj K)) a b).symm.trans ?_
    refine Iff.trans ?_ (hasTorAmplitudeIn_iff_hasTorAmplitude C'
      (canonicalTensorComparison _) (canonicalTensorIsLeftDerived _)
      (G'.mapDerivedCategory.obj K) a b)
    exact hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse (liftedRingHom.{u, v, w} f)
      (liftedRingHom_surjective f hf) (liftedRingHom_isNilpotent_ker f hnil) LL
      (liftedComparison.{u, v, w} f) C' C (G'.mapDerivedCategory.obj K) a b
  exact h1.trans (h3.trans (h4.trans h2.symm))

end Endpoint

end

end StacksDraft.TorAmplitude
