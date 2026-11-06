module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectComposite
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.BoundedBelowSubcategory
public import StacksFrontier.Homology.Tor.KFlatResolutionSingleTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedTensor.TorFlatness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOverSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeTorAmplitude
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk projection formula and the pointwise Tor bound of a composite

Let `f : Y ⟶ X` be a morphism of schemes, `T` a derived tensor product on `Y` (Stacks 06YU),
`M ∈ D(𝒪_Y)`, `K ∈ D(𝒪_X)` and `y : Y`. The stalk of `M ⊗ᴸ Lf^*K` at `y`, read over the local ring
`𝒪_{X, f y}`, is

`res((M ⊗ᴸ Lf^*K)_y) ≅ res(M_y) ⊗ᴸ_{𝒪_{X, f y}} K_{f y}`.

Both objects are represented by K-flat complexes. The stalk of the derived tensor product is the
derived tensor product of the stalks, the stalk of `Lf^*K` is `𝒪_{Y,y} ⊗_{𝒪_{X,f y}} K_{f y}`
(Stacks 0098), whose stalk complex is K-flat, and the chain-level projection formula
`res(L ⊗_B (B ⊗_A P)) = res(L) ⊗_A P` (Stacks 06Y6) identifies the two sides, the right-hand
derived tensor product being computed by `res(L) ⊗_A P` because `P` is K-flat.

With Stacks 0B66 this gives the pointwise Tor bound `RelativeStalkTensorBound` used for the
relative perfectness of `M ⊗ᴸ Lf^*K` in the proof of Stacks 0E30. Read with the lower end of a Tor
amplitude only, it bounds `F ⊗ᴸ Lh^*N` below for `F` of Tor amplitude `≥ a` over the target of
`h` and `N` bounded below: the relative Tor bound of `L pr₁^*M|_{W'}` along `f × f : W' ⟶ W`
that the sheaf-level form of Stacks 0ATN (3) asks for in the proof of Stacks 0E30.

## Main results

* `CochainComplex.DerivedTensor.restrictScalarsTensorExtendScalarsIso`: the projection formula
  for a ring map, at K-flat representatives.
* `AlgebraicGeometry.Scheme.Hom.stalkDerivedTensorDerivedPullbackIso`: the stalk projection
  formula.
* `AlgebraicGeometry.Scheme.Hom.relativeStalkTensorBound`: the pointwise Tor bound of a
  composite.
* `AlgebraicGeometry.Scheme.Hom.isGE_restrict_tensor_derivedPullback_of_hasTorAmplitudeOver`:
  a Tor-amplitude bound over the target bounds `F ⊗ᴸ Lh^*N` below.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_isGE_restrict_tensor_derivedPullbackProj`:
  the relative Tor bound of `L pr₁^*M|_{W'}` along `f × f`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 48.28.11 (Tag 0E30)](https://stacks.math.columbia.edu/tag/0E30)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory StrictlyPerfect TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace CochainComplex.DerivedTensor

variable {A : Type u} [CommRing A]

/-- **The canonical derived tensor product with a K-flat right factor.** If `P` is K-flat, the
derived tensor product of `X` and `P` is computed by the total tensor complex `X ⊗ P`, for any
`X`: a K-flat resolution `X' ⟶ X` stays a quasi-isomorphism after tensoring with `P`. -/
def canonicalTensorQIsoOfKFlatRight (X P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    ((canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj X)).obj
      (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (X ⊗ P) :=
  let h := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} X
  let X' := h.choose
  let q : X' ⟶ X := h.choose_spec.choose
  have hX' : X'.KFlat := h.choose_spec.choose_spec.1
  have hq : QuasiIso q := h.choose_spec.choose_spec.2.2.1
  have hqP : QuasiIso (q ▷ P) := StacksDraft.TorAmplitude.quasiIso_tensorRight_map hP q
  have h₁ : IsIso (DerivedCategory.Q.map q) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hq
  have h₂ : IsIso (DerivedCategory.Q.map (q ▷ P)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hqP
  ((canonicalDerivedTensorProduct A).tensor.mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map q) h₁).symm).app _ ≪≫
    (canonicalDerivedTensorProduct A).comparison X' P hX' hP ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map (q ▷ P)) h₂

/-- Restriction of scalars along a ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_stalkTensor
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along a ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_stalkTensor
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along a ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_stalkTensor
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

/-- **The canonical derived tensor product with a K-flat left factor.** If `P` is K-flat, the
derived tensor product of `P` and `X` is computed by the total tensor complex `P ⊗ X`, for any
`X`. -/
def canonicalTensorQIsoOfKFlatLeft (P X : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    ((canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj P)).obj
      (DerivedCategory.Q.obj X) ≅ DerivedCategory.Q.obj (P ⊗ X) :=
  let h := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} X
  let X' := h.choose
  let q : X' ⟶ X := h.choose_spec.choose
  have hX' : X'.KFlat := h.choose_spec.choose_spec.1
  have hq : QuasiIso q := h.choose_spec.choose_spec.2.2.1
  have hPq : QuasiIso (P ◁ q) := quasiIso_tleftCochain_map_of_kFlat P hP q hq
  have h₁ : IsIso (DerivedCategory.Q.map q) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hq
  have h₂ : IsIso (DerivedCategory.Q.map (P ◁ q)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hPq
  ((canonicalDerivedTensorProduct A).tensor.obj _).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map q) h₁).symm ≪≫
    (canonicalDerivedTensorProduct A).comparison P X' hP hX' ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map (P ◁ q)) h₂

/-- **A lower Tor bound bounds derived tensor products below.** If `K` has Tor amplitude in
`[a, d]` and `L` has no cohomology below `b`, then `K ⊗ᴸ L` has no cohomology below `a + b`: `K` is
represented by a complex of flat modules in degrees `[a, d]`, which is K-flat, and `L` by a
complex vanishing below `b`. -/
@[sga "4 XVII 4.1.9" "(i)⇒(ii)"]
theorem isGE_canonicalTensor_of_hasTorAmplitudeCanonical (K L : DerivedCategory (ModuleCat.{u} A))
    (a d b : ℤ) (hK : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical A K a d) (hL : L.IsGE b) :
    (((canonicalDerivedTensorProduct A).tensor.obj K).obj L).IsGE (a + b) := by
  obtain ⟨E, hflat, hGE, hLE, ⟨eK⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative A K a d).1 hK
  have := hLE
  have := hGE
  have : ∀ n : ℤ, Module.Flat A (E.X n) := hflat
  have hE : E.KFlat := CochainComplex.KFlat.kFlat_of_flat.{u, u} E d
  obtain ⟨L', hL', ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L b
  have := hL'
  have : (E ⊗ L').IsStrictlyGE (a + b) :=
    CochainComplex.KFlatMonoidal.isStrictlyGE_tensorObj (ModuleCat.{u} A) E L' a b
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((canonicalTensorQIsoOfKFlatLeft E L' hE).symm ≪≫
      ((canonicalDerivedTensorProduct A).tensor.mapIso eK.symm).app _ ≪≫
      ((canonicalDerivedTensorProduct A).tensor.obj K).mapIso eL.symm) (a + b)

variable {B : Type u} [CommRing B] (φ : A →+* B)

/-- **The projection formula at K-flat representatives.** For a ring homomorphism
`φ : A →+* B`, a K-flat complex `L` of `B`-modules and a K-flat complex `P` of `A`-modules,
restriction of scalars carries `L ⊗ᴸ_B (B ⊗_A P)` to `L ⊗ᴸ_A P`. -/
def restrictScalarsTensorExtendScalarsIso (L : CochainComplex (ModuleCat.{u} B) ℤ)
    (hL : L.KFlat) (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
      (((canonicalDerivedTensorProduct B).tensor.obj (DerivedCategory.Q.obj L)).obj
        (DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} φ).obj P))) ≅
    ((canonicalDerivedTensorProduct A).tensor.obj
      ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj (DerivedCategory.Q.obj L))).obj
        (DerivedCategory.Q.obj P) :=
  (ModuleCat.restrictScalars φ).mapDerivedCategory.mapIso
      ((canonicalDerivedTensorProduct B).comparison L _ hL
        (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars φ P hP)) ≪≫
    (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso φ P L) ≪≫
    (canonicalTensorQIsoOfKFlatRight _ P hP).symm ≪≫
    ((canonicalDerivedTensorProduct A).tensor.mapIso
      ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.app L).symm).app _

end CochainComplex.DerivedTensor

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] StacksDraft.StalkTensor.commRing_stalk

section StalkSpellings

variable {Z : Scheme.{u}} (z : Z)

/-- The stalk over the local ring `𝒪_{Z,z}`, with scalars restricted along
`ringCatStalkRingEquiv`, is the stalk over the `RingCat`-valued stalk of the ring sheaf:
`AlgebraicGeometry.restrictScalarsStalkObjIso` read through the equivalence of module categories
of the ring isomorphism. -/
def restrictScalarsModulesStalkIso :
    Stacks.ModuleSkyscraper.modulesStalkFunctor Z z ⋙
        ModuleCat.restrictScalars (AlgebraicGeometry.ringCatStalkRingEquiv z).toRingHom ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor Z.ringCatSheaf z :=
  Functor.isoWhiskerRight
      (NatIso.ofComponents (AlgebraicGeometry.restrictScalarsStalkObjIso z) (fun _ => rfl)).symm
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (AlgebraicGeometry.ringCatStalkRingEquiv z).symm).unitIso.symm ≪≫
    Functor.rightUnitor _

end StalkSpellings

/-- Extension of scalars along the inverse of a ring isomorphism is restriction of scalars along
the isomorphism: both are left adjoint to restriction of scalars along the inverse. -/
def extendScalarsSymmIsoRestrictScalars {B B' : Type u} [CommRing B] [CommRing B']
    (e : B ≃+* B') :
    ModuleCat.extendScalars.{u, u, u} e.symm.toRingHom ≅
      ModuleCat.restrictScalars.{u} e.toRingHom :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} e.symm.toRingHom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).toAdjunction

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)

/-- The ring map `𝒪_{X, f y} ⟶ 𝒪_{Y,y}` landing in the `RingCat`-valued stalk of `𝒪_Y`. -/
abbrev stalkMapRingCat : ToType (X.presheaf.stalk (f.base y)) →+*
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) y) :=
  (SemilinearStalk.commStalkRingEquiv Y.presheaf y).symm.toRingHom.comp (f.stalkMap y).hom

/-- **Stacks 0098 over the `RingCat`-valued stalk.** The stalk at `y` of the pullback of an
`𝒪_X`-module, over the `RingCat`-valued stalk of `𝒪_Y`, is the base change of its stalk over the
local ring `𝒪_{X, f y}` along `stalkMapRingCat`. -/
def pullbackStalkRingCatIso :
    Scheme.Modules.pullback f ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf y ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X (f.base y) ⋙
        ModuleCat.extendScalars.{u, u, u} (stalkMapRingCat f y) :=
  Functor.isoWhiskerLeft _ (restrictScalarsModulesStalkIso y).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.ModuleSkyscraper.pullbackStalkIso f y).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (extendScalarsSymmIsoRestrictScalars
          (AlgebraicGeometry.ringCatStalkRingEquiv y)).symm ≪≫
        (ModuleCat.extendScalarsComp (f.stalkMap y).hom
          (AlgebraicGeometry.ringCatStalkRingEquiv y).symm.toRingHom).symm)

section LowerBounds

/-- A lower bound on cohomology transports along an isomorphism, stated with the bound as an
explicit hypothesis. -/
theorem isGE_of_iso_of_isGE {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : DerivedCategory C} (e : K ≅ L) (n : ℤ) (hK : K.IsGE n) : L.IsGE n := by
  have := hK
  exact DerivedCategory.TStructure.t.isGE_of_iso e n

/-- An exact functor carries objects with no cohomology below `n` to such objects. -/
theorem isGE_mapDerivedCategory_obj_of_isGE {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C) (n : ℤ)
    (hK : K.IsGE n) : (F.mapDerivedCategory.obj K).IsGE n := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro i hi
  exact (F.map_isZero (hK i hi)).of_iso ((F.mapDerivedCategoryHomologyIso i).app K)

/-- An exact functor reflecting zero objects reflects lower bounds on cohomology. -/
theorem isGE_of_isGE_mapDerivedCategory_obj {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : C, IsZero (F.obj M) → IsZero M) (K : DerivedCategory C) (n : ℤ)
    (hK : (F.mapDerivedCategory.obj K).IsGE n) : K.IsGE n := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro i hi
  exact hF _ ((hK i hi).of_iso ((F.mapDerivedCategoryHomologyIso i).app K).symm)

/-- Restriction of scalars reflects zero modules: it does not change the underlying group. -/
theorem isZero_of_isZero_restrictScalars {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (M : ModuleCat.{u} S) (h : IsZero ((ModuleCat.restrictScalars.{u} φ).obj M)) : IsZero M := by
  have : Subsingleton ((ModuleCat.restrictScalars.{u} φ).obj M) :=
    ModuleCat.subsingleton_of_isZero h
  have : Subsingleton M := ‹Subsingleton ((ModuleCat.restrictScalars.{u} φ).obj M)›
  exact ModuleCat.isZero_of_subsingleton M

/-- **Lower bounds are detected on stalks.** -/
theorem isGE_of_forall_stalk {Z : TopCat.{u}}
    (O : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) RingCat.{u})
    (E : DerivedCategory (_root_.SheafOfModules.{u} O)) (n : ℤ)
    (h : ∀ z : Z, ((AlgebraicGeometry.SheafOfModules.stalkFunctor O z).mapDerivedCategory.obj
      E).IsGE n) : E.IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  rw [AlgebraicGeometry.SheafOfModules.isZero_homologyFunctor_obj_iff_forall_stalk]
  intro z
  exact (DerivedCategory.isGE_iff _ n).1 (h z) i hi

end LowerBounds

section ProjectionFormula

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X : Scheme.{u}}

/-- A K-flat complex of `𝒪_X`-modules representing an object of `D(𝒪_X)`. -/
def kFlatRep (K : DerivedCategory X.Modules) : CochainComplex X.Modules ℤ :=
  (Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toSheafedSpace
    (DerivedCategory.Q.objPreimage K)).choose

/-- `kFlatRep K` is K-flat. -/
theorem kFlatComplex_kFlatRep (K : DerivedCategory X.Modules) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace (kFlatRep K) :=
  (Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toSheafedSpace
    (DerivedCategory.Q.objPreimage K)).choose_spec.choose_spec.1

/-- `kFlatRep K` represents `K`. -/
def kFlatRepIso (K : DerivedCategory X.Modules) : DerivedCategory.Q.obj (kFlatRep K) ≅ K :=
  let h := (Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toSheafedSpace
    (DerivedCategory.Q.objPreimage K)).choose_spec
  @asIso _ _ _ _ (DerivedCategory.Q.map h.choose)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr h.choose_spec.2.2.1) ≪≫
    DerivedCategory.Q.objObjPreimageIso K

variable {Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)

/-- **The derived stalk of a derived pullback, over the `RingCat`-valued stalk.** At a K-flat
representative `P` of `K`, the stalk at `y` of `Lf^*K` is the base change along
`stalkMapRingCat` of the stalk complex of `P` at `f y` over the local ring. -/
def derivedStalkDerivedPullbackRingCatIso (K : DerivedCategory X.Modules) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf y).mapDerivedCategory.obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).obj K) ≅
      DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} (stalkMapRingCat f y)).obj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (f.base y)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (kFlatRep K))) :=
  letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive Y.ringCatSheaf y
  letI : (ModuleCat.extendScalars.{u, u, u} (stalkMapRingCat f y)).Additive :=
    haveI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (stalkMapRingCat f y)).isLeftAdjoint
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (stalkMapRingCat f y))
          infer_instance)
  (AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf y).mapDerivedCategory.mapIso
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).mapIso (kFlatRepIso K).symm ≪≫
        @asIso _ _ _ _ (AlgebraicGeometry.pullbackComparisonOnComplex f (kFlatRep K))
          (AlgebraicGeometry.isIso_pullbackComparisonOnComplex_of_kFlat f (kFlatRep K)
            (kFlatComplex_kFlatRep K))) ≪≫
    (AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf y).mapDerivedCategoryFactors.app
      _ ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun i => (pullbackStalkRingCatIso f y).app ((kFlatRep K).X i))
      (fun i j _ => ((pullbackStalkRingCatIso f y).hom.naturality ((kFlatRep K).d i j)).symm))

/-- The stalk complex of `kFlatRep K` at `x` over the local ring is, in the derived category, the
derived stalk of `K` over the `RingCat`-valued stalk read along `commStalkRingEquiv`. -/
def kFlatRepStalkIso (K : DerivedCategory X.Modules) (x : X) :
    DerivedCategory.Q.obj (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (kFlatRep K)) ≅
      (ModuleCat.restrictScalars.{u}
          (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj K) :=
  DerivedCategory.Q.mapIso (AlgebraicGeometry.stalkComplexIso x (kFlatRep K)).symm ≪≫
    ((ModuleCat.restrictScalars.{u}
      (SemilinearStalk.commStalkRingEquiv
        X.presheaf x).symm.toRingHom).mapDerivedCategoryFactors.app _).symm ≪≫
    (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom).mapDerivedCategory.mapIso
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategoryFactors.app
            (kFlatRep K)).symm ≪≫
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.mapIso (kFlatRepIso K))

/-- **The stalk projection formula.** For a morphism of schemes `f : Y ⟶ X`, any derived tensor
product `T` on `Y` (Stacks 06YU), `M ∈ D(𝒪_Y)`, `K ∈ D(𝒪_X)` and `y : Y`, the stalk at `y` of
`M ⊗ᴸ Lf^*K`, read over `𝒪_{X, f y}`, is `M_y ⊗ᴸ_{𝒪_{X, f y}} K_{f y}`:

`res((M ⊗ᴸ Lf^*K)_y) ≅ res(M_y) ⊗ᴸ_{𝒪_{X,f y}} K_{f y}`.

Both arguments are replaced by K-flat representatives; the stalk of the tensor product is the
tensor product of the stalks, the stalk of `Lf^*K` is `𝒪_{Y,y} ⊗_{𝒪_{X,f y}} K_{f y}`
(Stacks 0098), and the chain-level projection formula
`res(L ⊗_{𝒪_{Y,y}} (𝒪_{Y,y} ⊗_{𝒪_{X,f y}} P)) = res(L) ⊗_{𝒪_{X,f y}} P` finishes. -/
def stalkDerivedTensorDerivedPullbackIso
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Y.toRingedSpace.sheaf)
    (M : DerivedCategory (OXMod.{u, u} Y.toRingedSpace))
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (ModuleCat.restrictScalars.{u}
        ((SemilinearStalk.commStalkRingEquiv Y.presheaf y).symm.toRingHom.comp
          (f.stalkMap y).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} Y.toRingedSpace) y).mapDerivedCategory.obj
            ((T.tensor.obj M).obj
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                f.toLRSHom.toShHom).obj K))) ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (ToType (X.presheaf.stalk (f.base y)))).tensor.obj
        ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv Y.presheaf y).symm.toRingHom.comp
            (f.stalkMap y).hom)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} Y.toRingedSpace) y).mapDerivedCategory.obj M))).obj
        ((ModuleCat.restrictScalars.{u}
            (SemilinearStalk.commStalkRingEquiv X.presheaf
              (f.base y)).symm.toRingHom).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} X.toRingedSpace) (f.base y)).mapDerivedCategory.obj K)) :=
  have hLm := (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise Y.sheaf
    (kFlatRep M)).1 (kFlatComplex_kFlatRep M) y
  have hP' := AlgebraicGeometry.kFlat_modulesStalkFunctor (f.base y) (kFlatRep K)
    (kFlatComplex_kFlatRep K)
  let eM :=
    (AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf y).mapDerivedCategory.mapIso
        (kFlatRepIso M).symm ≪≫
    (AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf y).mapDerivedCategoryFactors.app
      (kFlatRep M)
  (ModuleCat.restrictScalars.{u} (stalkMapRingCat f y)).mapDerivedCategory.mapIso
      (Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoOfDerivedTensorProduct
          Y.toRingedSpace.sheaf y T M
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj K) ≪≫
        ((Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor
            Y.toRingedSpace.sheaf y).mapIso eM).app _ ≪≫
        ((Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor
            Y.toRingedSpace.sheaf y).obj _).mapIso
          (derivedStalkDerivedPullbackRingCatIso f y K)) ≪≫
    CochainComplex.DerivedTensor.restrictScalarsTensorExtendScalarsIso (stalkMapRingCat f y)
      _ hLm _ hP' ≪≫
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        (ToType (X.presheaf.stalk (f.base y)))).tensor.mapIso
      ((ModuleCat.restrictScalars.{u} (stalkMapRingCat f y)).mapDerivedCategory.mapIso
        eM.symm)).app _ ≪≫
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        (ToType (X.presheaf.stalk (f.base y)))).tensor.obj _).mapIso (kFlatRepStalkIso K (f.base y))

/-- Restriction of scalars along a composite of ring maps, on derived categories, is the
composite of the restrictions. -/
def restrictScalarsCompDerivedIso {R₁ R₂ R₃ : Type u} [Ring R₁] [Ring R₂] [Ring R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (h : gf = g.comp f)
    (N : DerivedCategory (ModuleCat.{u} R₃)) :
    (ModuleCat.restrictScalars.{u} gf).mapDerivedCategory.obj N ≅
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj N) :=
  ((Functor.mapDerivedCategoryCompIsoOfCompIso
    (ModuleCat.restrictScalarsComp'.{u} f g gf h).symm).app N).symm

/-- **The pointwise Tor bound of a composite** (the hypothesis of
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_comp_derivedTensor_of_stalkBound`). By the
stalk projection formula `stalkDerivedTensorDerivedPullbackIso`, the stalk of `M ⊗ᴸ Lf^*K` at
`y`, read over `𝒪_{X, f y}`, is `M_y ⊗ᴸ_{𝒪_{X, f y}} K_{f y}`, and Stacks 0B66 along
`𝒪_{S, g (f y)} ⟶ 𝒪_{X, f y}` adds the two Tor-amplitude intervals. -/
theorem relativeStalkTensorBound {S : Scheme.{u}} (g : X ⟶ S)
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Y.toRingedSpace.sheaf) :
    RelativeStalkTensorBound g f T := by
  intro K M y a b c d hM hK
  have hring : (SemilinearStalk.commStalkRingEquiv Y.presheaf y).symm.toRingHom.comp
      ((f ≫ g).stalkMap y).hom = (stalkMapRingCat f y).comp (g.stalkMap (f.base y)).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  have hL := StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_derivedTensor
    (g.stalkMap (f.base y)).hom _ _ c d a b hM
    (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (restrictScalarsCompDerivedIso (g.stalkMap (f.base y)).hom
        (SemilinearStalk.commStalkRingEquiv X.presheaf (f.base y)).symm.toRingHom _ rfl _) a b hK)
  rw [add_comm a c, add_comm b d]
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars.{u} (g.stalkMap (f.base y)).hom).mapDerivedCategory.mapIso
        (stalkDerivedTensorDerivedPullbackIso f y T M K).symm ≪≫
      (restrictScalarsCompDerivedIso _ _ _ hring _).symm) _ _ hL

section RelativeTorBound

open Stacks.Cohomology.DerivedInternalHomPullback Stacks.Cohomology.HigherDirectImage

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X' X : Scheme.{u}}

/-- **A Tor-amplitude bound over the target bounds tensor products with pullbacks below.** Let
`h : X' ⟶ X` be a morphism of schemes and `U ⊆ X'` an open on which `F` has Tor amplitude in
`[a, d]` over `X` along `h`. Then for every `N ∈ D(𝒪_X)` with no cohomology below `b`, the
restriction to `U` of `F ⊗ᴸ Lh^*N` has no cohomology below `a + b`. At a point `u` of `U` the
stalk of `F ⊗ᴸ Lh^*N`, read over `𝒪_{X, h u}`, is `F_u ⊗ᴸ_{𝒪_{X, h u}} N_{h u}` by the stalk
projection formula, and `F_u` has Tor amplitude `≥ a` there. This is the bound asked for by the
relative Tor amplitude of `F` along `h` in the sheaf-level form of Stacks 0ATN (3). -/
theorem isGE_restrict_tensor_derivedPullback_of_hasTorAmplitudeOver (h : X' ⟶ X)
    (U : X'.Opens) (F : DerivedCategory X'.Modules) (a d : ℤ)
    (hF : HasTorAmplitudeOver (U.ι ≫ h)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj F) a d)
    (N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace)) (b : ℤ) (hN : N.IsGE b) :
    ((derivedPullbackFunctor (openSubspaceInclusion X'.toRingedSpace U)).obj
      ((internalHomTensorUncurried X'.toRingedSpace).obj
        (F, (derivedPullbackFunctor h.toLRSHom.toShHom).obj N))).IsGE (a + b) := by
  let FU := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj F
  let E := ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (U : Scheme.{u}).toRingedSpace.sheaf).tensor.obj FU).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (U.ι ≫ h).toLRSHom.toShHom).obj N)
  have hE : E.IsGE (a + b) := by
    refine isGE_of_forall_stalk (structureSheafOfRings.{u} (U : Scheme.{u}).toRingedSpace) E _
      fun u => ?_
    refine isGE_of_isGE_mapDerivedCategory_obj
      (ModuleCat.restrictScalars.{u}
        ((SemilinearStalk.commStalkRingEquiv (U : Scheme.{u}).presheaf u).symm.toRingHom.comp
          ((U.ι ≫ h).stalkMap u).hom))
      (isZero_of_isZero_restrictScalars _) _ _ ?_
    let := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.toRingedSpace.sheaf) ((U.ι ≫ h).base u)
    let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.toRingedSpace.sheaf) ((U.ι ≫ h).base u)
    let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.toRingedSpace.sheaf) ((U.ι ≫ h).base u)
    have hT := CochainComplex.DerivedTensor.isGE_canonicalTensor_of_hasTorAmplitudeCanonical
      _ _ a d b ((hasTorAmplitudeOver_iff_forall_derivedStalk (U.ι ≫ h) FU a d).1 hF u)
      (isGE_mapDerivedCategory_obj_of_isGE (ModuleCat.restrictScalars.{u}
          (SemilinearStalk.commStalkRingEquiv X.presheaf ((U.ι ≫ h).base u)).symm.toRingHom) _ _
        (isGE_mapDerivedCategory_obj_of_isGE (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.toRingedSpace.sheaf)
            ((U.ι ≫ h).base u)) N b hN))
    exact isGE_of_iso_of_isGE
      (stalkDerivedTensorDerivedPullbackIso (U.ι ≫ h) u _ FU N).symm (a + b) hT
  refine isGE_of_iso_of_isGE ?_ (a + b) hE
  exact ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (U : Scheme.{u}).toRingedSpace.sheaf).tensor.obj FU).mapIso
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        U.ι.toLRSHom.toShHom h.toLRSHom.toShHom).app N).symm ≪≫
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (U : Scheme.{u}).toRingedSpace.sheaf).tensor.mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback U.ι).app F)).app _ ≪≫
    (tensorBridge (U : Scheme.{u}).toRingedSpace).app
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          U.ι.toLRSHom.toShHom).obj F,
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback U.ι.toLRSHom.toShHom).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            h.toLRSHom.toShHom).obj N)) ≪≫
    ((pullbackTensorIso (openSubspaceInclusion X'.toRingedSpace U)).app
      (F, (derivedPullbackFunctor h.toLRSHom.toShHom).obj N)).symm

/-- **`L pr₁^*M|_{W'}` has Tor amplitude locally bounded below relative to `f × f : W' ⟶ W`**, in
the form asked for by the sheaf-level Stacks 0ATN (3): near every point of the diagonal open `W'`
of `f ≫ g` there are an open `U` and an integer `a` such that for every `N ∈ D(𝒪_W)` with no
cohomology below `b`, `(L pr₁^*M ⊗ᴸ L(f × f)^*N)|_U` has no cohomology below `a + b`. -/
theorem DiagonalOpen.exists_isGE_restrict_tensor_derivedPullbackProj
    {S : Scheme.{u}} {g : X ⟶ S} {f : X' ⟶ X} [Flat f] [LocallyOfFinitePresentation f]
    (Dg : Scheme.Hom.DiagonalOpen g) (Df : Scheme.Hom.DiagonalOpen f)
    (M : DerivedCategory X'.Modules)
    (hM : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage X.toRingedSpace f.base)) M) :
    ∀ w : (Dg.comp Df).W.carrier, ∃ U : TopologicalSpace.Opens (Dg.comp Df).W.carrier, w ∈ U ∧
      ∃ a : ℤ, ∀ (N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
          Dg.W.toRingedSpace)) (b : ℤ), N.IsGE b →
        ((derivedPullbackFunctor (openSubspaceInclusion (Dg.comp Df).W.toRingedSpace U)).obj
          ((internalHomTensorUncurried (Dg.comp Df).W.toRingedSpace).obj
            ((Dg.comp Df).derivedPullbackProj M,
              (derivedPullbackFunctor (Dg.compProd Df).toLRSHom.toShHom).obj N))).IsGE (a + b) := by
  intro w
  obtain ⟨U, hwU, c, d, hcd⟩ := Dg.exists_hasTorAmplitudeOver_compProd Df M hM w
  exact ⟨U, hwU, c, fun N b hN =>
    isGE_restrict_tensor_derivedPullback_of_hasTorAmplitudeOver (Dg.compProd Df) U _ c d hcd N b hN⟩

end RelativeTorBound

end ProjectionFormula

end AlgebraicGeometry.Scheme.Hom

end
