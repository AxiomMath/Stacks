module

public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.ProperSmoothLocalModel
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.Global
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDegreeZeroDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedPullbackAdditive

/-!
# The derived direct image of the structure sheaf of a proper smooth morphism

Let `f : X ⟶ S` be a proper smooth morphism of schemes. Locally on `S`,

`Rf_*𝒪_X ≅ f_*𝒪_X ⊕ P`

in `D(𝒪_S)`, with `P` perfect of Tor amplitude in `[1, ∞)`.

## Main results

* `AlgebraicGeometry.nonempty_derivedPullback_derivedPushforward_unit_iso`: the formation of
  `Rf_*𝒪_X` commutes with base change for a flat, quasi-compact and separated `f`.
* `AlgebraicGeometry.nonempty_derivedPushforward_iso_tilde`: over an affine base `Spec B`,
  `Rf_*𝒢` is the sheaf associated with `RΓ(X, 𝒢)` for `𝒢` quasi-coherent ([Stacks, Tag 06Z0]
  with Leray).
* `AlgebraicGeometry.exists_nhds_derivedPushforward_unit_iso_biprod`: the decomposition.

## Implementation notes

Over an affine open `V` of `S` inside the neighbourhood of
`exists_nhds_globalFunctions_finiteEtale_and_split` (in the namespace
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections`) the base change `X'` of `X` to
`Spec Γ(S, V)` has `RΓ(X', 𝒪) ≅ Γ(S, V)^r[0] ⊕ K` with `K` a bounded complex of finite free
modules in degrees `≥ 1`. Sheafifying on `Spec Γ(S, V)`, moving to `V` along `V ≅ Spec Γ(S, V)`,
and using base change along `Spec Γ(S, V) ⟶ S` gives `(Rf_*𝒪_X)|_V ≅ N ⊕ P` with `N`
concentrated in degree `0` and `P` perfect of Tor amplitude in `[1, b]`. The summand `N` is then
the degree-zero cohomology `f_*𝒪_X|_V`.

All derived categories are taken at the standard model `HasDerivedCategory.standard`, the model
of the base-change, Leray and Čech results this file uses; the scope
`Stacks.StandardDerivedModel` fixes it for every spelling of the categories of modules involved.

## References

* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
* [Stacks Project, Tag 0G8H](https://stacks.math.columbia.edu/tag/0G8H)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Modules (toShHom_comm)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.AlgebraicGeometry.FlatSourceBaseChange StrictlyPerfect

universe u

namespace AlgebraicGeometry

/-- A biproduct whose second summand is a zero object is its first summand, via the
projection. -/
def biprodIsoFstOfIsZeroSnd {C : Type*} [Category C] [Preadditive C] {X Y : C}
    [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ⊞ Y ≅ X where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := biprod.hom_ext' _ _ (by simp) (hY.eq_of_src _ _)
  inv_hom_id := biprod.inl_fst

/-- **A decomposition off a degree-zero object identifies that object with the degree-zero
cohomology.** If `E ≅ N ⊕ P` in `D(C)` with `N` concentrated in degree `0` and `P` in degrees
`≥ 1`, then `E ≅ H⁰(E)[0] ⊕ P`. -/
theorem DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_zero_biprod {C : Type*}
    [Category C] [Abelian C] [HasDerivedCategory C] {E N P : DerivedCategory C} (e : E ≅ N ⊞ P)
    [N.IsGE 0] [N.IsLE 0] (hP : P.IsGE 1) :
    Nonempty (E ≅ (DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C 0).obj E) ⊞ P) := by
  obtain ⟨eN⟩ := N.nonempty_iso_singleFunctor_homologyFunctor 0
  have : PreservesBinaryBiproducts (DerivedCategory.homologyFunctor C 0) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let eH : (DerivedCategory.homologyFunctor C 0).obj E ≅
      (DerivedCategory.homologyFunctor C 0).obj N :=
    (DerivedCategory.homologyFunctor C 0).mapIso e ≪≫
      (DerivedCategory.homologyFunctor C 0).mapBiprod N P ≪≫
        biprodIsoFstOfIsZeroSnd ((P.isGE_iff 1).1 hP 0 (by omega))
  exact ⟨e ≪≫ biprod.mapIso (eN ≪≫ (DerivedCategory.singleFunctor C 0).mapIso eH.symm)
    (Iso.refl P)⟩

/-- **Derived pullback preserves binary biproducts.** An isomorphism `E ≅ A ⊕ B` in `D(𝒪_Y)`
gives `Lh^*E ≅ Lh^*A ⊕ Lh^*B` in `D(𝒪_X)`. -/
theorem nonempty_derivedPullback_iso_biprod {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    {E A B : DerivedCategory (OXMod.{u, u} Y)} (e : E ≅ A ⊞ B) :
    Nonempty (((derivedPullback h).obj E : DerivedCategory (OXMod.{u, u} X)) ≅
      ((derivedPullback h).obj A : DerivedCategory (OXMod.{u, u} X)) ⊞
        ((derivedPullback h).obj B : DerivedCategory (OXMod.{u, u} X))) := by
  let F : DerivedCategory (OXMod.{u, u} Y) ⥤ DerivedCategory (OXMod.{u, u} X) := derivedPullback h
  have : F.Additive := Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive h
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts _
  exact ⟨F.mapIso e ≪≫ F.mapBiprod A B⟩

/-- The structure sheaf `𝒪_Y` placed in degree zero, as an object of `D(𝒪_Y)`. -/
abbrev structureSheafDegreeZeroObj (Y : Scheme.{u}) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
      (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))))

/-- **Base change for `Rf_*𝒪_X`.** For a cartesian square with `f` flat, quasi-compact and
separated, `Lg^* Rf_*𝒪_X ≅ Rf'_*𝒪_{X'}`: the derived base change map of Stacks 08HY at `𝒪_X`,
followed by `Rf'_*` of the identification `L(g')^*𝒪_X ≅ 𝒪_{X'}`. -/
theorem nonempty_derivedPullback_derivedPushforward_unit_iso {X S X' S' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [IsSeparated f] [Flat f] :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj (structureSheafDegreeZeroObj X)) ≅
      (derivedPushforward f'.toLRSHom.toShHom).obj (structureSheafDegreeZeroObj X')) := by
  have hbc := isIso_derivedBaseChangeMap_single hsq
    ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩ (isFlatOver_unit_of_flat f)
    (Stacks.Cohomology.DerivedPullbackUnit.isFlat_unit X.toRingedSpace)
  have hcomp := isIso_derivedPullbackComparison_single_of_isFlat g'.toLRSHom.toShHom
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (Stacks.Cohomology.DerivedPullbackUnit.isFlat_unit X.toRingedSpace)
  exact ⟨@asIso _ _ _ _ (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm hsq.w)
      (structureSheafDegreeZeroObj X)) hbc ≪≫
    (derivedPushforward f'.toLRSHom.toShHom).mapIso
      (asIso ((derivedPullbackComparison g'.toLRSHom.toShHom).app _) ≪≫
        DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (modulePullback g'.toLRSHom.toShHom)
              (ComplexShape.up ℤ) 0).app
                (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) ≪≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
              (modulePullbackObjUnitIso g'.toLRSHom.toShHom))))⟩

/-- **Base change for `Rf_*𝒪_X`, in the spelling of `Scheme.Modules`.** -/
theorem nonempty_derivedPullback_derivedPushforwardModules_unit_iso {X S X' S' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [IsSeparated f] [Flat f] :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.unitModule X))) ≅
      (derivedPushforwardModules f').obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj (Scheme.unitModule X'))) := by
  obtain ⟨e⟩ := nonempty_derivedPullback_derivedPushforward_unit_iso hsq
  exact ⟨(derivedPullback g.toLRSHom.toShHom).mapIso
    ((derivedPushforward f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))).app _).symm) ≪≫ e ≪≫
    (derivedPushforward f'.toLRSHom.toShHom).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))).app _)⟩

/-- **Over an affine base, the derived direct image is the sheaf associated with the derived
global sections.** For `f' : X' ⟶ Spec B` quasi-compact and quasi-separated and `𝒢` a
quasi-coherent `𝒪_{X'}`-module, `Rf'_*𝒢 ≅ RΓ(X', 𝒢)^~` in `D(𝒪_{Spec B})`: `Rf'_*𝒢` has
quasi-coherent cohomology ([Stacks, Tag 01XJ]), hence is `M̃` for some `M` in `D(B)`
([Stacks, Tag 06Z0]), and `M ≅ RΓ(Spec B, M̃) ≅ RΓ(X', 𝒢)` by the unit of the derived Spec–Γ
adjunction and Leray ([Stacks, Tag 0D5W]). -/
theorem nonempty_derivedPushforward_iso_tilde {B : Type u} [CommRing B] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of B)) [QuasiCompact f'] [QuasiSeparated f'] (G : X'.Modules)
    [G.IsQuasicoherent] :
    Nonempty ((derivedPushforwardModules f').obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj G) ≅
      (tilde.functor (.of B)).mapDerivedCategory.obj
        ((derivedGlobalSectionsOver f').obj
          ((DerivedCategory.singleFunctor X'.Modules 0).obj G))) := by
  let E := (derivedPushforwardModules f').obj ((DerivedCategory.singleFunctor X'.Modules 0).obj G)
  obtain ⟨M, ⟨eM⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (.of B) E
    (isQuasicoherent_homology_derivedPushforward_single_zero f' G ‹_›)
  have := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit (.of B)
  let eu : M ≅ (derivedGlobalSectionsOver (𝟙 (Spec (.of B)))).obj
      ((derivedTilde (.of B) ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec (.of B)).Modules)
        (SheafOfModules.isQuasicoherent (Spec (.of B)).ringCatSheaf)).ι).obj M) :=
    asIso ((derivedTildeGlobalSectionsAdjunction (.of B)).val.unit.app M)
  let e' : M ≅ (derivedGlobalSectionsOver f').obj
      ((DerivedCategory.singleFunctor X'.Modules 0).obj G) :=
    eu ≪≫ (derivedGlobalSectionsOver (𝟙 (Spec (.of B)))).mapIso
      ((derivedTildeCompι (.of B)).app M ≪≫ eM) ≪≫
      ((derivedGlobalSectionsOverPushforwardIso f').app _).symm
  exact ⟨eM.symm ≪≫ (tilde.functor (.of B)).mapDerivedCategory.mapIso e'⟩

/-- **A sum of a degree-zero piece and a perfect piece in degrees `≥ 1`.** If `F ≅ N ⊕ P` in
`D(𝒪_Z)` with `N` of Tor amplitude in `[0, 0]` and `P` of Tor amplitude in `[1, b]`, and
`H⁰(F) ≅ M₀`, then `F ≅ M₀[0] ⊕ P`. -/
theorem nonempty_iso_singleFunctor_biprod_of_hasTorAmplitude {Z : RingedSpace.{u, u}}
    {F' F N P : DerivedCategory (OXMod.{u, u} Z)} {M₀ : OXMod.{u, u} Z} {b : ℤ}
    (hN : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Z N 0 0)
    (hP : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Z P 1 b) (e₀ : F' ≅ F) (e : F ≅ N ⊞ P)
    (eH : (DerivedCategory.homologyFunctor (OXMod.{u, u} Z) 0).obj F ≅ M₀) :
    Nonempty (F' ≅ (DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj M₀ ⊞ P) := by
  have hGE : ∀ {M : DerivedCategory (OXMod.{u, u} Z)} {a b : ℤ},
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Z M a b → M.IsGE a := fun h =>
    Stacks.Cohomology.TorAmplitude.isGE_of_hasTorAmplitudeGE Z _ _
      (Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_hasTorAmplitude Z _ _ _ h)
  have := hGE hN
  have : N.IsLE 0 := (DerivedCategory.isLE_iff _ 0).2 fun i hi =>
    Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isZero_homology_of_hasTorAmplitude
      _ 0 0 hN i (by simp; omega)
  obtain ⟨e'⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_zero_biprod e (hGE hP)
  exact ⟨e₀ ≪≫ e' ≪≫ biprod.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eH) (Iso.refl P)⟩

/-- **The pullback of a perfect `M̃` along an isomorphism onto `Spec R` is perfect.** -/
theorem isPerfect_derivedPullback_tilde {Z : RingedSpace.{u, u}} {R : CommRingCat.{u}}
    (φ : Z ≅ (Spec R).toRingedSpace) (M : DerivedCategory (ModuleCat.{u} R))
    (hM : StacksDraft.Perfect.IsPerfect M) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z)
      ((derivedPullback φ.hom).obj ((tilde.functor R).mapDerivedCategory.obj M)) :=
  (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff φ _).2
    ((isPerfect_tilde_iff M).2 hM)

/-- **The pullback of `M̃` along an isomorphism onto `Spec R` has the Tor amplitude of `M`.** -/
theorem hasTorAmplitude_derivedPullback_tilde {Z : RingedSpace.{u, u}} {R : CommRingCat.{u}}
    (φ : Z ≅ (Spec R).toRingedSpace) (M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hM : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R M a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude Z
      ((derivedPullback φ.hom).obj ((tilde.functor R).mapDerivedCategory.obj M)) a b :=
  (Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_iff φ _ a b).2
    ((hasTorAmplitude_tilde_iff M a b).2 hM)

/-- The isomorphism `V ≅ Spec Γ(S, V)` of an affine open, read on the underlying ringed spaces. -/
def isoSpecRingedSpaceIso {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V) :
    S.toRingedSpace.restrict V.isOpenEmbedding ≅ (Spec (CommRingCat.of Γ(S, V))).toRingedSpace where
  hom := hV.isoSpec.hom.toLRSHom.toShHom
  inv := hV.isoSpec.inv.toLRSHom.toShHom
  hom_inv_id := by
    change (hV.isoSpec.hom ≫ hV.isoSpec.inv).toLRSHom.toShHom = _
    rw [Iso.hom_inv_id]
    rfl
  inv_hom_id := by
    change (hV.isoSpec.inv ≫ hV.isoSpec.hom).toLRSHom.toShHom = _
    rw [Iso.inv_hom_id]
    rfl

/-- **A flat module in degree zero has Tor amplitude in `[0, 0]`.** -/
theorem hasTorAmplitudeCanonical_singleFunctor_of_flat {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) [Module.Flat R M] :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) 0 0 :=
  (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ 0 0).2
    ⟨(HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M,
      fun i => by
        obtain rfl | hi := eq_or_ne i 0
        · exact Module.Flat.of_linearEquiv
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).toLinearEquiv
        · have := ModuleCat.subsingleton_of_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
          have := Module.Free.of_subsingleton R
            (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).X i)
          exact Module.Flat.of_free,
      inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-- **The restriction of `Rf_*𝒪_X` to an affine open, from the derived global sections of the
base change.** Let `V` be an affine open of `S` and let `X'` be the base change of `X` along
`Spec Γ(S, V) ⟶ S`, with `RΓ(X', 𝒪_{X'}) ≅ A ⊕ B` in `D(Γ(S, V))`. Then
`(Rf_*𝒪_X)|_V ≅ Lφ^*Ã ⊕ Lφ^*B̃`, where `φ : V ≅ Spec Γ(S, V)`. -/
theorem nonempty_derivedRestrictModules_derivedPushforward_iso_biprod {X S X' : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Smooth f] {V : S.Opens} (hV : IsAffineOpen V)
    {f' : X' ⟶ Spec (.of Γ(S, V))} {j : X' ⟶ X} (hsq : IsPullback j f' f hV.fromSpec)
    {A B : DerivedCategory (ModuleCat.{u} Γ(S, V))}
    (eR : (derivedGlobalSectionsOver f').obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj (Scheme.unitModule X')) ≅ A ⊞ B) :
    Nonempty ((RingedSpace.derivedRestrictModules S.toRingedSpace V).obj
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.unitModule X))) ≅
      (derivedPullback (isoSpecRingedSpaceIso hV).hom).obj
        ((tilde.functor (CommRingCat.of Γ(S, V))).mapDerivedCategory.obj (A ⊞ B))) := by
  have : IsProper f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  let eV := isoSpecRingedSpaceIso hV
  -- on `Spec Γ(S, V)`: `Rf'_*𝒪_{X'} ≅ (A ⊕ B)~`
  let e₁ := (nonempty_derivedPushforward_iso_tilde f' (Scheme.unitModule X')).some ≪≫
    (tilde.functor (CommRingCat.of Γ(S, V))).mapDerivedCategory.mapIso eR
  -- base change along `Spec Γ(S, V) ⟶ S`
  let e₂ := (nonempty_derivedPullback_derivedPushforwardModules_unit_iso
    (hsq : IsPullback j f' f (hV.isoSpec.inv ≫ V.ι))).some ≪≫ e₁
  -- from `Spec Γ(S, V)` to `V`
  let E := (derivedPushforwardModules f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.unitModule X))
  exact ⟨(Scheme.Modules.derivedRestrictModulesIsoDerivedPullback S V).app E ≪≫
    ((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackInvHomIso eV).app
      ((derivedPullback V.ι.toLRSHom.toShHom).obj E)).symm ≪≫
    (derivedPullback eV.hom).mapIso
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical eV.inv
        V.ι.toLRSHom.toShHom).app E ≪≫ e₂)⟩

/-- **The degree-zero cohomology of `(Rf_*𝒪_X)|_V` is `(f_*𝒪_X)|_V`.** -/
def derivedRestrictModulesHomologyZeroIso {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (V : S.Opens) :
    (DerivedCategory.homologyFunctor
        (OXMod.{u, u} (S.toRingedSpace.restrict V.isOpenEmbedding)) 0).obj
        ((RingedSpace.derivedRestrictModules S.toRingedSpace V).obj
          ((derivedPushforwardModules f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.unitModule X)))) ≅
      (RingedSpace.restrictModules S.toRingedSpace V).obj
        ((Scheme.Modules.pushforward f).obj (Scheme.unitModule X)) :=
  RingedSpace.derivedRestrictModulesHomologyIso V 0 _ ≪≫
    (RingedSpace.restrictModules S.toRingedSpace V).mapIso
      ((ProperFlatFibreEulerCharacteristic.hdiIsoHomologyDerivedPushforwardModule
        f (Scheme.unitModule X) 0).symm ≪≫
        (Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.app _)

/-- **The decomposition over one affine open.** Let `V` be an affine open of `S` over which the
base change `X'` of `X` to `Spec Γ(S, V)` has `RΓ(X', 𝒪_{X'}) ≅ Γ(S, V)^r[0] ⊕ K` with `K` a
complex of finite free modules in degrees `[1, b]`. Then `(Rf_*𝒪_X)|_V ≅ (f_*𝒪_X)|_V ⊕ P` with `P`
perfect of Tor amplitude in `[1, ∞)`. -/
theorem exists_derivedRestrictModules_derivedPushforward_unit_iso_biprod_of_isAffineOpen
    {X S X' : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] {V : S.Opens} (hV : IsAffineOpen V)
    {f' : X' ⟶ Spec (.of Γ(S, V))} {j : X' ⟶ X} (hsq : IsPullback j f' f hV.fromSpec) (r : ℕ)
    {b : ℤ} (K : CochainComplex (ModuleCat.{u} Γ(S, V)) ℤ) [K.IsStrictlyGE 1] [K.IsStrictlyLE b]
    (hKfree : ∀ i, Module.Free Γ(S, V) (K.X i) ∧ Module.Finite Γ(S, V) (K.X i))
    (eR : (derivedGlobalSectionsOver f').obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj (Scheme.unitModule X')) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(S, V)) 0).obj
          (ModuleCat.of Γ(S, V) (Fin r → Γ(S, V))) ⊞ DerivedCategory.Q.obj K) :
    ∃ P : DerivedCategory (OXMod.{u, u} (S.toRingedSpace.restrict V.isOpenEmbedding)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect P ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE
        (S.toRingedSpace.restrict V.isOpenEmbedding) P 1 ∧
      Nonempty ((RingedSpace.derivedRestrictModules S.toRingedSpace V).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj (structureSheafDegreeZeroObj X)) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((RingedSpace.restrictModules S.toRingedSpace V).obj
            ((Scheme.Modules.pushforward f).obj (Scheme.unitModule X))) ⊞ P) := by
  obtain ⟨hfree, hfin⟩ := forall_and.1 hKfree
  have hKperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj K) :=
    ⟨K, 1, b, inferInstance, inferInstance, hfin, fun i => inferInstance, ⟨Iso.refl _⟩⟩
  have hKtor : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ(S, V)
      (DerivedCategory.Q.obj K) 1 b :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ 1 b).2
      ⟨K, fun i => inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  obtain ⟨e₃⟩ := nonempty_derivedRestrictModules_derivedPushforward_iso_biprod f hV hsq eR
  let T := (tilde.functor (CommRingCat.of Γ(S, V))).mapDerivedCategory
  have : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBiproducts _
  let eV := isoSpecRingedSpaceIso hV
  let e₄ := e₃ ≪≫ (nonempty_derivedPullback_iso_biprod eV.hom
    (T.mapBiprod _ _)).some
  have hPtor := hasTorAmplitude_derivedPullback_tilde eV _ 1 b hKtor
  exact ⟨_, isPerfect_derivedPullback_tilde eV _ hKperf,
    Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_hasTorAmplitude _ _ 1 b hPtor,
    nonempty_iso_singleFunctor_biprod_of_hasTorAmplitude
      (hasTorAmplitude_derivedPullback_tilde eV _ 0 0
        (hasTorAmplitudeCanonical_singleFunctor_of_flat
          (ModuleCat.of Γ(S, V) (Fin r → Γ(S, V))))) hPtor
      ((RingedSpace.derivedRestrictModules S.toRingedSpace V).mapIso
        ((derivedPushforward f.toLRSHom.toShHom).mapIso
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))).app _))) e₄
      (derivedRestrictModulesHomologyZeroIso f V)⟩

/-- **`Rf_*𝒪_X` of a proper smooth morphism splits off `f_*𝒪_X` locally on the base.** For
`f : X ⟶ S` proper and smooth and `s ∈ S` there are an open neighbourhood `U` of `s` and a perfect
object `P` of `D(𝒪_U)` of Tor amplitude in `[1, ∞)` with

`(Rf_*𝒪_X)|_U ≅ (f_*𝒪_X)|_U ⊕ P`

in `D(𝒪_U)`. -/
theorem exists_nhds_derivedPushforward_unit_iso_biprod {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] (s : S) :
    ∃ (U : S.Opens) (_ : s ∈ U)
      (P : DerivedCategory (OXMod.{u, u} (S.toRingedSpace.restrict U.isOpenEmbedding))),
      Stacks.Cohomology.PerfectComplexes.IsPerfect P ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE
        (S.toRingedSpace.restrict U.isOpenEmbedding) P 1 ∧
      Nonempty ((RingedSpace.derivedRestrictModules S.toRingedSpace U).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj (structureSheafDegreeZeroObj X)) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((RingedSpace.restrictModules S.toRingedSpace U).obj
            ((Scheme.Modules.pushforward f).obj (Scheme.unitModule X))) ⊞ P) := by
  obtain ⟨G, hsG, r, b, H⟩ := open Stacks.AlgebraicGeometry.ProperFlatGlobalSections in
    exists_nhds_globalFunctions_finiteEtale_and_split f s
  obtain ⟨V, hV, hsV, hVG⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := G) hsG
  obtain ⟨X', f', j, hsq, -, K, hK1, hKb, hKfree, ⟨eR⟩⟩ := H V hV hVG
  exact ⟨V, hsV,
    exists_derivedRestrictModules_derivedPushforward_unit_iso_biprod_of_isAffineOpen f hV hsq r
      (b := b) K hKfree eR⟩

end AlgebraicGeometry

end
