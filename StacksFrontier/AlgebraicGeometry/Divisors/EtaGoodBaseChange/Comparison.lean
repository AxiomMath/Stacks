module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatIdealTorsionFree
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorProductCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.ResolvingDatumUnconditional

/-!
# The unconditional chain-level comparison for the décalage under pullback

Let `h : Y ⟶ X` be a morphism of schemes, let `D ⊆ X` be an effective Cartier divisor with
ideal sheaf `I = ℐ_D`, and suppose the pullback `E = h^{-1}D` is defined, with ideal sheaf
`J = ℐ_E`.  For a complex `𝒦` of flat `𝒪_X`-modules this file builds the chain-level comparison

`h^*(η_I 𝒦) ⟶ η_J(h^* 𝒦)`

with **no flatness hypothesis on `h`**.  It is the composite of
`Stacks.IdealTorsion.Eta.pullbackEtaMap`, which compares with the décalage by the pulled-back
ideal `h^*I`, and the transport `Stacks.IdealTorsion.Eta.IdealCongr.etaIso` along the
identification `h^*ℐ_D ≅ ℐ_E` of `Stacks.Divisors.pullbackIdealSheafComapIso`.  Both are
defined because the terms of `𝒦` and of `h^*𝒦` are torsion free for the relevant ideals.

## Main results

* `Stacks.Divisors.Eta.mono_pullbackIdealIncl_of_isPullbackDefined`: the inclusion
  `h^*ℐ_D ⟶ 𝒪_Y` is a monomorphism as soon as `h^{-1}D` is defined.
* `Stacks.Divisors.Eta.isIdealTorsionFree_of_isFlat_divisor`: a flat `𝒪_X`-module has no
  `ℐ_D`-torsion.
* `Stacks.Divisors.Eta.etaPullbackChainMap`: the comparison.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)
open Stacks.IdealTorsion (IsIdealTorsionFree)
open Stacks.IdealTorsion.Eta (pullbackIdealIncl pullbackComplex etaObj)

universe u

namespace Stacks.Divisors.Eta

/-- Sheaves of modules on a ringed space form an abelian category, restated at the spelling of
the structure sheaf that the degreewise pullback of complexes is written in; instance search
does not find `SheafOfModules.instAbelian` there once the décalage files are in scope. -/
instance abelianModulePullbackTarget (W : RingedSpace.{u, u}) :
    Abelian (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)) :=
  SheafOfModules.instAbelian _

/-- The same restatement at the `structureRingSheaf` spelling, which is the one the pullback
functor of `Stacks.RingedSpace.pullbackFunctor` is typed over. -/
instance abelianStructureRingSheaf (W : RingedSpace.{u, u}) :
    Abelian (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf W)) :=
  SheafOfModules.instAbelian _

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **The inclusion `h^*ℐ_D ⟶ 𝒪_Y` is a monomorphism whenever `h^{-1}D` is defined.** -/
theorem mono_pullbackIdealIncl_of_isPullbackDefined
    (hD : Stacks.Divisors.IsPullbackDefined h D) :
    Mono (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D)) := by
  have : Mono (Stacks.Divisors.pullbackIdealSheafComapIso h D hD).hom :=
    ((Stacks.Divisors.pullbackIdealSheafComapIso h D hD).isIso_hom).mono_of_iso
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  -- `idealSheafι (D.comap h)` is indexed by the `FullSubcategory.mk` spelling of the structure
  -- sheaf and this composite by the `Scheme.sheaf` one, so `Mono (idealSheafι (D.comap h))` is
  -- not synthesized here although the instance is in scope; it is given by name.
  have hmono : Mono ((Stacks.Divisors.pullbackIdealSheafComapIso h D hD).hom ≫
      idealSheafι (D.comap h)) :=
    @CategoryTheory.mono_comp _ _ _ _ _ _ inferInstance _ (mono_idealSheafι (D.comap h))
  rwa [Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD] at hmono

/-- **A flat `𝒪_X`-module has no `ℐ_D`-torsion.** -/
theorem isIdealTorsionFree_of_isFlat_divisor (F : X.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    IsIdealTorsionFree X.toRingedSpace (idealSheafι D) F :=
  @Stacks.IdealTorsion.isIdealTorsionFree_of_isFlat X.toRingedSpace _
    (idealSheafι D) (mono_idealSheafι D)
    (@Stacks.IdealTorsion.isLocallyGeneratedByRegular_of_isInvertible X.toRingedSpace
      inferInstance _ (idealSheafι D) (mono_idealSheafι D)
      (isInvertible_idealSheaf D)) F hF

/-- **The pullback of a flat module has no `h^*ℐ_D`-torsion**, as soon as `h^{-1}D` is
defined. -/
theorem isIdealTorsionFree_pullbackIdealIncl_of_isFlat
    (hD : Stacks.Divisors.IsPullbackDefined h D) (F : X.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    IsIdealTorsionFree Y.toRingedSpace
      (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D))
      ((pullbackFunctor h.toLRSHom.toShHom).obj F) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  refine (Stacks.IdealTorsion.Eta.IdealCongr.isIdealTorsionFree_congr Y.toRingedSpace
    (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D))
    (idealSheafι (D.comap h)) (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD) _).2 ?_
  exact isIdealTorsionFree_of_isFlat_divisor (D.comap h) _
    (Stacks.SheafOfModules.modulePullback_isFlat h.toLRSHom.toShHom F hF)

variable (hD : Stacks.Divisors.IsPullbackDefined h D) (𝒦 : CochainComplex X.Modules ℤ)
  (hflat : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (𝒦.X n))

include hflat in
/-- The terms of a complex of flat `𝒪_X`-modules have no `ℐ_D`-torsion, so its chain-level
décalage is defined. -/
theorem isIdealTorsionFree_flatComplex (n : ℤ) :
    IsIdealTorsionFree X.toRingedSpace (idealSheafι D) (𝒦.X n) :=
  isIdealTorsionFree_of_isFlat_divisor D (𝒦.X n) (hflat n)

include hD hflat in
/-- The terms of the pullback of a complex of flat `𝒪_X`-modules have no `h^*ℐ_D`-torsion, so
the chain-level décalage of the pullback by the pulled-back ideal is defined. -/
theorem isIdealTorsionFree_pullback_flatComplex (n : ℤ) :
    IsIdealTorsionFree Y.toRingedSpace
      (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D))
      ((pullbackComplex h.toLRSHom.toShHom 𝒦).X n) :=
  isIdealTorsionFree_pullbackIdealIncl_of_isFlat h D hD (𝒦.X n) (hflat n)

omit [IsEffectiveCartierDivisor D] in
include hD hflat in
/-- The terms of the pullback of a complex of flat `𝒪_X`-modules have no `ℐ_E`-torsion. -/
theorem isIdealTorsionFree_pullback_flatComplex' (n : ℤ) :
    IsIdealTorsionFree Y.toRingedSpace (idealSheafι (D.comap h))
      ((pullbackComplex h.toLRSHom.toShHom 𝒦).X n) :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  isIdealTorsionFree_of_isFlat_divisor (D.comap h) _
    (Stacks.SheafOfModules.modulePullback_isFlat h.toLRSHom.toShHom (𝒦.X n) (hflat n))

/-- **The unconditional chain-level comparison `h^*(η_ℐ 𝒦) ⟶ η_𝒥(h^* 𝒦)`**, for `𝒦` a complex
of flat `𝒪_X`-modules and `h` an arbitrary morphism of schemes along which the pullback of the
divisor is defined.

It is `Stacks.IdealTorsion.Eta.pullbackEtaMap`, which compares with the décalage by the
pulled-back ideal `h^*ℐ_D` and carries no flatness hypothesis, followed by the transport
`Stacks.IdealTorsion.Eta.IdealCongr.etaIso` along the identification `h^*ℐ_D ≅ ℐ_E`.  Stacks
tag 0F9X is the assertion that this comparison is a quasi-isomorphism when the triple is
good. -/
def etaPullbackChainMap :
    pullbackComplex h.toLRSHom.toShHom
        (etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) 𝒦
          (isIdealTorsionFree_flatComplex D 𝒦 hflat)) ⟶
      etaObj Y.toRingedSpace (idealSheaf (D.comap h)) (idealSheafι (D.comap h))
        (pullbackComplex h.toLRSHom.toShHom 𝒦)
        (isIdealTorsionFree_pullback_flatComplex' h D hD 𝒦 hflat) :=
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  -- `pullbackEtaMap` and `pullbackIdealIncl` are indexed by `Tensor.ringSheaf X.sheaf` whereas
  -- `idealSheaf`/`idealSheafι` are indexed by `Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩`, so the
  -- two `Mono` instances are not synthesized at these applications although both are in scope;
  -- each is applied with `@` and the instances given by name, the application itself unifying
  -- the spellings at default transparency.
  @Stacks.IdealTorsion.Eta.pullbackEtaMap _ _ h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D)
        (mono_idealSheafι D) (isInvertible_idealSheaf D)
        (mono_pullbackIdealIncl_of_isPullbackDefined h D hD) 𝒦
      (isIdealTorsionFree_flatComplex D 𝒦 hflat)
      (isIdealTorsionFree_pullback_flatComplex h D hD 𝒦 hflat) ≫
    (@Stacks.IdealTorsion.Eta.IdealCongr.etaIso Y.toRingedSpace
      ((pullbackFunctor h.toLRSHom.toShHom).obj (idealSheaf D)) (idealSheaf (D.comap h))
      inferInstance inferInstance
      (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D))
      (idealSheafι (D.comap h)) (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
      (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD)
      (pullbackComplex h.toLRSHom.toShHom 𝒦)
      (mono_pullbackIdealIncl_of_isPullbackDefined h D hD) (mono_idealSheafι (D.comap h))
      (isIdealTorsionFree_pullback_flatComplex h D hD 𝒦 hflat)
      (isIdealTorsionFree_pullback_flatComplex' h D hD 𝒦 hflat)).hom

/-! ### Passage to the derived category -/

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

include hD hflat in
/-- **From the chain-level comparison to the derived one.**  Let `𝒦` be a K-flat complex of
flat `𝒪_X`-modules and let `p : P ⟶ η_ℐ𝒦` be a quasi-isomorphism from a K-flat complex.  If
the composite `h^*P ⟶ h^*(η_ℐ𝒦) ⟶ η_𝒥(h^*𝒦)` is a quasi-isomorphism, then

`Lh^*(Lη_ℐ [𝒦]) ≅ Lη_𝒥(Lh^* [𝒦])`

in `D(𝒪_Y)`. -/
theorem nonempty_derivedPullback_derivedEta_iso_of_quasiIso
    (h𝒦 : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace 𝒦)
    (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace P)
    (p : P ⟶ etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) 𝒦
      (isIdealTorsionFree_flatComplex D 𝒦 hflat))
    (hp : QuasiIso p)
    (hΨ : QuasiIso ((((pullbackFunctor h.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map p) ≫ etaPullbackChainMap h D hD 𝒦 hflat)) :
    Nonempty ((derivedPullback h.toLRSHom.toShHom).obj
        ((derivedEtaData D).functor.obj (DerivedCategory.Q.obj 𝒦)) ≅
      (derivedEtaData (D.comap h)).functor.obj
        ((derivedPullback h.toLRSHom.toShHom).obj (DerivedCategory.Q.obj 𝒦))) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  have := hp
  have := hΨ
  let e₁ : (derivedEtaData D).functor.obj (DerivedCategory.Q.obj 𝒦) ≅
      DerivedCategory.Q.obj P :=
    (derivedEtaData D).objIso 𝒦 (isIdealTorsionFree_flatComplex D 𝒦 hflat) ≪≫
      (@asIso _ _ _ _ (DerivedCategory.Q.map p)
        ((DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp)).symm
  let e₂ := Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat
    h.toLRSHom.toShHom P hP
  let e₃ := Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat
    h.toLRSHom.toShHom 𝒦 h𝒦
  let e₄ := (derivedEtaData (D.comap h)).objIso
    (pullbackComplex h.toLRSHom.toShHom 𝒦)
    (isIdealTorsionFree_pullback_flatComplex' h D hD 𝒦 hflat)
  exact ⟨(derivedPullback h.toLRSHom.toShHom).mapIso e₁ ≪≫ e₂ ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map
        ((((pullbackFunctor h.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map p) ≫ etaPullbackChainMap h D hD 𝒦 hflat))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hΨ) ≪≫
    e₄.symm ≪≫ ((derivedEtaData (D.comap h)).functor.mapIso e₃).symm⟩

/-- **Every object of `D(𝒪_X)` is represented by a K-flat complex of flat `𝒪_X`-modules.** -/
theorem exists_kFlat_isFlat_rep' (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (M : DerivedCategory X.Modules) :
    ∃ 𝒦 : CochainComplex X.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace 𝒦 ∧
        (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
          (O := X.sheaf) (𝒦.X n)) ∧
        Nonempty (DerivedCategory.Q.obj 𝒦 ≅ M) := by
  obtain ⟨F, -, ⟨eF⟩⟩ := (derivedEtaData D).exists_isIdealTorsionFree_rep M
  obtain ⟨𝒦, q, h𝒦, hfl, hq, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toRingedSpace F
  exact ⟨𝒦, h𝒦, hfl,
    ⟨(@asIso _ _ _ _ (DerivedCategory.Q.map q)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq)) ≪≫ eF⟩⟩

include hD hflat in
/-- **Stacks tag 0F9X, reduced to one quasi-isomorphism of complexes of `𝒪_Y`-modules**, at an
arbitrary object `M` of `D(𝒪_X)` presented by a K-flat complex of flat modules. -/
theorem nonempty_derivedPullback_derivedEta_iso_of_quasiIso'
    (h𝒦 : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace 𝒦)
    (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace P)
    (p : P ⟶ etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) 𝒦
      (isIdealTorsionFree_flatComplex D 𝒦 hflat))
    (hp : QuasiIso p)
    (hΨ : QuasiIso ((((pullbackFunctor h.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map p) ≫ etaPullbackChainMap h D hD 𝒦 hflat))
    (M : DerivedCategory X.Modules) (e : DerivedCategory.Q.obj 𝒦 ≅ M) :
    Nonempty ((derivedPullback h.toLRSHom.toShHom).obj ((derivedEtaData D).functor.obj M) ≅
      (derivedEtaData (D.comap h)).functor.obj
        ((derivedPullback h.toLRSHom.toShHom).obj M)) := by
  obtain ⟨c⟩ := nonempty_derivedPullback_derivedEta_iso_of_quasiIso h D hD 𝒦 hflat h𝒦 P hP p hp hΨ
  exact ⟨((derivedPullback h.toLRSHom.toShHom).mapIso
      ((derivedEtaData D).functor.mapIso e)).symm ≪≫ c ≪≫
    (derivedEtaData (D.comap h)).functor.mapIso
      ((derivedPullback h.toLRSHom.toShHom).mapIso e)⟩

include hD hflat in
/-- **Stacks tag 0F9X, reduced to the comparison at one auxiliary presentation.**  Let `𝒦` be a
K-flat complex of flat `𝒪_X`-modules presenting `M`, and let `ψ : 𝒢 ⟶ 𝒦` be a
quasi-isomorphism out of a complex `𝒢` of flat `𝒪_X`-modules such that

* `𝒢` and `η_ℐ 𝒢` are K-flat, and
* the chain-level comparison `h^*(η_ℐ 𝒢) ⟶ η_𝒥(h^* 𝒢)` at `𝒢` is an isomorphism.

Then `Lh^*(Lη_ℐ M) ≅ Lη_𝒥(Lh^* M)`. -/
theorem nonempty_derivedPullback_derivedEta_iso_of_isIso_etaPullbackChainMap
    (h𝒦 : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace 𝒦)
    (𝒢 : CochainComplex X.Modules ℤ)
    (h𝒢flat : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) (𝒢.X n))
    (h𝒢 : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace 𝒢)
    (hη𝒢 : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace
      (etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) 𝒢
        (isIdealTorsionFree_flatComplex D 𝒢 h𝒢flat)))
    (hiso : IsIso (etaPullbackChainMap h D hD 𝒢 h𝒢flat))
    (ψ : 𝒢 ⟶ 𝒦) (hψ : QuasiIso ψ)
    (M : DerivedCategory X.Modules) (e : DerivedCategory.Q.obj 𝒦 ≅ M) :
    Nonempty ((derivedPullback h.toLRSHom.toShHom).obj ((derivedEtaData D).functor.obj M) ≅
      (derivedEtaData (D.comap h)).functor.obj
        ((derivedPullback h.toLRSHom.toShHom).obj M)) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  have := mono_pullbackIdealIncl_of_isPullbackDefined h D hD
  have := hiso
  refine nonempty_derivedPullback_derivedEta_iso_of_quasiIso' h D hD 𝒦 hflat h𝒦
    (etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) 𝒢
      (isIdealTorsionFree_flatComplex D 𝒢 h𝒢flat)) hη𝒢
    (Stacks.IdealTorsion.Eta.etaMap X.toRingedSpace (idealSheaf D) (idealSheafι D) ψ
      (isIdealTorsionFree_flatComplex D 𝒢 h𝒢flat) (isIdealTorsionFree_flatComplex D 𝒦 hflat))
    (Stacks.IdealTorsion.Eta.quasiIso_etaMap X.toRingedSpace (idealSheaf D) (idealSheafι D) ψ
      (isIdealTorsionFree_flatComplex D 𝒢 h𝒢flat) (isIdealTorsionFree_flatComplex D 𝒦 hflat) hψ)
    ?_ M e
  have hpsi : QuasiIso (((pullbackFunctor h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ψ) :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.quasiIso_modulePullback_of_kFlat
      h.toLRSHom.toShHom ψ hψ h𝒢 h𝒦
  have hetapsi : QuasiIso (@Stacks.IdealTorsion.Eta.etaMap Y.toRingedSpace
      ((pullbackFunctor h.toLRSHom.toShHom).obj (idealSheaf D))
      (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D))
      (mono_pullbackIdealIncl_of_isPullbackDefined h D hD) inferInstance _ _
      (((pullbackFunctor h.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)
      (isIdealTorsionFree_pullback_flatComplex h D hD 𝒢 h𝒢flat)
      (isIdealTorsionFree_pullback_flatComplex h D hD 𝒦 hflat)) :=
    @Stacks.IdealTorsion.Eta.quasiIso_etaMap Y.toRingedSpace _
      (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D))
      (mono_pullbackIdealIncl_of_isPullbackDefined h D hD) inferInstance _ _ _ _ _ hpsi
  have hnat := @Stacks.IdealTorsion.Eta.pullbackEtaMap_natural _ _ h.toLRSHom.toShHom
    (idealSheaf D) (idealSheafι D) (isInvertible_idealSheaf D) _ _ ψ
    (mono_idealSheafι D) (mono_pullbackIdealIncl_of_isPullbackDefined h D hD)
    (isIdealTorsionFree_flatComplex D 𝒢 h𝒢flat)
    (isIdealTorsionFree_flatComplex D 𝒦 hflat)
    (isIdealTorsionFree_pullback_flatComplex h D hD 𝒢 h𝒢flat)
    (isIdealTorsionFree_pullback_flatComplex h D hD 𝒦 hflat)
  -- the transport along `h^*ℐ ≅ 𝒥` in `etaPullbackChainMap` is abstracted to an isomorphism,
  -- its term being long and playing no part
  have key : ∀ (K : CochainComplex X.Modules ℤ)
      (hf : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X n)),
      ∃ c : _ ≅ _, etaPullbackChainMap h D hD K hf =
        @Stacks.IdealTorsion.Eta.pullbackEtaMap _ _ h.toLRSHom.toShHom (idealSheaf D)
            (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)
            (mono_pullbackIdealIncl_of_isPullbackDefined h D hD) K
          (isIdealTorsionFree_flatComplex D K hf)
          (isIdealTorsionFree_pullback_flatComplex h D hD K hf) ≫ c.hom :=
    fun _ _ => ⟨_, rfl⟩
  obtain ⟨c𝒦, hc𝒦⟩ := key 𝒦 hflat
  obtain ⟨c𝒢, hc𝒢⟩ := key 𝒢 h𝒢flat
  rw [hc𝒦]
  erw [← Category.assoc, hnat, Category.assoc]
  have hqc : QuasiIso c𝒦.hom := inferInstance
  -- the composite mixes the two spellings of the structure sheaf, so it is not type-correct at
  -- `implicit` transparency and instance search cannot act on it either; the composition lemma
  -- is applied with each of its three quasi-isomorphisms given by name.
  refine quasiIso_comp (hφ := ?_) (hφ' := quasiIso_comp (hφ := hetapsi) (hφ' := hqc) _ _) _ _
  rw [c𝒢.eq_comp_inv.2 hc𝒢.symm]
  refine @quasiIso_of_isIso _ _ _ _ _ _ _ _ ?_ _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso c𝒢.isIso_inv

end Stacks.Divisors.Eta

end
