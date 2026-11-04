module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ModelTransport
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtAnOpenFromTheCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis

/-!
# The hypotheses of the degree-zero Künneth step of Tag 0G0A

The degree-zero Künneth formula over a field,
`AlgebraicGeometry.isIso_degreeZeroKunnethMap` (and its tensor-pairing form
`AlgebraicGeometry.isTensorPairing_degreeZeroKunnethPairing`), takes four hypotheses on the two
objects `K` of `D(𝒪_X)` and `M` of `D(𝒪_Y)`: quasi-coherent cohomology sheaves (`hK`, `hM`), and
no cohomology of `RΓ` in negative degrees (`hK₀`, `hM₀`). In the computation of
[Stacks, Tag 0G0A] it is applied to `K = R𝓗om(ℰᵢ, ℰⱼ)` on `X`, for the finite locally free first
factors of a resolution of the diagonal, and to `M = R𝓗om(F(𝒢ᵢ), F(𝒢ⱼ))` on `Y`, for the images
under the exact fully faithful `F` of the second factors. This file proves all four there.

## Main results

* `AlgebraicGeometry.RingedSpace.isZero_homology_sectionsOverBase_derivedSheafHom` and its scheme
  form `AlgebraicGeometry.isZero_homology_sectionsOverBase_derivedSheafHom`: **[Stacks, Tag 08DK]
  in degree `i`, over a base, as vanishing**: `Hⁱ RΓ(V, R𝓗om(K, L)) = 0` as soon as
  `Hom(K, L⟦i⟧) = 0`.
* `AlgebraicGeometry.isZero_homology_sectionsOverBase_derivedSheafHom_single`: `hK₀` for
  `R𝓗om(M[0], N[0])`, any two modules, since negative Exts between modules vanish.
* `DiagonalResolution.isZero_homology_sectionsOverBase_derivedSheafHom_secondFactorImageStd`:
  `hM₀` for `R𝓗om(F(𝒢ᵢ), F(𝒢ⱼ))`, from the base's
  `AlgebraicGeometry.DiagonalResolution.subsingleton_hom_map_secondFactor_shift`.
* `AlgebraicGeometry.isQCohAll_derivedSheafHom_of_isPerfect`: [Stacks, Tag 0A6H] (2) between two
  perfect objects, as `IsQCohAll`; with
  `AlgebraicGeometry.DiagonalResolution.isQCohAll_derivedSheafHom_left` and
  `AlgebraicGeometry.DiagonalResolution.isQCohAll_derivedSheafHom_secondFactorImageStd` it gives
  `hK` and `hM`.
* `AlgebraicGeometry.DiagonalResolution.isIso_degreeZeroKunnethMap_derivedSheafHom` and
  `AlgebraicGeometry.DiagonalResolution.isTensorPairing_degreeZeroKunnethPairing_derivedSheafHom`:
  the degree-zero Künneth step with all four hypotheses discharged.

## Implementation notes

*Model.* Everything about `RΓ` and `R𝓗om` is at `HasDerivedCategory.standard`, turned on as a
local instance at the priority `AlgebraicGeometry.isIso_degreeZeroKunnethMap` uses, so that the
statements here are literally its hypotheses. The images `F(𝒢ᵢ)` are
`AlgebraicGeometry.DiagonalResolution.secondFactorImageStd`, the standard-model reading of the
objects of `D_perf(𝒪_Y)` from
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ModelTransport`; the two
facts about them that live at the locally small model — the vanishing of their negative Exts and
their perfectness — are carried across by `StacksDraft.DerivedModel.subsingleton_hom_shift_inverse`
(which needs the comparison to commute with the shift,
`StacksDraft.DerivedModel.schemeModulesComparisonCommShift`) and
`StacksDraft.DerivedModel.isPerfect_inverse_obj`.

*Why 08DK in every degree and not a t-structure argument.* For the first factors,
`R𝓗om(ℰᵢ, ℰⱼ)` is concentrated in degree zero and `RΓ` is left t-exact, but for the second factors
`R𝓗om(F(𝒢ᵢ), F(𝒢ⱼ))` can have cohomology sheaves in negative degrees, and only its global
sections are bounded below. Reading `Hⁱ RΓ(R𝓗om(K, L))` as `Hom(K, L⟦i⟧)` treats both cases
alike, and in the first it needs no hypothesis on the modules at all.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)

universe u

namespace StacksDraft.DerivedModel

/-! ### The comparison of the two models commutes with the shift -/

section Shift

variable (X : AlgebraicGeometry.Scheme.{u})

/-- **The comparison of the two models of `D(𝒪_X)` commutes with the shift.** It carries the
localization functor of the standard model to that of the locally small one on the nose, and
both localization functors commute with the shift, so the commutation descends along the
localization (`CategoryTheory.Functor.commShiftOfLocalization`). Not an instance: a second
`CommShift` structure on the same functor would be a diamond. -/
@[instance_reducible]
def schemeModulesComparisonCommShift : (schemeModulesComparison X).functor.CommShift ℤ :=
  letI : Localization.Lifting
      (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _))
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := X.Modules)) (schemeModulesComparison X).functor :=
    ⟨Iso.refl _⟩
  Functor.commShiftOfLocalization
    (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _))
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
    (DerivedCategory.Q (C := X.Modules)) (schemeModulesComparison X).functor

/-- **The vanishing of a shifted Hom group passes from the locally small model to the standard
one.** If `Hom(K, L⟦n⟧) = 0` in the locally small model, then `Hom(K, L⟦n⟧) = 0` in the standard
model, the objects being carried across by the inverse comparison. -/
theorem subsingleton_hom_shift_inverse (K L : DerivedCategory X.Modules) (n : ℤ)
    (h : Subsingleton (K ⟶ L⟦n⟧)) :
    Subsingleton ((schemeModulesComparison X).inverse.obj K ⟶
      ((schemeModulesComparison X).inverse.obj L)⟦n⟧) := by
  let := schemeModulesComparisonCommShift X
  have h' : Subsingleton ((schemeModulesComparison X).functor.obj
      ((schemeModulesComparison X).inverse.obj K) ⟶
        ((schemeModulesComparison X).functor.obj ((schemeModulesComparison X).inverse.obj L))⟦n⟧) :=
    ⟨fun a b => (Iso.homCongr ((schemeModulesComparison X).counitIso.app K)
      ((shiftFunctor _ n).mapIso ((schemeModulesComparison X).counitIso.app L))).injective
        (h.elim _ _)⟩
  have := h'
  refine ⟨fun a b => (schemeModulesComparison X).functor.map_injective ?_⟩
  exact (cancel_mono (((schemeModulesComparison X).functor.commShiftIso n).hom.app _)).mp
    (h'.elim _ _)

/-- **Perfectness passes from the locally small model to the standard one.** A perfect
representative of `K` at the locally small model is one of the same object at the standard model:
the comparison matches the two localization functors on the nose and is fully faithful. -/
theorem isPerfect_inverse_obj (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace (HasDerivedCategory.standard _)
      ((schemeModulesComparison X).inverse.obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  exact ⟨E, hE, ⟨(schemeModulesComparison X).fullyFaithfulFunctor.preimageIso
    (e ≪≫ ((schemeModulesComparison X).counitIso.app K).symm)⟩⟩

end Shift

end StacksDraft.DerivedModel

namespace AlgebraicGeometry

open StacksDraft.DerivedModel

/-! ### The images of the second factors, at the locally small model -/

section LocallySmall

attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (R : DiagonalResolution f) (F : perfectDerived X ⥤ perfectDerived Y)

/-- `Hom(F(𝒢ᵢ), F(𝒢ⱼ)⟦p⟧) = 0` for `p < 0`, read in the ambient locally small `D(𝒪_Y)` rather
than in `D_perf(𝒪_Y)`: the base's
`AlgebraicGeometry.DiagonalResolution.subsingleton_hom_map_secondFactor_shift`, with the shift of
the full subcategory moved out to the ambient one. -/
theorem DiagonalResolution.subsingleton_hom_obj_map_secondFactor_shift [F.CommShift ℤ]
    (hff : F.FullyFaithful) (i j : ℕ) (p : ℤ) (hp : p < 0) :
    Subsingleton ((F.obj (R.secondFactor i)).obj ⟶ ((F.obj (R.secondFactor j)).obj)⟦p⟧) := by
  have := R.subsingleton_hom_map_secondFactor_shift F hff i j p hp
  have eshift : ((F.obj (R.secondFactor j))⟦p⟧).obj ≅ ((F.obj (R.secondFactor j)).obj)⟦p⟧ :=
    ((ObjectProperty.ι _).commShiftIso p).app (F.obj (R.secondFactor j))
  have h' : Subsingleton ((F.obj (R.secondFactor i)).obj ⟶ ((F.obj (R.secondFactor j))⟦p⟧).obj) :=
    (DiagonalResolution.perfectDerivedHomEquiv (F.obj (R.secondFactor i))
      ((F.obj (R.secondFactor j))⟦p⟧)).injective.subsingleton
  exact (Iso.homCongr (Iso.refl _) eshift).symm.injective.subsingleton

end LocallySmall

/-! ### `H^i RΓ(V, R𝓗om(K, L))` vanishes when `Hom(K, L⟦i⟧)` does -/

section Standard

attribute [local instance 100000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08DK] in degree `i`, as a vanishing statement, over a base.** For a morphism
of ringed spaces `c : V ⟶ S` and objects `K`, `L` of `D(𝒪_V)`, the degree-`i` cohomology of
`RΓ(V, R𝓗om(K, L))`, as a complex of `Γ(S, 𝒪_S)`-modules, vanishes as soon as
`Hom(K, L⟦i⟧) = Ext^i(K, L)` does.

`RΓ(V, -)` over the base is derived sections over `c⁻¹ ⊤`, so this is
`UnboundedHigherDirectImage.isZero_homologyDerivedPreimageSections_homSheafObject_iff` at `⊤`, read
through the representative `Stacks.SheafOfModules.homSheafObjectIso` of `R𝓗om(K, L)`;
restriction to the slice over `⊤` does not change the Hom group
(`Stacks.DerivedGlueing.subsingleton_shiftedHom_overFunctorTop`). -/
theorem RingedSpace.isZero_homology_sectionsOverBase_derivedSheafHom {S V : RingedSpace.{u, u}}
    (c : V ⟶ S) (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (i : ℤ)
    (h : Subsingleton (K ⟶ L⟦i⟧)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).obj
      ((sectionsOverBase c).obj
        (((Stacks.SheafOfModules.derivedSheafHom V.sheaf).obj (op K)).obj L))) := by
  open Stacks.Cohomology.UnboundedHigherDirectImage in
  exact ((isZero_homologyDerivedPreimageSections_homSheafObject_iff c K L ⊤ i).2
    (Stacks.DerivedGlueing.subsingleton_shiftedHom_overFunctorTop _ K L i h)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).mapIso
        ((sectionsOverBase c).mapIso (Stacks.SheafOfModules.homSheafObjectIso V.sheaf K L)))

variable {S V : Scheme.{u}} (c : V ⟶ S)

/-- **[Stacks, Tag 08DK] in degree `i`, over a base, for schemes**: the scheme form of
`AlgebraicGeometry.RingedSpace.isZero_homology_sectionsOverBase_derivedSheafHom`, in the shape of
the hypotheses `hK₀`, `hM₀` of `AlgebraicGeometry.isIso_degreeZeroKunnethMap`. -/
theorem isZero_homology_sectionsOverBase_derivedSheafHom (K L : DerivedCategory V.Modules) (i : ℤ)
    (h : Subsingleton (K ⟶ L⟦i⟧)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) i).obj
      ((sectionsOverBase c.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.derivedSheafHom V.sheaf).obj (op K)).obj L))) :=
  RingedSpace.isZero_homology_sectionsOverBase_derivedSheafHom c.toLRSHom.toShHom K L i h

/-- **`RΓ(V, R𝓗om(M[0], N[0]))` has no cohomology in negative degrees**, for any two
`𝒪_V`-modules `M` and `N`: its degree-`i` cohomology is `Ext^i(M, N)`, which vanishes for
`i < 0` (`AlgebraicGeometry.subsingleton_hom_singleFunctor_shift`). This is the hypothesis `hK₀`
of `AlgebraicGeometry.isIso_degreeZeroKunnethMap` at `K = R𝓗om(ℰᵢ, ℰⱼ)`. -/
theorem isZero_homology_sectionsOverBase_derivedSheafHom_single (M N : V.Modules) (i : ℤ)
    (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) i).obj
      ((sectionsOverBase c.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.derivedSheafHom V.sheaf).obj
          (op ((DerivedCategory.singleFunctor V.Modules 0).obj M))).obj
            ((DerivedCategory.singleFunctor V.Modules 0).obj N)))) :=
  isZero_homology_sectionsOverBase_derivedSheafHom c _ _ i
    (subsingleton_hom_singleFunctor_shift M N i hi)

/-! ### Quasi-coherence of the derived internal Homs, at the standard model -/

/-- **A finite locally free module placed in degree zero is perfect, at the standard model.** -/
theorem isPerfect_singleFunctor_of_isFiniteLocallyFree_std (W : Scheme.{u}) (M : W.Modules)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) M) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace)
      ((DerivedCategory.singleFunctor W.Modules 0).obj M) :=
  ⟨(CochainComplex.singleFunctor W.Modules 0).obj M,
    isPerfectComplex_single_of_isFiniteLocallyFree W M hM,
    ⟨((DerivedCategory.singleFunctorIsoCompQ W.Modules 0).app M).symm⟩⟩

/-- **[Stacks, Tag 0A6H] part (2), in the form `IsQCohAll`.** The derived internal Hom from a
perfect object of `D(𝒪_W)` to a perfect one has quasi-coherent cohomology sheaves: the target
has them by `AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect`, and
`AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect` does the rest. -/
theorem isQCohAll_derivedSheafHom_of_isPerfect {W : Scheme.{u}} (P Q : DerivedCategory W.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) P)
    (hQ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q) :
    IsQCohAll (((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op P)).obj Q) :=
  derivedCategoryB_derivedSheafHom_of_isPerfect W P Q hP
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect W Q hQ)

/-- **`R𝓗om(M[0], N[0])` has quasi-coherent cohomology sheaves** for finite locally free `M` and
`N`: the hypothesis `hK` of `AlgebraicGeometry.isIso_degreeZeroKunnethMap` at
`K = R𝓗om(ℰᵢ, ℰⱼ)`. -/
theorem isQCohAll_derivedSheafHom_single {W : Scheme.{u}} (M N : W.Modules)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) M)
    (hN : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) N) :
    IsQCohAll (((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj
      (op ((DerivedCategory.singleFunctor W.Modules 0).obj M))).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj N)) :=
  isQCohAll_derivedSheafHom_of_isPerfect _ _
    (isPerfect_singleFunctor_of_isFiniteLocallyFree_std W M hM)
    (isPerfect_singleFunctor_of_isFiniteLocallyFree_std W N hN)

end Standard

/-! ### The images of the second factors, at the standard model -/

section SecondFactor

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (R : DiagonalResolution f) (F : perfectDerived X ⥤ perfectDerived Y)

/-- **`Hom(F(𝒢ᵢ), F(𝒢ⱼ)⟦p⟧) = 0` for `p < 0`, at the standard model.** The base's vanishing at
the locally small model, carried across by
`StacksDraft.DerivedModel.subsingleton_hom_shift_inverse`. -/
theorem DiagonalResolution.subsingleton_hom_secondFactorImageStd_shift [F.CommShift ℤ]
    (hff : F.FullyFaithful) (i j : ℕ) (p : ℤ) (hp : p < 0) :
    Subsingleton (R.secondFactorImageStd F i ⟶ (R.secondFactorImageStd F j)⟦p⟧) :=
  subsingleton_hom_shift_inverse Y _ _ p
    (R.subsingleton_hom_obj_map_secondFactor_shift F hff i j p hp)

/-- **`RΓ(Y, R𝓗om(F(𝒢ᵢ), F(𝒢ⱼ)))` has no cohomology in negative degrees.** Its degree-`p`
cohomology is `Hom(F(𝒢ᵢ), F(𝒢ⱼ)⟦p⟧)` by [Stacks, Tag 08DK], which vanishes for `p < 0` by
exactness and full faithfulness of `F`. This is the hypothesis `hM₀` of
`AlgebraicGeometry.isIso_degreeZeroKunnethMap` at `M = R𝓗om(F(𝒢ᵢ), F(𝒢ⱼ))`. -/
theorem DiagonalResolution.isZero_homology_sectionsOverBase_derivedSheafHom_secondFactorImageStd
    [F.CommShift ℤ] (hff : F.FullyFaithful) {S : Scheme.{u}} (c : Y ⟶ S) (i j : ℕ) (p : ℤ)
    (hp : p < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) p).obj
      ((sectionsOverBase c.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
          (op (R.secondFactorImageStd F i))).obj (R.secondFactorImageStd F j)))) :=
  isZero_homology_sectionsOverBase_derivedSheafHom c _ _ p
    (R.subsingleton_hom_secondFactorImageStd_shift F hff i j p hp)

/-- A first factor of a resolution of the diagonal is finite locally free, in the form
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` that the perfectness lemmas take. -/
theorem DiagonalResolution.isFiniteLocallyFree_left (i : ℕ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (R.left i) :=
  ⟨(R.left_finiteLocallyFree i).exists_isFiniteLocallyFreeData⟩

/-- **`R𝓗om(ℰᵢ, ℰⱼ)` has quasi-coherent cohomology sheaves**, the first factors of a resolution
of the diagonal being finite locally free: the hypothesis `hK` of
`AlgebraicGeometry.isIso_degreeZeroKunnethMap`. -/
theorem DiagonalResolution.isQCohAll_derivedSheafHom_left (i j : ℕ) :
    IsQCohAll (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
      (op ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left i)))).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left j))) :=
  isQCohAll_derivedSheafHom_single _ _ (R.isFiniteLocallyFree_left i) (R.isFiniteLocallyFree_left j)

/-- **The image `F(𝒢ᵢ)` of a second factor is perfect, at the standard model.** It is perfect at
the locally small model, being an object of `D_perf(𝒪_Y)`, and perfectness passes to the
standard model (`StacksDraft.DerivedModel.isPerfect_inverse_obj`). -/
theorem DiagonalResolution.isPerfect_secondFactorImageStd (i : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      (R.secondFactorImageStd F i) :=
  isPerfect_inverse_obj Y _ (F.obj (R.secondFactor i)).property

/-- **`R𝓗om(F(𝒢ᵢ), F(𝒢ⱼ))` has quasi-coherent cohomology sheaves**, at the standard model: the
hypothesis `hM` of `AlgebraicGeometry.isIso_degreeZeroKunnethMap`. -/
theorem DiagonalResolution.isQCohAll_derivedSheafHom_secondFactorImageStd (i j : ℕ) :
    IsQCohAll (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
      (op (R.secondFactorImageStd F i))).obj (R.secondFactorImageStd F j)) :=
  isQCohAll_derivedSheafHom_of_isPerfect _ _ (R.isPerfect_secondFactorImageStd F i)
    (R.isPerfect_secondFactorImageStd F j)

end SecondFactor

/-! ### The degree-zero Künneth step of Tag 0G0A with its hypotheses discharged -/

section Kunneth

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

variable (k : Type u) [Field k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} (g : Y ⟶ Spec (.of k))
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  (R : DiagonalResolution f) (F : perfectDerived X ⥤ perfectDerived Y)

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`RΓ(X, R𝓗om(ℰᵢ, ℰⱼ))` has no cohomology in negative degrees**: the hypothesis `hK₀` of
`AlgebraicGeometry.isIso_degreeZeroKunnethMap` at the first factors of a resolution of the
diagonal. -/
theorem DiagonalResolution.isZero_homology_sectionsOverBase_derivedSheafHom_left (i j : ℕ) (p : ℤ)
    (hp : p < 0) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) p).obj
      ((sectionsOverBase f.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left i)))).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left j))))) :=
  isZero_homology_sectionsOverBase_derivedSheafHom_single f _ _ p hp

/-- **The degree-zero Künneth map of Tag 0G0A is an isomorphism**:
`H⁰RΓ(X, R𝓗om(ℰᵢ, ℰⱼ)) ⊗ H⁰RΓ(Y, R𝓗om(F(𝒢ᵢ'), F(𝒢ⱼ'))) ⟶ H⁰RΓ(X ×_k Y, -)` is
`AlgebraicGeometry.isIso_degreeZeroKunnethMap` with its four hypotheses discharged: quasi-coherence
of both derived internal Homs by [Stacks, Tag 0A6H] (2), and the vanishing of their negative
cohomology by [Stacks, Tag 08DK] together with, on `Y`, exactness and full faithfulness of `F`. -/
theorem DiagonalResolution.isIso_degreeZeroKunnethMap_derivedSheafHom [F.CommShift ℤ]
    (hff : F.FullyFaithful) (i j i' j' : ℕ) :
    IsIso (degreeZeroKunnethMap k f g
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left i)))).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left j)))
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
        (op (R.secondFactorImageStd F i'))).obj (R.secondFactorImageStd F j'))) :=
  isIso_degreeZeroKunnethMap k f g _ _ (R.isQCohAll_derivedSheafHom_left i j)
    (R.isQCohAll_derivedSheafHom_secondFactorImageStd F i' j')
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_left k i j p hp)
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_secondFactorImageStd F hff g
      i' j' p hp)

/-- **The degree-zero Künneth pairing of Tag 0G0A is a tensor pairing**, over `k`:
`AlgebraicGeometry.isTensorPairing_degreeZeroKunnethPairing` with its four hypotheses discharged
as in `AlgebraicGeometry.DiagonalResolution.isIso_degreeZeroKunnethMap_derivedSheafHom`. -/
theorem DiagonalResolution.isTensorPairing_degreeZeroKunnethPairing_derivedSheafHom [F.CommShift ℤ]
    (hff : F.FullyFaithful) (i j i' j' : ℕ) :
    IsTensorPairing k
      (degreeZeroSectionsField k f (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left i)))).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left j))))
      (degreeZeroSectionsField k g (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
        (op (R.secondFactorImageStd F i'))).obj (R.secondFactorImageStd F j')))
      (degreeZeroKunnethPairing k f g _ _) :=
  isTensorPairing_degreeZeroKunnethPairing k f g _ _ (R.isQCohAll_derivedSheafHom_left i j)
    (R.isQCohAll_derivedSheafHom_secondFactorImageStd F i' j')
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_left k i j p hp)
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_secondFactorImageStd F hff g
      i' j' p hp)

end Kunneth

end AlgebraicGeometry

end
