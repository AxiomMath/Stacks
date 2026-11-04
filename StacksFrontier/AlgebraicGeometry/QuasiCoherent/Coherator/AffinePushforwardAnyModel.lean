module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardLeray

/-!
# The derived direct image along an affine morphism, at an arbitrary derived category

Let `f : X ⟶ Y` be an affine morphism of schemes. Two facts about the unbounded derived direct
image are proved in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardQuasiCoherence.lean` and
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardLeray.lean`, both at
`CategoryTheory.HasDerivedCategory.standard`:

* `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`, which is part (1) of [Stacks, Tag 08D5];
* a complex of quasi-coherent modules computes its own derived direct image, which is
  [Stacks, Tag 0G9N] for an affine morphism.

`HasDerivedCategory` carries the localized category as *data*, so neither statement says anything
about the locally small model `SheafOfModules.hasDerivedCategory` at which
`AlgebraicGeometry.derivedTilde` and the comparison functor of [Stacks, Tag 06VT] are read — and
that model is where the affine duality statements of [Stacks, Tag 0A9F] live. The pin cannot be
removed at the source: it enters through
`AlgebraicGeometry.isLE_derivedPushforward_obj_of_isAffineHom`, whose input is the
truncation-tower convergence of [Stacks, Tag 08D3] and [Stacks, Tag 0D6P], which is available only
at the standard model and installs `HasDerivedCategory` instances *inside* proofs throughout
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/`.

This file crosses the gap the way
`StacksFrontier/AlgebraicGeometry/AffineVanishingQuasicoherentComplex.lean` crosses it for unbounded
affine vanishing: each statement is re-expressed with **no derived category in it at all** — a
statement about a complex and a K-injective resolution of it — and then read back at an arbitrary
`[HasDerivedCategory.{w}]`. The hinge is
`Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff`, the K-injective criterion of
[Stacks, Tag 070K], which is stated at a free `HasDerivedCategory` binder and turns invertibility
of the structure map of *any* total right derived functor into the assertion that the functor
inverts one K-injective resolution.

## Main definitions

* `Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors` — the factorization of
  `K(F) ⋙ Qh` through termwise application of `F`, which is what identifies the structure map of a
  derived functor with a map of complexes.
* `AlgebraicGeometry.pushforwardSheafOfModules` — direct image of `𝒪_X`-modules, with source and
  target spelled `SheafOfModules X.ringCatSheaf`.
* `AlgebraicGeometry.AnyModel.derivedPushforward` and
  `AlgebraicGeometry.AnyModel.derivedPushforwardUnit` — `Rf_*` and its comparison map at an
  arbitrary chosen model of the two derived categories.
* `AlgebraicGeometry.AnyModel.derivedPushforwardObjIso` — `Rf_*K` is the termwise direct image of a
  K-injective resolution of `K`.

## Main results

* `AlgebraicGeometry.quasiIso_modulePushforward_map_of_isAffineHom` — **[Stacks, Tag 0G9N] for an
  affine morphism, with no derived category in the statement**: `f_*` carries a quasi-isomorphism
  from a complex of quasi-coherent modules into a K-injective complex to a quasi-isomorphism.
* `AlgebraicGeometry.isQuasicoherent_homology_modulePushforward_of_isAffineHom` — **part (1) of
  [Stacks, Tag 08D5] for an affine morphism, with no derived category in the statement**: the
  cohomology sheaves of `f_*I` are quasi-coherent, for `I` a K-injective resolution of a complex
  with quasi-coherent cohomology.
* `AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom` and
  `AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom` —
  the same two results at an arbitrary chosen model of the derived categories.

## Implementation notes

**No `@[stacks 0G9N]` or `@[stacks 08D5]` attribute is placed**, for the reasons already recorded
in the two files whose results are transported: 0G9N is stated for a quasi-compact quasi-separated
morphism and 08D5 has three parts and the integer `N` of [Stacks, Tag 01XJ], while what is
available is the affine case with `N = 1`.

**`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.**
The import closure contains the locally small instances `SheafOfModules.hasDerivedCategory` and
`ModuleCat.hasDerivedCategory`; at equal priority instance search picks those for the sheaf
categories, which would make the statements of the standard-model section mention a model their
inputs are not stated at.

**Two spellings of the module category, and why `Rf_*` is rebuilt rather than transported.**
`SheafOfModules X.ringCatSheaf` and
`SheafOfModules (structureSheafRing X.toRingedSpace)` are definitionally equal,
but they carry separately declared `Preadditive` and `HasDerivedCategory` instances and instance
search does not cross them. The
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` is in the second spelling
and the comparison functor of [Stacks, Tag 06VT] is in the first; a `Localization.Lifting` or a
`CategoryTheory.Functor.Additive` goal that mixes the two is not solved, and obtaining
one derived functor from the other by `inferInstanceAs` exhausts the elaborator's heartbeats on
the Kan extension. The arbitrary-model `Rf_*` below is therefore built in the first spelling by
`CategoryTheory.Functor`'s
`hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`,
exactly as the pinned one is built in the second; no cohomology is reproved, the only input being
the existence of K-injective resolutions, quoted from
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`. The two
statements of the standard-model section are the bridge between the pinned `Rf_*` and this one:
being about complexes and quasi-isomorphisms only, they cross the two spellings by a definitional
unfolding of `AlgebraicGeometry.pushforwardSheafOfModules` and nothing more.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit pushforwardToDerivedCategory
    exists_quasiIso_isKInjective isIso_derivedPushforwardUnit_app_of_isKInjective)

universe w u

namespace Stacks.SmallDerivedCategory

/-! ### Reading the structure map of a derived functor as a map of complexes -/

section

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- **Termwise application of `F`, read in `D(B)`, factors the functor induced by `F` on homotopy
categories.** Both sides send a complex `K` of `A` to the object of `D(B)` represented by `F(K)`;
the composite on the left reads it through the homotopy category of `B` and the one on the right
through `DerivedCategory.Q`, and `DerivedCategory.Q` is not reducible, so the comparison has to be
made by this isomorphism rather than by unfolding. -/
public def mapHomotopyCategoryCompQhFactors :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)

/-- **`F` carries a map of complexes to a quasi-isomorphism exactly when the induced functor on
homotopy categories carries its homotopy class to an isomorphism of `D(B)`.** This is the
translation that turns the hypothesis of the K-injective criterion
`Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff` — an invertibility in a
derived category of the *target* — into a statement about complexes. -/
public theorem isIso_mapHomotopyCategoryCompQh_map_quotient_map_iff {K L : CochainComplex A ℤ}
    (φ : K ⟶ L) :
    IsIso ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ)) ↔
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  rw [← Functor.comp_map, NatIso.isIso_map_iff (mapHomotopyCategoryCompQhFactors F)]
  exact DerivedCategory.isIso_Q_map_iff_quasiIso (C := B) _

/-- **A map of complexes becomes invertible in the derived category exactly when it is a
quasi-isomorphism**, read through the homotopy category. -/
public theorem isIso_Qh_map_quotient_map_iff [HasDerivedCategory A] {K L : CochainComplex A ℤ}
    (φ : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ)) ↔ QuasiIso φ :=
  (DerivedCategory.isIso_Qh_map_iff _).trans
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).trans
      (HomologicalComplex.mem_quasiIso_iff _))

end

end Stacks.SmallDerivedCategory

namespace AlgebraicGeometry

/-! ### Direct image in the spelling the quasi-coherent modules are stated in -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Every complex of `𝒪_X`-modules admits a quasi-isomorphism into a K-injective complex**, with
the category of modules spelled `SheafOfModules X.ringCatSheaf`. -/
public theorem exists_quasiIso_isKInjective_ringCatSheaf (X : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (s : K ⟶ I),
      I.IsKInjective ∧ QuasiIso s :=
  exists_quasiIso_isKInjective X.toRingedSpace K

/-- **Direct image of `𝒪_X`-modules, with source and target spelled
`SheafOfModules X.ringCatSheaf`.** This is `RingedSpaceModuleAdjunction.modulePushforward` of the
underlying morphism of ringed spaces; the ascription moves it to the view in which the
quasi-coherent modules are a subcategory, where `CategoryTheory.Functor.Additive` is a different
proposition and instance search finds only the re-registered form below. -/
public def pushforwardSheafOfModules :
    SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} Y.ringCatSheaf :=
  modulePushforward f.toLRSHom.toShHom

/-- `AlgebraicGeometry.pushforwardSheafOfModules` is additive. -/
public instance pushforwardSheafOfModules_additive : (pushforwardSheafOfModules f).Additive :=
  inferInstanceAs ((modulePushforward f.toLRSHom.toShHom).Additive)

/-! ### The two results with no derived category in the statement -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- A property closed under isomorphisms holds for the homology of a complex `K` exactly when it
holds for the corresponding cohomology object of any object of `D(A)` isomorphic to `Q K`. -/
private theorem prop_homology_iff_prop_homologyFunctor_obj {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    {K : CochainComplex A ℤ} {E : DerivedCategory A} (e : E ≅ DerivedCategory.Q.obj K) (n : ℤ) :
    P (K.homology n) ↔ P ((DerivedCategory.homologyFunctor A n).obj E) :=
  ⟨P.prop_of_iso (((DerivedCategory.homologyFunctor A n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors A n).app K).symm),
    P.prop_of_iso ((DerivedCategory.homologyFunctor A n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors A n).app K)⟩

/-- **[Stacks, Tag 0G9N] for an affine morphism, with no derived category in the statement.** Let
`f : X ⟶ Y` be an affine morphism of schemes, let `K` be a complex of quasi-coherent
`𝒪_X`-modules — no boundedness is assumed — and let `s : K ⟶ I` be a quasi-isomorphism into a
K-injective complex of `𝒪_X`-modules. Then `f_*s` is again a quasi-isomorphism: the complex
`f_*K` already computes `Rf_*K`.

This is `AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom` read through the
K-injective criterion of [Stacks, Tag 070K]. Separating the statement from the derived category is
what lets it be used at a model other than `CategoryTheory.HasDerivedCategory.standard`; see the
module documentation. -/
public theorem quasiIso_modulePushforward_map_of_isAffineHom [IsAffineHom f]
    {K I : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ}
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) (s : K ⟶ I) (hI : I.IsKInjective) (hs : QuasiIso s) :
    QuasiIso (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) :=
  (Stacks.SmallDerivedCategory.isIso_mapHomotopyCategoryCompQh_map_quotient_map_iff
    (modulePushforward f.toLRSHom.toShHom) s).1
    ((Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
      (exists_quasiIso_isKInjective X.toRingedSpace)
      (pushforwardToDerivedCategory f.toLRSHom.toShHom)
      (derivedPushforward f.toLRSHom.toShHom) (derivedPushforwardUnit f.toLRSHom.toShHom)
      s hI hs).1 (isIso_derivedPushforwardUnit_app_of_isAffineHom f K hqc))

/-- **Part (1) of [Stacks, Tag 08D5] for an affine morphism, with no derived category in the
statement.** Let `f : X ⟶ Y` be an affine morphism of schemes, let `K` be a complex of
`𝒪_X`-modules whose cohomology sheaves are quasi-coherent, and let `s : K ⟶ I` be a
quasi-isomorphism into a K-injective complex. Then the cohomology sheaves of `f_*I` — the complex
computing `Rf_*K` — are quasi-coherent.

This is `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom` read
at the object represented by `K`. That object is `Rf_*K`, and the isomorphism identifying it with
the object represented by `f_*I` is assembled here from the invertibility of the comparison map at
the K-injective `I` and the invertibility of `s` in the derived category. -/
public theorem isQuasicoherent_homology_modulePushforward_of_isAffineHom [IsAffineHom f]
    {K I : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ}
    (hqc : ∀ n : ℤ, (K.homology n).IsQuasicoherent) (s : K ⟶ I) (hI : I.IsKInjective)
    (hs : QuasiIso s) (i : ℤ) :
    ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology i).IsQuasicoherent := by
  let E := DerivedCategory.Qh.obj ((HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).obj K)
  have hcoh : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E).IsQuasicoherent :=
    fun n => (prop_homology_iff_prop_homologyFunctor_obj
      (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace))
      ((DerivedCategory.quotientCompQhIso _).app K) n).1 (hqc n)
  have := (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom I hI
  let objIso : (derivedPushforward f.toLRSHom.toShHom).obj E ≅
      DerivedCategory.Q.obj (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    (derivedPushforward f.toLRSHom.toShHom).mapIso (asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
      (asIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
      (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
        (modulePushforward f.toLRSHom.toShHom)).app I
  exact (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).mapIso objIso ≪≫
      (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).app _)
    (isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom f E hcoh i)

end Standard

/-! ### The derived direct image at an arbitrary model -/

namespace AnyModel

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} Y.ringCatSheaf)]

/-- Degreewise direct image of `𝒪_X`-modules, read in a chosen derived category of the target. -/
public abbrev pushforwardToDerivedCategory :
    HomotopyCategory (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} Y.ringCatSheaf) :=
  (pushforwardSheafOfModules f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute the derived direct image pointwise, at any chosen model: the
criterion asks only for the existence of K-injective resolutions in the source, which is
model-free. -/
public instance pushforward_hasPointwiseRightDerivedFunctor :
    (pushforwardToDerivedCategory.{w} f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, w, w, u + 1, u + 1, u + 1}
      (pushforwardToDerivedCategory.{w} f) (exists_quasiIso_isKInjective_ringCatSheaf X)).1

/-- The derived direct image exists at any chosen model of the two derived categories. -/
public instance pushforward_hasRightDerivedFunctor :
    (pushforwardToDerivedCategory.{w} f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **`Rf_*` at an arbitrary chosen model of the two derived categories.** This is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` with the choice of derived
category a binder rather than a term, and with the category of modules in the spelling the
quasi-coherent subcategory is stated in. -/
public abbrev derivedPushforward :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} Y.ringCatSheaf) :=
  (pushforwardToDerivedCategory.{w} f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- The canonical comparison `f_* ⟶ Rf_*`, at an arbitrary chosen model. -/
public abbrev derivedPushforwardUnit :
    pushforwardToDerivedCategory.{w} f ⟶ DerivedCategory.Qh ⋙ derivedPushforward.{w} f :=
  (pushforwardToDerivedCategory.{w} f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- A K-injective complex computes the derived direct image at any chosen model: on it the
canonical comparison `f_*I ⟶ Rf_*I` is invertible. -/
public theorem isIso_derivedPushforwardUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, w, w, u + 1, u + 1, u + 1}
      (pushforwardToDerivedCategory.{w} f) (exists_quasiIso_isKInjective_ringCatSheaf X)).2
    DerivedCategory.Qh (derivedPushforward.{w} f) (derivedPushforwardUnit.{w} f) I hI

/-- **`Rf_*K` is the termwise direct image of a K-injective resolution of `K`.** Given a
quasi-isomorphism `s : K ⟶ I` into a K-injective complex, the object `Rf_*K` of the chosen derived
category of the target is the one represented by the complex `f_*I`: the comparison map is
invertible at `I`, and `s` becomes invertible in the derived category of the source. -/
public def derivedPushforwardObjIso
    {K I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ} (s : K ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) :
    (derivedPushforward.{w} f).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
          (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj (((pushforwardSheafOfModules f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  have := (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have := isIso_derivedPushforwardUnit_app_of_isKInjective.{w} f I hI
  (derivedPushforward.{w} f).mapIso (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
    (asIso ((derivedPushforwardUnit.{w} f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
      (pushforwardSheafOfModules f)).app I

/-- **[Stacks, Tag 0G9N] for an affine morphism, at an arbitrary chosen model of the derived
categories.** A complex `K` of quasi-coherent `𝒪_X`-modules computes its own derived direct
image: the canonical comparison `f_*K ⟶ Rf_*K` is invertible.

Both directions of the K-injective criterion of [Stacks, Tag 070K] are used: the model-free
`AlgebraicGeometry.quasiIso_modulePushforward_map_of_isAffineHom` is its content at the standard
model, and the criterion reads that back here. -/
public theorem isIso_derivedPushforwardUnit_app_of_isAffineHom [IsAffineHom f]
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso ((derivedPushforwardUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_ringCatSheaf X K
  exact (Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
    (exists_quasiIso_isKInjective_ringCatSheaf X)
    (pushforwardToDerivedCategory.{w} f) (derivedPushforward.{w} f)
    (derivedPushforwardUnit.{w} f) s hI hs).2
    ((Stacks.SmallDerivedCategory.isIso_mapHomotopyCategoryCompQh_map_quotient_map_iff
      (pushforwardSheafOfModules f) s).2
      (quasiIso_modulePushforward_map_of_isAffineHom f hqc s hI hs))

/-- **Part (1) of [Stacks, Tag 08D5] for an affine morphism, at an arbitrary chosen model of the
derived categories.** If every cohomology sheaf of `E` is quasi-coherent then so is every
cohomology sheaf of `Rf_*E`; that is, `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.

Every object of the derived category is represented by a complex `K`, and
`AlgebraicGeometry.AnyModel.derivedPushforwardObjIso` identifies `Rf_*E` with the object
represented by `f_*I` for a K-injective resolution `K ⟶ I`; the cohomology sheaves of that complex
are quasi-coherent by the model-free
`AlgebraicGeometry.isQuasicoherent_homology_modulePushforward_of_isAffineHom`. -/
public theorem isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).obj
      ((derivedPushforward.{w} f).obj E)).IsQuasicoherent := by
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hKcoh : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (prop_homology_iff_prop_homologyFunctor_obj (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      eQ.symm n).2 (hcoh n)
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_ringCatSheaf X K
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} Y.ringCatSheaf) i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).mapIso
        ((derivedPushforwardObjIso.{w} f s hI hs).symm ≪≫
          (derivedPushforward.{w} f).mapIso
            ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app K ≪≫ eQ)))
    (isQuasicoherent_homology_modulePushforward_of_isAffineHom f hKcoh s hI hs i)

end AnyModel

end AlgebraicGeometry

end
