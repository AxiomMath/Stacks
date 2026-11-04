module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Derived pushforward along an affine morphism reflects isomorphisms

Let `f : X ⟶ S` be an affine morphism of schemes, with `S` an arbitrary scheme. Then
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` reflects isomorphisms: a map `α : E ⟶ F` of complexes of
`𝒪_X`-modules with quasi-coherent cohomology is invertible in `D_QCoh(𝒪_X)` as soon as `Rf_*α` is
invertible.

The route is the one the source indicates, with the reduction to the affine case replaced by the
t-exactness statement that reduction is used to prove. Direct image along an affine morphism
detects vanishing of cohomology on complexes with quasi-coherent cohomology,
`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isZero_homology_derivedPushforward_iff`:
`H^i(Rf_*E) = 0` exactly when `H^i(E) = 0`, because `H^i(Rf_*E) = f_*H^i(E)` and `f_*` is
conservative on quasi-coherent modules. So `Rf_*` carries a nonzero object of `D_QCoh(𝒪_X)` to a
nonzero object, and the passage from conservativity to reflection of isomorphisms is the usual
triangulated one: complete `α` to a distinguished triangle whose third object `Z` again has
quasi-coherent cohomology, `Rf_*` is exact so it carries that triangle to a distinguished one,
invertibility of `Rf_*α` makes `Rf_*Z` vanish, conservativity makes `Z` vanish, and a
distinguished triangle with vanishing third object has invertible first map.

## Main results

* `AlgebraicGeometry.isZero_homology_modulePushforward_iff_of_isAffineHom` — the vanishing
  criterion with **no derived category in the statement**: for `s : K ⟶ I` a quasi-isomorphism
  into a K-injective complex, with `K` having quasi-coherent cohomology, `(f_*I)` has vanishing
  cohomology in degree `i` exactly when `K` does.
* `AlgebraicGeometry.AnyModel.isZero_homologyFunctor_derivedPushforward_iff_of_isAffineHom`,
  `AlgebraicGeometry.AnyModel.isZero_derivedPushforward_obj_iff_of_isAffineHom` — the same
  criterion, and the resulting conservativity of `Rf_*` on `D_QCoh(𝒪_X)`, at an arbitrary chosen
  model of the two derived categories.
* `AlgebraicGeometry.AnyModel.isTriangulated_derivedPushforward` — `Rf_*` is exact at an arbitrary
  chosen model.
* `AlgebraicGeometry.AnyModel.isIso_of_isIso_derivedPushforward_map_of_isAffineHom` — **the
  content of [Stacks, Tag 08I8]**: a map of `D_QCoh(𝒪_X)` whose derived direct image is invertible
  is invertible.
* `AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward` — **[Stacks, Tag 08I8]**
  as a statement about the functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` of
  `AlgebraicGeometry.derivedQuasicoherentPushforward`.

## Implementation notes

**Why the detour through a statement with no derived category in it.** The t-exactness input is
available only at `CategoryTheory.HasDerivedCategory.standard` and in the module spelling
`SheafOfModules (structureSheafRing X.toRingedSpace)`, whereas
`AlgebraicGeometry.derivedQuasicoherentPushforward` — the functor the tag is about — is read at
the locally small model and in the spelling `SheafOfModules X.ringCatSheaf`. `HasDerivedCategory`
carries the localized category as data, so a statement proved at one model says nothing about
another. The crossing is made exactly as in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean`: the
criterion is first re-expressed as a statement about a complex and a K-injective resolution of it,
in which no derived category occurs, and then read back at an arbitrary `[HasDerivedCategory.{w}]`
through `AlgebraicGeometry.AnyModel.derivedPushforwardObjIso`.

**Exactness of `Rf_*` at an arbitrary model** is
`Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor` applied to the right derived
functor `AlgebraicGeometry.AnyModel.derivedPushforward`, whose only input is the existence of
K-injective resolutions of complexes of `𝒪_X`-modules; the shift-commutation datum is the
canonical one attached to the unit, which is also the instance Mathlib registers on a
`CategoryTheory.Functor.totalRightDerived`.

**That the third object of the triangle stays in `D_QCoh`** is the triangulated subcategory
statement `DerivedCategoryB.derivedCategoryB_isTriangulated` fed with
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`, which mentions no
model and so may be read at the model in force.

**The hypotheses.** The source says "let `f : X ⟶ S` be an affine morphism of schemes", and
`[IsAffineHom f]` is that hypothesis; nothing else is assumed, in particular neither `X` nor `S`
is required to be affine, quasi-compact or quasi-separated. The quasi-coherence hypotheses on `E`
and `F` are the assertion that they are objects of `D_QCoh(𝒪_X)`, which is where the source's
`α : E ⟶ F` lives; in the packaged form
`AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward` they are the
subcategory-membership fields of the objects and so do not appear.

## References

* [Stacks Project, Tag 08I8](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction

universe w u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The vanishing criterion with no derived category in the statement -/

section Standard

/-- The cohomology of an object of the derived category isomorphic to `Q K` is that of `K`. -/
private def homologyFunctorObjIsoHomology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) {E : DerivedCategory C}
    (e : DerivedCategory.Q.obj K ≅ E) (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).obj E ≅ K.homology n :=
  ((DerivedCategory.homologyFunctor C n).mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors C n).app K

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit
    isIso_derivedPushforwardUnit_app_of_isKInjective) in
/-- **The vanishing criterion of [Stacks, Tag 08I8] with no derived category in the statement.**
Let `f : X ⟶ Y` be an affine morphism of schemes, let `K` be a complex of `𝒪_X`-modules whose
cohomology sheaves are quasi-coherent, and let `s : K ⟶ I` be a quasi-isomorphism into a
K-injective complex, so that `f_*I` computes `Rf_*K`. Then `f_*I` has vanishing cohomology in a
degree exactly when `K` does.

This is
`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isZero_homology_derivedPushforward_iff` read
at the object represented by `K`; separating the statement from the derived category is what lets
it be used at a model other than `CategoryTheory.HasDerivedCategory.standard`. -/
public theorem isZero_homology_modulePushforward_iff_of_isAffineHom [IsAffineHom f]
    {K I : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ}
    (hqc : ∀ n : ℤ, (K.homology n).IsQuasicoherent) (s : K ⟶ I) (hI : I.IsKInjective)
    (hs : QuasiIso s) (i : ℤ) :
    IsZero ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i) ↔ IsZero (K.homology i) := by
  set E := DerivedCategory.Qh.obj ((HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).obj K) with hE
  let eH := homologyFunctorObjIsoHomology K
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))).app K).symm
  have hcoh : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E).IsQuasicoherent :=
    fun n => (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      (eH n).symm (hqc n)
  have _ := (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have _ := isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom I hI
  let objIso : (derivedPushforward f.toLRSHom.toShHom).obj E ≅
      DerivedCategory.Q.obj (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    (derivedPushforward f.toLRSHom.toShHom).mapIso (asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
      (asIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
      (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
        (modulePushforward f.toLRSHom.toShHom)).app I
  let eT := homologyFunctorObjIsoHomology _ objIso.symm i
  exact (Iso.isZero_iff eT).symm.trans
    ((Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isZero_homology_derivedPushforward_iff
      f E hcoh i).trans (Iso.isZero_iff (eH i)))

end Standard

/-! ### Conservativity and exactness at an arbitrary model -/

namespace AnyModel

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} Y.ringCatSheaf)]

/-- **The derived direct image along an affine morphism detects vanishing of cohomology, at an
arbitrary chosen model of the derived categories**: for `E` with quasi-coherent cohomology,
`H^i(Rf_*E) = 0` exactly when `H^i(E) = 0`.

Every object of the derived category is represented by a complex `K`, and
`AlgebraicGeometry.AnyModel.derivedPushforwardObjIso` identifies `Rf_*E` with the object
represented by `f_*I` for a K-injective resolution `K ⟶ I`; the criterion for that complex is the
model-free `AlgebraicGeometry.isZero_homology_modulePushforward_iff_of_isAffineHom`. -/
public theorem isZero_homologyFunctor_derivedPushforward_iff_of_isAffineHom [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).obj
        ((derivedPushforward.{w} f).obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj E) := by
  set K := DerivedCategory.Q.objPreimage E with hK
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eE : DerivedCategory.Qh.obj ((HomotopyCategory.quotient
      (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)).obj K) ≅ E :=
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app K ≪≫ eQ
  let eH := homologyFunctorObjIsoHomology K eQ
  have hKcoh : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (eH n) (hcoh n)
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_ringCatSheaf X K
  let eT := homologyFunctorObjIsoHomology _
    ((derivedPushforwardObjIso.{w} f s hI hs).symm ≪≫ (derivedPushforward.{w} f).mapIso eE) i
  exact (Iso.isZero_iff eT).trans
    ((isZero_homology_modulePushforward_iff_of_isAffineHom f hKcoh s hI hs i).trans
      (Iso.isZero_iff (eH i)).symm)

/-- **The derived direct image along an affine morphism is conservative on `D_QCoh(𝒪_X)`**, at an
arbitrary chosen model: `Rf_*E = 0` exactly when `E = 0`, for `E` with quasi-coherent cohomology.
Both vanishings are detected on cohomology. -/
public theorem isZero_derivedPushforward_obj_iff_of_isAffineHom [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) :
    IsZero ((derivedPushforward.{w} f).obj E) ↔ IsZero E := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology,
    DerivedCategory.isZero_iff_forall_isZero_homology]
  exact forall_congr' fun i =>
    isZero_homologyFunctor_derivedPushforward_iff_of_isAffineHom.{w} f E hcoh i

/-- **The derived direct image is exact**, at an arbitrary chosen model of the derived categories:
it is a right derived functor of an exact functor out of `K(𝒪_X)`, and complexes of `𝒪_X`-modules
admit K-injective resolutions. -/
public theorem isTriangulated_derivedPushforward : (derivedPushforward.{w} f).IsTriangulated := by
  have hK : ((pushforwardSheafOfModules f).mapHomotopyCategory
      (ComplexShape.up ℤ)).IsTriangulated := inferInstance
  have hQ : (DerivedCategory.Qh (C := SheafOfModules.{u} Y.ringCatSheaf)).IsTriangulated :=
    inferInstance
  have hF : (pushforwardToDerivedCategory.{w} f).IsTriangulated :=
    ⟨fun T hT => Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.Qh.map_distinguished _
        (((pushforwardSheafOfModules f).mapHomotopyCategory
          (ComplexShape.up ℤ)).map_distinguished T hT)) _
      ((Functor.mapTriangleCompIso ((pushforwardSheafOfModules f).mapHomotopyCategory
        (ComplexShape.up ℤ)) DerivedCategory.Qh).app T)⟩
  exact Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (exists_quasiIso_isKInjective_ringCatSheaf X) (pushforwardToDerivedCategory.{w} f)
    (derivedPushforward.{w} f) (derivedPushforwardUnit.{w} f)

/-- **[Stacks, Tag 08I8], as the assertion the source says the statement means.** Let
`f : X ⟶ Y` be an affine morphism of schemes and let `α : E ⟶ F` be a map of complexes of
`𝒪_X`-modules with quasi-coherent cohomology, that is, a morphism of `D_QCoh(𝒪_X)`. If `Rf_*α` is
invertible then so is `α`.

Complete `α` to a distinguished triangle `E ⟶ F ⟶ Z`; the third object `Z` again has
quasi-coherent cohomology because `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`. Since
`Rf_*` is exact it carries the triangle to a distinguished triangle, whose first map `Rf_*α` is
invertible, so `Rf_*Z = 0`; conservativity on `D_QCoh(𝒪_X)` gives `Z = 0`, and a distinguished
triangle with vanishing third object has invertible first map. -/
public theorem isIso_of_isIso_derivedPushforward_map_of_isAffineHom [IsAffineHom f]
    {E F : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)}
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent)
    (hF : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj F).IsQuasicoherent)
    (α : E ⟶ F) (h : IsIso ((derivedPushforward.{w} f).map α)) : IsIso α := by
  have hW := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X
  have hP : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _ hW
  have hPiso : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _ hW
  obtain ⟨Z, hZ, g, δ, hT⟩ := ObjectProperty.distinguished_cocone_triangle
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)) α hE hF
  have := isTriangulated_derivedPushforward.{w} f
  have hRT := (derivedPushforward.{w} f).map_distinguished _ hT
  have hRZ : IsZero ((derivedPushforward.{w} f).obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ hRT).2 h
  have hZ0 : IsZero Z :=
    (isZero_derivedPushforward_obj_iff_of_isAffineHom.{w} f Z hZ).1 hRZ
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ0

end AnyModel

/-! ### Stacks 08I8 -/

/-- **[Stacks, Tag 08I8].** Let `f : X ⟶ Y` be an affine morphism of schemes, with `Y` an
arbitrary scheme. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms.

`AlgebraicGeometry.derivedQuasicoherentPushforward` is by construction the lift of
`D_QCoh(𝒪_X) ⥤ D(𝒪_X) ⥤ D(𝒪_Y)` through the inclusion of `D_QCoh(𝒪_Y)`, so a map of
`D_QCoh(𝒪_X)` whose derived direct image is invertible in `D_QCoh(𝒪_Y)` has invertible derived
direct image in `D(𝒪_Y)`;
`AlgebraicGeometry.AnyModel.isIso_of_isIso_derivedPushforward_map_of_isAffineHom` makes it
invertible in `D(𝒪_X)`, and the inclusion of `D_QCoh(𝒪_X)` is fully faithful, hence reflects
isomorphisms. -/
@[stacks 08I8]
public theorem reflectsIsomorphisms_derivedQuasicoherentPushforward [IsAffineHom f] :
    (derivedQuasicoherentPushforward f).ReflectsIsomorphisms where
  reflects {E F'} α h := by
    have := h
    have hι : IsIso ((AnyModel.derivedPushforward.{u} f).map
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map α)) :=
      inferInstanceAs (IsIso ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι.map
        ((derivedQuasicoherentPushforward f).map α)))
    have := AnyModel.isIso_of_isIso_derivedPushforward_map_of_isAffineHom.{u} f E.2 F'.2
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map α) hι
    exact isIso_of_reflects_iso α (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι

end AlgebraicGeometry

end
