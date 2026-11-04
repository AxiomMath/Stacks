module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernel
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness

/-!
# Derived direct image is supported on the image of the morphism

Let `h : V ⟶ W` be a morphism of schemes and let `T ⊆ W` be a closed set containing the
set-theoretic image of `h`. Then for *every* object `E` of the unbounded derived category of
`𝒪_V`-modules the cohomology of `Rh_*E` is supported on `T`, with no hypothesis on `E` at all.

This generalizes `Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward`, which is the
case of the inclusion of an open subscheme, and there the hypothesis that `E` be supported on
the preimage of `T` is genuinely needed. Here it is automatic: writing `O = W \ T`, the preimage
`h ⁻¹ᵁ O` is **empty**, because every point of the image of `h` lies in `T`, so the restriction
of `E` to `h ⁻¹ᵁ O` is a zero object outright. The geometry is otherwise the same argument. The
square
```
h ⁻¹ᵁ O ----> O
   |          |
   v          v
   V ---h---> W
```
is Cartesian (`AlgebraicGeometry.isPullback_morphismRestrict`), so the base-change isomorphism
of [Stacks, Tag 08FE] identifies the restriction to `O` of `Rh_*E` with the derived direct image
along `h ∣_ O` of the restriction of `E` to `h ⁻¹ᵁ O`. That restriction is zero, hence so is its
derived direct image, derived direct image being an exact functor of triangulated categories; so
`Rh_*E` restricts to zero on `O`, and an object restricting to zero on an open subscheme has its
cohomology supported on the complement of that open subscheme, which is `T`.

The second statement is the case the Fourier-Mukai theory uses. For `f : X ⟶ S` separated the
diagonal `Δ : X ⟶ X ×_S X` is a closed immersion ([Stacks, Tag 0FYV], item (1)), so its image is
closed; the diagonal kernel `𝒪_Δ = RΔ_*𝒪_X` therefore has all its cohomology supported on that
image.

## Main results

* `AlgebraicGeometry.cohomologySupportedOn_derivedPushforward_of_range_subset`: the cohomology of
  `Rh_*E` is supported on any closed set containing the image of `h`.
* `AlgebraicGeometry.cohomologySupportedOn_diagonalKernel`: the diagonal kernel of a separated
  morphism has its cohomology supported on the image of the diagonal.

## Implementation notes

Everything is stated at the **standard model** of the derived category,
`CategoryTheory.HasDerivedCategory.standard`, with a raised local instance priority. That is
forced twice over: `AlgebraicGeometry.CohomologySupportedOn` is stated at that model, and so is
`AlgebraicGeometry.diagonalKernel`; a statement about either at another model is a different
statement. The priority is needed because the import closure carries the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `SheafOfModules.hasDerivedCategory` at
universe `u` as global instances, and with those in play at equal priority instance search no
longer resolves `HasDerivedCategory.{u + 1}`.

The derived direct image is an *arbitrary* total right derived functor of direct image, given by
a functor together with its derivation unit rather than a chosen model, exactly as in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDerivedModules.lean`; the proof transports
the chosen model `Stacks.Duality.derivedPushforward` — which is the one whose exactness is
recorded — along the canonical isomorphism of `CategoryTheory.Functor.rightDerivedUnique`. This
is what lets the diagonal statement be read off for the library's canonical
`AlgebraicGeometry.derivedPushforwardModules`, which is the functor `diagonalKernel` is built
from.

Where the open-immersion statement obtains the additivity of the derived direct image along the
restricted morphism from the derived restriction-pushforward adjunction, that route is not
available for an arbitrary morphism — there the right adjoint is the content of [Stacks, Tag
0A9E]. Instead `isZero_map_of_isZero` derives the only consequence of additivity the argument
uses, that a zero object is carried to a zero object, from exactness alone: the contractible
triangle on an object maps to a distinguished triangle whose first map is invertible, so its
third vertex, the image of the zero object, vanishes. Exactness of
`Stacks.Duality.derivedPushforward` holds for an arbitrary morphism of schemes and an arbitrary
model, by `Stacks.Duality.DerivedPushforward.isTriangulated_derivedPushforward`.

The category of `𝒪_X`-modules has two definitionally equal but syntactically distinct spellings,
`AlgebraicGeometry.Scheme.Modules X` and `SheafOfModules X.ringCatSheaf`, and instance search
does not cross between them, `AlgebraicGeometry.Scheme.Modules` being a semireducible `def`. The
support predicate and the stalk API are stated in the second spelling and the restriction functor
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` in the first, so the comparison
`restrictFunctorIsoJStar` between the two restriction functors — the two left adjoints of one
direct image — is named and the crossing made at the term level. A third spelling enters with
[Stacks, Tag 08FE], which is available only for ringed spaces: there the structure sheaf of `X`
is `structureSheafRing X.toRingedSpace`, and that definition is made implicitly reducible so that
the abelian-category and derived-category instances of the sheaves of modules on an open subspace
of a scheme are found.

No `@[stacks]` attribute is attached: these are auxiliary statements about the support of a
derived direct image, and the diagonal statement is one clause of a larger example whose tag sits
on the definition of the diagonal kernel.

## References

* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction ZeroObject
open Stacks.Cohomology.ClosedSupportPerfect (pullbackOpenRestrictionIso
  derivedRestrictionAlongOpen_isRightDerived)
open Stacks.Cohomology.PushforwardRestriction (isZero_derived_of_homology_isZero
  isZero_sheafOfModules_of_stalk_isZero)
open Stacks.LocalCohomology (schemeRestrictFunctor_eq_moduleRestriction)

universe u

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing

namespace AlgebraicGeometry

/-- Restriction of sheaves of modules along the inclusion of an open subscheme is the restriction
of modules to an open subspace of the underlying space: both are left adjoint to direct image
along that inclusion. -/
private def restrictFunctorIsoJStar {X : Scheme.{u}} (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι ≅ jStar U X.ringCatSheaf :=
  ((jStarAdjunction U X.ringCatSheaf).leftAdjointUniq
    (Scheme.Modules.restrictAdjunction U.ι)).symm

/-- **The stalks of a cohomology sheaf of a restriction.** At a point `y` of an open subscheme
`U ⊆ X`, the stalk of the `n`-th cohomology sheaf of the restriction of `E` to `U` is the stalk
at the image of `y` of the `n`-th cohomology sheaf of `E`.

Restriction is exact, so it commutes with the cohomology sheaves, and restriction of modules to
an open subspace does not change stalks at points of that subspace. -/
private def stalkDerivedRestrictIso {X : Scheme.{u}} (U : X.Opens) (n : ℤ)
    (E : DerivedCategory X.Modules) (y : Usp U) :
    TopCat.Presheaf.stalk (X := Usp U)
        (((DerivedCategory.homologyFunctor U.toScheme.Modules n).obj
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)).val.presheaf) y ≅
      TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules n).obj E).val.presheaf) y.1 :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((toAb (resRing U X.ringCatSheaf)).mapIso
        (((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso n).app E ≪≫
          (restrictFunctorIsoJStar U).app _)) ≪≫
    TopCat.Presheaf.stalkRestrictIso U
      (((DerivedCategory.homologyFunctor X.Modules n).obj E).val.presheaf) y

/-- A sheaf of modules which is a zero object has all its stalks zero. -/
private theorem isZero_stalk_of_isZero_sheafOfModules {Y : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) {M : SheafOfModules.{u} O}
    (hM : IsZero M) (y : Y) :
    IsZero (TopCat.Presheaf.stalk (X := Y) M.val.presheaf y) :=
  (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero ((SheafOfModules.toSheaf O).obj M)).1
    (Functor.map_isZero (SheafOfModules.toSheaf O) hM) y

/-- **An exact functor of triangulated categories carries a zero object to a zero object.** The
contractible triangle on an object is distinguished with third vertex the zero object, and its
image under the functor is a distinguished triangle whose first map is invertible; so the image
of the zero object is zero, and so therefore is the image of any object isomorphic to it.

This is the only consequence of additivity used below, and it is available for derived direct
image along an arbitrary morphism, where additivity through a right adjoint is not. -/
private theorem isZero_map_of_isZero {A B : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    {Z : DerivedCategory A} (hZ : IsZero Z) :
    IsZero (F.obj Z) := by
  have hdist := F.map_distinguished _ (Pretriangulated.contractible_distinguished Z)
  have hiso : IsIso ((F.mapTriangle.obj (Pretriangulated.Triangle.mk (𝟙 Z)
      (0 : Z ⟶ 0) 0)).mor₁) := show IsIso (F.map (𝟙 Z)) from inferInstance
  have h0 : IsZero (F.obj (0 : DerivedCategory A)) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _ hdist hiso
  exact h0.of_iso (F.mapIso hZ.isoZero)

/-- An object of the derived category restricts to zero on an open subscheme with no points: all
the stalks of all the cohomology sheaves of the restriction are indexed by points of that open
subscheme, of which there are none. -/
private theorem isZero_derivedRestrict_of_isEmpty {X : Scheme.{u}} (U : X.Opens)
    (hU : ∀ x : X, x ∉ U) (E : DerivedCategory X.Modules) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) := by
  refine isZero_derived_of_homology_isZero _ fun n => ?_
  exact isZero_sheafOfModules_of_stalk_isZero (resRing U X.ringCatSheaf) _
    fun y => absurd y.2 (hU y.1)

/-- Alias of `Stacks.DerivedQCoh.cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict`. -/
private alias cohomologySupportedOn_compl_of_isZero_derivedRestrict :=
  Stacks.DerivedQCoh.cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict

/-- Any total right derived functor of direct image along a morphism of schemes is canonically
isomorphic to the one of
`StacksFrontier/AlgebraicGeometry/Duality/QuasiCoherentPushforwardAdjoint.lean`: both are total
right derived functors of the same functor, and a total right derived functor is unique up to a
canonical isomorphism. -/
private def derivedPushforwardIsoOfModel {V W : Scheme.{u}} (h : V ⟶ W)
    (Rh : DerivedCategory V.Modules ⥤ DerivedCategory W.Modules)
    (ηh : (Scheme.Modules.pushforward h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rh)
    [Rh.IsRightDerivedFunctor ηh
      (HomotopyCategory.quasiIso V.Modules (ComplexShape.up ℤ))] :
    Rh ≅ Stacks.Duality.derivedPushforward h :=
  Functor.rightDerivedUnique Rh (Stacks.Duality.derivedPushforward h) ηh
    ((Stacks.Duality.homotopyPushforward h).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso V.Modules (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso V.Modules (ComplexShape.up ℤ))

/-- **Derived direct image is supported on the image of the morphism.** Let `h : V ⟶ W` be a
morphism of schemes and let `T ⊆ W` be a closed set containing the set-theoretic image of `h`.
Then for every object `E` of the unbounded derived category of `𝒪_V`-modules the cohomology of
`Rh_*E` is supported on `T`, for an arbitrary total right derived functor `Rh_*` of direct image
along `h`.

Writing `O = W \ T`, the preimage `h ⁻¹ᵁ O` is empty, so the restriction of `E` to it is a zero
object; the square cut out by `O` is Cartesian, so [Stacks, Tag 08FE] identifies the restriction
to `O` of `Rh_*E` with the derived direct image along `h ∣_ O` of that zero object, which is
zero. Hence `Rh_*E` restricts to zero on `O`, and its cohomology is supported on the complement
of `O`, which is `T`. -/
theorem cohomologySupportedOn_derivedPushforward_of_range_subset {V W : Scheme.{u}} (h : V ⟶ W)
    (T : Set W) (hT : IsClosed T) (hrange : Set.range h.base ⊆ T)
    (Rh : DerivedCategory V.Modules ⥤ DerivedCategory W.Modules)
    (ηh : (Scheme.Modules.pushforward h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rh)
    [Rh.IsRightDerivedFunctor ηh
      (HomotopyCategory.quasiIso V.Modules (ComplexShape.up ℤ))]
    (E : DerivedCategory V.Modules) :
    CohomologySupportedOn W.ringCatSheaf T (Rh.obj E) := by
  let O : W.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let P : V.Opens := h ⁻¹ᵁ O
  have hPempty : ∀ x : V, x ∉ P := fun x hx => hx (hrange ⟨x, rfl⟩)
  have hsquare : IsPullback P.ι (h ∣_ O) h O.ι :=
    (AlgebraicGeometry.isPullback_morphismRestrict h O).flip
  have hRinged := AlgebraicGeometry.isPullback_toShHom P.ι (h ∣_ O) h O.ι hsquare
  let fR := h.toLRSHom.toShHom
  let gR := (h ∣_ O).toLRSHom.toShHom
  let iR := P.ι.toLRSHom.toShHom
  let jR := O.ι.toLRSHom.toShHom
  let Fi := modulePullback iR
  let Fj := modulePullback jR
  have : PreservesFiniteLimits Fi := inferInstanceAs (PreservesFiniteLimits
    (modulePullback (V.toRingedSpace.ofRestrict P.isOpenEmbedding)))
  have : PreservesFiniteColimits Fi := inferInstanceAs (PreservesFiniteColimits
    (modulePullback (V.toRingedSpace.ofRestrict P.isOpenEmbedding)))
  have : PreservesFiniteLimits Fj := inferInstanceAs (PreservesFiniteLimits
    (modulePullback (W.toRingedSpace.ofRestrict O.isOpenEmbedding)))
  have : PreservesFiniteColimits Fj := inferInstanceAs (PreservesFiniteColimits
    (modulePullback (W.toRingedSpace.ofRestrict O.isOpenEmbedding)))
  let Ri := Fi.mapDerivedCategory
  let Rv := Fj.mapDerivedCategory
  let αi := Fi.mapDerivedCategoryFactorsh.inv
  let αv := Fj.mapDerivedCategoryFactorsh.inv
  have hRi : Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    derivedRestrictionAlongOpen_isRightDerived V.toRingedSpace P
  have hRv : Rv.IsRightDerivedFunctor αv (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    derivedRestrictionAlongOpen_isRightDerived W.toRingedSpace O
  let Df := Stacks.Duality.derivedPushforward h
  let Dg := Stacks.Duality.derivedPushforward (h ∣_ O)
  let αf := (Stacks.Duality.homotopyPushforward h).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso V.Modules (ComplexShape.up ℤ))
  let αg := (Stacks.Duality.homotopyPushforward (h ∣_ O)).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso P.toScheme.Modules (ComplexShape.up ℤ))
  have hDf : Df.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso V.Modules (ComplexShape.up ℤ)) := inferInstance
  have hDg : Dg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso P.toScheme.Modules (ComplexShape.up ℤ)) := inferInstance
  have eBC : Df ⋙ Rv ≅ Ri ⋙ Dg :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _ fR iR jR gR _ _ hRinged
      _ _ _ _ Df Dg Ri Rv αf αg αi αv hDf hDg hRi hRv
  have hzeroRi : IsZero (Ri.obj E) := by
    refine isZero_derived_of_homology_isZero _ fun n => ?_
    refine IsZero.of_iso ?_ ((Fi.mapDerivedCategoryHomologyIso n).app E)
    refine IsZero.of_iso ?_ ((pullbackOpenRestrictionIso V.toRingedSpace P).app _)
    rw [← schemeRestrictFunctor_eq_moduleRestriction V P]
    refine IsZero.of_iso ?_
      (((Scheme.Modules.restrictFunctor P.ι).mapDerivedCategoryHomologyIso n).app E).symm
    exact Stacks.DerivedQCoh.isZero_homology_of_isZero
      (isZero_derivedRestrict_of_isEmpty P hPempty E) n
  have hzeroDg : IsZero ((Stacks.Duality.derivedPushforward (h ∣_ O)).obj (Ri.obj E)) :=
    isZero_map_of_isZero _ hzeroRi
  have hzeroDf : IsZero (Rv.obj (Df.obj E)) := hzeroDg.of_iso (eBC.app E)
  have hzeroRh : IsZero (Rv.obj (Rh.obj E)) :=
    hzeroDf.of_iso (Rv.mapIso ((derivedPushforwardIsoOfModel h Rh ηh).app E))
  have hzeroRes :
      IsZero ((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategory.obj (Rh.obj E)) := by
    refine isZero_derived_of_homology_isZero _ fun n => ?_
    refine IsZero.of_iso ?_
      (((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategoryHomologyIso n).app _)
    rw [schemeRestrictFunctor_eq_moduleRestriction W O]
    refine IsZero.of_iso ?_ ((pullbackOpenRestrictionIso W.toRingedSpace O).app _).symm
    refine IsZero.of_iso ?_ ((Fj.mapDerivedCategoryHomologyIso n).app _).symm
    exact Stacks.DerivedQCoh.isZero_homology_of_isZero hzeroRh n
  exact fun n x hx =>
    cohomologySupportedOn_compl_of_isZero_derivedRestrict O (Rh.obj E) hzeroRes n x fun hc => hc hx

/-- **The diagonal kernel is supported on the diagonal.** For `f : X ⟶ S` separated the diagonal
`Δ : X ⟶ X ×_S X` is a closed immersion, so the image of `Δ` is a closed subset of `X ×_S X`
containing the image of `Δ`; the diagonal kernel `𝒪_Δ = RΔ_*𝒪_X` of [Stacks, Tag 0FYV]
therefore has every one of its cohomology sheaves supported on that image. -/
theorem cohomologySupportedOn_diagonalKernel {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    CohomologySupportedOn (Limits.pullback f f).ringCatSheaf
      (Set.range (Limits.pullback.diagonal f).base) (diagonalKernel f) :=
  cohomologySupportedOn_derivedPushforward_of_range_subset (Limits.pullback.diagonal f) _
    (IsClosedImmersion.isClosedEmbedding (Limits.pullback.diagonal f)).isClosed_range
    subset_rfl (derivedPushforwardModules (Limits.pullback.diagonal f))
    (derivedPushforwardModulesUnit (Limits.pullback.diagonal f)) _

end AlgebraicGeometry

end
