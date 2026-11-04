module

public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRelativeTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOverTorAmplitude
import StacksCore.Tactic.StacksAttribute

/-!
# Locally finite Tor dimension across the Zariski-to-étale comparison

Let `f : X ⟶ Y` be a morphism of schemes and let
`ε = id_{small, étale, Zar} : X_étale ⟶ X_Zar` be the comparison of Stacks 08H7 read with
coefficients in `f⁻¹𝒪_Y`, with `ε^*` its pullback of sheaves of modules.  An object `E` of
`D(f⁻¹𝒪_Y)` locally has finite Tor dimension, in the sense of Stacks 08FZ (3), exactly when
`ε^*E` does: this is part (2) of Stacks 0DK7.

## Main results

All results live in the namespace `AlgebraicGeometry.SmallEtale`.

* `hasTorAmplitude_derivedRestriction_inverseImageRingedSite_iff`: `E|_V` has Tor amplitude in
  `[a, b]` on an open `V` of `X` exactly when the stalk `E_y` does at every `y ∈ V`.
* `hasTorAmplitude_derivedRestriction_relativeRingedTopos_iff`: `(ε^*E)|_W` has Tor amplitude in
  `[a, b]` on an object `W` of the small étale site of `X` exactly when the stalk `E_x` does at
  every point `x` of `X` whose geometric point lifts to `W`.
* `hasTorAmplitude_derivedRestriction_of_relativeDerivedAssociatedModule`: Tor amplitude of
  `ε^*E` in a nonempty interval gives Tor amplitude of `E|_U` in that interval, for every open
  `U` of `X`.
* `locallyHasFiniteTorDimension_of_relativeDerivedAssociatedModule`: finite Tor dimension of
  `ε^*E` gives locally finite Tor dimension of `E`.
* `hasTorAmplitude_derivedRestriction_relativeDerivedAssociatedModule`: Tor amplitude of `E`
  gives Tor amplitude of `(ε^*E)|_W` in the same interval, for every object `W` of the small étale
  site of `X`.
* `locallyHasFiniteTorDimension_relativeDerivedAssociatedModule`: **Stacks 0DK7, part (2).**

## Implementation notes

*Everything is read at the stalks.*  Tor amplitude on a slice is read at the points of the slice
by Stacks 0DJJ, and the points of a slice are the localizations of the points of the site lying
over it (Mathlib's `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over`, which
applies because both families used are indexed by the points of `X`); the stalk of a
restriction at a localized point is the stalk at the point itself (Stacks 04H2, in the form
`Stacks.hasTorAmplitudeCanonical_sheafModuleFiber_over_iff`), and the stalk of `ε^*E` at the
geometric point of `X` at `x` is the stalk of `E` at `x`
(`hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff`).

*The two local-to-global steps.*  An open covering of `X` with an interval on each member gives
the étale covering of any `W` by the objects mapping into one of the members, by
cover-preservation of the inclusion of the small Zariski site
(`AlgebraicGeometry.SmallEtale.coverPreserving_opensToSmallEtale`).  Conversely an étale covering
of `X` with an interval on each member gives the open covering of `X` by the images of the
members, which are open, the members being étale over `X`; every point of such an image has its
geometric point lifting to the member, because the source of the geometric point is the spectrum
of a separably closed field (`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`).

*The derived tensor products on the slices.*  Tor amplitude on a slice is measured against a
derived tensor product datum on that slice, so the local predicate takes a family indexed by
the objects of the site; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/LocallyFiniteTorDimension.lean`.  The
families are arbitrary in all the statements, as they are there.

## References

* [Stacks Project, Tag 0DK7](https://stacks.math.columbia.edu/tag/0DK7)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u d e u₁ v₁

attribute [local instance] AlgebraicGeometry.smallEtale_hasSheafify
  AlgebraicGeometry.smallEtale_wEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  Stacks.hasSheafCompose_forget₂_commRingCat

namespace AlgebraicGeometry.SmallEtale

open Stacks.SheafOfModules.DerivedTensorProduct StacksDraft.TorAmplitude

/-! ### The stalk of a restriction at a localized point -/

section SliceStalk

/-- The derived stalk at a localized point `Φ.over q` of the restriction of `E` to a slice has
Tor amplitude in `[a, b]` exactly when the derived stalk of `E` at `Φ` does (Stacks 04H2), for
derived categories of sheaves of modules at an arbitrary hom universe. -/
private theorem hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z : RingedSite.{u₁, v₁, u}) [LocallySmall.{u} Z.C]
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
    [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [hZ : HasDerivedCategory.{d} (RingedSite.Modules.{u₁, v₁, u} Z)]
    [hZs : ∀ U : Z.C, HasDerivedCategory.{d} (RingedSite.Modules.{max u₁ v₁, v₁, u} (Z.over U))]
    (Φ : Z.J.Point.{u}) {V : Z.C} (q : Φ.fiber.obj V)
    (E : RingedSite.DerivedModules.{u₁, v₁, u, d} Z) (a b : ℤ) :
    letI : HasDerivedCategory.{d} (SheafOfModules.{u}
        (Stacks.commRingSheafToRingSheaf.{v₁, max u₁ v₁, u} (J := Z.J.over V)
        (Z.over V).O)) := hZs V
    letI : HasDerivedCategory.{d} (SheafOfModules.{u}
        (Stacks.commRingSheafToRingSheaf.{v₁, u₁, u} Z.O)) := hZ
    letI := HasDerivedCategory.standard (ModuleCat.{u}
      (((Φ.over q).presheafFiber (A := CommRingCat.{u})).obj (Z.over V).O.obj))
    letI := HasDerivedCategory.standard (ModuleCat.{u}
      ((Φ.presheafFiber (A := CommRingCat.{u})).obj Z.O.obj))
    HasTorAmplitudeCanonical (((Φ.over q).presheafFiber (A := CommRingCat.{u})).obj
        (Z.over V).O.obj)
      ((Stacks.derivedModuleFiber (Φ.over q) (Z.over V).O).obj
        ((RingedSite.derivedRestriction.{u₁, v₁, u, d} Z V).obj E)) a b ↔
      HasTorAmplitudeCanonical ((Φ.presheafFiber (A := CommRingCat.{u})).obj Z.O.obj)
        ((Stacks.derivedModuleFiber Φ Z.O).obj E) a b := by
  let : HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{v₁, max u₁ v₁, u} (J := Z.J.over V)
        (Z.over V).O)) := hZs V
  let : HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{v₁, u₁, u} Z.O)) := hZ
  let := HasDerivedCategory.standard (ModuleCat.{u}
    (((Φ.over q).presheafFiber (A := CommRingCat.{u})).obj (Z.over V).O.obj))
  let := HasDerivedCategory.standard (ModuleCat.{u}
    ((Φ.presheafFiber (A := CommRingCat.{u})).obj Z.O.obj))
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let Fib := Stacks.sheafModuleFiberOfCommRing Φ Z.O
  let Fib' := Stacks.sheafModuleFiberOfCommRing (Φ.over q) (Z.over V).O
  let Res := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u₁, v₁, u} Z.O) V
  let e₁ : (Stacks.derivedModuleFiber (Φ.over q) (Z.over V).O).obj
        ((RingedSite.derivedRestriction Z V).obj E) ≅
      DerivedCategory.Q.obj ((Fib'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Res.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    (Stacks.derivedModuleFiber (Φ.over q) (Z.over V).O).mapIso
        ((RingedSite.derivedRestriction Z V).mapIso eK.symm ≪≫
          Res.mapDerivedCategoryFactors.app K) ≪≫
      Fib'.mapDerivedCategoryFactors.app _
  let e₂ : (Stacks.derivedModuleFiber Φ Z.O).obj E ≅
      DerivedCategory.Q.obj ((Fib.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (Stacks.derivedModuleFiber Φ Z.O).mapIso eK.symm ≪≫ Fib.mapDerivedCategoryFactors.app K
  have key := Stacks.hasTorAmplitudeCanonical_sheafModuleFiber_over_iff Φ q Z.O K a b
  exact ⟨fun h => BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₂.symm a b
      (key.1 (BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₁ a b h)),
    fun h => BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₁.symm a b
      (key.2 (BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₂ a b h))⟩

/-- Tor amplitude of the restriction of `E` to a slice `Z/V` is read at the stalks, over the points
of a conservative family of `Z`, at the points `Φ` of the family which lie over `V`
(Stacks 0DJJ on the slice and Stacks 04H2). -/
private theorem hasTorAmplitude_derivedRestriction_iff_forall_fiber
    (Z : RingedSite.{u₁, v₁, u}) [LocallySmall.{u} Z.C]
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify Z.J (Type u)] [Z.J.WEqualsLocallyBijective (Type u)]
    [∀ U : Z.C, LocallySmall.{u} (Z.over U).C]
    [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
    [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [hZ : HasDerivedCategory.{d} (RingedSite.Modules.{u₁, v₁, u} Z)]
    [hZs : ∀ U : Z.C, HasDerivedCategory.{d} (RingedSite.Modules.{max u₁ v₁, v₁, u} (Z.over U))]
    [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{max u₁ v₁, v₁, u, u, u}
      (Z.over U).O).Additive]
    [∀ (U : Z.C) M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u₁ v₁, v₁, u, u, u}
      (Z.over U).O).obj M).Additive]
    [∀ (U : Z.C) (K L : CochainComplex
        (RingedSite.Modules.{max u₁ v₁, v₁, u} (Z.over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]
    {P : ObjectProperty Z.J.Point.{u}} [P.Small.{u}] (hP : P.IsConservativeFamilyOfPoints)
    {V : Z.C} [HasSheafify (Z.J.over V) (Type u)]
    (TV : Stacks.SheafOfModules.DerivedTensorProduct.{max u₁ v₁, v₁, u, d} (Z.over V))
    (E : RingedSite.DerivedModules.{u₁, v₁, u, d} Z) (a b : ℤ) :
    HasTorAmplitude TV ((RingedSite.derivedRestriction.{u₁, v₁, u, d} Z V).obj E) a b ↔
      ∀ Φ : P.FullSubcategory, Φ.obj.fiber.obj V →
        letI : HasDerivedCategory.{d} (SheafOfModules.{u}
            (Stacks.commRingSheafToRingSheaf.{v₁, u₁, u} Z.O)) := hZ
        letI := HasDerivedCategory.standard (ModuleCat.{u}
          ((Φ.obj.presheafFiber (A := CommRingCat.{u})).obj Z.O.obj))
        HasTorAmplitudeCanonical ((Φ.obj.presheafFiber (A := CommRingCat.{u})).obj Z.O.obj)
          ((Stacks.derivedModuleFiber Φ.obj Z.O).obj E) a b :=
  ⟨fun h Φ q => (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff Z Φ.obj q E a b).1
      (hasTorAmplitudeCanonical_derivedModuleFiber TV _ a b h _),
    fun h => hasTorAmplitude_of_forall_derivedModuleFiber_family TV _ a b
      (fun ψ : Σ Φ : P.FullSubcategory, Φ.obj.fiber.obj V => ψ.1.obj.over ψ.2) (hP.over V)
      fun ψ => (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff Z ψ.1.obj ψ.2 E a b).2
        (h ψ.1 ψ.2)⟩

end SliceStalk

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) {Y : Scheme.{u}}
  (f : X ⟶ Y)

section Derived

variable
  [hd : HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Scheme.Hom.inverseImageRingedSite f))]
  [he : HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} (relativeRingedTopos B X hX f).toRingedSite)]

/-! ### Tor amplitude on a slice, read at the points of `X` -/

section ZariskiSlices

variable
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    HasSheafify ((Scheme.Hom.inverseImageRingedSite f).J.over U) AddCommGrpCat.{u}]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    ((Scheme.Hom.inverseImageRingedSite f).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C, HasDerivedCategory.{d}
    (RingedSite.Modules.{u, u, u} ((Scheme.Hom.inverseImageRingedSite f).over U))]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Scheme.Hom.inverseImageRingedSite f).over U).O).Additive]
  [∀ (U : (Scheme.Hom.inverseImageRingedSite f).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Scheme.Hom.inverseImageRingedSite f).over U).O).obj M).Additive]
  [∀ (U : (Scheme.Hom.inverseImageRingedSite f).C) (K L : CochainComplex
      (RingedSite.Modules.{u, u, u} ((Scheme.Hom.inverseImageRingedSite f).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((Scheme.Hom.inverseImageRingedSite f).over U).O) (ComplexShape.up ℤ)]

/-- **Tor amplitude on an open of `X`, read at its points.**  The restriction of `E` to an open
`V` of `X` has Tor amplitude in `[a, b]` exactly when the derived stalk `E_y` has Tor amplitude in
`[a, b]` over `(f⁻¹𝒪_Y)_y` at every point `y ∈ V`: Stacks 0DJJ on the slice, whose points are the
localizations of the points of `X` lying in `V`, and Stacks 04H2. -/
theorem hasTorAmplitude_derivedRestriction_inverseImageRingedSite_iff
    (V : (Scheme.Hom.inverseImageRingedSite f).C)
    (TV : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
      ((Scheme.Hom.inverseImageRingedSite f).over V))
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f))
    (a b : ℤ) :
    HasTorAmplitude TV
        ((RingedSite.derivedRestriction.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f) V).obj
          E) a b ↔
      ∀ y : X, y ∈ V →
        letI : HasDerivedCategory.{d} (SheafOfModules.{u}
            (Stacks.commRingSheafToRingSheaf.{u, u, u} (Scheme.Hom.inverseImageRingedSite f).O)) :=
          hd
        letI := HasDerivedCategory.standard (ModuleCat.{u}
          (((Opens.pointGrothendieckTopology y).presheafFiber (A := CommRingCat.{u})).obj
            (Scheme.Hom.inverseImageRingedSite f).O.obj))
        HasTorAmplitudeCanonical
          (((Opens.pointGrothendieckTopology y).presheafFiber (A := CommRingCat.{u})).obj
            (Scheme.Hom.inverseImageRingedSite f).O.obj)
          ((Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology y)
            (Scheme.Hom.inverseImageRingedSite f).O).obj E) a b := by
  refine (hasTorAmplitude_derivedRestriction_iff_forall_fiber (Scheme.Hom.inverseImageRingedSite f)
    (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X) TV E a b).trans
    ⟨fun h y hy => h ⟨_, ⟨y⟩⟩ ⟨⟨hy⟩⟩, ?_⟩
  rintro h ⟨_, ⟨y⟩⟩ z
  exact h y z.down.down

end ZariskiSlices

section EtaleSlices

variable
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    HasSheafify ((relativeRingedTopos B X hX f).toRingedSite.J.over W) AddCommGrpCat.{u}]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    ((relativeRingedTopos B X hX f).toRingedSite.J.over W).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C, HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} ((relativeRingedTopos B X hX f).toRingedSite.over W))]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((relativeRingedTopos B X hX f).toRingedSite.over W).O).Additive]
  [∀ (W : (relativeRingedTopos B X hX f).toRingedSite.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((relativeRingedTopos B X hX f).toRingedSite.over W).O).obj M).Additive]
  [∀ (W : (relativeRingedTopos B X hX f).toRingedSite.C) (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u}
        ((relativeRingedTopos B X hX f).toRingedSite.over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((relativeRingedTopos B X hX f).toRingedSite.over W).O) (ComplexShape.up ℤ)]

/-- **Tor amplitude of `ε^*E` on an object of the small étale site, read at the points of `X`.**
The restriction of `ε^*E` to an object `W` of the small étale site of `X` has Tor amplitude in
`[a, b]` exactly when the derived stalk `E_x` has Tor amplitude in `[a, b]` over `(f⁻¹𝒪_Y)_x` at
every point `x` of `X` whose geometric point lifts to `W`: Stacks 0DJJ on the slice, whose points
are the localizations of the geometric points of `X` lifting to `W`, Stacks 04H2, and the
comparison of the stalks of `ε^*E` with those of `E`. -/
theorem hasTorAmplitude_derivedRestriction_relativeRingedTopos_iff
    (W : (relativeRingedTopos B X hX f).toRingedSite.C)
    (TW : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
      ((relativeRingedTopos B X hX f).toRingedSite.over W))
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f))
    (a b : ℤ) :
    HasTorAmplitude TW
        ((RingedSite.derivedRestriction.{u + 1, u, u, e}
          (relativeRingedTopos B X hX f).toRingedSite W).obj
          ((relativeDerivedAssociatedModule B X hX f).obj E)) a b ↔
      ∀ x : X, (relativeEtalePoint B X hX x).fiber.obj W →
        letI : HasDerivedCategory.{d} (SheafOfModules.{u}
            (Stacks.commRingSheafToRingSheaf.{u, u, u} (Scheme.Hom.inverseImageRingedSite f).O)) :=
          hd
        letI := HasDerivedCategory.standard (ModuleCat.{u}
          (((Opens.pointGrothendieckTopology x).presheafFiber (A := CommRingCat.{u})).obj
            (Scheme.Hom.inverseImageRingedSite f).O.obj))
        HasTorAmplitudeCanonical
          (((Opens.pointGrothendieckTopology x).presheafFiber (A := CommRingCat.{u})).obj
            (Scheme.Hom.inverseImageRingedSite f).O.obj)
          ((Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology x)
            (Scheme.Hom.inverseImageRingedSite f).O).obj E) a b := by
  let : (topology B X hX).WEqualsLocallyBijective (Type u) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasSheafify ((topology B X hX).over W) (Type u) := hasSheafifyEssentiallySmallSite _ _
  refine (hasTorAmplitude_derivedRestriction_iff_forall_fiber
    (relativeRingedTopos B X hX f).toRingedSite
    (isConservativeFamilyOfPoints_geometricSitePoints B X hX) TW
    ((relativeDerivedAssociatedModule B X hX f).obj E) a b).trans ⟨fun h x p => ?_, ?_⟩
  · exact (hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff
      B X hX f x E a b).1 (h ⟨_, ⟨x⟩⟩ p)
  · rintro h ⟨_, ⟨x⟩⟩ z
    exact (hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff
      B X hX f x E a b).2 (h x z)

end EtaleSlices

/-! ### Tor amplitude on the slices, from either side of the comparison -/

section Global

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (Scheme.Hom.inverseImageRingedSite f).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (Scheme.Hom.inverseImageRingedSite f).O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u, u, u} (Scheme.Hom.inverseImageRingedSite f)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Scheme.Hom.inverseImageRingedSite f).O)
      (ComplexShape.up ℤ)]

variable
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
    (Scheme.Hom.inverseImageRingedSite f))

section Zariski

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (relativeRingedTopos B X hX f).toRingedSite.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (relativeRingedTopos B X hX f).toRingedSite.O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} (relativeRingedTopos B X hX f).toRingedSite) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (relativeRingedTopos B X hX f).toRingedSite.O)
      (ComplexShape.up ℤ)]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    HasSheafify ((Scheme.Hom.inverseImageRingedSite f).J.over U) AddCommGrpCat.{u}]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    ((Scheme.Hom.inverseImageRingedSite f).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C, HasDerivedCategory.{d}
    (RingedSite.Modules.{u, u, u} ((Scheme.Hom.inverseImageRingedSite f).over U))]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Scheme.Hom.inverseImageRingedSite f).over U).O).Additive]
  [∀ (U : (Scheme.Hom.inverseImageRingedSite f).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Scheme.Hom.inverseImageRingedSite f).over U).O).obj M).Additive]
  [∀ (U : (Scheme.Hom.inverseImageRingedSite f).C) (K L : CochainComplex
      (RingedSite.Modules.{u, u, u} ((Scheme.Hom.inverseImageRingedSite f).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((Scheme.Hom.inverseImageRingedSite f).over U).O) (ComplexShape.up ℤ)]

variable
  (T' : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
    (relativeRingedTopos B X hX f).toRingedSite)

include T in
/-- **Tor amplitude read off from the étale side restricts to every open.**  If `ε^*E` has Tor
amplitude in a nonempty interval `[a, b]`, then the restriction of `E` to the Zariski site of
`X` localized at an open `U` has Tor amplitude in `[a, b]`.

This is part (1) of Stacks 0DK7 followed by the inheritance of Tor amplitude by a slice. -/
theorem hasTorAmplitude_derivedRestriction_of_relativeDerivedAssociatedModule
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f))
    (U : (Scheme.Hom.inverseImageRingedSite f).C)
    (TU : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
      ((Scheme.Hom.inverseImageRingedSite f).over U))
    (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T' ((relativeDerivedAssociatedModule B X hX f).obj E) a b) :
    HasTorAmplitude TU
      ((RingedSite.derivedRestriction.{u, u, u, d}
        (Scheme.Hom.inverseImageRingedSite f) U).obj E) a b :=
  hasTorAmplitude_derivedRestriction T U TU E a b hab
    ((hasTorAmplitude_relativeDerivedAssociatedModule_iff B X hX f T T' E a b).2 hamp)

include T in
/-- **Finite Tor dimension on the étale side gives locally finite Tor dimension on the Zariski
side.**  If `ε^*E` has finite Tor dimension then `E` locally has finite Tor dimension in the
sense of Stacks 08FZ (3), the maximal covering of each open witnessing the local condition. -/
theorem locallyHasFiniteTorDimension_of_relativeDerivedAssociatedModule
    (TU : ∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
        ((Scheme.Hom.inverseImageRingedSite f).over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f))
    (h : HasFiniteTorDimension T' ((relativeDerivedAssociatedModule B X hX f).obj E)) :
    LocallyHasFiniteTorDimension TU E :=
  locallyHasFiniteTorDimension_of_hasFiniteTorDimension T TU E
    ((hasFiniteTorDimension_relativeDerivedAssociatedModule_iff B X hX f T T' E).2 h)

end Zariski

section Etale

variable
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    HasSheafify ((relativeRingedTopos B X hX f).toRingedSite.J.over W) AddCommGrpCat.{u}]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    ((relativeRingedTopos B X hX f).toRingedSite.J.over W).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C, HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} ((relativeRingedTopos B X hX f).toRingedSite.over W))]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((relativeRingedTopos B X hX f).toRingedSite.over W).O).Additive]
  [∀ (W : (relativeRingedTopos B X hX f).toRingedSite.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((relativeRingedTopos B X hX f).toRingedSite.over W).O).obj M).Additive]
  [∀ (W : (relativeRingedTopos B X hX f).toRingedSite.C) (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u}
        ((relativeRingedTopos B X hX f).toRingedSite.over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((relativeRingedTopos B X hX f).toRingedSite.over W).O) (ComplexShape.up ℤ)]

/-- **Tor amplitude transported to a slice of the small étale site.**  If `E` has Tor amplitude
in `[a, b]`, then the restriction of `ε^*E` to the small étale site of `X` localized at an object
`W` has Tor amplitude in `[a, b]`.

The stalks of `E` have Tor amplitude in `[a, b]` by Stacks 0DJJ (1), and those are the stalks of
`(ε^*E)|_W` by `hasTorAmplitude_derivedRestriction_relativeRingedTopos_iff`. -/
theorem hasTorAmplitude_derivedRestriction_relativeDerivedAssociatedModule
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f))
    (W : (relativeRingedTopos B X hX f).toRingedSite.C)
    (TW : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
      ((relativeRingedTopos B X hX f).toRingedSite.over W))
    (a b : ℤ) (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude TW
      ((RingedSite.derivedRestriction.{u + 1, u, u, e}
        (relativeRingedTopos B X hX f).toRingedSite W).obj
        ((relativeDerivedAssociatedModule B X hX f).obj E)) a b :=
  (hasTorAmplitude_derivedRestriction_relativeRingedTopos_iff B X hX f W TW E a b).2
    fun _ _ => hasTorAmplitudeCanonical_derivedModuleFiber T E a b hamp _

end Etale

end Global

/-! ### Stacks 0DK7, part (2) -/

section Local

variable
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    HasSheafify ((Scheme.Hom.inverseImageRingedSite f).J.over U) AddCommGrpCat.{u}]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    ((Scheme.Hom.inverseImageRingedSite f).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C, HasDerivedCategory.{d}
    (RingedSite.Modules.{u, u, u} ((Scheme.Hom.inverseImageRingedSite f).over U))]
  [∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Scheme.Hom.inverseImageRingedSite f).over U).O).Additive]
  [∀ (U : (Scheme.Hom.inverseImageRingedSite f).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Scheme.Hom.inverseImageRingedSite f).over U).O).obj M).Additive]
  [∀ (U : (Scheme.Hom.inverseImageRingedSite f).C) (K L : CochainComplex
      (RingedSite.Modules.{u, u, u} ((Scheme.Hom.inverseImageRingedSite f).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((Scheme.Hom.inverseImageRingedSite f).over U).O) (ComplexShape.up ℤ)]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    HasSheafify ((relativeRingedTopos B X hX f).toRingedSite.J.over W) AddCommGrpCat.{u}]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    ((relativeRingedTopos B X hX f).toRingedSite.J.over W).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C, HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} ((relativeRingedTopos B X hX f).toRingedSite.over W))]
  [∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((relativeRingedTopos B X hX f).toRingedSite.over W).O).Additive]
  [∀ (W : (relativeRingedTopos B X hX f).toRingedSite.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((relativeRingedTopos B X hX f).toRingedSite.over W).O).obj M).Additive]
  [∀ (W : (relativeRingedTopos B X hX f).toRingedSite.C) (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u}
        ((relativeRingedTopos B X hX f).toRingedSite.over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((relativeRingedTopos B X hX f).toRingedSite.over W).O) (ComplexShape.up ℤ)]

/-- **Stacks 0DK7, part (2).**  Let `f : X ⟶ Y` be a morphism of schemes and let `E` be an object
of `D(f⁻¹𝒪_Y)`.  Then `E` locally has finite Tor dimension if and only if `ε^*E` locally has
finite Tor dimension as an object of `D(ε⁻¹f⁻¹𝒪_Y)`, in the sense of Stacks 08FZ (3), for any
families of derived tensor products on the slices of the two sites.

Both conditions are read at the points of `X`.  An open covering of `X` with an interval on each
member gives, on any object `W` of the small étale site, the covering by the objects mapping into
one of the members, which is the pullback to `W` of the image of the open covering, a covering
because the inclusion of the small Zariski site is cover-preserving.  An étale covering of `X`
with an interval on each member gives the open covering of `X` by the images of the members,
open because the members are étale over `X`, every point of an image having its geometric point
lift to the member. -/
@[stacks 0DK7 "part (2), with `ε⁻¹f⁻¹𝒪_Y` for `f_small⁻¹𝒪_{Y_étale}`; see the implementation \
notes of the module of part (1).  The form with `f_small⁻¹𝒪_{Y_étale}` itself is, in \
`AlgebraicGeometry.Space`, \
`locallyHasFiniteTorDimension_derivedScalarRestriction_iff_representedZariskiDerivedPullback`"]
theorem locallyHasFiniteTorDimension_relativeDerivedAssociatedModule
    (TU : ∀ U : (Scheme.Hom.inverseImageRingedSite f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
        ((Scheme.Hom.inverseImageRingedSite f).over U))
    (TW : ∀ W : (relativeRingedTopos B X hX f).toRingedSite.C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((relativeRingedTopos B X hX f).toRingedSite.over W))
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f)) :
    LocallyHasFiniteTorDimension TU E ↔
      LocallyHasFiniteTorDimension TW ((relativeDerivedAssociatedModule B X hX f).obj E) := by
  refine ⟨fun h W => ?_, fun h U => ?_⟩
  · obtain ⟨S₀, hS₀, hfin⟩ := h ⊤
    let g₀ : W ⟶ (opensToSmallEtale B X hX).obj ⊤ := homOfRangeLe B X hX ⊤ (by simp)
    let R : Sieve W :=
      ((Sieve.generate S₀).functorPushforward (opensToSmallEtale B X hX)).pullback g₀
    have hR : R ∈ topology B X hX W := (topology B X hX).pullback_stable g₀
      ((coverPreserving_opensToSmallEtale B X hX).cover_preserve hS₀)
    refine ⟨R.arrows, by rwa [Sieve.generate_sieve], fun W' g hg => ?_⟩
    obtain ⟨V', k, h₁, ⟨V, k₁, k₂, hk₂, -⟩, -⟩ := hg
    obtain ⟨a, b, hab⟩ := hfin k₂ hk₂
    refine ⟨a, b, (hasTorAmplitude_derivedRestriction_relativeRingedTopos_iff B X hX f W' (TW W')
      E a b).2 fun x p => ?_⟩
    have hx : x ∈ V := mem_of_relativeEtalePoint_fiber B X hX
      ((relativeEtalePoint B X hX x).fiber.map (h₁ ≫ (opensToSmallEtale B X hX).map k₁) p)
    exact (hasTorAmplitude_derivedRestriction_inverseImageRingedSite_iff X f V (TU V) E a b).1
      hab x hx
  · obtain ⟨R, hR, hfin⟩ := h ((opensToSmallEtale B X hX).obj U)
    refine ⟨fun V _ => ∃ a b : ℤ, HasTorAmplitude (TU V)
        ((RingedSite.derivedRestriction (Scheme.Hom.inverseImageRingedSite f) V).obj E) a b, ?_,
      fun _ _ h => h⟩
    intro y hy
    obtain ⟨W'', g, ⟨W', h₁, g', hg', -⟩, p, -⟩ :=
      (relativeEtalePoint B X hX y).jointly_surjective _ hR (relativeEtalePointFiberOfMem B X hX hy)
    obtain ⟨a, b, hab⟩ := hfin g' hg'
    let p' := (relativeEtalePoint B X hX y).fiber.map h₁ p
    let φ := B.inclusion.map W'.obj.hom
    let V : X.Opens := ⟨Set.range φ, φ.isOpenMap.isOpen_range⟩
    have hVU : V ≤ U := BigEtaleOver.range_le_of_hom B X hX g'.hom
    refine ⟨V, homOfLE hVU, ⟨V, 𝟙 V, homOfLE hVU, ⟨a, b,
      (hasTorAmplitude_derivedRestriction_inverseImageRingedSite_iff X f V (TU V) E a b).2
        fun z hz => ?_⟩, Category.id_comp _⟩, ?_⟩
    · obtain ⟨w, hw⟩ := hz
      obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed φ
        (GeometricPoint.ofPoint X z).hom w (hw.trans (GeometricPoint.ofPoint_liesOver X z).symm)
      exact (hasTorAmplitude_derivedRestriction_relativeRingedTopos_iff B X hX f W' (TW W') E a
        b).1 hab z ⟨l, hl⟩
    · have hp' : p'.1 ≫ φ = (GeometricPoint.ofPoint X y).hom := p'.2
      exact ⟨p'.1 default, (Scheme.Hom.comp_apply p'.1 φ _).symm.trans
        ((congrArg (fun k => k default) hp').trans (GeometricPoint.ofPoint_liesOver X y))⟩

end Local

end Derived

end AlgebraicGeometry.SmallEtale

end
