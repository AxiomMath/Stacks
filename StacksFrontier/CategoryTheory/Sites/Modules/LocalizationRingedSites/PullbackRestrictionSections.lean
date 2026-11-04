module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackRestrictionUnderlying

/-!
# The structure map of the localization of a ringed site, and morphism identities

Let `(C, O)` be a ringed site and `U` an object of `C`. This file shows that the localization
morphism of the modules development and the four-field morphism attached to the two-field
localization morphism of ringed topoi have the same structure map, names the inverse image of the
structure sheaf along the localization and the underlying-sheaf functors over it, and proves
identities between composites of morphisms, transports and natural isomorphisms in a category.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationInverseImageRingSheaf`: the inverse image of the
  structure sheaf along the localization at `U`, as a sheaf of rings.
* `AlgebraicGeometry.RingedSite.localizationRestrictScalarsFolded`: restriction of scalars along
  the structure map of the localization.
* `AlgebraicGeometry.RingedSite.localizationModuleForgetInverse`,
  `AlgebraicGeometry.RingedSite.localizationModuleForgetSlice` and
  `AlgebraicGeometry.RingedSite.localizationModuleForgetTarget`: underlying sheaves of sets of
  modules over the rings of the localization.

## Main results

* `Stacks.Sheaves.ToposPullback.comp_eqToHom_of_eq`: a morphism `ν a : P ⟶ B a` indexed by a
  parameter, followed by the transport along `a = a'`, is `ν a'`.
* `Stacks.Sheaves.ToposPullback.map_eqToIso_trans_iso_app`: a natural isomorphism preceded by two
  transports, at an object and through a functor, is one transport followed by the isomorphism.
* `AlgebraicGeometry.RingedSite.fSharpInverseImage_toModulesHom_localizationRingedToposHom`: the
  two presentations of the localization morphism have the same inverse-image structure map.
* `AlgebraicGeometry.RingedSite.fSharpCommRing_toModulesHom_localizationRingedToposHom`: the two
  presentations of the localization morphism have the same structure map, read as a morphism of
  presheaves of commutative rings.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
  Stacks.Sheaves.RingedToposModules

/-! ## A transport of a parametrized morphism -/

namespace Stacks.Sheaves.ToposPullback

/-- **A morphism out of a fixed object, indexed by a parameter, followed by the transport along an
equality of parameters.** If `ν a : P ⟶ B a` is defined for every value `a` of a parameter, and
two values are equal, then `ν` at the first followed by the transport is `ν` at the second. -/
theorem comp_eqToHom_of_eq {α : Type*} {T : Type*} [Category* T] {P : T} (B : α → T)
    (ν : ∀ a : α, P ⟶ B a) {a a' : α} (e : a = a') (p : B a = B a') :
    ν a ≫ eqToHom p = ν a' := by
  cases e
  exact Category.comp_id (ν a)

/-- **The underlying morphism of a composite of three natural isomorphisms, at an object.** -/
theorem map_iso_trans_three_app {A B D : Type*} [Category* A] [Category* B] [Category* D]
    {F G H K : A ⥤ B} (α : F ≅ G) (β : G ≅ H) (γ : H ≅ K) (Φ : B ⥤ D) (Z : A) :
    Φ.map ((α ≪≫ β ≪≫ γ).hom.app Z) =
      (Φ.map (α.hom.app Z) ≫ Φ.map (β.hom.app Z)) ≫ Φ.map (γ.hom.app Z) := by
  simp

/-- **Two transports of functors, at an object and through a functor, compose to one transport.**
-/
theorem map_eqToIso_app_trans {A B D : Type*} [Category* A] [Category* B] [Category* D]
    {F G H : A ⥤ B} (hFG : F = G) (hGH : G = H) (Φ : B ⥤ D) (Z : A)
    (p : Φ.obj (F.obj Z) = Φ.obj (H.obj Z)) :
    Φ.map ((eqToIso hFG).hom.app Z) ≫ Φ.map ((eqToIso hGH).hom.app Z) = eqToHom p := by
  cases hFG
  cases hGH
  simp

/-- **A natural isomorphism preceded by two transports, at an object and through a functor.**
The two transports collapse to one `CategoryTheory.eqToHom`, followed by the image of the
isomorphism. -/
theorem map_eqToIso_trans_iso_app {A B D : Type*} [Category* A] [Category* B] [Category* D]
    {F G H K : A ⥤ B} (hFG : F = G) (hGH : G = H) (γ : H ≅ K) (Φ : B ⥤ D) (Z : A)
    (p : Φ.obj (F.obj Z) = Φ.obj (H.obj Z)) :
    Φ.map ((eqToIso hFG ≪≫ eqToIso hGH ≪≫ γ).hom.app Z) =
      eqToHom p ≫ Φ.map (γ.hom.app Z) := by
  cases hFG
  cases hGH
  simp

/-- **A composite is recovered from a composite with an extra identity factor.** If `a` is `n`
followed by `i`, `i` is an identity, and `a ≫ m` is `z`, then `n ≫ m` is `z`. -/
theorem comp_eq_of_eq_comp_of_eq_id {T : Type*} [Category* T] {P Q R : T}
    (n a : P ⟶ Q) (i : Q ⟶ Q) (m : Q ⟶ R) (z : P ⟶ R)
    (ha : a = n ≫ i) (hi : i = 𝟙 Q) (hr : a ≫ m = z) : n ≫ m = z := by
  subst ha hi
  simpa using hr

/-- An identity factor in front of a morphism drops out. -/
theorem comp_eq_of_eq_id {T : Type*} [Category* T] {P Q : T} (i : P ⟶ P) (m : P ⟶ Q)
    (hi : i = 𝟙 P) : i ≫ m = m := by
  simp [hi]

/-- **A composite of three morphisms through a functor, with the first two regrouped.** Given
`a = n ≫ t` and `a ≫ m = r` in the source category, and the value `y` of `Φ t ≫ Φ m`, the image
`Φ n ≫ y` is the image of `r`. -/
theorem map_comp_eq_of_eq {T T' : Type*} [Category* T] [Category* T'] (Φ : T ⥤ T')
    {P Q R S : T} (n : P ⟶ R) (t : R ⟶ Q) (m : Q ⟶ S) (a : P ⟶ Q) (r : P ⟶ S)
    {y : Φ.obj R ⟶ Φ.obj S} {w : Φ.obj P ⟶ Φ.obj S}
    (ha : a = n ≫ t) (hr : a ≫ m = r) (hy : Φ.map t ≫ Φ.map m = y) (hw : Φ.map r = w) :
    Φ.map n ≫ y = w := by
  subst ha hr hy hw
  simp

end Stacks.Sheaves.ToposPullback

/-! ## The two presentations of the localization have the same structure map -/

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The two presentations of the localization morphism have the same inverse-image structure
map.** The four-field morphism of the modules development attached to the two-field localization
morphism of ringed topoi and the localization morphism of the modules development have the same
structure map in inverse-image form, at the level of sheaves of rings. -/
theorem fSharpInverseImage_toModulesHom_localizationRingedToposHom :
    (X.localizationRingedToposHom U).toModulesHom.fSharpInverseImage =
      (X.localizationMorphism U).fSharpInverseImage :=
  ((X.localizationRingedToposHom U).fSharpInverseImageRing_eq_ringFsharpInverseImage).trans
    (X.localizationRingedToposHom_ringFsharpInverseImage U)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The two presentations of the localization morphism have the same structure map, read as a
morphism of presheaves of commutative rings.** -/
theorem fSharpCommRing_toModulesHom_localizationRingedToposHom :
    fSharpCommRing (X.localizationRingedToposHom U).toModulesHom =
      fSharpCommRing (X.localizationMorphism U) := by
  refine NatTrans.ext (funext fun Z ↦ ?_)
  have h : (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((fSharpCommRing (X.localizationRingedToposHom U).toModulesHom).app Z) =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((fSharpCommRing (X.localizationMorphism U)).app Z) :=
    congrFun (congrArg NatTrans.app (congrArg (sheafToPresheaf (X.J.over U) RingCat.{u}).map
      (X.fSharpInverseImage_toModulesHom_localizationRingedToposHom U))) Z
  exact (forget₂ CommRingCat.{u} RingCat.{u}).map_injective h

/-! ## The inverse-image structure sheaf and the functors over it, folded behind names -/

/-- **The inverse image of the structure sheaf along the localization at `U`, as a sheaf of
rings**, given by `inverseImageStructureCommRing (X.localizationMorphism U)`. It is
definitionally equal to the image of `Stacks.SheafOfModules.Tensor.ringSheaf X.O` under
`inverseImageRingFunctor (X.overMorphismOfTopoi U)`. -/
def localizationInverseImageRingSheaf : Sheaf (X.over U).ringedTopos.J RingCat.{u} :=
  commRingSheaf (X.over U).ringedTopos.J
    (inverseImageStructureCommRing (X.localizationMorphism U))
    (Stacks.SheafOfModules.isSheaf_inverseImageStructureCommRing (X.localizationMorphism U))

/-- Restriction of scalars along the structure map of the localization,
`AlgebraicGeometry.RingedSite.localizationRestrictScalars`, with its target written as
`localizationInverseImageRingSheaf`. -/
def localizationRestrictScalarsFolded :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⥤
      SheafOfModules.{u} (localizationInverseImageRingSheaf X U) :=
  X.localizationRestrictScalars U

/-- Underlying sheaves of sets for modules over the inverse image of the structure sheaf along
the localization at `U`, stated at `localizationInverseImageRingSheaf`. -/
def localizationModuleForgetInverse :
    SheafOfModules.{u} (localizationInverseImageRingSheaf X U) ⥤
      Sheaf (X.over U).ringedTopos.J (Type u) :=
  moduleSheafFunctor (localizationInverseImageRingSheaf X U)

/-- Underlying sheaves of sets for modules over the structure sheaf of the localized ringed
site, in the spelling in which `AlgebraicGeometry.RingedSite.localizationRestrictScalars` and
`SheafOfModules.overFunctor` state their source. -/
def localizationModuleForgetSlice :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⥤
      Sheaf (X.over U).ringedTopos.J (Type u) :=
  moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)

/-- Underlying sheaves of sets for modules over the structure sheaf of the ringed topos of the
localized ringed site. -/
def localizationModuleForgetTarget :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).ringedTopos.O) ⥤
      Sheaf (X.over U).ringedTopos.J (Type u) :=
  moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).ringedTopos.O)

end AlgebraicGeometry.RingedSite

end
