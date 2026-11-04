module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.LocalRepresentationOfDerivedMaps
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Direct image of module sheaves along a morphism of ringed spaces

A morphism `f : X ⟶ Y` of ringed spaces carries module sheaves on `X` to module sheaves on `Y`:
the underlying sheaf is the direct image, and its module structure over the structure sheaf of
`Y` comes from the comparison map `f^* O_Y ⟶ O_X`. For an isomorphism of ringed spaces this is an
equivalence, under which strict perfection is preserved.

## Main definitions

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.directImage`: the direct image functor on module
  sheaves.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivOfIso`: the equivalence of module
  categories induced by an isomorphism of ringed spaces.

## Main results

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.directImageComp` and
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.directImageId`: the direct image is functorial.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_moduleEquiv`: strict perfection
  transports along an isomorphism of ringed spaces.

## Implementation notes

The space, ring and module universes all coincide.

Since `AlgebraicGeometry.RingedSpace.PseudoCoherence.directImage` is a function of the morphism of
ringed spaces, an equality of two morphisms gives, by `congrArg`, an equality of functors; so the
two coherence isomorphisms of the equivalence attached to `e : X ≅ Y` come from
`e.hom ≫ e.inv = 𝟙 X` and `e.inv ≫ e.hom = 𝟙 Y`, and `CategoryTheory.Equivalence.mk` supplies the
triangle identity.

That the direct image of the structure sheaf is the structure sheaf is Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`, which is an isomorphism here because the comparison map
of an isomorphism of ringed spaces is one; the finite free modules follow because the direct image
along an equivalence preserves biproducts.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

/-- The comparison map on structure sheaves of a morphism of ringed spaces. -/
def directImageRingHom {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    structureSheafOfRings Y ⟶
      ((Opens.map f.hom.base).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)).obj
        (structureSheafOfRings X) :=
  ObjectProperty.homMk (Functor.whiskerRight f.hom.c (forget₂ CommRingCat RingCat))

/-- The direct image of module sheaves along a morphism of ringed spaces. -/
def directImage {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) : OXMod.{u, u} X ⥤ OXMod.{u, u} Y :=
  SheafOfModules.pushforward (directImageRingHom f)

/-- The comparison map of a composite `f ≫ g` is the comparison map of `g` followed by the
direct image along `g` of the comparison map of `f`. -/
theorem directImageRingHom_comp {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    directImageRingHom (f ≫ g) = directImageRingHom g ≫
      ((Opens.map g.hom.base).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology Z.carrier)
        (Opens.grothendieckTopology Y.carrier)).map (directImageRingHom f) := by
  ext U x
  simp [directImageRingHom]
  rfl

/-- The direct image along `f` followed by the direct image along `g` is isomorphic to the direct
image along `f ≫ g`. -/
def directImageComp {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    directImage f ⋙ directImage g ≅ directImage (f ≫ g) := by
  dsimp [directImage]
  exact SheafOfModules.pushforwardComp (directImageRingHom g) (directImageRingHom f) ≪≫
    SheafOfModules.pushforwardCongr (directImageRingHom_comp f g)

/-- The direct image along the identity is isomorphic to the identity functor. -/
def directImageId (X : RingedSpace.{u, u}) : directImage (𝟙 X) ≅ 𝟭 (OXMod.{u, u} X) := by
  dsimp [directImage]
  exact SheafOfModules.pushforwardCongr
      (show directImageRingHom (𝟙 X) = 𝟙 (structureSheafOfRings X) from by ext U x; rfl) ≪≫
    SheafOfModules.pushforwardId _

/-- Direct image along an isomorphism of ringed spaces is an equivalence on modules. -/
def moduleEquivOfIso {X Y : RingedSpace.{u, u}} (e : X ≅ Y) : OXMod.{u, u} X ≌ OXMod.{u, u} Y :=
  CategoryTheory.Equivalence.mk (directImage e.hom) (directImage e.inv)
    (directImageComp e.hom e.inv ≪≫
      eqToIso (congrArg (directImage (X := X) (Y := X)) e.hom_inv_id) ≪≫
      directImageId X).symm
    (directImageComp e.inv e.hom ≪≫
      eqToIso (congrArg (directImage (X := Y) (Y := Y)) e.inv_hom_id) ≪≫
      directImageId Y)

/-- The direct image functor is additive. -/
instance {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) : (directImage f).Additive :=
  ⟨by intros; ext U x; rfl⟩

/-- The functor of the equivalence induced by an isomorphism of ringed spaces is additive. -/
instance {X Y : RingedSpace.{u, u}} (e : X ≅ Y) : (moduleEquivOfIso e).functor.Additive :=
  ⟨by intros; ext U x; rfl⟩

/-- The functor of the equivalence induced by an isomorphism of ringed spaces preserves finite
limits. -/
theorem moduleEquivOfIso_preservesFiniteLimits {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    PreservesFiniteLimits (moduleEquivOfIso e).functor := by
  infer_instance

attribute [instance] moduleEquivOfIso_preservesFiniteLimits

/-- The functor of the equivalence induced by an isomorphism of ringed spaces preserves finite
colimits. -/
theorem moduleEquivOfIso_preservesFiniteColimits {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    PreservesFiniteColimits (moduleEquivOfIso e).functor := by
  infer_instance

attribute [instance] moduleEquivOfIso_preservesFiniteColimits

/-! ### Transport of strict perfection -/

/-- The comparison map on structure sheaves of an isomorphism of ringed spaces is an
isomorphism. -/
theorem directImageRingHom_isIso {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    IsIso (directImageRingHom e.hom) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  dsimp [directImageRingHom]
  have : IsIso e.hom.hom.c := inferInstance
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  exact Functor.map_isIso (forget₂ CommRingCat RingCat) _

/-- If the comparison map `ψ` of sheaves of rings is an isomorphism, then so is the map
`SheafOfModules.unitToPushforwardObjUnit ψ` from the unit module to the pushforward of the unit
module. -/
theorem isIso_unitToPushforwardObjUnit
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) (hψ : IsIso ψ) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit.{u, u, u, u, u} ψ) := by
  have := hψ
  have hmap : IsIso ((sheafToPresheaf J RingCat.{u}).map ψ) := inferInstance
  rw [NatTrans.isIso_iff_isIso_app] at hmap
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ AddCommGrpCat.{u})]
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  have : IsIso (ψ.hom.app V) := hmap V
  exact inferInstanceAs (IsIso ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map (ψ.hom.app V)))

/-- The direct image of the structure sheaf along an isomorphism is the structure sheaf. -/
def moduleEquivStructureModuleIso {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    structureModule Y ≅ (moduleEquivOfIso e).functor.obj (structureModule X) :=
  @asIso _ _ _ _
    (SheafOfModules.unitToPushforwardObjUnit.{u, u, u, u, u} (directImageRingHom e.hom))
    (isIso_unitToPushforwardObjUnit _ (directImageRingHom_isIso e))

/-- The direct image of a finite free module along an isomorphism is finite free. -/
def moduleEquivFiniteFreeIso {X Y : RingedSpace.{u, u}} (e : X ≅ Y) (n : ℕ) :
    (moduleEquivOfIso e).functor.obj (finiteFree X n) ≅ finiteFree Y n :=
  letI : PreservesBiproduct (fun _ : Fin n => structureModule X)
      (moduleEquivOfIso e).functor := preservesBiproduct_of_preservesCoproduct _
  (Functor.mapBiproduct (moduleEquivOfIso e).functor
      (fun _ : Fin n => structureModule X)).trans
    (biproduct.whiskerEquiv (Equiv.refl (Fin n))
      (fun _ => moduleEquivStructureModuleIso e))

/-- The direct image along an isomorphism of ringed spaces of a direct summand of a finite free
module is a direct summand of a finite free module. -/
theorem isDirectSummandOfFiniteFree_moduleEquiv {X Y : RingedSpace.{u, u}} (e : X ≅ Y)
    (M : OXMod.{u, u} X) (hM : IsDirectSummandOfFiniteFree M) :
    IsDirectSummandOfFiniteFree ((moduleEquivOfIso e).functor.obj M) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract M).mp hM
  refine (isDirectSummandOfFiniteFree_iff_retract _).mpr ⟨n, ⟨?_⟩⟩
  exact (ρ.map (moduleEquivOfIso e).functor).trans (moduleEquivFiniteFreeIso e n).retract

/-- **Strict perfection transports along an isomorphism of ringed spaces.** -/
theorem isStrictlyPerfect_moduleEquiv {X Y : RingedSpace.{u, u}} (e : X ≅ Y)
    (P : CochainComplex (OXMod.{u, u} X) ℤ) (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect
      (((moduleEquivOfIso e).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  constructor
  · exact Set.Finite.subset hP.bounded fun i hi h =>
      hi ((moduleEquivOfIso e).functor.map_isZero h)
  · exact fun i => isDirectSummandOfFiniteFree_moduleEquiv e _ (hP.directSummand i)

end AlgebraicGeometry.RingedSpace.PseudoCoherence

end
