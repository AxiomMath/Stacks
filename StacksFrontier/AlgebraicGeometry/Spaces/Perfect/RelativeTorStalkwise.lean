module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalkwiseSlicePoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.UniformInterval
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Stalks
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections

/-!
# The Tor clause of relative perfectness, read at the geometric stalks

Let `f : X ⟶ Y` be a morphism of algebraic spaces and let `E` be an object of `D(𝒪_X)`. The
second clause of relative perfectness (Stacks 0DKN) asks that `E`, read as an object of
`D(f⁻¹𝒪_Y)` through restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`, locally have finite Tor
dimension. This holds if one interval bounds the Tor amplitude of all the geometric stalks `E_x̄`,
read over the stalk of `f⁻¹𝒪_Y`; conversely, on a quasi-compact `X` the clause gives such a bound.

On an arbitrary site, the stalk of a restriction of scalars along a morphism of sheaves of rings
is the restriction of scalars of the stalk along the map of stalk rings.

## Main definitions

* `Stacks.restrictScalarsStalkRingHom`: the map of stalks of a morphism of sheaves of rings.
* `Stacks.restrictScalarsModuleStalkIso`: the stalk of a restriction of scalars.

## Main results

* `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_derivedScalarRestriction_of_stalkBound`:
  a uniform bound on the Tor amplitude of the geometric stalks gives the Tor clause of 0DKN.
* `AlgebraicGeometry.Space.exists_stalkBound_of_locallyHasFiniteTorDimension`: conversely, on a
  quasi-compact algebraic space the Tor clause of 0DKN gives such a uniform bound.

## References

* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w d e

/-- A point of a site has a nonempty fibre at some member of every family covering the site. -/
theorem CategoryTheory.GrothendieckTopology.Point.exists_nonempty_fiber_of_coversTop
    {C : Type*} [Category C] {J : GrothendieckTopology C} (Φ : J.Point.{w}) {ι : Type*}
    {Y : ι → C} (hY : J.CoversTop Y) : ∃ i, Nonempty (Φ.fiber.obj (Y i)) := by
  obtain ⟨⟨W, w⟩⟩ := IsCofiltered.nonempty (C := Φ.fiber.Elements)
  obtain ⟨Z, g, ⟨i, ⟨h⟩⟩, z, -⟩ := Φ.jointly_surjective _ (hY W) w
  exact ⟨i, ⟨Φ.fiber.map h z⟩⟩

namespace Stacks

section RestrictScalarsStalk

variable {C : Type*} [Category C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Ψ : J.Point.{w}) {O₁ O₂ : Sheaf J CommRingCat.{w}}
  (ψ : Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₂)

/-- The map of stalks at `Ψ` of a morphism `ψ : O₁ ⟶ O₂` of sheaves of rings, as a homomorphism of
the stalks taken in commutative rings. -/
def restrictScalarsStalkRingHom :
    (Ψ.presheafFiber (A := CommRingCat.{w})).obj O₁.obj →+*
      (Ψ.presheafFiber (A := CommRingCat.{w})).obj O₂.obj :=
  (commRingSheafFiberIso Ψ O₂).hom.hom.comp
    ((Ψ.presheafFiber.map ψ.hom).hom.comp (commRingSheafFiberIso Ψ O₁).inv.hom)

/-- The comparison of the stalk of the underlying sheaf of rings with the stalk in commutative
rings takes germs to germs. -/
lemma commRingSheafFiberIso_hom_toPresheafFiber (O : Sheaf J CommRingCat.{w}) (U : C)
    (ξ : Ψ.fiber.obj U) (a : (commRingSheafToRingSheaf O).obj.obj (op U)) :
    (commRingSheafFiberIso Ψ O).hom.hom
        (Ψ.toPresheafFiber U ξ (commRingSheafToRingSheaf O).obj a) =
      ringStalkGerm Ψ O U ξ a :=
  ConcreteCategory.congr_hom
    (Ψ.toPresheafFiber_presheafFiberCompIso_hom_app (F := forget₂ CommRingCat.{w} RingCat.{w})
      U ξ O.obj) a

/-- The map of stalks of `ψ` takes the germ of `a` to the germ of `ψ(a)`. -/
lemma restrictScalarsStalkRingHom_ringStalkGerm (U : C) (ξ : Ψ.fiber.obj U)
    (a : (commRingSheafToRingSheaf O₁).obj.obj (op U)) :
    restrictScalarsStalkRingHom Ψ ψ (ringStalkGerm Ψ O₁ U ξ a) =
      ringStalkGerm Ψ O₂ U ξ ((ψ.hom.app (op U)).hom a) := by
  have h₁ : (commRingSheafFiberIso Ψ O₁).inv.hom (ringStalkGerm Ψ O₁ U ξ a) =
      Ψ.toPresheafFiber U ξ (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj a :=
    ringStalkComparison_ringStalkGerm Ψ O₁ U ξ a
  have h₂ := ConcreteCategory.congr_hom (Ψ.toPresheafFiber_naturality ψ.hom U ξ) a
  show (commRingSheafFiberIso Ψ O₂).hom.hom ((Ψ.presheafFiber.map ψ.hom).hom
    ((commRingSheafFiberIso Ψ O₁).inv.hom (ringStalkGerm Ψ O₁ U ξ a))) = _
  rw [h₁]
  exact (congrArg (commRingSheafFiberIso Ψ O₂).hom.hom h₂).trans
    (commRingSheafFiberIso_hom_toPresheafFiber Ψ O₂ U ξ _)

/-- The underlying presheaf of abelian groups of a restriction of scalars is that of the module. -/
def restrictScalarsPresheafIso
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((SheafOfModules.restrictScalars ψ).obj M).val.presheaf ≅ M.val.presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The stalk of a restriction of scalars, on underlying abelian groups. -/
def restrictScalarsStalkAddIso
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    (forget₂ _ AddCommGrpCat.{w}).obj
        (moduleStalk Ψ O₁ ((SheafOfModules.restrictScalars ψ).obj M)) ≅
      (forget₂ _ AddCommGrpCat.{w}).obj ((ModuleCat.restrictScalars
        (restrictScalarsStalkRingHom Ψ ψ)).obj (moduleStalk Ψ O₂ M)) :=
  AlgebraicGeometry.RingedSite.moduleStalkForget₂Iso Ψ O₁ _ ≪≫
    Ψ.presheafFiber.mapIso (restrictScalarsPresheafIso ψ M) ≪≫
    (AlgebraicGeometry.RingedSite.moduleStalkRestrictScalarsForget₂Iso Ψ O₂ _ M).symm

omit [LocallySmall.{w} C] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The identification `restrictScalarsPresheafIso` takes germs to germs. -/
lemma restrictScalarsPresheafIso_fiber_toPresheafFiber
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) (U : C)
    (ξ : Ψ.fiber.obj U) (t : M.val.obj (op U)) :
    (Ψ.presheafFiber.map (restrictScalarsPresheafIso ψ M).hom)
        (Ψ.toPresheafFiber U ξ ((SheafOfModules.restrictScalars ψ).obj M).val.presheaf t) =
      Ψ.toPresheafFiber U ξ M.val.presheaf t :=
  ConcreteCategory.congr_hom
    (Ψ.toPresheafFiber_naturality (restrictScalarsPresheafIso ψ M).hom U ξ) t

/-- The stalk of a restriction of scalars takes the germ of `t` to the germ of `t`. -/
lemma restrictScalarsStalkAddIso_hom_germ
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) (U : C)
    (ξ : Ψ.fiber.obj U) (t : M.val.obj (op U)) :
    (restrictScalarsStalkAddIso Ψ ψ M).hom
        (moduleStalkGerm Ψ O₁ ((SheafOfModules.restrictScalars ψ).obj M) U ξ t) =
      moduleStalkGerm Ψ O₂ M U ξ t := by
  show (AlgebraicGeometry.RingedSite.moduleStalkRestrictScalarsForget₂Iso Ψ O₂
      (restrictScalarsStalkRingHom Ψ ψ) M).inv ((Ψ.presheafFiber.map
        (restrictScalarsPresheafIso ψ M).hom) (Ψ.toPresheafFiber U ξ
          ((SheafOfModules.restrictScalars ψ).obj M).val.presheaf t)) = _
  rw [restrictScalarsPresheafIso_fiber_toPresheafFiber]
  rfl

/-- The stalk of a restriction of scalars is semilinear along the map of stalk rings. -/
lemma restrictScalarsStalkAddIso_hom_smul
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (r : (Ψ.presheafFiber (A := CommRingCat.{w})).obj O₁.obj)
    (n : moduleStalk Ψ O₁ ((SheafOfModules.restrictScalars ψ).obj M)) :
    (restrictScalarsStalkAddIso Ψ ψ M).hom (r • n) =
      restrictScalarsStalkRingHom Ψ ψ r •
        @id (moduleStalk Ψ O₂ M) ((restrictScalarsStalkAddIso Ψ ψ M).hom n) := by
  obtain ⟨W₁, y₁, s, rfl⟩ := moduleStalkGerm_jointly_surjective Ψ O₁
    ((SheafOfModules.restrictScalars ψ).obj M) n
  obtain ⟨W₂, y₂, a, rfl⟩ := ringStalkGerm_jointly_surjective Ψ O₁ r
  obtain ⟨W, y, g₁, g₂, h₁, h₂⟩ := exists_common_nbhd (Φ := Ψ) y₁ y₂
  have hs := moduleStalkGerm_restrict Ψ O₁ ((SheafOfModules.restrictScalars ψ).obj M) g₁ y s
  have ha := ringStalkGerm_restrict Ψ O₁ g₂ y a
  rw [h₁] at hs
  rw [h₂] at ha
  rw [← hs, ← ha]
  refine (congrArg (restrictScalarsStalkAddIso Ψ ψ M).hom
    (moduleStalkGerm_smul Ψ O₁ _ W y _ _).symm).trans ?_
  refine (restrictScalarsStalkAddIso_hom_germ Ψ ψ M W y _).trans ?_
  refine (moduleStalkGerm_smul Ψ O₂ M W y _ _).trans ?_
  rw [restrictScalarsStalkRingHom_ringStalkGerm]
  exact congrArg (fun m => ringStalkGerm Ψ O₂ W y _ • m)
    (restrictScalarsStalkAddIso_hom_germ Ψ ψ M W y _).symm

/-- **The stalk of a restriction of scalars is the restriction of scalars of the stalk.** -/
def restrictScalarsModuleStalkIso
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    moduleStalk Ψ O₁ ((SheafOfModules.restrictScalars ψ).obj M) ≅
      (ModuleCat.restrictScalars (restrictScalarsStalkRingHom Ψ ψ)).obj (moduleStalk Ψ O₂ M) :=
  ModuleCat.isoMk (restrictScalarsStalkAddIso Ψ ψ M) (fun r => by
    ext n
    exact (restrictScalarsStalkAddIso_hom_smul Ψ ψ M r n).symm)

/-- The stalk of a restriction of scalars takes the germ of `t` to the germ of `t`. -/
lemma restrictScalarsModuleStalkIso_hom_germ
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) (U : C)
    (ξ : Ψ.fiber.obj U) (t : M.val.obj (op U)) :
    (restrictScalarsModuleStalkIso Ψ ψ M).hom
        (moduleStalkGerm Ψ O₁ ((SheafOfModules.restrictScalars ψ).obj M) U ξ t) =
      moduleStalkGerm Ψ O₂ M U ξ t :=
  restrictScalarsStalkAddIso_hom_germ Ψ ψ M U ξ t

/-- **The stalk of a restriction of scalars, naturally in the module.** -/
def restrictScalarsModuleStalkNatIso :
    SheafOfModules.restrictScalars ψ ⋙ sheafModuleFiberOfCommRing Ψ O₁ ≅
      sheafModuleFiberOfCommRing Ψ O₂ ⋙
        ModuleCat.restrictScalars (restrictScalarsStalkRingHom Ψ ψ) :=
  NatIso.ofComponents (restrictScalarsModuleStalkIso Ψ ψ) (fun {M M'} g => by
    ext n
    obtain ⟨W, y, t, rfl⟩ := moduleStalkGerm_jointly_surjective Ψ O₁
      ((SheafOfModules.restrictScalars ψ).obj M) n
    change (restrictScalarsModuleStalkIso Ψ ψ M').hom ((sheafModuleFiberOfCommRing Ψ O₁).map
        ((SheafOfModules.restrictScalars ψ).map g) (moduleStalkGerm Ψ O₁ _ W y t)) =
      (sheafModuleFiberOfCommRing Ψ O₂).map g
        ((restrictScalarsModuleStalkIso Ψ ψ M).hom (moduleStalkGerm Ψ O₁ _ W y t))
    refine (congrArg (restrictScalarsModuleStalkIso Ψ ψ M').hom.hom
      (moduleStalkGerm_naturality Ψ O₁ ((SheafOfModules.restrictScalars ψ).map g) W y t)).trans ?_
    refine (restrictScalarsModuleStalkIso_hom_germ Ψ ψ M' W y (g.val.app (op W) t)).trans ?_
    refine (moduleStalkGerm_naturality Ψ O₂ g W y t).symm.trans ?_
    exact congrArg ((sheafModuleFiberOfCommRing Ψ O₂).map g).hom
      (restrictScalarsModuleStalkIso_hom_germ Ψ ψ M W y t).symm)

end RestrictScalarsStalk

end Stacks

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The map of stalks of `f⁻¹𝒪_Y ⟶ 𝒪_X` at a geometric point of `X`. -/
abbrev inverseImageStalkRingHom (x : GeometricPoint B S hS X.1) :=
  Stacks.restrictScalarsStalkRingHom (etaleSitePoint B S hS X.1 x X.2)
    (inverseImageStructureMap B S hS f)

/-- The stalk functor at a geometric point of `X`, on `𝒪_X`-modules. -/
abbrev geometricStalkFunctor (x : GeometricPoint B S hS X.1) :=
  RingedSite.stalkFunctor (Z := smallEtaleRingedSite B S hS X.1 X.2)
    (etaleSitePoint B S hS X.1 x X.2)

/-- The stalk functor at a geometric point of `X`, on `f⁻¹𝒪_Y`-modules. -/
abbrev inverseImageStalkFunctor (x : GeometricPoint B S hS X.1) :=
  RingedSite.stalkFunctor (Z := inverseImageRingedSite B S hS f) (etaleSitePoint B S hS X.1 x X.2)

/-- The stalk functor at a geometric point of `X` is additive. -/
instance geometricStalkFunctor_additive (x : GeometricPoint B S hS X.1) :
    (geometricStalkFunctor B S hS x).Additive :=
  RingedSite.stalkFunctor_additive _

/-- The stalk functor at a geometric point of `X` preserves finite limits. -/
instance geometricStalkFunctor_preservesFiniteLimits (x : GeometricPoint B S hS X.1) :
    PreservesFiniteLimits (geometricStalkFunctor B S hS x) :=
  RingedSite.stalkFunctor_preservesFiniteLimits _

/-- The stalk functor at a geometric point of `X` preserves finite colimits. -/
instance geometricStalkFunctor_preservesFiniteColimits (x : GeometricPoint B S hS X.1) :
    PreservesFiniteColimits (geometricStalkFunctor B S hS x) :=
  RingedSite.stalkFunctor_preservesFiniteColimits _

/-- Restriction of scalars along the map of stalks at a geometric point is additive. -/
instance inverseImageStalkRingHom_restrictScalars_additive (x : GeometricPoint B S hS X.1) :
    (ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f x)).Additive where
  map_add := by intros; rfl

/-- The stalk functor at a geometric point of `X`, on `f⁻¹𝒪_Y`-modules, is additive. -/
instance inverseImageStalkFunctor_additive (x : GeometricPoint B S hS X.1) :
    (inverseImageStalkFunctor B S hS f x).Additive :=
  RingedSite.stalkFunctor_additive _

/-- The stalk functor at a geometric point of `X`, on `f⁻¹𝒪_Y`-modules, preserves finite limits. -/
instance inverseImageStalkFunctor_preservesFiniteLimits (x : GeometricPoint B S hS X.1) :
    PreservesFiniteLimits (inverseImageStalkFunctor B S hS f x) :=
  RingedSite.stalkFunctor_preservesFiniteLimits _

/-- The stalk functor at a geometric point of `X`, on `f⁻¹𝒪_Y`-modules, preserves finite
colimits. -/
instance inverseImageStalkFunctor_preservesFiniteColimits (x : GeometricPoint B S hS X.1) :
    PreservesFiniteColimits (inverseImageStalkFunctor B S hS f x) :=
  RingedSite.stalkFunctor_preservesFiniteColimits _

/-- The stalk of a restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` at a geometric point, naturally
in the module, with the two stalk functors spelled on the two ringed sites. -/
def scalarRestrictionStalkNatIso (x : GeometricPoint B S hS X.1) :
    scalarRestriction B S hS f ⋙ inverseImageStalkFunctor B S hS f x ≅
      geometricStalkFunctor B S hS x ⋙
        ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f x) :=
  Stacks.restrictScalarsModuleStalkNatIso (etaleSitePoint B S hS X.1 x X.2)
    (inverseImageStructureMap B S hS f)

variable
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]

/-- **The derived stalk of a restriction of scalars**: the derived stalk at `x` of `E` read in
`D(f⁻¹𝒪_Y)` is the derived stalk of `E` with its scalars restricted along the map of stalks. -/
def derivedScalarRestrictionStalkIso (x : GeometricPoint B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (inverseImageStalkFunctor B S hS f x).mapDerivedCategory.obj
        ((derivedScalarRestriction B S hS f).obj E) ≅
      (ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f x)).mapDerivedCategory.obj
        ((geometricStalkFunctor B S hS x).mapDerivedCategory.obj E) :=
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let F₂ := inverseImageStalkFunctor B S hS f x
  let G₁ := geometricStalkFunctor B S hS x
  let G₂ := ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f x)
  let c : (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (scalarRestrictionStalkNatIso B S hS f x).app (K.X i))
      (fun i j _ => ((scalarRestrictionStalkNatIso B S hS f x).hom.naturality (K.d i j)).symm)
  F₂.mapDerivedCategory.mapIso ((derivedScalarRestriction B S hS f).mapIso eK.symm) ≪≫
    F₂.mapDerivedCategory.mapIso ((derivedScalarRestrictionFactors B S hS f).app K) ≪≫
    F₂.mapDerivedCategoryFactors.app
      (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso c ≪≫
    (G₂.mapDerivedCategoryFactors.app
      ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    G₂.mapDerivedCategory.mapIso (G₁.mapDerivedCategoryFactors.app K).symm ≪≫
    G₂.mapDerivedCategory.mapIso (G₁.mapDerivedCategory.mapIso eK)

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

/-- **The Tor clause of relative perfectness from a uniform bound at the geometric stalks.** If one
interval `[a, b]` contains, at every geometric point `x̄` of `X`, the Tor amplitude of the
geometric stalk `E_x̄` read over the stalk of `f⁻¹𝒪_Y`, then `E`, read as an object of
`D(f⁻¹𝒪_Y)`, locally has finite Tor dimension — for every family of derived tensor products on
the slices. -/
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_of_stalkBound
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a b : ℤ)
    (h : ∀ x : GeometricPoint B S hS X.1,
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f).O.obj)
        ((ModuleCat.restrictScalars.{u}
            (inverseImageStalkRingHom B S hS f x)).mapDerivedCategory.obj
          ((geometricStalkFunctor B S hS x).mapDerivedCategory.obj E)) a b) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension.{u + 1, u, u, e} T
      ((derivedScalarRestriction B S hS f).obj E) :=
  Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_uniform_pointBound T
    ((derivedScalarRestriction B S hS f).obj E) (fun x : GeometricPoint B S hS X.1 =>
      (etaleSitePoint B S hS X.1 x X.2 : (inverseImageRingedSite B S hS f).J.Point.{u}))
    (fun V => isConservativeFamilyOfPoints_etaleSitePointOver B S hS X.2 V) a b (fun x =>
      AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
        (Iso.refl _ ≪≫ derivedScalarRestrictionStalkIso B S hS f x E).symm a b (h x))

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **A uniform bound at the geometric stalks from the Tor clause, on a quasi-compact space.** Let
`X` be quasi-compact and let `E` be an object of `D(𝒪_X)` which, read as an object of `D(f⁻¹𝒪_Y)`,
locally has finite Tor dimension, for some family `T` of derived tensor products on the slices.
Then one interval `[a, b]` contains, at every geometric point `x̄` of `X`, the Tor amplitude of the
geometric stalk `E_x̄` read over the stalk of `f⁻¹𝒪_Y`. -/
theorem exists_stalkBound_of_locallyHasFiniteTorDimension
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : LocallyHasFiniteTorDimension.{u + 1, u, u, e} T
      ((derivedScalarRestriction B S hS f).obj E)) :
    ∃ a b : ℤ, ∀ x : GeometricPoint B S hS X.1,
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f).O.obj)
        ((ModuleCat.restrictScalars.{u}
            (inverseImageStalkRingHom B S hS f x)).mapDerivedCategory.obj
          ((geometricStalkFunctor B S hS x).mapDerivedCategory.obj E)) a b := by
  obtain ⟨U, hUaff, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS X.1 X.2 hqc
  obtain ⟨ι, -, V, g, a, b, hg, hamp⟩ :=
    exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension T _ hE U
      (isQuasiCompactObject_of_isAffine B S hS X.1 U hUaff)
  have hV : (inverseImageRingedSite B S hS f).J.CoversTop
      (fun p : (_ : PUnit.{u + 2}) × ι => V p.2) :=
    Stacks.Sites.coversTop_bind hcov (fun _ => g) fun _ => hg
  refine ⟨a, b, fun x => ?_⟩
  let Φ : (inverseImageRingedSite B S hS f).J.Point.{u} := etaleSitePoint B S hS X.1 x X.2
  obtain ⟨p, ⟨ξ⟩⟩ := Φ.exists_nonempty_fiber_of_coversTop hV
  let Ψ : ((inverseImageRingedSite B S hS f).over (V p.2)).J.Point.{u} := Φ.over ξ
  have h₁ := hasTorAmplitudeCanonical_derivedModuleFiber.{u + 1, u, u, e} (T (V p.2)) _ a b
    (hamp p.2) Ψ
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    (Iso.refl _ ≪≫ derivedScalarRestrictionStalkIso B S hS f x E) a b
    ((RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff Φ ξ _ a b).1 h₁)

end AlgebraicGeometry.Space

end
