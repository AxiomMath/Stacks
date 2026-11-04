module

public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparisonWeak
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange

/-!
# Flatness of a morphism of algebraic spaces and of its small étale ringed topos morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 073C says that `f`
is flat exactly when the morphism of small étale ringed topoi
`(f_small, f♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Stacks 03G8 is flat in the sense of
Stacks 04JB.  This file assembles that equivalence out of the two descriptions of its sides by
geometric stalks.

On the left, flatness of a morphism of algebraic spaces is pointwise flatness (Stacks 08EW),
and at a geometric point that is flatness of the canonical homomorphism of étale local rings of
Stacks 04NG.  On the right, the small étale site has enough points — the geometric points are a
conservative family, by Stacks 04K5 — so flatness of the structure map of the ringed topos is,
by Stacks 05VC, flatness of its fibre at every geometric point.  The two sides meet because the
fibre of `f♯` *is* the map of Stacks 04NG, which is the germ-action input taken as a hypothesis
here.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.uliftPresheafFiberIso`: raising the universe of a
  point of a site does not change the fibre of a presheaf.
* `Stacks.ringMapAsModule`: the target of a morphism of sheaves of commutative rings, as a sheaf
  of modules over the source.  Its flatness is `AlgebraicGeometry.SheafOfModules.IsFlatMap`.
* `AlgebraicGeometry.Space.etaleLocalRingMapAsStalkMap`: the canonical map on étale local rings
  of Stacks 04NG, read through the comparison of Stacks 05VQ as a map of the structure-sheaf
  fibres at the two small étale site points.

## Main results

* `Stacks.moduleStalkRingMapEquiv` and `Stacks.isFlatModuleStalk_ringMapAsModule_iff`: the stalk
  of `Stacks.ringMapAsModule` is the fibre of the target over the fibre of the source, so it is
  flat exactly when the fibre of the morphism is a flat ring map.
* `Stacks.uliftPresheafFiber_map_flat_iff`: neither that flatness nor the fibre changes when the
  universe of the sections and of the point are raised together.
* `Stacks.isFlatMapULift_iff_forall_flat`: a morphism of sheaves of commutative rings is flat
  exactly when its fibre at every point of a conservative family is a flat ring map.
* `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_uliftEtaleSitePoint`: the universe lifts
  of the geometric points are a conservative family of points of the small étale site.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_isFlat_iff` and
  `AlgebraicGeometry.Space.isFlat_iff_forall_etaleLocalRingMap_flat`: the two sides of
  Stacks 073C, each described by its geometric stalks.
* `AlgebraicGeometry.Space.etaleLocalRingMapAsStalkMap_eq` and
  `AlgebraicGeometry.Space.etaleLocalRingMap_flat_iff_stalkRingMap_flat`: the map of Stacks 04NG
  *is* the fibre of `f♯` at the geometric point, so the two sides agree point by point.
* `AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat`: **Stacks 073C**.

## Implementation notes

The germ action of the fibre of `f♯` is not computed here: it is
`AlgebraicGeometry.Space.stalkStructureMapAsEtaleLocalRingMap_eq`, which says that the fibre of
the inverse-image structure map, transported to the étale local rings by Stacks 05VQ, is the
canonical homomorphism of Stacks 04NG.  All that is done with it here is conjugation by the two
ring isomorphisms of Stacks 05VQ, in
`AlgebraicGeometry.Space.etaleLocalRingMapAsStalkMap_eq`.

The universe bookkeeping is the second half of the work.  A ringed topos carries its structure
sheaf in `Sheaf J CommRingCat.{u}` while the small étale site is a `Type (u + 1)` with
`Category.{u}`, and flatness of a morphism of sheaves of rings is
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift`, which first lifts the sections into
`CommRingCat.{u + 1}` so that the tensor product of sheaves of modules is available.  The points
of Stacks 04K0 are points relative to `u`, so Stacks 05VC, which is applied at the coefficient
universe `u + 1`, needs them raised by
`CategoryTheory.GrothendieckTopology.Point.ulift`; `Stacks.uliftPresheafFiber_map_flat_iff` is
what makes the raised statement say something about the unraised fibres, and
`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_uliftEtaleSitePoint` re-proves
conservativity at the raised universe — directly, by the sieve criterion, since the geometric
points of an algebraic space are not known to form a `u`-small family and
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.ulift` asks for one.

## References

* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

universe w' w v₁ u₁ v' u' v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Raising the universe of a point does not change the fibre of a presheaf: the two fibres
are colimits over equivalent categories of neighbourhoods, along the same projection. -/
noncomputable def uliftPresheafFiberIso {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{w, w} A] [HasColimitsOfSize.{max w w', max w w'} A]
    (Φ : J.Point.{w}) :
    (Φ.ulift.{w'}).presheafFiber (A := A) ≅ Φ.presheafFiber (A := A) := by
  let e : (Φ.ulift.{w'}).fiber.Elements ≌ Φ.fiber.Elements :=
    (Functor.Elements.uliftEquiv.{w'} Φ.fiber).symm
  let E := e.op.functor
  let π₁ : (Φ.fiber.Elements)ᵒᵖ ⥤ Cᵒᵖ := (CategoryOfElements.π Φ.fiber).op
  let π₂ : ((Φ.ulift.{w'}).fiber.Elements)ᵒᵖ ⥤ Cᵒᵖ :=
    (CategoryOfElements.π (Φ.ulift.{w'}).fiber).op
  have hπ : E ⋙ π₁ = π₂ := rfl
  let L : (((Φ.ulift.{w'}).fiber.Elements)ᵒᵖ ⥤ A) ⥤ A := Limits.colim
  let W : (Cᵒᵖ ⥤ A) ⥤ ((Φ.fiber.Elements)ᵒᵖ ⥤ A) :=
    (Functor.whiskeringLeft _ _ A).obj π₁
  let H : (((Φ.fiber.Elements)ᵒᵖ) ⥤ A) ⥤ (((Φ.ulift.{w'}).fiber.Elements)ᵒᵖ ⥤ A) :=
    (Functor.whiskeringLeft _ _ A).obj E
  let W' : (Cᵒᵖ ⥤ A) ⥤ (((Φ.ulift.{w'}).fiber.Elements)ᵒᵖ ⥤ A) :=
    (Functor.whiskeringLeft _ _ A).obj π₂
  have hW : W' = W ⋙ H := by
    dsimp only [W', W, H]
    rw [← hπ]
    exact Functor.whiskeringLeft_obj_comp E π₁
  change W' ⋙ L ≅ W ⋙ Limits.colim
  exact Functor.isoWhiskerRight (eqToIso hW) L ≪≫
    Functor.associator W H L ≪≫
    Functor.isoWhiskerLeft W (Functor.Final.colimIso E)

end CategoryTheory.GrothendieckTopology.Point

namespace Stacks

open AlgebraicGeometry.SheafOfModules

section RingULift

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}

/-- Lifting the universe of a commutative ring preserves filtered colimits indexed by a
category small enough to index colimits of rings in the smaller universe: on underlying sets
the lift is `uliftFunctor`, which preserves all colimits, and the forgetful functor of
`CommRingCat` reflects isomorphisms. -/
private theorem preservesColimit_commRingCatULift {D : Type u₁} [Category.{v₁} D] [IsFiltered D]
    [LocallySmall.{u} D] [FinallySmall.{u} D] (R : D ⥤ CommRingCat.{u}) :
    PreservesColimit R commRingCatULift.{u, u + 1} := by
  let : PreservesColimitsOfShape D (forget CommRingCat.{u}) :=
    FinallySmall.preservesColimitsOfShape_of_isFiltered.{u} D _
  let : PreservesFilteredColimitsOfSize.{u, u} (forget CommRingCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  let : HasColimitsOfSize.{u, u} CommRingCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let : PreservesColimitsOfShape D (forget CommRingCat.{u + 1}) :=
    FinallySmall.preservesColimitsOfShape_of_isFiltered.{u} D _
  let : HasColimitsOfShape D CommRingCat.{u + 1} :=
    hasColimitsOfShape_of_finallySmall.{u} D _
  let : PreservesColimit R (commRingCatULift.{u, u + 1} ⋙ forget CommRingCat.{u + 1}) := by
    show PreservesColimit R (forget CommRingCat.{u} ⋙ uliftFunctor.{u + 1, u})
    infer_instance
  let : ReflectsColimit (R ⋙ commRingCatULift.{u, u + 1})
      (forget CommRingCat.{u + 1}) := reflectsColimit_of_reflectsIsomorphisms _ _
  exact preservesColimit_of_reflects_of_preserves (K := R)
    commRingCatULift.{u, u + 1} (forget CommRingCat.{u + 1})

/-- Lifting the universe of a commutative ring preserves filtered colimits indexed by a
category small enough to index colimits of rings in the smaller universe. -/
alias preservesColimit_commRingCatULift' := preservesColimit_commRingCatULift

/-- The fibre at the universe lift of a point of a presheaf of rings whose sections have been
lifted is the universe lift of the fibre at the point. -/
noncomputable def uliftRingFiberIso' (Φ : J.Point.{u}) (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    ((Φ.ulift.{u + 1}).presheafFiber (A := CommRingCat.{u + 1})).obj
        (R ⋙ commRingCatULift.{u, u + 1}) ≅
      commRingCatULift.{u, u + 1}.obj
        ((Φ.presheafFiber (A := CommRingCat.{u})).obj R) := by
  let e := (Functor.Elements.uliftEquiv.{u + 1} Φ.fiber).symm.op
  let π := (CategoryOfElements.π Φ.fiber).op
  letI : HasColimitsOfSize.{u, u} CommRingCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  letI : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ CommRingCat.{u + 1} :=
    hasColimitsOfShape_of_finallySmall.{u} _ _
  letI := preservesColimit_commRingCatULift' (π ⋙ R)
  exact Functor.Final.colimitIso e.functor (π ⋙ R ⋙ commRingCatULift.{u, u + 1}) ≪≫
    (preservesColimitIso commRingCatULift.{u, u + 1} (π ⋙ R)).symm

/-- `Stacks.uliftRingFiberIso'` carries the germ of a lifted section to the lift of its germ. -/
theorem uliftRingFiberIso'_germ (Φ : J.Point.{u}) (R : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C)
    (x : Φ.fiber.obj U) :
    (Φ.ulift.{u + 1}).toPresheafFiber U (ULift.up x) (R ⋙ commRingCatULift.{u, u + 1}) ≫
        (uliftRingFiberIso' Φ R).hom =
      commRingCatULift.{u, u + 1}.map (Φ.toPresheafFiber U x R) := by
  let E := (Functor.Elements.uliftEquiv.{u + 1} Φ.fiber).symm.op.functor
  let π := (CategoryOfElements.π Φ.fiber).op
  let L := commRingCatULift.{u, u + 1}
  let : HasColimitsOfSize.{u, u} CommRingCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let := preservesColimit_commRingCatULift' (π ⋙ R)
  have h := Functor.Final.ι_colimitIso_hom E (π ⋙ R ⋙ L) (Opposite.op ⟨U, ULift.up x⟩)
  show colimit.ι _ _ ≫ (Functor.Final.colimitIso E (π ⋙ R ⋙ L)).hom ≫
    (preservesColimitIso L (π ⋙ R)).inv = _
  rw [← Category.assoc]
  exact (h =≫ (preservesColimitIso L (π ⋙ R)).inv).trans
    (ι_preservesColimitIso_inv L (π ⋙ R) (Opposite.op ⟨U, x⟩))

/-- `Stacks.uliftRingFiberIso'` is natural in the presheaf of rings. -/
theorem uliftRingFiberIso'_naturality (Φ : J.Point.{u})
    {R T : Cᵒᵖ ⥤ CommRingCat.{u}} (g : R ⟶ T) :
    (Φ.ulift.{u + 1}).presheafFiber.map
        (Functor.whiskerRight g commRingCatULift.{u, u + 1}) ≫
        (uliftRingFiberIso' Φ T).hom =
      (uliftRingFiberIso' Φ R).hom ≫
        commRingCatULift.{u, u + 1}.map (Φ.presheafFiber.map g) := by
  apply (Φ.ulift.{u + 1}).presheafFiber_hom_ext
  rintro U ⟨x⟩
  rw [← Category.assoc, (Φ.ulift.{u + 1}).toPresheafFiber_naturality
      (Functor.whiskerRight g commRingCatULift.{u, u + 1}) U (ULift.up x), Category.assoc,
    uliftRingFiberIso'_germ Φ T U x, ← Category.assoc, uliftRingFiberIso'_germ Φ R U x,
    ← Functor.map_comp, Φ.toPresheafFiber_naturality]
  rfl

/-- **Flatness of a fibre map does not change under raising the universe.** A morphism of
presheaves of commutative rings has flat fibre at the universe lift of a point, after its
sections are lifted, exactly when it has flat fibre at the point itself. -/
theorem uliftPresheafFiber_map_flat_iff (Φ : J.Point.{u})
    {R T : Cᵒᵖ ⥤ CommRingCat.{u}} (g : R ⟶ T) :
    (((Φ.ulift.{u + 1}).presheafFiber (A := CommRingCat.{u + 1})).map
        (Functor.whiskerRight g commRingCatULift.{u, u + 1})).hom.Flat ↔
      ((Φ.presheafFiber (A := CommRingCat.{u})).map g).hom.Flat :=
  (RingHom.Flat.respectsIso.arrow_mk_iso_iff (Arrow.isoMk
    (uliftRingFiberIso' Φ R) (uliftRingFiberIso' Φ T)
    (uliftRingFiberIso'_naturality Φ g).symm)).trans RingHom.Flat.ulift_iff

end RingULift

section FlatRingMapStalk

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The target of a morphism of sheaves of commutative rings, viewed as a sheaf of modules over
the source by restriction of scalars. Its flatness is by definition flatness of the morphism,
`AlgebraicGeometry.SheafOfModules.IsFlatMap`. -/
noncomputable def ringMapAsModule {O O' : Sheaf J CommRingCat.{w}} (g : O ⟶ O') :
    SheafOfModules.{w} (commRingSheafToRingSheaf O) :=
  (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map g)).obj
    (SheafOfModules.unit (commRingSheafToRingSheaf O'))

variable (Φ : J.Point.{w}) {O O' : Sheaf J CommRingCat.{w}} (g : O ⟶ O')

/-- The colimit of the sections of `Stacks.ringMapAsModule` over the neighbourhoods of a point
is the fibre of the target sheaf of rings, as an abelian group. -/
noncomputable def ringMapAsModuleColimitAddEquiv :
    PresheafOfModules.ModuleColimit
        (Φ.isColimitPresheafFiberCocone (commRingSheafToRingSheaf O).obj)
        (colimit.isColimit ((PresheafOfModules.pushforward
          (F := CategoryOfElements.π Φ.fiber) (𝟙 _)).obj (ringMapAsModule g).val).presheaf) ≃+
      (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O').obj := by
  let H := (PresheafOfModules.pushforward
    (F := CategoryOfElements.π Φ.fiber) (𝟙 _)).obj (ringMapAsModule g).val
  let hcM := colimit.isColimit H.presheaf
  let hcT := Φ.isColimitPresheafFiberCocone (commRingSheafToRingSheaf O').obj
  let hcTAdd := isColimitOfPreserves (forget₂ RingCat.{w} AddCommGrpCat.{w}) hcT
  let e := IsColimit.coconePointUniqueUpToIso hcM hcTAdd
  exact AddEquiv.ofBijective (ConcreteCategory.hom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom)

/-- `Stacks.ringMapAsModuleColimitAddEquiv` is linear over the fibre of the source sheaf of
rings, the module structure on the target fibre being multiplication through the fibre of the
morphism. -/
noncomputable def ringMapAsModuleColimitLinearEquiv :
    let hcR := Φ.isColimitPresheafFiberCocone (commRingSheafToRingSheaf O).obj
    let H := (PresheafOfModules.pushforward
      (F := CategoryOfElements.π Φ.fiber) (𝟙 _)).obj (ringMapAsModule g).val
    let hcM := colimit.isColimit H.presheaf
    let A := (Φ.presheafFiberCocone (commRingSheafToRingSheaf O).obj).pt
    let B := (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O').obj
    let ψ : A →+* B := ((Φ.presheafFiber (A := RingCat.{w})).map
      (Functor.whiskerRight g.hom (forget₂ CommRingCat.{w} RingCat.{w}))).hom
    letI : Module B B := (RingHom.id B).toModule
    letI : Module A B := Module.compHom B ψ
    PresheafOfModules.ModuleColimit hcR hcM ≃ₗ[A] B := by
  let cR := Φ.presheafFiberCocone (commRingSheafToRingSheaf O).obj
  let H := (PresheafOfModules.pushforward
    (F := CategoryOfElements.π Φ.fiber) (𝟙 _)).obj (ringMapAsModule g).val
  let e := ringMapAsModuleColimitAddEquiv Φ g
  let B := (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O').obj
  let ψ : cR.pt →+* B := ((Φ.presheafFiber (A := RingCat.{w})).map
    (Functor.whiskerRight g.hom (forget₂ CommRingCat.{w} RingCat.{w}))).hom
  letI : Module B B := (RingHom.id B).toModule
  letI : Module cR.pt B := Module.compHom B ψ
  let cT := Φ.presheafFiberCocone (commRingSheafToRingSheaf O').obj
  let hcM := colimit.isColimit H.presheaf
  let hcTAdd := isColimitOfPreserves (forget₂ RingCat.{w} AddCommGrpCat.{w})
    (Φ.isColimitPresheafFiberCocone (commRingSheafToRingSheaf O').obj)
  exact
    { e with
      map_smul' := by
        intro r m
        obtain ⟨U, a, x, rfl, rfl⟩ :=
          PresheafOfModules.ModuleColimit.jointly_surjective₂ r m
        have hIota (z : H.obj U) :
            e (PresheafOfModules.ModuleColimit.ιM z) = (cT.ι.app U).hom z := by
          change (((colimit.cocone H.presheaf).ι.app U) ≫
            (hcM.coconePointUniqueUpToIso hcTAdd).hom) z = _
          exact ConcreteCategory.congr_hom (hcM.comp_coconePointUniqueUpToIso_hom hcTAdd U) z
        have hψapp : ψ ((cR.ι.app U).hom a) =
            (cT.ι.app U).hom
              ((Functor.whiskerRight g.hom
                (forget₂ CommRingCat.{w} RingCat.{w})).app (Opposite.op U.unop.1) a) := by
          change ((Φ.toPresheafFiber U.unop.1 U.unop.2
              (commRingSheafToRingSheaf O).obj ≫
            Φ.presheafFiber.map (Functor.whiskerRight g.hom
              (forget₂ CommRingCat.{w} RingCat.{w}))) a) = _
          exact ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality
            (Functor.whiskerRight g.hom (forget₂ CommRingCat.{w} RingCat.{w}))
            U.unop.1 U.unop.2) a
        change e (PresheafOfModules.ModuleColimit.ιR cR a •
          PresheafOfModules.ModuleColimit.ιM x) =
            ψ ((cR.ι.app U).hom a) * e (PresheafOfModules.ModuleColimit.ιM x)
        rw [PresheafOfModules.ModuleColimit.smul_eq, hIota, hIota, hψapp]
        change (cT.ι.app U).hom (((g.hom.app _).hom a) *
          (show O'.obj.obj ((CategoryOfElements.π Φ.fiber).op.obj U) from x)) = _
        exact map_mul _ _ _ }

/-- The fibre of a morphism of sheaves of commutative rings, read through the comparison
`Stacks.commRingSheafFiberIso` on both sides, is the fibre of the induced morphism of the
underlying sheaves of rings. -/
theorem commRingSheafFiberIso_inv_comp :
    (commRingSheafFiberIso Φ O).inv ≫
        (Φ.presheafFiber (A := RingCat.{w})).map
          (Functor.whiskerRight g.hom (forget₂ CommRingCat.{w} RingCat.{w})) ≫
        (commRingSheafFiberIso Φ O').hom =
      (forget₂ CommRingCat.{w} RingCat.{w}).map
        ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom) := by
  rw [Iso.inv_comp_eq]
  apply Φ.presheafFiber_hom_ext
  intro X x
  show Φ.toPresheafFiber X x (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≫
      (Φ.presheafFiber (A := RingCat.{w})).map
        (Functor.whiskerRight g.hom (forget₂ CommRingCat.{w} RingCat.{w})) ≫
        (Φ.presheafFiberCompIso (forget₂ CommRingCat.{w} RingCat.{w})).hom.app O'.obj =
    Φ.toPresheafFiber X x (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≫
      (Φ.presheafFiberCompIso (forget₂ CommRingCat.{w} RingCat.{w})).hom.app O.obj ≫
      (forget₂ CommRingCat.{w} RingCat.{w}).map
        ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom)
  simp only [Φ.toPresheafFiber_naturality_assoc,
    Φ.toPresheafFiber_presheafFiberCompIso_hom_app,
    Φ.toPresheafFiber_presheafFiberCompIso_hom_app_assoc, Functor.whiskerRight_app,
    ← Functor.map_comp, Φ.toPresheafFiber_naturality]

/-- **The stalk of the target over the stalk of the source.** The stalk at a point of the
target of a morphism of sheaves of commutative rings, viewed as a module over the source, is
the fibre of the target as a module over the fibre of the source through the fibre of the
morphism. -/
noncomputable def moduleStalkRingMapEquiv :
    let R' := (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj
    let T' := (Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj
    letI : Module R' T' := ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom).hom.toModule
    let M := moduleStalk Φ O (ringMapAsModule g)
    letI : Module R' M := M.isModule
    M ≃ₗ[R'] T' := by
  let c := forget₂ CommRingCat.{w} RingCat.{w}
  let R' := (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj
  let T' := (Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj
  let φ := ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom).hom
  letI : Module R' T' := φ.toModule
  let M := moduleStalk Φ O (ringMapAsModule g)
  letI : Module R' M := M.isModule
  let A := (Φ.presheafFiberCocone (commRingSheafToRingSheaf O).obj).pt
  let B := (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O').obj
  let ψ : A →+* B := ((Φ.presheafFiber (A := RingCat.{w})).map
    (Functor.whiskerRight g.hom c)).hom
  let ρ : R' →+* A := (commRingSheafFiberIso Φ O).inv.hom
  letI : Module B B := (RingHom.id B).toModule
  letI : Module A B := Module.compHom B ψ
  let Mc := PresheafOfModules.ModuleColimit
    (Φ.isColimitPresheafFiberCocone (commRingSheafToRingSheaf O).obj)
    (colimit.isColimit ((PresheafOfModules.pushforward
      (F := CategoryOfElements.π Φ.fiber) (𝟙 _)).obj (ringMapAsModule g).val).presheaf)
  let e : Mc ≃ₗ[A] B := ringMapAsModuleColimitLinearEquiv Φ g
  refine { (e.toAddEquiv.trans
    (commRingSheafFiberIso Φ O').ringCatIsoToRingEquiv.toAddEquiv) with
    map_smul' := ?_ }
  intro r m
  have hsmul : e (show Mc from r • m) = ψ (ρ r) * e (show Mc from m) :=
    e.map_smul (ρ r) (show Mc from m)
  change (commRingSheafFiberIso Φ O').hom.hom (e (show Mc from r • m)) =
    φ r * (show T' from (commRingSheafFiberIso Φ O').hom.hom (e (show Mc from m)))
  rw [hsmul, map_mul]
  congr 1
  exact ConcreteCategory.congr_hom (commRingSheafFiberIso_inv_comp Φ g) r

/-- **Flatness of a morphism of sheaves of rings at a point is flatness of its fibre.** The
stalk of the target, as a module over the stalk of the source, is flat exactly when the fibre
of the morphism is a flat ring map. -/
theorem isFlatModuleStalk_ringMapAsModule_iff :
    IsFlatModuleStalk Φ O (ringMapAsModule g) ↔
      ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom).hom.Flat := by
  let R' := (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj
  let T' := (Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj
  let φ := ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom).hom
  let : Module R' T' := φ.toModule
  let M := moduleStalk Φ O (ringMapAsModule g)
  let : Module R' M := M.isModule
  exact Module.Flat.equiv_iff (moduleStalkRingMapEquiv Φ g)

end FlatRingMapStalk

section FlatMapStalks

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}

/-- **Stacks 05VC for a morphism of sheaves of commutative rings.** A morphism of sheaves of
commutative rings on a site is flat exactly when, at every point of a conservative family, the
fibre of its target is a flat module over the fibre of its source. -/
theorem isFlatMapULift_iff_forall_isFlatModuleStalk {t : Type*} (p : t → J.Point.{u + 1})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    {O O' : Sheaf J CommRingCat.{u}} (g : O ⟶ O') :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u + 1, u} g ↔
      ∀ i, IsFlatModuleStalk (p i) ((sheafULift.{u, u + 1, u} J).obj O)
        (ringMapAsModule.{u + 1, u, u + 1} ((sheafULift.{u, u + 1, u} J).map g)) := by
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} J
  have h : AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u + 1, u} g ↔
      Stacks.SheafOfModules.IsFlat
        (ringMapAsModule.{u + 1, u, u + 1} ((sheafULift.{u, u + 1, u} J).map g)) := Iff.rfl
  exact h.trans (isFlat_iff_forall_isFlatModuleStalk_of_weakSheafify p hp _ _)

/-- **Flatness of a morphism of sheaves of commutative rings is flatness of its fibres.** At
every point of a conservative family the fibre of the morphism, taken in the universe of the
sections, is a flat ring map. -/
theorem isFlatMapULift_iff_forall_flat {t : Type*} (p : t → J.Point.{u})
    (hp : (ObjectProperty.ofObj (fun i ↦ (p i).ulift.{u + 1})).IsConservativeFamilyOfPoints)
    {O O' : Sheaf J CommRingCat.{u}} (g : O ⟶ O') :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u + 1, u} g ↔
      ∀ i, (((p i).presheafFiber (A := CommRingCat.{u})).map g.hom).hom.Flat := by
  rw [isFlatMapULift_iff_forall_isFlatModuleStalk _ hp]
  exact forall_congr' fun i =>
    (isFlatModuleStalk_ringMapAsModule_iff.{u + 1, u, u + 1} ((p i).ulift.{u + 1})
      ((sheafULift.{u, u + 1, u} J).map g)).trans
    (uliftPresheafFiber_map_flat_iff (p i) g.hom)

end FlatMapStalks

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Conservative

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **The universe lifts of the geometric points are a conservative family.** A map of sheaves
of sets valued in `Type (u + 1)` on the small étale site of an algebraic space which is an
isomorphism on the fibre at every geometric point is an isomorphism.

This is `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePoint` at the universe of
the coefficients that the tensor product of sheaves of modules forces, the points themselves
being points relative to the universe of the schemes. The proof is the same sieve criterion;
only the `ULift` bookkeeping is added. -/
theorem isConservativeFamilyOfPoints_uliftEtaleSitePoint :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun x : GeometricPoint B S hS X =>
        (etaleSitePoint B S hS X x hX).ulift.{u + 1})) := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  apply smallEtale_sieve_of_pointwise_covering B S hS X U R
  intro z
  obtain ⟨x, p, z', hz⟩ := exists_geo_lift_at_chart_point B S hS X U z
  obtain ⟨V, g, hg, q, hq⟩ := hR ⟨(etaleSitePoint B S hS X x hX).ulift.{u + 1},
    ObjectProperty.ofObj_apply
      (fun y : GeometricPoint B S hS X => (etaleSitePoint B S hS X y hX).ulift.{u + 1}) x⟩
    (ULift.up p)
  refine ⟨V, g, hg, (BigFppfOver.toScheme B S hS).map q.down.val z', ?_⟩
  rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp,
    show q.down.val ≫ (SmallEtale.toOver B S hS X).map g = p.val from
      congrArg Subtype.val (congrArg ULift.down hq)]

end Conservative

section FlatTopos

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Flatness of the morphism of small étale ringed topoi is flatness of its fibres.** The
morphism of ringed topoi of Stacks 03G8 is flat exactly when the fibre at every geometric point
of the source of its inverse-image structure map is a flat ring map. -/
theorem smallEtaleRingedToposHom_isFlat_iff :
    RingedToposHom.IsFlat (smallEtaleRingedToposHom B S hS f) ↔
      ∀ x : GeometricPoint B S hS X.1,
        (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom).hom.Flat :=
  Stacks.isFlatMapULift_iff_forall_flat _
    (isConservativeFamilyOfPoints_uliftEtaleSitePoint B S hS X.1 X.2) _

/-- **Flatness of a morphism of algebraic spaces is flatness of its maps on étale local
rings.** This is the combination of Stacks 08EW, the equivalence of flatness with pointwise
flatness, with the criterion of Stacks 04NG at a geometric point. -/
theorem isFlat_iff_forall_etaleLocalRingMap_flat :
    IsFlat B S hS f.hom ↔
      ∀ x : GeometricPoint B S hS X.1, (etaleLocalRingMap X.2 f.hom x).Flat := by
  refine ((isFlat_tfae B S hS X.2 Y.2 f.hom).out 1 2).trans ?_
  constructor
  · intro hf x
    exact (isFlatAt_iff_etaleLocalRingMap_flat X.2 Y.2 f.hom x).mp (hf x.image)
  · intro hf x
    obtain ⟨x, rfl⟩ := exists_geometricRepresentative B S hS X.1 x
    exact (isFlatAt_iff_etaleLocalRingMap_flat X.2 Y.2 f.hom x).mpr (hf x)

variable (x : GeometricPoint B S hS X.1)

/-- The canonical map on étale local rings of Stacks 04NG, read through the germ-preserving
comparison of Stacks 05VQ as a map of structure-sheaf fibres at the two small étale site
points. -/
noncomputable def etaleLocalRingMapAsStalkMap :
    ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).presheafFiber
        (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O.obj ⟶
      ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj :=
  CommRingCat.ofHom
    ((pointStalkRingEquiv B S hS X x).symm.toRingHom.comp
      ((etaleLocalRingMap X.2 f.hom x).comp
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom))

variable {B S hS f x}

/-- Conjugating a ring homomorphism by two ring isomorphisms is inverted by conjugating
back. -/
private theorem ringHom_conj_symm {A A' L M : Type*} [CommRing A] [CommRing A'] [CommRing L]
    [CommRing M] (eA : A ≃+* L) (eB : A' ≃+* M) (c : A' →+* A) (φ : M →+* L)
    (hφ : (eA.toRingHom.comp c).comp eB.symm.toRingHom = φ) :
    eA.symm.toRingHom.comp (φ.comp eB.toRingHom) = c := by
  subst hφ
  ext
  simp

/-- The canonical map on étale local rings of Stacks 04NG is the fibre at `x` of the
inverse-image structure map, read through the comparison of Stacks 05VQ at the two geometric
points. -/
theorem etaleLocalRingMapAsStalkMap_eq :
    etaleLocalRingMapAsStalkMap B S hS f x = stalkStructureMap B S hS f x :=
  CommRingCat.hom_ext
    (ringHom_conj_symm (pointStalkRingEquiv B S hS X x)
      (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x))
      (stalkStructureMap B S hS f x).hom
      (etaleLocalRingMap X.2 f.hom x)
      (stalkStructureMapAsEtaleLocalRingMap_eq B S hS f x))

/-- **Flatness at a geometric point, on both sides.** Flatness of the canonical map on étale
local rings of Stacks 04NG is flatness of the fibre at `x` of the inverse-image structure
map. -/
theorem etaleLocalRingMap_flat_iff_stalkRingMap_flat :
    (etaleLocalRingMap X.2 f.hom x).Flat ↔
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom).hom.Flat := by
  set e := (smallEtaleInverseImageFiberRingIso B S hS f x).app
    (smallEtaleRingedTopos B S hS Y).O
  have hsplit : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber
      (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom =
      e.inv ≫ etaleLocalRingMapAsStalkMap B S hS f x := by
    rw [etaleLocalRingMapAsStalkMap_eq]
    exact (e.inv_hom_id_assoc _).symm
  rw [hsplit]
  have h1 : ((etaleLocalRingMapAsStalkMap B S hS f x).hom.comp
        (CommRingCat.Hom.hom e.inv)).Flat ↔
      ((pointStalkRingEquiv B S hS X x).symm.toRingHom.comp
        ((etaleLocalRingMap X.2 f.hom x).comp
          (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom)).Flat :=
    RingHom.Flat.comp_iff_of_bijective_right (ConcreteCategory.bijective_of_isIso e.inv)
  have h2 := RingHom.Flat.comp_iff_of_bijective_left
    (f := (etaleLocalRingMap X.2 f.hom x).comp
      (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom)
    (g := (pointStalkRingEquiv B S hS X x).symm.toRingHom)
    (pointStalkRingEquiv B S hS X x).symm.bijective
  have h3 := RingHom.Flat.comp_iff_of_bijective_right
    (f := etaleLocalRingMap X.2 f.hom x)
    (g := (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom)
    (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).bijective
  exact (h1.trans (h2.trans h3)).symm

variable (B S hS f)

/-- **Stacks 073C.** A morphism of algebraic spaces over `S` is flat if and only if the
morphism of small étale ringed topoi `(f_small, f♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)`
associated to it is flat. -/
@[stacks 073C]
theorem isFlat_iff_smallEtaleRingedToposHom_isFlat :
    IsFlat B S hS f.hom ↔
      RingedToposHom.IsFlat (smallEtaleRingedToposHom B S hS f) := by
  rw [isFlat_iff_forall_etaleLocalRingMap_flat, smallEtaleRingedToposHom_isFlat_iff]
  exact forall_congr' fun x => etaleLocalRingMap_flat_iff_stalkRingMap_flat

end FlatTopos

end AlgebraicGeometry.Space

end
