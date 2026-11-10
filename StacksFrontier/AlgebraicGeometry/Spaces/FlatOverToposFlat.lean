module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkFiberBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparisonWeak
public import StacksFrontier.RingTheory.Flat.LocalCriterionEssFP
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# Flatness over the target of a module on an algebraic space, in the ringed topos

Let `p : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `G` be an
`𝒪_X`-module. Stacks 05VV defines `G` to be flat over `Y` chartwise
(`AlgebraicGeometry.Space.IsFlatOver`). On the other hand the morphism of small étale ringed
topoi of Stacks 03G8 has a structure map `p⁻¹𝒪_Y ⟶ 𝒪_X`, through which `G` is a module over
`p⁻¹𝒪_Y`, and one can ask that it be flat in the sense of ringed topoi: tensoring with it over
`p⁻¹𝒪_Y` is exact. This file proves that for quasi-coherent `G` the two notions agree. This is the
form in which the deformation theory of ringed topoi (Stacks 08MQ and its consumers, notably
Stacks 0CZU and 0CZV) receives the flatness of modules over a base of the functors of quotients
of algebraic spaces.

Both sides are flatness of the geometric stalks. Stacks 05VC turns topos flatness into stalkwise
flatness at the conservative family of geometric points; the stalk of `G` read over `p⁻¹𝒪_Y` is
the stalk of `G` with its scalars restricted along the stalk of the structure map; the stalk of
`p⁻¹𝒪_Y` at `x̄` is the étale local ring `𝒪_{Y, ȳ}` and the stalk of the structure map is the map
of Stacks 04NG; and the chartwise flatness of Stacks 05VV is flatness of `G_{x̄}` over `𝒪_{Y, ȳ}`
by Stacks 05VU.

## Main results

* `Stacks.moduleStalkRestrictScalarsAddEquiv` and its `_smul`: the stalk of a restriction of
  scalars of a sheaf of modules is the stalk, with the scalars restricted along the stalk of the
  ring map.
* `AlgebraicGeometry.Space.isFlatModuleStalk_restrictScalars_iff`: relative flatness at a
  geometric point, on both sides.
* `AlgebraicGeometry.Space.isFlatOver_iff_isFlat_restrictScalars`: **chartwise flatness over the
  target is flatness in the small étale ringed topos.**

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

namespace Stacks

section RestrictScalarsStalk

universe w v' u'

variable {C : Type u'} [Category.{v'} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : J.Point.{w}) {O O' : Sheaf J CommRingCat.{w}} (g : O ⟶ O')
  (M : SheafOfModules.{w} (commRingSheafToRingSheaf O'))

/-- **The stalk of a restriction of scalars is the stalk.** For a morphism `g : O ⟶ O'` of
sheaves of commutative rings and an `O'`-module `M`, the stalk at `Φ` of `M` read over `O` has the
same underlying abelian group as the stalk of `M`; the two scalar actions correspond through the
stalk of `g` (`Stacks.moduleStalkRestrictScalarsAddEquiv_smul`). -/
noncomputable def moduleStalkRestrictScalarsAddEquiv :
    moduleStalk Φ O ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map g)).obj M) ≃+
      moduleStalk Φ O' M :=
  AddEquiv.refl _

/-- The identification of the stalks is semilinear along the stalk of `g`. -/
theorem moduleStalkRestrictScalarsAddEquiv_smul
    (r : (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (m : moduleStalk Φ O ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map g)).obj M)) :
    moduleStalkRestrictScalarsAddEquiv Φ g M (r • m) =
      ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom).hom r •
        moduleStalkRestrictScalarsAddEquiv Φ g M m := by
  let c := forget₂ CommRingCat.{w} RingCat.{w}
  let φ := ((Φ.presheafFiber (A := CommRingCat.{w})).map g.hom).hom
  let cR := Φ.presheafFiberCocone (commRingSheafToRingSheaf O).obj
  let cR' := Φ.presheafFiberCocone (commRingSheafToRingSheaf O').obj
  let ψ : cR.pt →+* cR'.pt := ((Φ.presheafFiber (A := RingCat.{w})).map
    (Functor.whiskerRight g.hom c)).hom
  let ρ : (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj →+* cR.pt :=
    (commRingSheafFiberIso Φ O).inv.hom
  let ρ' : (Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj →+* cR'.pt :=
    (commRingSheafFiberIso Φ O').inv.hom
  obtain ⟨U, a, x, ha, hx⟩ := PresheafOfModules.ModuleColimit.jointly_surjective₂ (ρ r) m
  have hψ := Φ.toPresheafFiber_naturality
    (Functor.whiskerRight g.hom (forget₂ CommRingCat.{w} RingCat.{w})) U.unop.1 U.unop.2
  have hψapp : ψ ((cR.ι.app U).hom a) =
      (cR'.ι.app U).hom ((Functor.whiskerRight g.hom c).app (Opposite.op U.unop.1) a) :=
    ConcreteCategory.congr_hom hψ a
  have hρ : ρ' (φ r) = ψ (ρ r) := by
    have h : (commRingSheafFiberIso Φ O').hom.hom (ψ (ρ r)) = φ r :=
      ConcreteCategory.congr_hom (commRingSheafFiberIso_inv_comp Φ g) r
    rw [← h]
    exact ConcreteCategory.congr_hom (commRingSheafFiberIso Φ O').hom_inv_id (ψ (ρ r))
  let Mc := PresheafOfModules.ModuleColimit
    (Φ.isColimitPresheafFiberCocone (commRingSheafToRingSheaf O).obj)
    (colimit.isColimit ((PresheafOfModules.pushforward (F := Functor.Elements.π Φ.fiber)
      (𝟙 _)).obj ((SheafOfModules.forget (commRingSheafToRingSheaf O)).obj
        ((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map g)).obj M))).presheaf)
  let Mc' := PresheafOfModules.ModuleColimit
    (Φ.isColimitPresheafFiberCocone (commRingSheafToRingSheaf O').obj)
    (colimit.isColimit ((PresheafOfModules.pushforward (F := Functor.Elements.π Φ.fiber)
      (𝟙 _)).obj ((SheafOfModules.forget (commRingSheafToRingSheaf O')).obj M)).presheaf)
  rw [← hx]
  change ((ρ r • (PresheafOfModules.ModuleColimit.ιM x : Mc)) : Mc) =
    ((ρ' (φ r) • (PresheafOfModules.ModuleColimit.ιM x : Mc')) : Mc')
  rw [hρ, ← ha, hψapp]
  erw [PresheafOfModules.ModuleColimit.smul_eq]
  exact (PresheafOfModules.ModuleColimit.smul_eq
    (M := (PresheafOfModules.pushforward (F := Functor.Elements.π Φ.fiber) (𝟙 _)).obj
      ((SheafOfModules.forget (commRingSheafToRingSheaf O')).obj M)) _ _ _ _).symm

end RestrictScalarsStalk

/-- The inverse of an additive equivalence semilinear along a ring isomorphism `e` is semilinear
along `e⁻¹`. -/
theorem addEquiv_symm_smul_of_smul {R₁ R₂ X Y : Type*} [CommRing R₁] [CommRing R₂]
    [AddCommGroup X] [AddCommGroup Y] [Module R₁ X] [Module R₂ Y] (e : R₁ ≃+* R₂) (φ : X ≃+ Y)
    (hφ : ∀ (r : R₁) (x : X), φ (r • x) = e r • φ x) (r : R₂) (y : Y) :
    φ.symm (r • y) = e.symm r • φ.symm y := by
  apply φ.injective
  rw [AddEquiv.apply_symm_apply, hφ, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)

/-- Flatness of an `𝒪_X`-module over `p⁻¹𝒪_Y`, the module read over the inverse image of the
structure sheaf of `Y` through the structure map of the small étale ringed topos morphism of `p`,
is flatness of its stalks at the geometric points (Stacks 05VC). -/
theorem isFlat_restrictScalars_iff_forall_isFlatModuleStalk (G : Modules.{u, u} B S hS X.1 X.2) :
    AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (smallEtaleRingedToposHom B S hS p).fSharpInverseImage)).obj G) ↔
      ∀ x : GeometricPoint B S hS X.1,
        Stacks.IsFlatModuleStalk (etaleSitePoint B S hS X.1 x X.2) _
          ((SheafOfModules.restrictScalars
            ((sheafCompose (smallEtaleRingedTopos B S hS X).J
              (forget₂ CommRingCat.{u} RingCat.{u})).map
              (smallEtaleRingedToposHom B S hS p).fSharpInverseImage)).obj G) :=
  Stacks.isFlat_iff_forall_isFlatModuleStalk_of_weakSheafify _
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2) _ _

/-- The stalk at a geometric point `x̄` of `p⁻¹𝒪_Y` is the étale local ring `𝒪_{Y, ȳ}` at the image
point: the stalk of the inverse image is the stalk at the image point (Stacks 04K0), read through
the comparison of Stacks 05VQ. -/
noncomputable def inverseImageStalkRingEquiv (x : GeometricPoint B S hS X.1) :
    ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS p).toToposHom).obj
            (smallEtaleRingedTopos B S hS Y).O).obj ≃+*
      etaleLocalRing B S hS Y.1 (geometricPointMap p.hom x) :=
  ((smallEtaleInverseImageFiberRingIso B S hS p x).app
      (smallEtaleRingedTopos B S hS Y).O).symm.commRingCatIsoToRingEquiv.trans
    (pointStalkRingEquiv B S hS Y (geometricPointMap p.hom x))

/-- The stalk of the structure map `p⁻¹𝒪_Y ⟶ 𝒪_X` at `x̄` is the canonical map
`𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` of Stacks 04NG, through the comparisons of Stacks 05VQ. -/
theorem pointStalkRingEquiv_presheafFiber_map_fSharpInverseImage
    (x : GeometricPoint B S hS X.1)
    (a : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS p).toToposHom).obj
            (smallEtaleRingedTopos B S hS Y).O).obj) :
    pointStalkRingEquiv B S hS X x
        ((((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).map
          (smallEtaleRingedToposHom B S hS p).fSharpInverseImage.hom).hom a) =
      etaleLocalRingMap X.2 p.hom x (inverseImageStalkRingEquiv B S hS p x a) := by
  have hsplit : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber
      (A := CommRingCat.{u})).map (smallEtaleRingedToposHom B S hS p).fSharpInverseImage.hom =
      ((smallEtaleInverseImageFiberRingIso B S hS p x).app
        (smallEtaleRingedTopos B S hS Y).O).inv ≫ etaleLocalRingMapAsStalkMap B S hS p x := by
    rw [etaleLocalRingMapAsStalkMap_eq]
    exact (((smallEtaleInverseImageFiberRingIso B S hS p x).app
      (smallEtaleRingedTopos B S hS Y).O).inv_hom_id_assoc _).symm
  rw [hsplit]
  change pointStalkRingEquiv B S hS X x ((pointStalkRingEquiv B S hS X x).symm
    (etaleLocalRingMap X.2 p.hom x (inverseImageStalkRingEquiv B S hS p x a))) = _
  exact RingEquiv.apply_symm_apply _ _

/-- The identification of the stalk with the geometric stalk is semilinear along the comparison of
Stacks 05VQ. -/
theorem fiberStalkAddEquiv_smul (G : Modules.{u, u} B S hS X.1 X.2)
    (x : GeometricPoint B S hS X.1)
    (b : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O.obj)
    (m : Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O G) :
    fiberStalkAddEquiv B S hS X x G (b • m) =
      pointStalkRingEquiv B S hS X x b • fiberStalkAddEquiv B S hS X x G m := by
  change geometricModuleStalkAddEquiv B S hS X x G
      ((Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G).symm (b • m)) = _
  rw [LinearEquiv.map_smul, geometricModuleStalkAddEquiv_smul]
  rfl

/-- The stalk at `x̄` of an `𝒪_X`-module read over `p⁻¹𝒪_Y` is its geometric stalk `G_{x̄}`. -/
noncomputable def restrictScalarsStalkGeometricAddEquiv (G : Modules.{u, u} B S hS X.1 X.2)
    (x : GeometricPoint B S hS X.1) :
    Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
        ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS p).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O)
        ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (smallEtaleRingedToposHom B S hS p).fSharpInverseImage)).obj G) ≃+
      geometricModuleStalk B S hS X x G :=
  (Stacks.moduleStalkRestrictScalarsAddEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedToposHom B S hS p).fSharpInverseImage G).trans
    (fiberStalkAddEquiv B S hS X x G)

/-- `AlgebraicGeometry.Space.restrictScalarsStalkGeometricAddEquiv` is semilinear along
`AlgebraicGeometry.Space.inverseImageStalkRingEquiv`, the geometric stalk being a module over
`𝒪_{Y, ȳ}` through the map of Stacks 04NG. -/
theorem restrictScalarsStalkGeometricAddEquiv_smul (G : Modules.{u, u} B S hS X.1 X.2)
    (x : GeometricPoint B S hS X.1)
    (a : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS p).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O).obj)
    (l : Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
        ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS p).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O)
        ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (smallEtaleRingedToposHom B S hS p).fSharpInverseImage)).obj G)) :
    letI : Module (etaleLocalRing B S hS Y.1 (geometricPointMap p.hom x))
        (geometricModuleStalk B S hS X x G) :=
      Module.compHom _ (etaleLocalRingMap X.2 p.hom x)
    restrictScalarsStalkGeometricAddEquiv B S hS p G x (a • l) =
      inverseImageStalkRingEquiv B S hS p x a •
        restrictScalarsStalkGeometricAddEquiv B S hS p G x l := by
  refine (congrArg (fiberStalkAddEquiv B S hS X x G)
    (Stacks.moduleStalkRestrictScalarsAddEquiv_smul (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedToposHom B S hS p).fSharpInverseImage G a l)).trans ?_
  exact (fiberStalkAddEquiv_smul B S hS G x _ _).trans
    ((congrArg (· • restrictScalarsStalkGeometricAddEquiv B S hS p G x l)
      (pointStalkRingEquiv_presheafFiber_map_fSharpInverseImage B S hS p x a)).trans rfl)

/-- **Relative flatness at a geometric point, on both sides.** The stalk at `x̄` of an
`𝒪_X`-module read over `p⁻¹𝒪_Y` is flat over the stalk of `p⁻¹𝒪_Y` exactly when the geometric
stalk `G_{x̄}` is flat over the étale local ring `𝒪_{Y, ȳ}` (condition (2) of Stacks 05VU). -/
theorem isFlatModuleStalk_restrictScalars_iff (G : Modules.{u, u} B S hS X.1 X.2)
    (x : GeometricPoint B S hS X.1) :
    Stacks.IsFlatModuleStalk (etaleSitePoint B S hS X.1 x X.2)
        ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS p).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O)
        ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (smallEtaleRingedToposHom B S hS p).fSharpInverseImage)).obj G) ↔
      IsFlatOverAtGeometricPoint B S hS p G x := by
  let : Module (etaleLocalRing B S hS Y.1 (geometricPointMap p.hom x))
      (geometricModuleStalk B S hS X x G) :=
    Module.compHom _ (etaleLocalRingMap X.2 p.hom x)
  constructor
  · intro h
    have := h
    exact Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
      (inverseImageStalkRingEquiv B S hS p x).symm
      (restrictScalarsStalkGeometricAddEquiv B S hS p G x).symm
      (Stacks.addEquiv_symm_smul_of_smul _ _
        (restrictScalarsStalkGeometricAddEquiv_smul B S hS p G x))
  · intro h
    have : Module.Flat (etaleLocalRing B S hS Y.1 (geometricPointMap p.hom x))
        (geometricModuleStalk B S hS X x G) := h
    exact Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
      (inverseImageStalkRingEquiv B S hS p x) (restrictScalarsStalkGeometricAddEquiv B S hS p G x)
      (restrictScalarsStalkGeometricAddEquiv_smul B S hS p G x)

/-- **Flatness over the target, chartwise and in the ringed topos.** For a morphism
`p : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_X`-module `G`, the chartwise flatness of
`G` over `Y` of Stacks 05VV holds exactly when `G`, read as a module over `p⁻¹𝒪_Y` through the
structure map of the morphism of small étale ringed topoi of Stacks 03G8, is flat in the sense of
ringed topoi: tensoring with it is exact. Both sides are flatness of the geometric stalks
(Stacks 05VU and Stacks 05VC). -/
theorem isFlatOver_iff_isFlat_restrictScalars (G : Modules.{u, u} B S hS X.1 X.2)
    [G.IsQuasicoherentOnSite] :
    IsFlatOver B S hS X.2 p.hom G ↔
      AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (smallEtaleRingedToposHom B S hS p).fSharpInverseImage)).obj G) := by
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS p G,
    isFlat_restrictScalars_iff_forall_isFlatModuleStalk B S hS p G]
  exact forall_congr' fun x => (isFlatModuleStalk_restrictScalars_iff B S hS p G x).symm

end AlgebraicGeometry.Space

end
