module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# A module flat over the base is flat over the inverse image of the base's structure sheaf

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢` a quasi-coherent `𝒪_X`-module which
is flat over `Y` (Stacks 05VV).  Then `𝒢`, read as a module over `f⁻¹𝒪_Y` by restriction of
scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`, is a flat sheaf of `f⁻¹𝒪_Y`-modules on the small étale site of
`X`.  The scheme version is `AlgebraicGeometry.Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver`.

## Main results

* `AlgebraicGeometry.Space.isFlatModuleStalk_scalarRestriction`: the pointwise statement, at
  the point of the small étale site determined by a geometric point `x̄` of `X`.
* `AlgebraicGeometry.Space.isFlat_scalarRestriction_of_isFlatOver`: the statement above.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of commutative rings on the small étale site of
`X`: the inverse-image form of the structure map of the morphism of small étale ringed topoi of
Stacks 03G8, with source and target spelled as the structure sheaves of
`AlgebraicGeometry.Space.inverseImageRingedSite` and
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
def inverseImageCommStructureMap :
    (inverseImageRingedSite B S hS f).O ⟶ (smallEtaleRingedTopos B S hS X).O :=
  (smallEtaleRingedToposHom B S hS f).fSharpInverseImage

/-- The structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of rings is the inverse-image form of the
structure map of the morphism of small étale ringed topoi of Stacks 03G8, with commutativity
forgotten. -/
theorem inverseImageStructureMap_eq :
    inverseImageStructureMap B S hS f =
      (smallEtaleRingedToposHom B S hS f).ringFsharpInverseImage :=
  rfl

/-- **Flatness transported along a ring isomorphism of the scalars**, with the two rings in
independent universes: if `M` is flat over `R'`, `e : R ≃+* R'` and `R` acts on `M` through `e`,
then `M` is flat over `R`. -/
theorem flat_of_ringEquiv_of_smul_eq {R R' M : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [Module R M] [Module R' M] [Module.Flat R' M]
    (e : R ≃+* R') (hsmul : ∀ (r : R) (m : M), r • m = e r • m) : Module.Flat R M := by
  let _inst : Algebra R R' := e.toRingHom.toAlgebra
  have hmap : ∀ r : R, algebraMap R R' r = e r := fun _ => rfl
  have _hst : IsScalarTower R R' M := by
    refine ⟨fun r s m => ?_⟩
    rw [Algebra.smul_def, hmap, hsmul r (s • m), smul_smul]
  have _hRS : Module.Flat R R' :=
    Module.Flat.of_linearEquiv
      { toFun := e.symm
        map_add' := fun x y => map_add e.symm x y
        map_smul' := fun r s => by
          change e.symm (r • s) = r * e.symm s
          rw [Algebra.smul_def, hmap, map_mul, e.symm_apply_apply]
        invFun := e
        left_inv := fun s => e.apply_symm_apply s
        right_inv := fun r => e.symm_apply_apply r }
  exact Module.Flat.trans R R' M

/-- The fibre comparison of Stacks 04K2 at a geometric point `x̄`, followed by the comparison of
Stacks 05VQ: the stalk of `f⁻¹𝒪_Y` at `x̄` is the étale local ring of `Y` at `ȳ = f ∘ x̄`. -/
def inverseImageRingedSiteStalkRingEquiv (x : GeometricPoint B S hS X.1) :
    ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj ≃+*
      etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x) :=
  ((smallEtaleInverseImageFiberRingIso B S hS f x).app
      (smallEtaleRingedTopos B S hS Y).O).symm.commRingCatIsoToRingEquiv.trans
    (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x))

/-- The map of étale local rings of Stacks 04NG, read on the stalk of `f⁻¹𝒪_Y` through
`AlgebraicGeometry.Space.inverseImageRingedSiteStalkRingEquiv`, is the fibre of the structure map
`f⁻¹𝒪_Y ⟶ 𝒪_X` followed by the comparison of Stacks 05VQ. -/
theorem etaleLocalRingMap_inverseImageStalkRingEquiv (x : GeometricPoint B S hS X.1)
    (a : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj) :
    etaleLocalRingMap X.2 f.hom x (inverseImageRingedSiteStalkRingEquiv B S hS f x a) =
      pointStalkRingEquiv B S hS X x
        (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom a) := by
  let iso := (smallEtaleInverseImageFiberRingIso B S hS f x).app (smallEtaleRingedTopos B S hS Y).O
  have h := congrArg (fun φ => φ.hom (iso.inv a))
    (etaleLocalRingMapAsStalkMap_eq (B := B) (S := S) (hS := hS) (f := f) (x := x))
  have h2 := h.trans (congrArg (fun z => (((etaleSitePoint B S hS X.1 x X.2).sheafFiber
      (A := CommRingCat.{u})).map (smallEtaleRingedToposHom B S hS f).fSharpInverseImage).hom z)
    (iso.inv_hom_id_apply a))
  exact ((pointStalkRingEquiv B S hS X x).symm_apply_eq).1 h2

/-- **The stalk of `𝒢` at a geometric point is flat over the stalk of `f⁻¹𝒪_Y`** when `𝒢`
satisfies condition (2) of Stacks 05VU there, the stalk of `f⁻¹𝒪_Y` acting through the fibre of
the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
theorem flat_moduleStalk_inverseImage (G : Modules.{u, u} B S hS X.1 X.2)
    (x : GeometricPoint B S hS X.1) (hG : IsFlatOverAtGeometricPoint B S hS f G x) :
    @Module.Flat (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj)
      (Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G) _ _
      (Module.compHom _ (((etaleSitePoint B S hS X.1 x X.2).presheafFiber
        (A := CommRingCat.{u})).map (inverseImageCommStructureMap B S hS f).hom).hom) := by
  let Φ := etaleSitePoint B S hS X.1 x X.2
  let O := (smallEtaleRingedTopos B S hS X).O
  let A := (Φ.presheafFiber (A := CommRingCat.{u})).obj (inverseImageRingedSite B S hS f).O.obj
  let φ := ((Φ.presheafFiber (A := CommRingCat.{u})).map
    (inverseImageCommStructureMap B S hS f).hom).hom
  let RY := etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)
  let ρ := etaleLocalRingMap X.2 f.hom x
  let e := inverseImageRingedSiteStalkRingEquiv B S hS f x
  let M := Stacks.moduleStalk Φ O G
  let N := geometricModuleStalk B S hS X x G
  let : Module A M := Module.compHom _ φ
  let : Module RY N := Module.compHom _ ρ
  have hN : Module.Flat RY N := hG
  let ψ : M ≃+ N := (Stacks.moduleStalkLargeLinearEquiv Φ O G).symm.toAddEquiv.trans
    (geometricModuleStalkAddEquiv B S hS X x G)
  have hψ : ∀ (a : A) (m : M), ψ (a • m) = ρ (e a) • ψ m := by
    intro a m
    rw [show ρ (e a) = pointStalkRingEquiv B S hS X x (φ a) from
      etaleLocalRingMap_inverseImageStalkRingEquiv B S hS f x a]
    change (geometricModuleStalkAddEquiv B S hS X x G)
        ((Stacks.moduleStalkLargeLinearEquiv Φ O G).symm (φ a • m)) = _
    rw [LinearEquiv.map_smul, geometricModuleStalkAddEquiv_smul]
    rfl
  let : Module RY M := Module.compHom M e.symm.toRingHom
  let ψ' : M ≃ₗ[RY] N :=
    { ψ with
      map_smul' := fun r m => by
        change ψ (e.symm r • m) = ρ r • ψ m
        rw [hψ, e.apply_symm_apply] }
  have hM : Module.Flat RY M := Module.Flat.of_linearEquiv ψ'
  exact flat_of_ringEquiv_of_smul_eq e fun a m => by
    change a • m = e.symm (e a) • m
    rw [e.symm_apply_apply]

/-- **The stalk of `𝒢` over `f⁻¹𝒪_Y` at a geometric point is flat** when `𝒢` satisfies
condition (2) of Stacks 05VU there: the stalk at `x̄` of the restriction of scalars of `𝒢` along
`f⁻¹𝒪_Y ⟶ 𝒪_X` is a flat module over the stalk of `f⁻¹𝒪_Y`. -/
theorem isFlatModuleStalk_scalarRestriction (G : Modules.{u, u} B S hS X.1 X.2)
    (x : GeometricPoint B S hS X.1) (hG : IsFlatOverAtGeometricPoint B S hS f G x) :
    Stacks.IsFlatModuleStalk (etaleSitePoint B S hS X.1 x X.2)
      (inverseImageRingedSite B S hS f).O ((scalarRestriction B S hS f).obj G) :=
  Stacks.isFlatModuleStalk_restrictScalars (etaleSitePoint B S hS X.1 x X.2)
    (inverseImageCommStructureMap B S hS f)
    (inverseImageStructureMap B S hS f) G
    (fun U a => by rw [inverseImageStructureMap_eq]; rfl)
    (flat_moduleStalk_inverseImage B S hS f G x hG)

/-- **A module flat over the base is flat over `f⁻¹𝒪_Y`.**  If a quasi-coherent `𝒪_X`-module
`𝒢` is flat over `Y` in the sense of Stacks 05VV, then `𝒢`, read as an `f⁻¹𝒪_Y`-module by
restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`, is a flat sheaf of modules on the small étale site
of `X` ringed by `f⁻¹𝒪_Y`. -/
theorem isFlat_scalarRestriction_of_isFlatOver (G : Modules.{u, u} B S hS X.1 X.2)
    [G.IsQuasicoherentOnSite] (hG : IsFlatOver B S hS X.2 f.hom G) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := (inverseImageRingedSite B S hS f).O)
      ((scalarRestriction B S hS f).obj G) := by
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint] at hG
  exact Stacks.isFlat_of_forall_isFlatModuleStalk (inverseImageRingedSite B S hS f).O _
    (fun x => etaleSitePoint B S hS X.1 x X.2)
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2)
    (fun x => isFlatModuleStalk_scalarRestriction B S hS f G x (hG x))

end AlgebraicGeometry.Space

end
