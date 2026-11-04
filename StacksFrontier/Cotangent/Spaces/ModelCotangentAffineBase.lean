module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelPoints
public import StacksFrontier.Cotangent.Spaces.AffineTargetStalk

/-!
# The cotangent complex of a morphism to an affine scheme over the constant base ring

Let `f : X ⟶ T` be a morphism from an algebraic space to an object `T` of the big fppf site with
affine underlying scheme, and let `Λ = Γ(T, 𝒪_T)`. The cotangent complex `L_{X/T}` of Stacks 08SU,
formed on the model of the small étale site of `X`
(`AlgebraicGeometry.Space.modelRingedToposHom`), is the cotangent complex of the homomorphism
`f⁻¹𝒪_T ⟶ 𝒪_X`. This file replaces the base `f⁻¹𝒪_T` by `f⁻¹Λ̲`, the inverse image of the constant
sheaf: the change-of-base map `L_{𝒪_X/f⁻¹Λ̲} ⟶ L_{𝒪_X/f⁻¹𝒪_T}` of the tower
`f⁻¹Λ̲ ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` is a quasi-isomorphism
(`AlgebraicGeometry.Space.quasiIso_modelTowerChangeOfBase`). This is the argument of Stacks 08VG:
the first vertex of the fundamental triangle of the tower (Tag 08SZ) vanishes, because at the
point of a geometric point `x̄` of `X` the stalk of `f⁻¹Λ̲ ⟶ f⁻¹𝒪_T` is the stalk map
`Λ → 𝒪_{T, f(x̄)}` of `T` (Stacks 04K2), whose ring-level cotangent complex is acyclic
(`AlgebraicGeometry.Space.acyclic_cotangentComplex_schemeSpaceStalkMap`), and the geometric
points form a conservative family of points of the model.

It then exhibits `f⁻¹Λ̲` as the sheafification of the constant presheaf `Λ` on the model
(`AlgebraicGeometry.Space.W_modelConstantBaseMap`), through a map whose composite with the tower
is, on the object of the model lying over an étale scheme chart `U` of `X`, the ring map
`Γ(U ⟶ T)` (`AlgebraicGeometry.Space.modelConstantBaseMap_comp`). These are the data of the
presheaf-base form of Tag 08SX, `AlgebraicGeometry.Sheaf.presheafBaseCohomologySheafIso`.

## Main definitions

* `AlgebraicGeometry.Space.modelTowerBase`, `AlgebraicGeometry.Space.modelTowerLower`: `f⁻¹Λ̲` and
  `f⁻¹Λ̲ ⟶ f⁻¹𝒪_T` on the model.
* `AlgebraicGeometry.Space.modelConstantBaseMap`: the constant presheaf `Λ ⟶ f⁻¹Λ̲`.

## Main results

* `AlgebraicGeometry.Space.isCotangentAcyclicAt_modelTowerLower`
* `AlgebraicGeometry.Space.quasiIso_modelTowerChangeOfBase`
* `AlgebraicGeometry.Space.W_modelConstantBaseMap`
* `AlgebraicGeometry.Space.modelConstantBaseMap_comp`

## References

* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-! ### The tower `f⁻¹Λ̲ ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` on the model -/

/-- The inverse image of sheaves of commutative rings along the transported morphism of `f`. -/
abbrev modelInverseImage :
    Sheaf (SmallEtale.topology B S hS (schemeSpace T).1) CommRingCat.{u} ⥤
      Sheaf (modelTopos X).J CommRingCat.{u} :=
  Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
    (modelRingedToposHom f).toToposHom

/-- The base `f⁻¹Λ̲` of the tower: the inverse image of the constant sheaf `Λ̲`, where
`Λ = Γ(T, 𝒪_T)`. -/
abbrev modelTowerBase : Sheaf (modelTopos X).J CommRingCat.{u} :=
  (modelInverseImage f).obj (chartBaseConstantRing (X := schemeSpace T) (T := T))

/-- The middle term `f⁻¹𝒪_T` of the tower. -/
abbrev modelTowerMiddle : Sheaf (modelTopos X).J CommRingCat.{u} :=
  (modelInverseImage f).obj (smallEtaleRingedTopos B S hS (schemeSpace T)).O

/-- The lower map `f⁻¹Λ̲ ⟶ f⁻¹𝒪_T` of the tower: the inverse image of the structure map of `T`. -/
abbrev modelTowerLower : modelTowerBase f ⟶ modelTowerMiddle f :=
  (modelInverseImage f).map (chartBaseStructureMap (𝟙 (schemeSpace T)))

/-- **The lower map of the tower has acyclic stalkwise cotangent complex**: at the point of a
geometric point `x̄` of `X` its stalk is the stalk map `Λ → 𝒪_{T, f(x̄)}` of `T` (Stacks 04K2). -/
theorem isCotangentAcyclicAt_modelTowerLower
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (x : GeometricPoint B S hS X.1) :
    CategoryTheory.Sheaf.IsCotangentAcyclicAt.{u, u, u} (modelTowerLower f)
      (modelSitePoint B S hS X x) := by
  let y := geometricPointMap f.hom x
  let θ := modelInverseImageFiberRingIso f x
  let σ := chartBaseStructureMap (𝟙 (schemeSpace T))
  let : Algebra (baseRing B S hS T) (schemeSpaceStalk y) := (schemeSpaceStalkMap y).toAlgebra
  let e₀ : ((modelSitePoint B S hS X x).presheafFiber (A := CommRingCat.{u})).obj
      (modelTowerBase f).obj ≃+* baseRing B S hS T :=
    (θ.app (chartBaseConstantRing (X := schemeSpace T) (T := T))).commRingCatIsoToRingEquiv.trans
      (chartBaseConstantFiberEquiv y)
  let e : ((modelSitePoint B S hS X x).presheafFiber (A := CommRingCat.{u})).obj
      (modelTowerMiddle f).obj ≃+* schemeSpaceStalk y :=
    (θ.app (smallEtaleRingedTopos B S hS (schemeSpace T)).O).commRingCatIsoToRingEquiv
  refine ⟨baseRing B S hS T, schemeSpaceStalk y, inferInstance, inferInstance, inferInstance,
    e₀, e, fun z => ?_, acyclic_cotangentComplex_schemeSpaceStalkMap y hT⟩
  refine (ConcreteCategory.congr_hom (θ.hom.naturality σ) z).trans
    ((ConcreteCategory.comp_apply _ _ z).trans ?_)
  exact congrArg (((schemeSpaceEtalePoint y).presheafFiber (A := CommRingCat.{u})).map σ.hom)
    ((RingEquiv.ofBijective _ (bijective_chartBaseConstantGerm y)).apply_symm_apply _).symm

/-- **`L_{𝒪_X/f⁻¹Λ̲} ⟶ L_{X/T}` is a quasi-isomorphism** for `T` affine, `Λ = Γ(T, 𝒪_T)`: the
change-of-base map of the tower `f⁻¹Λ̲ ⟶ f⁻¹𝒪_T ⟶ 𝒪_X`, formed on the model of the small étale
site of `X`. The first vertex of the fundamental triangle of the tower (Tag 08SZ) vanishes,
stalkwise at the geometric points of `X`, which are a conservative family of points of the
model. -/
theorem quasiIso_modelTowerChangeOfBase (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    QuasiIso (CategoryTheory.Sheaf.towerCotangentChangeOfBase.{u, u, u} (modelTopos X).J
      (modelTowerLower f) (modelRingedToposHom f).fSharpInverseImage) := by
  let := HasDerivedCategory.standard (Sheaf.targetModules.{u, u, u} (modelTopos X).J
    (modelTopos X).O)
  have hz := CategoryTheory.Sheaf.isZero_Q_obj_baseChangedCotangentComplex_of_isCotangentAcyclicAt
    (modelTowerLower f) (isConservativeFamilyOfPoints_modelSitePoint B S hS X)
    (fun Φ hΦ => by
      obtain ⟨x⟩ := hΦ
      exact isCotangentAcyclicAt_modelTowerLower f hT x)
    (modelRingedToposHom f).fSharpInverseImage
  obtain ⟨δ, hT'⟩ := CategoryTheory.Sheaf.exists_distTriang_towerCotangent.{u, u, u}
    (modelTopos X).J (modelTowerLower f) (modelRingedToposHom f).fSharpInverseImage
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 ((Triangle.isZero₁_iff_isIso₂ _ hT').1 hz)

/-! ### `f⁻¹Λ̲` as the sheafification of the constant presheaf -/

/-- Restriction of sheaves of commutative rings from `X_et` to the model. -/
abbrev modelRingRestriction :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} ⥤
      Sheaf (modelTopos X).J CommRingCat.{u} :=
  (smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)

/-- The constant presheaf of rings with value `Λ = Γ(T, 𝒪_T)` on the model. -/
abbrev modelConstantPresheaf : ((modelTopos X).C)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const ((modelTopos X).C)ᵒᵖ).obj (CommRingCat.of (baseRing B S hS T))

/-- **The constant presheaf `Λ ⟶ f⁻¹Λ̲` on the model**: the restriction to the model of the
sheafification map of the constant presheaf on `X_et`, followed by the identifications
`Λ̲_X ≅ f⁻¹Λ̲_T` of constant sheaves and of the inverse image along the transported morphism with
the restriction of the inverse image along `f`. -/
def modelConstantBaseMap : modelConstantPresheaf (X := X) (T := T) ⟶ (modelTowerBase f).obj :=
  Functor.whiskerLeft (smallEtaleModelEquiv B S hS X).inverse.op
      (toSheafify (SmallEtale.topology B S hS X.1)
        ((Functor.const (SmallEtale B S hS X.1)ᵒᵖ).obj (CommRingCat.of (baseRing B S hS T)))) ≫
    ((modelRingRestriction (X := X)).map
      ((constantSheafInverseImageIso f).hom.app (CommRingCat.of (baseRing B S hS T)))).hom ≫
    ((modelInverseImageRingIso f).inv.app (chartBaseConstantRing (X := schemeSpace T) (T := T))).hom

/-- **`f⁻¹Λ̲` is the sheafification of the constant presheaf `Λ` on the model.** -/
theorem W_modelConstantBaseMap : (modelTopos X).J.W (modelConstantBaseMap f) := by
  have hw : (smallEtaleModelTopology B S hS X.1).W (Functor.whiskerLeft
      (smallEtaleModelEquiv B S hS X).inverse.op (toSheafify (SmallEtale.topology B S hS X.1)
        ((Functor.const (SmallEtale B S hS X.1)ᵒᵖ).obj (CommRingCat.of (baseRing B S hS T))))) :=
    (GrothendieckTopology.W_whiskerLeft_iff (SmallEtale.topology B S hS X.1)
      (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse _).2
      (GrothendieckTopology.W_toSheafify _ _)
  rw [GrothendieckTopology.W_iff] at hw ⊢
  rw [modelConstantBaseMap, Functor.map_comp]
  have hi : IsIso (((modelRingRestriction (X := X)).map
      ((constantSheafInverseImageIso f).hom.app (CommRingCat.of (baseRing B S hS T)))).hom ≫
      ((modelInverseImageRingIso f).inv.app
        (chartBaseConstantRing (X := schemeSpace T) (T := T))).hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).mapIso ((modelRingRestriction (X := X)).mapIso
      ((constantSheafInverseImageIso f).app (CommRingCat.of (baseRing B S hS T))) ≪≫
        ((modelInverseImageRingIso f).app
          (chartBaseConstantRing (X := schemeSpace T) (T := T))).symm)).hom)
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ hw ?_
  exact @Functor.map_isIso _ _ _ _ _ _ _ _ hi

/-- The structure map of the transported morphism is the restriction of that of `f`. -/
theorem modelRingedToposHom_fSharpInverseImage_eq :
    (modelRingedToposHom f).fSharpInverseImage =
      (modelInverseImageRingIso f).hom.app (smallEtaleRingedTopos B S hS (schemeSpace T)).O ≫
        (modelRingRestriction (X := X)).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage :=
  Deformation.ToposThickening.RingedToposExtensionProblem.siteTransportHom_fSharpInverseImage
    (X := smallEtaleRingedTopos B S hS X) (B := smallEtaleRingedTopos B S hS (schemeSpace T))
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)
    (smallEtaleRingedToposHom B S hS f)

/-- The tower on the model, read from `f⁻¹Λ̲_T` restricted from `X_et`, is the restriction of the
tower on `X_et`. -/
theorem modelInverseImageRingIso_inv_comp_tower :
    (modelInverseImageRingIso f).inv.app (chartBaseConstantRing (X := schemeSpace T) (T := T)) ≫
        (modelTowerLower f ≫ (modelRingedToposHom f).fSharpInverseImage) =
      (modelRingRestriction (X := X)).map
        ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom).map
            (chartBaseStructureMap (𝟙 (schemeSpace T))) ≫
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) := by
  rw [modelRingedToposHom_fSharpInverseImage_eq, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ _) ?_
  rw [← (modelInverseImageRingIso f).inv.naturality, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl

/-- **The tower on the sections of the constant presheaf**: on the object of the model lying over
an étale scheme chart `U` of `X`, the composite `Λ ⟶ f⁻¹Λ̲ ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` is the ring map
`Γ(U ⟶ T)`. -/
theorem modelConstantBaseMap_comp :
    modelConstantBaseMap f ≫ (modelTowerLower f ≫ (modelRingedToposHom f).fSharpInverseImage).hom =
      Functor.whiskerLeft (smallEtaleModelEquiv B S hS X).inverse.op
        (chartBaseStructurePresheafMap f) := by
  have h1 := congrArg (fun t => ((modelRingRestriction (X := X)).map
      ((constantSheafInverseImageIso f).hom.app (CommRingCat.of (baseRing B S hS T)))).hom ≫ t.hom)
    (modelInverseImageRingIso_inv_comp_tower f)
  have hg := congrArg (fun φ => Functor.whiskerLeft (smallEtaleModelEquiv B S hS X).inverse.op φ)
    (toSheafify_comp_inverseImageStructureMap f)
  refine Eq.trans ?_ hg
  refine Eq.trans ?_ (congrArg (fun t => Functor.whiskerLeft
    (smallEtaleModelEquiv B S hS X).inverse.op
    (toSheafify (SmallEtale.topology B S hS X.1)
      ((Functor.const (SmallEtale B S hS X.1)ᵒᵖ).obj (CommRingCat.of (baseRing B S hS T)))) ≫ t)
    h1)
  rfl

end AlgebraicGeometry.Space

end
