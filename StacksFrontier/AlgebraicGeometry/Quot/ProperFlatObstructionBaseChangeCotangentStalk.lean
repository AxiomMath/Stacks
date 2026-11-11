module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeCotangentInverseImage
public import StacksFrontier.Cotangent.Spaces.FibreProductTorIndependent

/-!
# The rings of the base change of the cotangent complex on the models, at a geometric point

Let

```
W --p--> X
|        |
q        f
v        v
Y --g--> Z
```

be a commutative square of algebraic spaces. On the `Type u` model of the small étale site of `W`
the derived pullback along the model morphism `p_m` of `L_{X/Z}` (formed on the model of `X`) is
the cotangent complex `L_{B/A} ⊗_B 𝒪_W` of the tower `A = p_m⁻¹f_m⁻¹𝒪_Z ⟶ B = p_m⁻¹𝒪_X ⟶ 𝒪_W`
(`AlgebraicGeometry.RingedToposHom.derivedPullbackCotangentComplexIso`). This file supplies the
map of rings `a : A ⟶ q_m⁻¹𝒪_Y` over `𝒪_W` along which `L_{𝒪_W/A}` is compared with
`L_{W/Y} = L_{𝒪_W/q_m⁻¹𝒪_Y}` (`AlgebraicGeometry.Space.modelSquareBaseMap`,
`AlgebraicGeometry.Space.sq_modelSquareBaseMap`), and it identifies the stalks at the point of a
geometric point `w̄` of `W` of the four rings `A`, `q_m⁻¹𝒪_Y`, `B`, `𝒪_W` with the étale local rings
`𝒪_{Z, g(q(w̄))}`, `𝒪_{Y, q(w̄)}`, `𝒪_{X, p(w̄)}`, `𝒪_{W, w̄}`,
compatibly with the four maps between
them, which become the homomorphisms of étale local rings of Stacks 04NG.

Everything is read on the restriction to the model of the corresponding sheaves of rings on the
small étale site of `W`: `p_m⁻¹(-|_model) ≅ (p⁻¹ -)|_model`
(`AlgebraicGeometry.Space.modelPullbackInverseImageRingIso`), the stalk at the point of `w̄` of a
restricted sheaf is its stalk on `W_et` (`AlgebraicGeometry.Space.modelRestrictionFiberRingIso`),
and on `W_et` the stalks of inverse images are those at the image points (Stacks 04K2).

## Main definitions

* `AlgebraicGeometry.Space.modelSquareBaseMap`: `a : p_m⁻¹f_m⁻¹𝒪_Z ⟶ q_m⁻¹𝒪_Y`.
* `AlgebraicGeometry.Space.modelTowerBaseStalkEquiv`, `.modelInverseImageStalkEquiv`,
  `.modelPullbackStalkEquiv`, `.modelStructureStalkEquiv`: the four stalk identifications.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z W : AlgebraicSpaces B S hS}

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/-! ### Stalks of inverse images on the small étale site -/

section Etale

variable (B S hS) in
/-- The stalk at `w̄` of `l⁻¹𝒪_X` is the étale local ring `𝒪_{X, l(w̄)}` (Stacks 04K2). -/
def etaleInverseImageStalkEquiv (l : W ⟶ X) (w : GeometricPoint B S hS W.1) :
    ((etaleSitePoint B S hS W.1 w W.2).presheafFiber (A := CommRingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS X).O).obj ≃+*
      etaleLocalRing B S hS X.1 (geometricPointMap l.hom w) :=
  (((smallEtaleInverseImageFiberRingIso B S hS l w).app
      (smallEtaleRingedTopos B S hS X).O).symm.commRingCatIsoToRingEquiv).trans
    (pointStalkRingEquiv B S hS X (geometricPointMap l.hom w))

/-- **The stalk of the structure map `l⁻¹𝒪_X ⟶ 𝒪_W` is the homomorphism of étale local rings of
Stacks 04NG.** -/
theorem fSharpInverseImage_etaleStalk_apply (l : W ⟶ X) (w : GeometricPoint B S hS W.1)
    (x : ((etaleSitePoint B S hS W.1 w W.2).presheafFiber (A := CommRingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS X).O).obj) :
    pointStalkRingEquiv B S hS W w
        (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
          (smallEtaleRingedToposHom B S hS l).fSharpInverseImage x) =
      etaleLocalRingMap W.2 l.hom w (etaleInverseImageStalkEquiv B S hS l w x) :=
  (congrArg (pointStalkRingEquiv B S hS W w)
    (ConcreteCategory.congr_hom (Iso.inv_hom_id_app_assoc
      (smallEtaleInverseImageFiberRingIso B S hS l w) (smallEtaleRingedTopos B S hS X).O
      (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS l).fSharpInverseImage)) x).symm).trans
    (pointStalkRingEquiv_stalkStructureMap_apply l w _)

/-- **The stalk of the inverse image along `k` of the structure map of `l` is the homomorphism of
étale local rings of Stacks 04NG of `l` at `k(w̄)`**, the source read through the comparison
`k⁻¹l⁻¹ ≅ (k ≫ l)⁻¹`. -/
theorem inverseImage_fSharpInverseImage_etaleStalk_apply (k : W ⟶ Y) (l : Y ⟶ Z)
    (w : GeometricPoint B S hS W.1)
    (x : ((etaleSitePoint B S hS W.1 w W.2).presheafFiber (A := CommRingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS k).obj
          ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS Z).O)).obj) :
    etaleInverseImageStalkEquiv B S hS k w
        (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
          ((smallEtaleInverseImageRing B S hS k).map
            (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) x) =
      etaleLocalRingMap Y.2 l.hom (geometricPointMap k.hom w)
        (etaleInverseImageStalkEquiv B S hS (k ≫ l) w
          (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
            ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).hom.app
              (smallEtaleRingedTopos B S hS Z).O) x)) := by
  have E1 := fun y => ConcreteCategory.congr_hom
    ((smallEtaleInverseImageFiberRingIso B S hS (k ≫ l) w).inv_hom_id_app
      (smallEtaleRingedTopos B S hS Z).O) y
  have E2 := fun y => (ConcreteCategory.congr_hom
    (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map_comp
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).hom.app
        (smallEtaleRingedTopos B S hS Z).O)
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).inv.app
          (smallEtaleRingedTopos B S hS Z).O ≫
        (smallEtaleInverseImageRing B S hS k).map
          (smallEtaleRingedToposHom B S hS l).fSharpInverseImage)).symm y).trans
    (ConcreteCategory.congr_hom
      (congrArg ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        (Iso.hom_inv_id_app_assoc (smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l)
          (smallEtaleRingedTopos B S hS Z).O _)) y)
  have E3 := fun y => (ConcreteCategory.congr_hom (fiberRingIso_comp_sheafFiber_map k l w) y).symm
  refine (congrArg (fun y => pointStalkRingEquiv B S hS Y (geometricPointMap k.hom w)
    ((smallEtaleInverseImageFiberRingIso B S hS k w).inv.app (smallEtaleRingedTopos B S hS Y).O y))
    ((E2 x).symm.trans (congrArg (fun y => ((etaleSitePoint B S hS W.1 w W.2).sheafFiber
      (A := CommRingCat.{u})).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).inv.app
          (smallEtaleRingedTopos B S hS Z).O ≫
        (smallEtaleInverseImageRing B S hS k).map
          (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) y)
      (E1 (((etaleSitePoint B S hS W.1 w W.2).sheafFiber
      (A := CommRingCat.{u})).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).hom.app
        (smallEtaleRingedTopos B S hS Z).O) x)).symm))).trans ?_
  refine (congrArg (pointStalkRingEquiv B S hS Y (geometricPointMap k.hom w)) (E3 _).symm).trans ?_
  exact pointStalkRingEquiv_stalkStructureMap_apply l (geometricPointMap k.hom w) _

/-- Transport along an equality of morphisms commutes with the stalk identifications. -/
theorem etaleInverseImageStalkEquiv_eqToHom {k₁ k₂ : W ⟶ X} (e : k₁ = k₂)
    (w : GeometricPoint B S hS W.1)
    (y : ((etaleSitePoint B S hS W.1 w W.2).presheafFiber (A := CommRingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS k₁).obj (smallEtaleRingedTopos B S hS X).O).obj) :
    etaleInverseImageStalkEquiv B S hS k₂ w
        (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
          (eqToHom (congrArg (fun k : W ⟶ X =>
            (smallEtaleInverseImageRing B S hS k).obj (smallEtaleRingedTopos B S hS X).O) e)) y) =
      (eqToHom (congrArg (fun k : W ⟶ X => etaleLocalRing B S hS X.1 (geometricPointMap k.hom w))
        e)).hom (etaleInverseImageStalkEquiv B S hS k₁ w y) := by
  subst e
  exact congrArg (etaleInverseImageStalkEquiv B S hS k₁ w)
    (ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id _ _) y)

variable (B S hS) in
/-- The stalk at `w̄` of `k⁻¹l⁻¹𝒪_Z` is `𝒪_{Z, l(k(w̄))}`, through `k⁻¹l⁻¹ ≅ (k ≫ l)⁻¹`. -/
def etaleTowerStalkEquiv (k : W ⟶ Y) (l : Y ⟶ Z) (w : GeometricPoint B S hS W.1) :
    ((etaleSitePoint B S hS W.1 w W.2).presheafFiber (A := CommRingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS k).obj
          ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS Z).O)).obj ≃+*
      etaleLocalRing B S hS Z.1 (geometricPointMap l.hom (geometricPointMap k.hom w)) :=
  (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).mapIso
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).app
        (smallEtaleRingedTopos B S hS Z).O)).commRingCatIsoToRingEquiv.trans
    (etaleInverseImageStalkEquiv B S hS (k ≫ l) w)

/-- **The comparison `p⁻¹f⁻¹𝒪_Z ≅ q⁻¹g⁻¹𝒪_Z` of a commuting square is, on stalks, the transport
`𝒪_{Z, f(p(w̄))} = 𝒪_{Z, g(q(w̄))}`.** -/
theorem etaleTowerStalkEquiv_square {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}
    (h : p ≫ f = q ≫ g) (w : GeometricPoint B S hS W.1)
    (x : ((etaleSitePoint B S hS W.1 w W.2).presheafFiber (A := CommRingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS p).obj
          ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Z).O)).obj) :
    etaleTowerStalkEquiv B S hS q g w
        (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
          (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom x) =
      (eqToHom (congrArg (fun k : W ⟶ Z => etaleLocalRing B S hS Z.1 (geometricPointMap k.hom w))
        h)).hom (etaleTowerStalkEquiv B S hS p f w x) := by
  have e : (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS q g).hom.app
        (smallEtaleRingedTopos B S hS Z).O =
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).hom.app
          (smallEtaleRingedTopos B S hS Z).O ≫
        eqToHom (congrArg (fun k : W ⟶ Z =>
          (smallEtaleInverseImageRing B S hS k).obj (smallEtaleRingedTopos B S hS Z).O) h) := by
    simp only [smallEtaleRingedToposHom_squareInverseImageRingIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_inv, Iso.app_hom, eqToIso.hom, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id]
  have E := (ConcreteCategory.congr_hom
    (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map_comp
      (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS q g).hom.app
        (smallEtaleRingedTopos B S hS Z).O)).symm x).trans
      ((ConcreteCategory.congr_hom (congrArg
        ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map e) x).trans
        (ConcreteCategory.congr_hom
          (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map_comp
            ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).hom.app
              (smallEtaleRingedTopos B S hS Z).O)
            (eqToHom (congrArg (fun k : W ⟶ Z =>
              (smallEtaleInverseImageRing B S hS k).obj (smallEtaleRingedTopos B S hS Z).O) h))) x))
  exact (congrArg (etaleInverseImageStalkEquiv B S hS (q ≫ g) w) E).trans
    (etaleInverseImageStalkEquiv_eqToHom h w _)

end Etale

/-! ### The square on the models -/

section Model

variable {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

/-- The model morphism `p_m` of `p`, between the models `AlgebraicGeometry.Space.modelTopos`. -/
abbrev modelPullbackHom (p : W ⟶ X) : RingedToposHom (modelTopos W) (modelTopos X) :=
  smallEtaleModelPullbackRingedToposHom p

/-- The structure map of the transported morphism `f_m` is the restriction of that of `f`. -/
theorem modelRingedToposHom_fSharpInverseImage_eq_restriction (f : X ⟶ Z) :
    (modelRingedToposHom f).fSharpInverseImage =
      (modelInverseImageRingIso f).hom.app (smallEtaleRingedTopos B S hS Z).O ≫
        (modelRingRestriction (X := X)).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage :=
  Deformation.ToposThickening.RingedToposExtensionProblem.siteTransportHom_fSharpInverseImage
    (X := smallEtaleRingedTopos B S hS X) (B := smallEtaleRingedTopos B S hS Z)
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)
    (smallEtaleRingedToposHom B S hS f)

variable (f p) in
/-- The base `A = p_m⁻¹f_m⁻¹𝒪_Z` of the tower, identified with `(p⁻¹f⁻¹𝒪_Z)|_model`. -/
def modelTowerBaseIso :
    (modelPullbackHom p).toToposHom.inverseImageRing.obj
        ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1} (modelRingedToposHom f).toToposHom).obj
          (smallEtaleRingedTopos B S hS Z).O) ≅
      (modelRingRestriction (X := W)).obj ((smallEtaleInverseImageRing B S hS p).obj
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Z).O)) :=
  (modelPullbackHom p).toToposHom.inverseImageRing.mapIso
      ((modelInverseImageRingIso f).app (smallEtaleRingedTopos B S hS Z).O) ≪≫
    (modelPullbackInverseImageRingIso p).app
      ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Z).O)

/-- The base map of the tower, read through `modelTowerBaseIso` and
`modelPullbackInverseImageRingIso`, is the restriction of `p⁻¹(f⁻¹𝒪_Z ⟶ 𝒪_X)`. -/
theorem towerBaseMap_comp_modelPullbackInverseImageRingIso :
    RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p) ≫
        (modelPullbackInverseImageRingIso p).hom.app (smallEtaleRingedTopos B S hS X).O =
      (modelTowerBaseIso f p).hom ≫ (modelRingRestriction (X := W)).map
        ((smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) := by
  have hn := (modelPullbackInverseImageRingIso p).hom.naturality
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage
  calc RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p) ≫
        (modelPullbackInverseImageRingIso p).hom.app (smallEtaleRingedTopos B S hS X).O =
      (modelPullbackHom p).toToposHom.inverseImageRing.map
          ((modelInverseImageRingIso f).hom.app (smallEtaleRingedTopos B S hS Z).O ≫
            (modelRingRestriction (X := X)).map
              (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) ≫
        (modelPullbackInverseImageRingIso p).hom.app (smallEtaleRingedTopos B S hS X).O :=
        eq_whisker (congrArg (modelPullbackHom p).toToposHom.inverseImageRing.map
          (modelRingedToposHom_fSharpInverseImage_eq_restriction f)) _
    _ = (modelPullbackHom p).toToposHom.inverseImageRing.map
          ((modelInverseImageRingIso f).hom.app (smallEtaleRingedTopos B S hS Z).O) ≫
        ((modelPullbackHom p).toToposHom.inverseImageRing.map
            ((modelRingRestriction (X := X)).map
              (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) ≫
          (modelPullbackInverseImageRingIso p).hom.app (smallEtaleRingedTopos B S hS X).O) :=
        (eq_whisker (Functor.map_comp _ _ _) _).trans (Category.assoc _ _ _)
    _ = (modelTowerBaseIso f p).hom ≫ (modelRingRestriction (X := W)).map
        ((smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) :=
        (whisker_eq _ hn).trans (Category.assoc _ _ _).symm

variable (f g p q) in
/-- **The map of base rings `a : p_m⁻¹f_m⁻¹𝒪_Z ⟶ q_m⁻¹𝒪_Y`**, through which `L_{𝒪_W/A}` is
compared with `L_{W/Y}`: the restriction to the model of
`p⁻¹f⁻¹𝒪_Z ≅ q⁻¹g⁻¹𝒪_Z ⟶ q⁻¹𝒪_Y`. -/
def modelSquareBaseMap (h : p ≫ f = q ≫ g) :
    (modelPullbackHom p).toToposHom.inverseImageRing.obj
        ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1} (modelRingedToposHom f).toToposHom).obj
          (smallEtaleRingedTopos B S hS Z).O) ⟶
      (inverseImageCommRingFunctor.{u, u, u, u, u, u + 1} (modelRingedToposHom q).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O :=
  (modelTowerBaseIso f p).hom ≫
    (modelRingRestriction (X := W)).map
      ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
        (smallEtaleInverseImageRing B S hS q).map
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫
    (modelInverseImageRingIso q).inv.app (smallEtaleRingedTopos B S hS Y).O

/-- **`a` is a map of rings over `𝒪_W`**: the structure map of the tower of `f_m` and `p_m` is `a`
followed by the structure map of `q_m`. -/
theorem sq_modelSquareBaseMap (h : p ≫ f = q ≫ g) :
    (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p) ≫
        (modelPullbackHom p).fSharpInverseImage) ≫ 𝟙 _ =
      modelSquareBaseMap f g p q h ≫ (modelRingedToposHom q).fSharpInverseImage := by
  have hsq := smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage B S hS h
  calc (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p) ≫
        (modelPullbackHom p).fSharpInverseImage) ≫ 𝟙 _ =
      (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p) ≫
          (modelPullbackInverseImageRingIso p).hom.app (smallEtaleRingedTopos B S hS X).O) ≫
        (modelRingRestriction (X := W)).map
          (smallEtaleRingedToposHom B S hS p).fSharpInverseImage :=
        (Category.comp_id _).trans ((congrArg (_ ≫ ·)
          (smallEtaleModelPullbackRingedToposHom_fSharpInverseImage p)).trans
            (Category.assoc _ _ _).symm)
    _ = (modelTowerBaseIso f p).hom ≫ (modelRingRestriction (X := W)).map
          ((smallEtaleInverseImageRing B S hS p).map
            (smallEtaleRingedToposHom B S hS f).fSharpInverseImage ≫
          (smallEtaleRingedToposHom B S hS p).fSharpInverseImage) :=
        (congrArg (· ≫ _) towerBaseMap_comp_modelPullbackInverseImageRingIso).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm))
    _ = (modelTowerBaseIso f p).hom ≫ (modelRingRestriction (X := W)).map
          (((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
            (smallEtaleInverseImageRing B S hS q).map
              (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫
          (smallEtaleRingedToposHom B S hS q).fSharpInverseImage) :=
        congrArg (fun t => (modelTowerBaseIso f p).hom ≫ (modelRingRestriction (X := W)).map t)
          (hsq.symm.trans (Category.assoc _ _ _).symm)
    _ = modelSquareBaseMap f g p q h ≫ (modelRingedToposHom q).fSharpInverseImage := by
        refine (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ?_
        refine Eq.trans ?_ (congrArg (_ ≫ ·)
          (modelRingedToposHom_fSharpInverseImage_eq_restriction q).symm)
        simp only [modelSquareBaseMap, Category.assoc, Iso.inv_hom_id_app_assoc]

end Model

end AlgebraicGeometry.Space

end
