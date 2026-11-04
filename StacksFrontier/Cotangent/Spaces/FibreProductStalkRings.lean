module

public import StacksFrontier.Cotangent.Spaces.FibreProductCornerStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageFiberRingIsoComp
public import StacksFrontier.Cotangent.Spaces.RepresentableStalks

/-!
# The stalk rings of the right column of Stacks 09DK are the étale local rings

Let `p : W ⟶ X`, `q : W ⟶ Y`, `f : X ⟶ Z`, `g : Y ⟶ Z` be morphisms of algebraic spaces with
`p ≫ f = q ≫ g` and let `w̄` be a geometric point of `W`. The right column of the diagram of
Stacks 09DK is read at `w̄` on four sheaves of rings on the small étale site of `W`: the base
`q⁻¹g⁻¹𝒪_Z` of the tower of `q`, `q⁻¹𝒪_Y`, `𝒪_W` and `p⁻¹𝒪_X`. This file identifies their stalks at
`w̄` with the étale local rings `𝒪_{Z, f(p(w̄))}`, `𝒪_{Y, q(w̄)}`, `𝒪_{W, w̄}` and `𝒪_{X, p(w̄)}`
(`AlgebraicGeometry.Space.towerBaseStalkEquiv`, `AlgebraicGeometry.Space.inverseImageStalkEquiv`,
`AlgebraicGeometry.Space.smallEtaleStructureSheafULiftStalkEquiv`,
`AlgebraicGeometry.Space.liftedBaseRingStalkEquiv`), compatibly with the four maps between them:
under the identifications they are the homomorphisms of étale local rings of Stacks 04NG
(`AlgebraicGeometry.Space.liftedStructureMap_stalk_apply`,
`AlgebraicGeometry.Space.fSharpInverseImageULift_stalk_apply`,
`AlgebraicGeometry.Space.columnBaseMap_stalk_apply`,
`AlgebraicGeometry.Space.towerBaseMap_stalk_apply`).

The identifications are built from the fibre comparison of Stacks 04K2 (4)
(`AlgebraicGeometry.Space.smallEtaleInverseImageFiberRingIso`), its transitivity, and the
computation of the fibre of a structure map as the map of Stacks 04NG
(`AlgebraicGeometry.Space.stalkStructureMapAsEtaleLocalRingMap_eq`).

## References

* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z W : AlgebraicSpaces B S hS}

/-- **The tower base map of `k` and `l`, read through the universe comparisons, is the lift of the
inverse image along `k` of the structure map of `l`.** -/
theorem towerBaseULiftIso_inv_comp_towerBaseMap (k : W ⟶ Y) (l : Y ⟶ Z) :
    (towerBaseULiftIso k l).inv ≫
        RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
          (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k) ≫
        (smallEtaleInverseImageRingULiftIso k).inv.app (smallEtaleRingedTopos B S hS Y).O =
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).inv.app
            (smallEtaleRingedTopos B S hS Z).O ≫
          (smallEtaleInverseImageRing B S hS k).map
            (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) := by
  have hnat := (smallEtaleInverseImageRingULiftIso k).hom.naturality
    (smallEtaleRingedToposHom B S hS l).fSharpInverseImage
  simp only [Functor.comp_map] at hnat
  simp only [towerBaseULiftIso, RingedToposHom.towerBaseMap,
    smallEtaleRingedToposHomULift_fSharpInverseImage, smallEtaleFSharpInverseImageULift,
    Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Functor.mapIso_inv,
    Iso.app_inv, Category.assoc, Functor.map_comp]
  refine congrArg (_ ≫ ·) ?_
  change (smallEtaleInverseImageRingULiftIso k).hom.app _ ≫
      (inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS k)).map
        ((smallEtaleInverseImageRingULiftIso l).hom.app (smallEtaleRingedTopos B S hS Z).O) ≫
      (inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS k)).map
        ((smallEtaleInverseImageRingULiftIso l).inv.app (smallEtaleRingedTopos B S hS Z).O ≫
          (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS Y.1)).map
            (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) ≫
      (smallEtaleInverseImageRingULiftIso k).inv.app (smallEtaleRingedTopos B S hS Y).O = _
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((Iso.comp_inv_eq ((smallEtaleInverseImageRingULiftIso k).app _)).mpr hnat.symm)

variable (B S hS) in
/-- **The stalk of `l⁻¹𝒪_X` at a geometric point is the étale local ring of `X` at its image.**
For `l : W ⟶ X` and a geometric point `w̄` of `W`, the stalk of the lifted base ring
`l⁻¹𝒪_X` of `L_{W/X}` at the point of the small étale site attached to `w̄` is
`𝒪_{X, l(w̄)}`: the stalk of a lifted sheaf is the lift of the stalk, the stalk of an inverse
image is the stalk at the image point (Stacks 04K2, part (4)), and the stalk of the structure
sheaf is the étale local ring. -/
def liftedBaseRingStalkEquiv (l : W ⟶ X) (w : GeometricPoint B S hS W.1) :
    ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        (liftedBaseRing (B := B) (S := S) (hS := hS) l).obj ≃+*
      etaleLocalRing B S hS X.1 (geometricPointMap l.hom w) :=
  (Stacks.uliftRingFiberIso' (etaleSitePoint B S hS W.1 w W.2)
      ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS X).O).obj
    ).commRingCatIsoToRingEquiv.trans
    (ULift.ringEquiv.trans
      ((((smallEtaleInverseImageFiberRingIso B S hS l w).app
          (smallEtaleRingedTopos B S hS X).O).symm.commRingCatIsoToRingEquiv).trans
        (pointStalkRingEquiv B S hS X (geometricPointMap l.hom w))))

/-- The stalk at `w̄` of the structure map of `l` is the homomorphism of étale local rings induced
by `l`, read through `pointStalkRingEquiv`. -/
private theorem pointStalkRingEquiv_stalkStructureMap (l : W ⟶ X) (w : GeometricPoint B S hS W.1)
    (z : ((etaleSitePoint B S hS X.1 (geometricPointMap l.hom w) X.2).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :
    pointStalkRingEquiv B S hS W w ((stalkStructureMap B S hS l w).hom z) =
      etaleLocalRingMap W.2 l.hom w
        (pointStalkRingEquiv B S hS X (geometricPointMap l.hom w) z) := by
  rw [← RingHom.congr_fun (stalkStructureMapAsEtaleLocalRingMap_eq B S hS l w)]
  exact congrArg (fun t => pointStalkRingEquiv B S hS W w ((stalkStructureMap B S hS l w).hom t))
    ((pointStalkRingEquiv B S hS X (geometricPointMap l.hom w)).symm_apply_apply z).symm

/-- **The stalk of the structure map of `L_{W/X}` is the homomorphism of étale local rings of
Stacks 04NG.** -/
theorem liftedStructureMap_stalk_apply (l : W ⟶ X) (w : GeometricPoint B S hS W.1)
    (x : ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        (liftedBaseRing (B := B) (S := S) (hS := hS) l).obj) :
    smallEtaleStructureSheafULiftStalkEquiv B S hS W w
        (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
          (liftedStructureMap l).hom x) =
      etaleLocalRingMap W.2 l.hom w (liftedBaseRingStalkEquiv B S hS l w x) := by
  have h1 := ConcreteCategory.congr_hom (Stacks.uliftRingFiberIso'_naturality
    (etaleSitePoint B S hS W.1 w W.2) (smallEtaleRingedToposHom B S hS l).fSharpInverseImage.hom) x
  refine Eq.trans ?_ (pointStalkRingEquiv_stalkStructureMap l w _)
  have h1' : ((Stacks.uliftRingFiberIso' (etaleSitePoint B S hS W.1 w W.2)
      (smallEtaleRingedTopos B S hS W).O.obj).hom
        (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
          (liftedStructureMap l).hom x)).down =
      ((etaleSitePoint B S hS W.1 w W.2).presheafFiber.map
        (smallEtaleRingedToposHom B S hS l).fSharpInverseImage.hom).hom
        ((Stacks.uliftRingFiberIso' (etaleSitePoint B S hS W.1 w W.2)
          ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS X).O).obj).hom
            x).down :=
    congrArg ULift.down h1
  have h4 : ∀ y, (stalkStructureMap B S hS l w).hom
      (((smallEtaleInverseImageFiberRingIso B S hS l w).inv.app
        (smallEtaleRingedTopos B S hS X).O).hom y) =
      (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS l).fSharpInverseImage).hom y := by
    intro y
    rw [stalkStructureMap, ConcreteCategory.comp_apply]
    refine congrArg _ ?_
    have h5 := ConcreteCategory.congr_hom
      ((smallEtaleInverseImageFiberRingIso B S hS l w).inv_hom_id_app
        (smallEtaleRingedTopos B S hS X).O) y
    rw [ConcreteCategory.comp_apply] at h5
    exact h5
  exact congrArg (pointStalkRingEquiv B S hS W w) (h1'.trans (h4 _).symm)

/-- **The fibre at `w̄` of the inverse image along `k` of the structure map of `l`**, read through
the fibre comparisons of Stacks 04K2 (4) for `k ≫ l` and for `k`, is the fibre of the structure
map of `l` at `k(w̄)`. -/
theorem fiberRingIso_comp_sheafFiber_map (k : W ⟶ Y) (l : Y ⟶ Z) (w : GeometricPoint B S hS W.1) :
    (smallEtaleInverseImageFiberRingIso B S hS (k ≫ l) w).hom.app (smallEtaleRingedTopos B S hS
        Z).O ≫
        ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).inv.app
              (smallEtaleRingedTopos B S hS Z).O ≫
            (smallEtaleInverseImageRing B S hS k).map
              (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) ≫
        (smallEtaleInverseImageFiberRingIso B S hS k w).inv.app (smallEtaleRingedTopos B S hS Y).O =
      stalkStructureMap B S hS l (geometricPointMap k.hom w) := by
  have hn := (smallEtaleInverseImageFiberRingIso B S hS k w).hom.naturality
    (smallEtaleRingedToposHom B S hS l).fSharpInverseImage
  rw [← smallEtaleInverseImageFiberRingIso_comp B S hS k l w]
  simp only [Functor.comp_map] at hn
  have e1 : ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).hom.app
          (smallEtaleRingedTopos B S hS Z).O) ≫
      ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).inv.app
            (smallEtaleRingedTopos B S hS Z).O ≫
          (smallEtaleInverseImageRing B S hS k).map
            (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) =
      ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        ((smallEtaleInverseImageRing B S hS k).map
          (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) :=
    (Functor.map_comp _ _ _).symm.trans (congrArg _ (Iso.hom_inv_id_app_assoc _ _ _))
  have e2 : (smallEtaleInverseImageFiberRingIso B S hS k w).hom.app
        ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS Z).O) ≫
      ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        ((smallEtaleInverseImageRing B S hS k).map
          (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) ≫
      (smallEtaleInverseImageFiberRingIso B S hS k w).inv.app (smallEtaleRingedTopos B S hS Y).O =
      ((etaleSitePoint B S hS Y.1 (geometricPointMap k.hom w) Y.2).sheafFiber
        (A := CommRingCat.{u})).map (smallEtaleRingedToposHom B S hS l).fSharpInverseImage :=
    (Category.assoc _ _ _).symm.trans
      ((Iso.comp_inv_eq ((smallEtaleInverseImageFiberRingIso B S hS k w).app _)).mpr hn.symm)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e1))))).trans ?_)
  exact congrArg (_ ≫ ·) e2

/-- Under the identifications of stalks with étale local rings, the stalk at `ȳ` of the structure
map of `l` is the homomorphism of étale local rings `𝒪_{Z, l(ȳ)} → 𝒪_{Y, ȳ}` induced by `l`. -/
theorem pointStalkRingEquiv_stalkStructureMap_apply (l : Y ⟶ Z) (y : GeometricPoint B S hS Y.1)
    (z : ((etaleSitePoint B S hS Z.1 (geometricPointMap l.hom y) Z.2).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Z).O.obj) :
    pointStalkRingEquiv B S hS Y y ((stalkStructureMap B S hS l y).hom z) =
      etaleLocalRingMap Y.2 l.hom y (pointStalkRingEquiv B S hS Z (geometricPointMap l.hom y) z) :=
  pointStalkRingEquiv_stalkStructureMap l y z

/-- **The stalk of the lifted inverse image along `k` of the structure map of `l` is the
homomorphism of étale local rings of Stacks 04NG of `l` at `k(w̄)`.** -/
theorem liftedInverseImageStructureMap_stalk_apply (k : W ⟶ Y) (l : Y ⟶ Z)
    (w : GeometricPoint B S hS W.1)
    (x : ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        (liftedBaseRing (B := B) (S := S) (hS := hS) (k ≫ l)).obj) :
    liftedBaseRingStalkEquiv B S hS k w
        (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
          ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
            ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).inv.app
                (smallEtaleRingedTopos B S hS Z).O ≫
              (smallEtaleInverseImageRing B S hS k).map
                (smallEtaleRingedToposHom B S hS l).fSharpInverseImage)).hom x) =
      etaleLocalRingMap Y.2 l.hom (geometricPointMap k.hom w)
        (liftedBaseRingStalkEquiv B S hS (k ≫ l) w x) := by
  have h1 := ConcreteCategory.congr_hom (Stacks.uliftRingFiberIso'_naturality
    (etaleSitePoint B S hS W.1 w W.2)
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS k l).inv.app
        (smallEtaleRingedTopos B S hS Z).O ≫
      (smallEtaleInverseImageRing B S hS k).map
        (smallEtaleRingedToposHom B S hS l).fSharpInverseImage).hom) x
  have h3 := ConcreteCategory.congr_hom ((Iso.inv_comp_eq
    ((smallEtaleInverseImageFiberRingIso B S hS (k ≫ l) w).app
      (smallEtaleRingedTopos B S hS Z).O)).mpr (fiberRingIso_comp_sheafFiber_map k l w).symm)
    ((Stacks.uliftRingFiberIso' (etaleSitePoint B S hS W.1 w W.2)
      ((smallEtaleInverseImageRing B S hS (k ≫ l)).obj (smallEtaleRingedTopos B S hS Z).O).obj).hom
        x).down
  refine Eq.trans ?_ (pointStalkRingEquiv_stalkStructureMap_apply l (geometricPointMap k.hom w) _)
  exact congrArg (pointStalkRingEquiv B S hS Y (geometricPointMap k.hom w))
    ((congrArg (fun t => ((smallEtaleInverseImageFiberRingIso B S hS k w).inv.app
      (smallEtaleRingedTopos B S hS Y).O).hom t) (congrArg ULift.down h1)).trans h3.symm)

variable (B S hS) in
/-- The isomorphism of stalks at a geometric point induced by an isomorphism of sheaves of rings
on the small étale site. -/
abbrev stalkRingEquivOfIso (w : GeometricPoint B S hS W.1)
    {F G : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u + 1}} (e : F ≅ G) :
    ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj F.obj ≃+*
      ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj G.obj :=
  (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).mapIso
    ((sheafToPresheaf _ _).mapIso e)).commRingCatIsoToRingEquiv

/-- Transport along an equality of morphisms commutes with the stalk identifications. -/
theorem liftedBaseRingStalkEquiv_eqToHom {k₁ k₂ : W ⟶ Z} (e : k₁ = k₂)
    (w : GeometricPoint B S hS W.1)
    (y : ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        (liftedBaseRing (B := B) (S := S) (hS := hS) k₁).obj) :
    liftedBaseRingStalkEquiv B S hS k₂ w
        (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
          (eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) e)).hom y) =
      (eqToHom (congrArg (fun k : W ⟶ Z => etaleLocalRing B S hS Z.1 (geometricPointMap k.hom w))
        e)).hom (liftedBaseRingStalkEquiv B S hS k₁ w y) := by
  subst e
  simp

/-- Transporting an element of a commutative ring along an equality and back returns it. -/
theorem eqToHom_hom_apply_eqToHom {R₁ R₂ : CommRingCat.{u + 1}} (h₁ : R₁ = R₂) (h₂ : R₂ = R₁)
    (t : R₁) : (eqToHom h₂).hom ((eqToHom h₁).hom t) = t := by
  subst h₁
  rfl

section FibreProduct

variable {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

variable (B S hS) in
/-- The stalk of `q⁻¹𝒪_Y` (at the universe of the site) at `w̄` is `𝒪_{Y, q(w̄)}`. -/
def inverseImageStalkEquiv (q : W ⟶ Y) (w : GeometricPoint B S hS W.1) :
    ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj (smallEtaleStructureSheafULift B S hS Y)).obj ≃+*
      etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w) :=
  (stalkRingEquivOfIso B S hS w ((smallEtaleInverseImageRingULiftIso q).app
    (smallEtaleRingedTopos B S hS Y).O).symm).trans (liftedBaseRingStalkEquiv B S hS q w)

variable (B S hS) in
/-- The stalk of the base `q⁻¹g⁻¹𝒪_Z` of the tower of the second projection at `w̄` is
`𝒪_{Z, f(p(w̄))}`. -/
def towerBaseStalkEquiv (h : p ≫ f = q ≫ g) (w : GeometricPoint B S hS W.1) :
    ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj ≃+*
      etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap p.hom w)) :=
  (stalkRingEquivOfIso B S hS w (towerBaseULiftIso q g ≪≫
    eqToIso (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm))).trans
    (liftedBaseRingStalkEquiv B S hS (p ≫ f) w)

/-- Under the identifications of stalks with étale local rings, the stalk at `w̄` of the map
`q⁻¹𝒪_Y → 𝒪_W` is the homomorphism of étale local rings `𝒪_{Y, q(w̄)} → 𝒪_{W, w̄}` induced by `q`.
-/
theorem fSharpInverseImageULift_stalk_apply (w : GeometricPoint B S hS W.1)
    (x : ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj (smallEtaleStructureSheafULift B S hS Y)).obj) :
    smallEtaleStructureSheafULiftStalkEquiv B S hS W w
        (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
            (smallEtaleRingedToposHomULift q).fSharpInverseImage.hom x) =
      etaleLocalRingMap W.2 q.hom w (inverseImageStalkEquiv B S hS q w x) := by
  have hA : (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
      (smallEtaleRingedToposHomULift q).fSharpInverseImage.hom) x =
      (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
          (liftedStructureMap q).hom)
        ((((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
            ((smallEtaleInverseImageRingULiftIso q).inv.app
          (smallEtaleRingedTopos B S hS Y).O).hom) x) := by
    rw [smallEtaleRingedToposHomULift_fSharpInverseImage q]
    exact ConcreteCategory.congr_hom (((geometricSitePoint B S hS W w).presheafFiber (A :=
        CommRingCat.{u + 1})).map_comp
      ((smallEtaleInverseImageRingULiftIso q).inv.app (smallEtaleRingedTopos B S hS Y).O).hom
      (liftedStructureMap q).hom) x
  rw [hA]
  exact liftedStructureMap_stalk_apply q w _

/-- Under the identifications of stalks with étale local rings, the stalk at `w̄` of the map
`q⁻¹g⁻¹𝒪_Z → p⁻¹𝒪_X` is the homomorphism of étale local rings `𝒪_{Z, f(p(w̄))} → 𝒪_{X, p(w̄)}`
induced by `f`. -/
theorem columnBaseMap_stalk_apply (h : p ≫ f = q ≫ g) (w : GeometricPoint B S hS W.1)
    (x : ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj) :
    liftedBaseRingStalkEquiv B S hS p w (((geometricSitePoint B S hS W w).presheafFiber (A :=
        CommRingCat.{u + 1})).map
        ((towerBaseULiftIso q g).hom ≫
      eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm) ≫
      (towerBaseULiftIso p f).inv ≫
      RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p) ≫
      (smallEtaleInverseImageRingULiftIso p).inv.app (smallEtaleRingedTopos B S hS X).O).hom x) =
      etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w) (towerBaseStalkEquiv B S hS h w x) :=
          by
  have e : ((towerBaseULiftIso q g).hom ≫
      eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm) ≫
      (towerBaseULiftIso p f).inv ≫
      RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p) ≫
      (smallEtaleInverseImageRingULiftIso p).inv.app (smallEtaleRingedTopos B S hS X).O) =
          ((towerBaseULiftIso q g).hom ≫
      eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm)) ≫
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).inv.app
            (smallEtaleRingedTopos B S hS Z).O ≫
          (smallEtaleInverseImageRing B S hS p).map
            (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) :=
    (congrArg (fun t => (towerBaseULiftIso q g).hom ≫
      eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm) ≫ t)
      (towerBaseULiftIso_inv_comp_towerBaseMap p f)).trans (Category.assoc _ _ _).symm
  rw [e]
  exact (congrArg (liftedBaseRingStalkEquiv B S hS p w) (ConcreteCategory.congr_hom
      (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map_comp
          ((towerBaseULiftIso q g).hom ≫
        eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm)).hom
    ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).inv.app
            (smallEtaleRingedTopos B S hS Z).O ≫
          (smallEtaleInverseImageRing B S hS p).map
            (smallEtaleRingedToposHom B S hS f).fSharpInverseImage)).hom) x)).trans
                (liftedInverseImageStructureMap_stalk_apply p f w _)

/-- Under the identifications of stalks with étale local rings, the stalk at `w̄` of the map
`q⁻¹g⁻¹𝒪_Z → q⁻¹𝒪_Y` is the transport `𝒪_{Z, f(p(w̄))} = 𝒪_{Z, g(q(w̄))}` along `h` followed by
the homomorphism of étale local rings `𝒪_{Z, g(q(w̄))} → 𝒪_{Y, q(w̄)}` induced by `g`. -/
theorem towerBaseMap_stalk_apply (h : p ≫ f = q ≫ g) (w : GeometricPoint B S hS W.1)
    (x : ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj) :
    inverseImageStalkEquiv B S hS q w (((geometricSitePoint B S hS W w).presheafFiber (A :=
        CommRingCat.{u + 1})).map
        (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
          (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q)).hom x) =
      (eqToHom (congrArg (etaleLocalRing B S hS Z.1)
          (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) h)) ≫
        CommRingCat.ofHom (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w))).hom
        (towerBaseStalkEquiv B S hS h w x) := by
  have hL2 := (Iso.inv_comp_eq (towerBaseULiftIso q g)).mp (towerBaseULiftIso_inv_comp_towerBaseMap
      q g)
  have s1 : ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
      ((smallEtaleInverseImageRingULiftIso q).inv.app (smallEtaleRingedTopos B S hS Y).O).hom
          (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
              (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
          (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q)).hom x) =
      ((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
          ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS q g).inv.app
              (smallEtaleRingedTopos B S hS Z).O ≫
            (smallEtaleInverseImageRing B S hS q).map
              (smallEtaleRingedToposHom B S hS g).fSharpInverseImage)).hom (((geometricSitePoint B
                  S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map (towerBaseULiftIso q
                      g).hom.hom x) :=
    by
    have e1 := ConcreteCategory.congr_hom (((geometricSitePoint B S hS W w).presheafFiber (A :=
        CommRingCat.{u + 1})).map_comp (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u
            + 1, u + 1}
          (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q)).hom
              ((smallEtaleInverseImageRingULiftIso q).inv.app (smallEtaleRingedTopos B S hS
                  Y).O).hom) x
    have e2 := ConcreteCategory.congr_hom (((geometricSitePoint B S hS W w).presheafFiber (A :=
        CommRingCat.{u + 1})).map_comp (towerBaseULiftIso q g).hom.hom
      ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS q g).inv.app
              (smallEtaleRingedTopos B S hS Z).O ≫
            (smallEtaleInverseImageRing B S hS q).map
              (smallEtaleRingedToposHom B S hS g).fSharpInverseImage)).hom) x
    have e3 := congrArg (fun t => ConcreteCategory.hom
      (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map t.hom) x) hL2
    exact e1.symm.trans (e3.trans e2)
  have s2 := liftedInverseImageStructureMap_stalk_apply q g w
    (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
        (towerBaseULiftIso q g).hom.hom x)
  have s3 := liftedBaseRingStalkEquiv_eqToHom h.symm w (((geometricSitePoint B S hS W
      w).presheafFiber (A := CommRingCat.{u + 1})).map (towerBaseULiftIso q g).hom.hom x)
  have s4 : towerBaseStalkEquiv B S hS h w x = liftedBaseRingStalkEquiv B S hS (p ≫ f) w
      (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map (eqToHom
          (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm)).hom
              (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
                  (towerBaseULiftIso q g).hom.hom x)) :=
    congrArg (liftedBaseRingStalkEquiv B S hS (p ≫ f) w)
      (ConcreteCategory.congr_hom (((geometricSitePoint B S hS W w).presheafFiber (A :=
          CommRingCat.{u + 1})).map_comp (towerBaseULiftIso q g).hom.hom (eqToHom (congrArg (fun k
              => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm)).hom) x)
  refine (congrArg (liftedBaseRingStalkEquiv B S hS q w) s1).trans (s2.trans ?_)
  refine congrArg (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w)) ?_
  rw [s4, s3]
  exact (eqToHom_hom_apply_eqToHom _ _ _).symm

end FibreProduct

end AlgebraicGeometry.Space

end
