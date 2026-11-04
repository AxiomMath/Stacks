module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtensionCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPowerMap
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections

/-!
# The comparison `Tot(𝓟^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•` and restriction to an open

Let `X` be a scheme, `𝓘 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, `𝓕^•` a complex of
`𝒪_X`-modules with quasi-coherent terms and `π : 𝓟^• ⟶ 𝓕^•` a map of complexes. The maps
`Tot(𝓟^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•` of `AlgebraicGeometry.idealPowerResolutionNatTrans`, which compute
the canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` of [Stacks, Tag 0G4U] when `𝓟^•` is K-flat, form a map
of inverse systems of complexes. This file proves that this map is compatible with restriction
along an open immersion `f : Y ⟶ X`: the restriction of the system `(Tot(𝓟^• ⊗ 𝓘^n[0]))_n` is the
system `(Tot(𝓟^•|_Y ⊗ (𝓘|_Y)^n[0]))_n`, the restriction of `(𝓘^n 𝓕^•)_n` is
`((𝓘|_Y)^n (𝓕^•|_Y))_n`, and under these identifications the restricted map is the map attached
to `𝓘|_Y` and `π|_Y`. Moreover `𝓟^•|_Y` is K-flat when `𝓟^•` is ([Stacks, Tag 06YC]).

The identifications are made degree by degree. A total complex against a module in degree zero
is the termwise complex `p ↦ 𝓟^p ⊗ 𝓘^n`; restriction commutes with tensor products
([Stacks, Tag 01CD]) and carries `𝓘^n` to `(𝓘|_Y)^n`; and the multiplication maps
`𝓜 ⊗ 𝓘^n ⟶ 𝓘^n 𝓜` commute with restriction, which is checked on local sections.

## Main definitions

* `AlgebraicGeometry.restrictIdealPowerSheafIso`: `𝓘^n|_Y ≅ (𝓘|_Y)^n`.
* `AlgebraicGeometry.restrictSheafTensorIso`: `(A ⊗ B)|_Y ≅ A|_Y ⊗ B|_Y`, at the spelling of the
  tensor product at which total tensor complexes are formed.
* `AlgebraicGeometry.restrictRowComplexIso`: the restriction of the termwise complex
  `p ↦ 𝓟^p ⊗ M`.
* `AlgebraicGeometry.restrictIdealPowerResolutionTermIso`:
  `Tot(𝓟^• ⊗ 𝓘^n[0])|_Y ≅ Tot(𝓟^•|_Y ⊗ (𝓘|_Y)^n[0])`.
* `AlgebraicGeometry.restrictIdealPowerResolutionSystemIso` and
  `AlgebraicGeometry.restrictIdealPowerTensorComplexSystemIso`: the restrictions of the source and
  of the target of `AlgebraicGeometry.idealPowerResolutionNatTrans`, as inverse systems.

## Main results

* `AlgebraicGeometry.idealPowerResolutionNatTrans_restrict`: the restriction of
  `AlgebraicGeometry.idealPowerResolutionNatTrans` for `(𝓘, π)` is the one for `(𝓘|_Y, π|_Y)`.
* `AlgebraicGeometry.kFlatComplex_restrict`: the restriction of a K-flat complex is K-flat.
* `AlgebraicGeometry.restrictSheafTensorIso_inv_idealPowerTensorMulAmbient`: the multiplication
  maps `𝓜 ⊗ 𝓘^n ⟶ 𝓜` commute with restriction.

## Implementation notes

Complexes entering a tensor product are stated at the spelling `Stacks.Duality.TensorComplex`,
and restriction of complexes is retyped once to it as
`AlgebraicGeometry.restrictTensorComplexFunctor`. The total complexes and their transition maps
are likewise retyped once (`AlgebraicGeometry.idealPowerTotalSingleIso`,
`AlgebraicGeometry.idealPowerResolutionTransition`), so that the squares which are pasted together
match syntactically; the pasting itself is done by lemmas stated in an arbitrary pair of
categories.

## References

* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)

/-- **The restriction of `𝓘^n` is `(𝓘|_Y)^n`.** For an open immersion `f : Y ⟶ X`, the
restriction of the subsheaf `𝓘^n 𝒪_X ⊆ 𝒪_X` is the subsheaf `(𝓘|_Y)^n 𝒪_Y ⊆ 𝒪_Y`: restriction
carries `𝓘^n 𝒪_X` onto `(𝓘|_Y)^n (𝒪_X|_Y)`, as `𝒪_X` is quasi-coherent
(`Stacks.Algebraization.isIso_idealPowerMultipleRestrictMap`), and `𝒪_X|_Y ≅ 𝒪_Y` carries
`(𝓘|_Y)^n (𝒪_X|_Y)` to `(𝓘|_Y)^n 𝒪_Y`. -/
public def restrictIdealPowerSheafIso (n : ℕ) :
    (Scheme.Modules.restrictFunctor f).obj (idealPowerSheaf I n) ≅
      idealPowerSheaf (I.comap f) n :=
  haveI : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  @asIso _ _ _ _ (Stacks.Algebraization.idealPowerMultipleRestrictMap f I n
      (SheafOfModules.unit X.ringCatSheaf))
    (Stacks.Algebraization.isIso_idealPowerMultipleRestrictMap f I n _) ≪≫
    (DeligneTriangle.idealPowerFunctor (I.comap f) n).mapIso (Scheme.Modules.restrictUnitIso f)

/-- `AlgebraicGeometry.restrictIdealPowerSheafIso` composed with the inclusion into `𝒪_Y` is the
restriction of the inclusion into `𝒪_X`, followed by `𝒪_X|_Y ≅ 𝒪_Y`. -/
public lemma restrictIdealPowerSheafIso_hom_ι (n : ℕ) :
    (restrictIdealPowerSheafIso f I n).hom ≫
        (idealPowerMultiple (I.comap f) n (SheafOfModules.unit Y.ringCatSheaf)).ι =
      (Scheme.Modules.restrictFunctor f).map
          (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι ≫
        (Scheme.Modules.restrictUnitIso f).hom := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  exact (Category.assoc _ _ _).trans
    ((congrArg (Stacks.Algebraization.idealPowerMultipleRestrictMap f I n
      (SheafOfModules.unit X.ringCatSheaf) ≫ ·)
      (DeligneTriangle.idealPowerTermMap_comp_ι (I.comap f) n
        (Scheme.Modules.restrictUnitIso f).hom)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (Scheme.Modules.restrictUnitIso f).hom)
          (idealPowerMultipleRestrictMap_comp_ι f I n _))))

/-- **The restriction of a tensor product is the tensor product of the restrictions**,
`(A ⊗ B)|_Y ≅ A|_Y ⊗ B|_Y` ([Stacks, Tag 01CD]). This is
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso`, retyped at the spelling
`Stacks.SheafOfModules.Tensor.sheafTensor` of the tensor product at which total tensor complexes
are formed; the two spellings are equal by `rfl`. -/
public abbrev restrictSheafTensorIso (A B : X.Modules) :
    (Scheme.Modules.restrictFunctor f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
        ((Scheme.Modules.restrictFunctor f).obj A)).obj
          ((Scheme.Modules.restrictFunctor f).obj B) :=
  Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso f A B

/-- The inverse of `AlgebraicGeometry.restrictSheafTensorIso` on local sections: it carries the
image of a pure tensor `a ⊗ b` of sections over `W` to the image of `a ⊗ b` over `f(W)`. -/
public lemma restrictSheafTensorIso_inv_toTensorSheafSection (A B : X.Modules) (W : Y.Opens)
    (a : A.val.obj (op (f ''ᵁ W))) (b : B.val.obj (op (f ''ᵁ W))) :
    ((restrictSheafTensorIso f A B).inv.val.app (op W)).hom
        (toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.restrictFunctor f).obj A)
          ((Scheme.Modules.restrictFunctor f).obj B) (op W) (a ⊗ₜ b)) =
      toTensorSheafSection X.toRingedSpace A B (op (f ''ᵁ W)) (a ⊗ₜ b) :=
  (congrArg ((restrictSheafTensorIso f A B).inv.val.app (op W)).hom
      (Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso_hom_unit_tmul
        f A B W a b).symm).trans
    (congrArg (fun k => (k.val.app (op W)).hom
      (toTensorSheafSection X.toRingedSpace A B (op (f ''ᵁ W)) (a ⊗ₜ b)))
      (restrictSheafTensorIso f A B).hom_inv_id)

/-- The inverse of `AlgebraicGeometry.restrictSheafTensorIso` is natural in both variables. -/
public lemma restrictSheafTensorIso_inv_naturality {A A' B B' : X.Modules} (u : A ⟶ A')
    (v : B ⟶ B') :
    (restrictSheafTensorIso f A B).inv ≫
        (Scheme.Modules.restrictFunctor f).map ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
          (X := (A, B)) (Y := (A', B')) (u, v)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map
          (X := ((Scheme.Modules.restrictFunctor f).obj A,
            (Scheme.Modules.restrictFunctor f).obj B))
          (Y := ((Scheme.Modules.restrictFunctor f).obj A',
            (Scheme.Modules.restrictFunctor f).obj B'))
          ((Scheme.Modules.restrictFunctor f).map u, (Scheme.Modules.restrictFunctor f).map v) ≫
        (restrictSheafTensorIso f A' B').inv := by
  refine tensorSheaf_hom_ext fun U m b => ?_
  obtain ⟨W⟩ := U
  change (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
          (X := (A, B)) (Y := (A', B')) (u, v)).val.app (op (f ''ᵁ W))).hom
      (((restrictSheafTensorIso f A B).inv.val.app (op W)).hom
        (toTensorSheafSection Y.toRingedSpace _ _ (op W) (m ⊗ₜ b))) =
    ((restrictSheafTensorIso f A' B').inv.val.app (op W)).hom
      ((((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map
          (X := ((Scheme.Modules.restrictFunctor f).obj A,
            (Scheme.Modules.restrictFunctor f).obj B))
          (Y := ((Scheme.Modules.restrictFunctor f).obj A',
            (Scheme.Modules.restrictFunctor f).obj B'))
          ((Scheme.Modules.restrictFunctor f).map u,
            (Scheme.Modules.restrictFunctor f).map v)).val.app (op W)).hom
        (toTensorSheafSection Y.toRingedSpace _ _ (op W) (m ⊗ₜ b)))
  refine (congrArg (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
          (X := (A, B)) (Y := (A', B')) (u, v)).val.app (op (f ''ᵁ W))).hom
    (restrictSheafTensorIso_inv_toTensorSheafSection f A B W m b)).trans ?_
  refine (tensorSheafMap_app_toTensorSheafSection X.toRingedSpace A B A' B' u v _ m b).trans ?_
  refine Eq.trans ?_ (congrArg ((restrictSheafTensorIso f A' B').inv.val.app (op W)).hom
    (tensorSheafMap_app_toTensorSheafSection Y.toRingedSpace _ _ _ _
      ((Scheme.Modules.restrictFunctor f).map u) ((Scheme.Modules.restrictFunctor f).map v)
      W m b)).symm
  exact (restrictSheafTensorIso_inv_toTensorSheafSection f A' B' W _ _).symm

/-- The uncurried tensor product functor on `(u, 𝟙 B)` is the whiskering of `u` by `B`. -/
private lemma uncurry_sheafTensor_map_left {Z : Scheme.{u}} {A A' : Z.Modules} (u : A ⟶ A')
    (B : Z.Modules) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map
      (X := (A, B)) (Y := (A', B)) (u, 𝟙 B) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map u).app B :=
  (congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map u).app B ≫ ·)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj A').map_id B)).trans
    (Category.comp_id _)

/-- The uncurried tensor product functor on `(𝟙 A, v)` is the tensoring of `v` with `A`. -/
private lemma uncurry_sheafTensor_map_right {Z : Scheme.{u}} (A : Z.Modules) {B B' : Z.Modules}
    (v : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map
      (X := (A, B)) (Y := (A, B')) (𝟙 A, v) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj A).map v :=
  (congrArg (· ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj A).map v)
    (congrArg (fun g => g.app B)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map_id A))).trans
    (Category.id_comp _)

/-- **Multiplication `m ⊗ a ↦ a • m` commutes with restriction**: restricting
`𝓜 ⊗ 𝓘^n ⟶ 𝓜` is, through `AlgebraicGeometry.restrictSheafTensorIso` and
`AlgebraicGeometry.restrictIdealPowerSheafIso`, the multiplication `𝓜|_Y ⊗ (𝓘|_Y)^n ⟶ 𝓜|_Y`.
It is checked on local sections, where both sides are `a • m`. -/
public lemma restrictSheafTensorIso_inv_idealPowerTensorMulAmbient (n : ℕ) (M : X.Modules) :
    (restrictSheafTensorIso f M (idealPowerSheaf I n)).inv ≫
        (Scheme.Modules.restrictFunctor f).map (idealPowerTensorMulAmbient I n M) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
          ((Scheme.Modules.restrictFunctor f).obj M)).map (restrictIdealPowerSheafIso f I n).hom ≫
        idealPowerTensorMulAmbient (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M) := by
  refine tensorSheaf_hom_ext fun U m a => ?_
  obtain ⟨W⟩ := U
  change ((idealPowerTensorMulAmbient I n M).val.app (op (f ''ᵁ W))).hom
      (((restrictSheafTensorIso f M (idealPowerSheaf I n)).inv.val.app (op W)).hom
        (toTensorSheafSection Y.toRingedSpace _ _ (op W) (m ⊗ₜ a))) =
    ((idealPowerTensorMulAmbient (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M)).val.app
        (op W)).hom
      (((((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
          ((Scheme.Modules.restrictFunctor f).obj M)).map
            (restrictIdealPowerSheafIso f I n).hom).val.app
          (op W)).hom (toTensorSheafSection Y.toRingedSpace _ _ (op W) (m ⊗ₜ a)))
  have hY := tensorSheafMap_app_toTensorSheafSection Y.toRingedSpace
    ((Scheme.Modules.restrictFunctor f).obj M)
    ((Scheme.Modules.restrictFunctor f).obj (idealPowerSheaf I n))
    ((Scheme.Modules.restrictFunctor f).obj M) (idealPowerSheaf (I.comap f) n) (𝟙 _)
    (restrictIdealPowerSheafIso f I n).hom W m a
  have e1 := uncurry_sheafTensor_map_right ((Scheme.Modules.restrictFunctor f).obj M)
    (restrictIdealPowerSheafIso f I n).hom
  have hY' := (congrArg (fun φ => (φ.val.app (op W)).hom
    (toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.restrictFunctor f).obj M)
      ((Scheme.Modules.restrictFunctor f).obj (idealPowerSheaf I n)) (op W)
      (m ⊗ₜ[Y.presheaf.obj (op W)] a))) e1).symm.trans hY
  refine (congrArg ((idealPowerTensorMulAmbient I n M).val.app (op (f ''ᵁ W))).hom
    (restrictSheafTensorIso_inv_toTensorSheafSection f M (idealPowerSheaf I n) W m a)).trans ?_
  refine (idealPowerTensorMulAmbient_app_toTensorSheafSection I n M (f ''ᵁ W) m a).trans ?_
  refine Eq.trans ?_ (congrArg ((idealPowerTensorMulAmbient (I.comap f) n
      ((Scheme.Modules.restrictFunctor f).obj M)).val.app (op W)).hom hY').symm
  refine Eq.trans ?_ (idealPowerTensorMulAmbient_app_toTensorSheafSection (I.comap f) n
    ((Scheme.Modules.restrictFunctor f).obj M) W m _).symm
  let x : X.ringCatSheaf.obj.obj (op (f ''ᵁ W)) :=
    ((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι.val.app (op (f ''ᵁ W))).hom a
  let m' : M.val.obj (op (f ''ᵁ W)) := m
  change x • m' = (show X.ringCatSheaf.obj.obj (op (f ''ᵁ W)) from
    (f.appIso W).inv ((f.appIso W).hom x)) • m'
  exact (congrArg (fun r : X.ringCatSheaf.obj.obj (op (f ''ᵁ W)) => r • m')
    (Iso.hom_inv_id_apply (f.appIso W) x)).symm

/-- `AlgebraicGeometry.restrictSheafTensorIso` is natural in both variables. -/
public lemma restrictSheafTensorIso_hom_naturality {A A' B B' : X.Modules} (u : A ⟶ A')
    (v : B ⟶ B') :
    (Scheme.Modules.restrictFunctor f).map ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
          (X := (A, B)) (Y := (A', B')) (u, v)) ≫
        (restrictSheafTensorIso f A' B').hom =
      (restrictSheafTensorIso f A B).hom ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map
          (X := ((Scheme.Modules.restrictFunctor f).obj A,
            (Scheme.Modules.restrictFunctor f).obj B))
          (Y := ((Scheme.Modules.restrictFunctor f).obj A',
            (Scheme.Modules.restrictFunctor f).obj B'))
          ((Scheme.Modules.restrictFunctor f).map u, (Scheme.Modules.restrictFunctor f).map v) :=
  (Iso.inv_comp_eq _).mp ((Category.assoc _ _ _).symm.trans
    ((Iso.eq_comp_inv _).mp (restrictSheafTensorIso_inv_naturality f u v)))

/-- `AlgebraicGeometry.restrictSheafTensorIso` is natural in the first variable. -/
public lemma restrictSheafTensorIso_hom_naturality_left {A A' : X.Modules} (u : A ⟶ A')
    (B : X.Modules) :
    (Scheme.Modules.restrictFunctor f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map u).app B) ≫
        (restrictSheafTensorIso f A' B).hom =
      (restrictSheafTensorIso f A B).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map
          ((Scheme.Modules.restrictFunctor f).map u)).app
            ((Scheme.Modules.restrictFunctor f).obj B) := by
  have eX := uncurry_sheafTensor_map_left (Z := X) u B
  have eY := uncurry_sheafTensor_map_left (Z := Y) ((Scheme.Modules.restrictFunctor f).map u)
    ((Scheme.Modules.restrictFunctor f).obj B)
  exact (congrArg (fun g => (Scheme.Modules.restrictFunctor f).map g ≫
    (restrictSheafTensorIso f A' B).hom) eX).symm.trans
    ((restrictSheafTensorIso_hom_naturality f u (𝟙 B)).trans
      ((congrArg (fun g => (restrictSheafTensorIso f A B).hom ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map
          (X := ((Scheme.Modules.restrictFunctor f).obj A,
            (Scheme.Modules.restrictFunctor f).obj B))
          (Y := ((Scheme.Modules.restrictFunctor f).obj A',
            (Scheme.Modules.restrictFunctor f).obj B))
          ((Scheme.Modules.restrictFunctor f).map u, g))
        ((Scheme.Modules.restrictFunctor f).map_id B)).trans
          (congrArg ((restrictSheafTensorIso f A B).hom ≫ ·) eY)))

/-- `AlgebraicGeometry.restrictSheafTensorIso` is natural in the second variable. -/
public lemma restrictSheafTensorIso_hom_naturality_right (A : X.Modules) {B B' : X.Modules}
    (v : B ⟶ B') :
    (Scheme.Modules.restrictFunctor f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).map v) ≫
        (restrictSheafTensorIso f A B').hom =
      (restrictSheafTensorIso f A B).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
          ((Scheme.Modules.restrictFunctor f).obj A)).map
            ((Scheme.Modules.restrictFunctor f).map v) := by
  have eX := uncurry_sheafTensor_map_right (Z := X) A v
  have eY := uncurry_sheafTensor_map_right (Z := Y) ((Scheme.Modules.restrictFunctor f).obj A)
    ((Scheme.Modules.restrictFunctor f).map v)
  exact (congrArg (fun g => (Scheme.Modules.restrictFunctor f).map g ≫
    (restrictSheafTensorIso f A B').hom) eX).symm.trans
    ((restrictSheafTensorIso_hom_naturality f (𝟙 A) v).trans
      ((congrArg (fun g => (restrictSheafTensorIso f A B).hom ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map
          (X := ((Scheme.Modules.restrictFunctor f).obj A,
            (Scheme.Modules.restrictFunctor f).obj B))
          (Y := ((Scheme.Modules.restrictFunctor f).obj A,
            (Scheme.Modules.restrictFunctor f).obj B'))
          (g, (Scheme.Modules.restrictFunctor f).map v))
        ((Scheme.Modules.restrictFunctor f).map_id A)).trans
          (congrArg ((restrictSheafTensorIso f A B).hom ≫ ·) eY)))

/-- `AlgebraicGeometry.restrictIdealPowerSheafIso` is compatible with the inclusions
`𝓘^{n+1} ⊆ 𝓘^n` and `(𝓘|_Y)^{n+1} ⊆ (𝓘|_Y)^n`. -/
public lemma restrictIdealPowerSheafIso_transition (n : ℕ) :
    (Scheme.Modules.restrictFunctor f).map (idealPowerSheafTransition I n) ≫
        (restrictIdealPowerSheafIso f I n).hom =
      (restrictIdealPowerSheafIso f I (n + 1)).hom ≫
        idealPowerSheafTransition (I.comap f) n := by
  refine cancel_sheafSubmodule_ι
    (idealPowerMultiple (I.comap f) n (SheafOfModules.unit Y.ringCatSheaf)) _ _ ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (restrictIdealPowerSheafIso_hom_ι f I n)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (Scheme.Modules.restrictUnitIso f).hom)
    ((Functor.map_comp _ _ _).symm.trans (congrArg (Scheme.Modules.restrictFunctor f).map
      (idealPowerMultipleMap_comp_ι I (SheafOfModules.unit X.ringCatSheaf)
        (Nat.le_succ n))))).trans ?_
  refine (restrictIdealPowerSheafIso_hom_ι f I (n + 1)).symm.trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) (idealPowerMultipleMap_comp_ι (I.comap f)
    (SheafOfModules.unit Y.ringCatSheaf) (Nat.le_succ n)).symm

/-- `AlgebraicGeometry.restrictSheafTensorIso_inv_idealPowerTensorMulAmbient`, solved for the
restriction of the multiplication map. -/
public lemma restrict_idealPowerTensorMulAmbient (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor f).map (idealPowerTensorMulAmbient I n M) =
      (restrictSheafTensorIso f M (idealPowerSheaf I n)).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
          ((Scheme.Modules.restrictFunctor f).obj M)).map (restrictIdealPowerSheafIso f I n).hom ≫
        idealPowerTensorMulAmbient (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M) :=
  (Iso.inv_comp_eq _).mp (restrictSheafTensorIso_inv_idealPowerTensorMulAmbient f I n M)

/-- Restriction of complexes of `𝒪_X`-modules along `f`, termwise, at the spelling
`Stacks.Duality.TensorComplex` of complexes at which the tensor product is stated. -/
public abbrev restrictTensorComplexFunctor :
    Stacks.Duality.TensorComplex X ⥤ Stacks.Duality.TensorComplex Y :=
  (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The identification `(A ⊗ M)|_Y ≅ A|_Y ⊗ N` obtained from `(A ⊗ M)|_Y ≅ A|_Y ⊗ M|_Y` and an
isomorphism `e : M|_Y ≅ N`. -/
public abbrev restrictSheafTensorWhiskerIso (A M : X.Modules) {N : Y.Modules}
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N) :
    (Scheme.Modules.restrictFunctor f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj M) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
        ((Scheme.Modules.restrictFunctor f).obj A)).obj N :=
  restrictSheafTensorIso f A M ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
      ((Scheme.Modules.restrictFunctor f).obj A)).mapIso e

/-- `AlgebraicGeometry.restrictSheafTensorWhiskerIso` is natural in the first variable. -/
public lemma restrictSheafTensorWhiskerIso_naturality_left {A A' : X.Modules} (u : A ⟶ A')
    (M : X.Modules) {N : Y.Modules} (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N) :
    (Scheme.Modules.restrictFunctor f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map u).app M) ≫
        (restrictSheafTensorWhiskerIso f A' M e).hom =
      (restrictSheafTensorWhiskerIso f A M e).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map
          ((Scheme.Modules.restrictFunctor f).map u)).app N :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (restrictSheafTensorIso_hom_naturality_left f u M)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg ((restrictSheafTensorIso f A M).hom ≫ ·)
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map
            ((Scheme.Modules.restrictFunctor f).map u)).naturality e.hom).symm).trans
          (Category.assoc _ _ _).symm)))

/-- `AlgebraicGeometry.restrictSheafTensorWhiskerIso` is natural in the second variable, for
morphisms compatible with the given isomorphisms. -/
public lemma restrictSheafTensorWhiskerIso_naturality_right (A : X.Modules) {M M' : X.Modules}
    (g : M ⟶ M') {N N' : Y.Modules} (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (e' : (Scheme.Modules.restrictFunctor f).obj M' ≅ N') (h : N ⟶ N')
    (hgh : (Scheme.Modules.restrictFunctor f).map g ≫ e'.hom = e.hom ≫ h) :
    (Scheme.Modules.restrictFunctor f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).map g) ≫
        (restrictSheafTensorWhiskerIso f A M' e').hom =
      (restrictSheafTensorWhiskerIso f A M e).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
          ((Scheme.Modules.restrictFunctor f).obj A)).map h := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
    ((Scheme.Modules.restrictFunctor f).obj A)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ T.map e'.hom) (restrictSheafTensorIso_hom_naturality_right f A g)).trans
      ((Category.assoc _ _ _).trans ((congrArg ((restrictSheafTensorIso f A M).hom ≫ ·)
        ((T.map_comp _ _).symm.trans ((congrArg T.map hgh).trans (T.map_comp _ _)))).trans
          (Category.assoc _ _ _).symm)))

/-- **Restriction of the termwise complex `p ↦ 𝓟^p ⊗ M`.** Given an isomorphism
`e : M|_Y ≅ N`, the restriction of the complex `p ↦ 𝓟^p ⊗ M` is the complex
`p ↦ 𝓟^p|_Y ⊗ N`, termwise by `AlgebraicGeometry.restrictSheafTensorWhiskerIso`. -/
public def restrictRowComplexIso (P : Stacks.Duality.TensorComplex X) (M : X.Modules)
    {N : Y.Modules} (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N) :
    (restrictTensorComplexFunctor f).obj
        (CochainComplex.KFlatBifunctor.rowComplex
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) P M) ≅
      CochainComplex.KFlatBifunctor.rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
        ((restrictTensorComplexFunctor f).obj P) N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => restrictSheafTensorWhiskerIso f (P.X p) M e)
    (fun p q _ => (restrictSheafTensorWhiskerIso_naturality_left f (P.d p q) M e).symm)

/-- The components of `AlgebraicGeometry.restrictRowComplexIso`. -/
public lemma restrictRowComplexIso_hom_f (P : Stacks.Duality.TensorComplex X) (M : X.Modules)
    {N : Y.Modules} (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N) (p : ℤ) :
    (restrictRowComplexIso f P M e).hom.f p = (restrictSheafTensorWhiskerIso f (P.X p) M e).hom :=
  rfl

/-- `AlgebraicGeometry.restrictRowComplexIso` is natural in the complex. -/
public lemma restrictRowComplexIso_naturality_left {P Q : Stacks.Duality.TensorComplex X}
    (π : P ⟶ Q) (M : X.Modules) {N : Y.Modules}
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N) :
    (restrictTensorComplexFunctor f).map (CochainComplex.KFlatBifunctor.rowComplexMap
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) π M) ≫
        (restrictRowComplexIso f Q M e).hom =
      (restrictRowComplexIso f P M e).hom ≫ CochainComplex.KFlatBifunctor.rowComplexMap
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
        ((restrictTensorComplexFunctor f).map π) N := by
  ext p : 1
  exact restrictSheafTensorWhiskerIso_naturality_left f (π.f p) M e

/-- `AlgebraicGeometry.restrictRowComplexIso` is natural in the module, for morphisms compatible
with the given isomorphisms. -/
public lemma restrictRowComplexIso_naturality_right (P : Stacks.Duality.TensorComplex X)
    {M M' : X.Modules} (g : M ⟶ M') {N N' : Y.Modules}
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (e' : (Scheme.Modules.restrictFunctor f).obj M' ≅ N') (h : N ⟶ N')
    (hgh : (Scheme.Modules.restrictFunctor f).map g ≫ e'.hom = e.hom ≫ h) :
    (restrictTensorComplexFunctor f).map (CochainComplex.KFlatBifunctor.rowComplexMapRight
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) P g) ≫
        (restrictRowComplexIso f P M' e').hom =
      (restrictRowComplexIso f P M e).hom ≫ CochainComplex.KFlatBifunctor.rowComplexMapRight
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
        ((restrictTensorComplexFunctor f).obj P) h := by
  ext p : 1
  exact restrictSheafTensorWhiskerIso_naturality_right f (P.X p) g e e' h hgh

/-! generic -/

section Generic

variable {Z : Scheme.{u}} (J : Z.IdealSheafData)

/-- The transition `Tot(𝓟^• ⊗ 𝓘^{n+1}[0]) ⟶ Tot(𝓟^• ⊗ 𝓘^n[0])` of
`AlgebraicGeometry.idealPowerResolutionSystem`, typed with the total tensor complexes as source and
target. -/
public abbrev idealPowerResolutionTransition (P : Stacks.Duality.TensorComplex Z) (n : ℕ) :
    Stacks.Duality.totalTensorComplex P (idealPowerSingle J (n + 1)) ⟶
      Stacks.Duality.totalTensorComplex P (idealPowerSingle J n) :=
  HomologicalComplex.mapBifunctorMap (𝟙 P) (idealPowerSingleTransition J n)
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) (ComplexShape.up ℤ)

/-- The map `Tot(𝓟^• ⊗ 𝓘^n[0]) ⟶ Tot(𝓠^• ⊗ 𝓘^n[0])` induced by a map of complexes
`𝓟^• ⟶ 𝓠^•`, typed with the total tensor complexes as source and target. -/
public abbrev idealPowerResolutionLeftMap {P Q : Stacks.Duality.TensorComplex Z} (π : P ⟶ Q)
    (n : ℕ) :
    Stacks.Duality.totalTensorComplex P (idealPowerSingle J n) ⟶
      Stacks.Duality.totalTensorComplex Q (idealPowerSingle J n) :=
  HomologicalComplex.mapBifunctorMap π (𝟙 (idealPowerSingle J n))
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) (ComplexShape.up ℤ)

/-- `Tot(𝓟^• ⊗ 𝓘^n[0]) ≅ (p ↦ 𝓟^p ⊗ 𝓘^n)`: the identification
`CochainComplex.KFlatBifunctor.totalSingleIso` of a total complex against an object in degree zero,
typed with the total tensor complex as source. -/
public abbrev idealPowerTotalSingleIso (P : Stacks.Duality.TensorComplex Z) (n : ℕ) :
    Stacks.Duality.totalTensorComplex P (idealPowerSingle J n) ≅
      CochainComplex.KFlatBifunctor.rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)
        P (idealPowerSheaf J n) :=
  CochainComplex.KFlatBifunctor.totalSingleIso
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) P (idealPowerSheaf J n)

/-- `AlgebraicGeometry.idealPowerTotalSingleIso` is compatible with the transitions. -/
private lemma idealPowerTotalSingleIso_hom_transition (P : Stacks.Duality.TensorComplex Z)
    (n : ℕ) :
    idealPowerResolutionTransition J P n ≫ (idealPowerTotalSingleIso J P n).hom =
      (idealPowerTotalSingleIso J P (n + 1)).hom ≫
        CochainComplex.KFlatBifunctor.rowComplexMapRight
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) P (idealPowerSheafTransition J n) :=
  CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) P (idealPowerSheafTransition J n)

/-- The inverse of `AlgebraicGeometry.idealPowerTotalSingleIso` is compatible with the
transitions. -/
private lemma idealPowerTotalSingleIso_inv_transition (P : Stacks.Duality.TensorComplex Z)
    (n : ℕ) :
    (idealPowerTotalSingleIso J P (n + 1)).inv ≫ idealPowerResolutionTransition J P n =
      CochainComplex.KFlatBifunctor.rowComplexMapRight
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) P (idealPowerSheafTransition J n) ≫
        (idealPowerTotalSingleIso J P n).inv :=
  (Iso.inv_comp_eq _).mpr (((Iso.eq_comp_inv _).mpr
    (idealPowerTotalSingleIso_hom_transition J P n)).trans (Category.assoc _ _ _))

/-- `AlgebraicGeometry.idealPowerTotalSingleIso` is natural in the complex. -/
private lemma idealPowerTotalSingleIso_hom_left {P Q : Stacks.Duality.TensorComplex Z}
    (π : P ⟶ Q) (n : ℕ) :
    idealPowerResolutionLeftMap J π n ≫ (idealPowerTotalSingleIso J Q n).hom =
      (idealPowerTotalSingleIso J P n).hom ≫
        CochainComplex.KFlatBifunctor.rowComplexMap
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) π (idealPowerSheaf J n) :=
  CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) π (idealPowerSheaf J n)

/-- `AlgebraicGeometry.idealPowerResolutionMap` through the termwise complex. -/
private lemma idealPowerResolutionMap_eq {F : CochainComplex Z.Modules ℤ}
    {P : Stacks.Duality.TensorComplex Z} (π : P ⟶ (show Stacks.Duality.TensorComplex Z from F))
    (n : ℕ) :
    idealPowerResolutionMap J n π = idealPowerResolutionLeftMap J π n ≫
      (idealPowerTotalSingleIso J (show Stacks.Duality.TensorComplex Z from F) n).hom ≫
        idealPowerRowMap J n F :=
  rfl

/-- The transition maps of `AlgebraicGeometry.idealPowerResolutionSystem`. -/
public lemma idealPowerResolutionSystem_map_succ (P : Stacks.Duality.TensorComplex Z) (n : ℕ) :
    (idealPowerResolutionSystem J P).map (homOfLE (Nat.le_succ n)).op =
      idealPowerResolutionTransition J P n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

end Generic

/-- The pasting of squares behind `restrictIdealPowerResolutionTermIso_transition`. -/
private lemma paste_transition {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {a₀ a₁ b₀ b₁ : C} {c₀ c₁ e₀ e₁ : D}
    {mb : a₁ ⟶ a₀} {t₀ : a₀ ⟶ b₀} {t₁ : a₁ ⟶ b₁} {rr : b₁ ⟶ b₀} {R₀ : G.obj b₀ ⟶ c₀}
    {R₁ : G.obj b₁ ⟶ c₁} {rr' : c₁ ⟶ c₀} {s₀ : c₀ ⟶ e₀} {s₁ : c₁ ⟶ e₁} {mb' : e₁ ⟶ e₀}
    (h1 : mb ≫ t₀ = t₁ ≫ rr) (h2 : G.map rr ≫ R₀ = R₁ ≫ rr') (h3 : s₁ ≫ mb' = rr' ≫ s₀) :
    G.map mb ≫ G.map t₀ ≫ R₀ ≫ s₀ = (G.map t₁ ≫ R₁ ≫ s₁) ≫ mb' := by
  rw [← G.map_comp_assoc, h1, G.map_comp_assoc, reassoc_of% h2]
  simp only [Category.assoc, h3]

/-- The pasting of squares behind `restrict_idealPowerResolutionMap`. -/
private lemma paste_component {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {a b c d k : C} {a' b' : D} {c' d' k' : D}
    {L : a ⟶ b} {tF : b ⟶ c} {μ : c ⟶ k} {tP : a ⟶ d} {rc : d ⟶ c} {C₀ : G.obj k ⟶ k'}
    {RP : G.obj d ⟶ d'} {RF : G.obj c ⟶ c'} {rc' : d' ⟶ c'} {μ' : c' ⟶ k'}
    {tP' : a' ≅ d'} {L' : a' ⟶ b'} {tF' : b' ⟶ c'}
    (hL : L ≫ tF = tP ≫ rc) (hL' : L' ≫ tF' = tP'.hom ≫ rc') (hR : G.map rc ≫ RF = RP ≫ rc')
    (hK : G.map μ ≫ C₀ = RF ≫ μ') :
    G.map (L ≫ tF ≫ μ) ≫ C₀ = (G.map tP ≫ RP ≫ tP'.inv) ≫ L' ≫ tF' ≫ μ' := by
  have hL₂ : G.map L ≫ G.map tF = G.map tP ≫ G.map rc := by
    rw [← G.map_comp, hL, G.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hL₂, hK, reassoc_of% hR, reassoc_of% hL', Iso.inv_hom_id_assoc]

/-- **The restriction of `Tot(𝓟^• ⊗ 𝓘^n[0])` is `Tot(𝓟^•|_Y ⊗ (𝓘|_Y)^n[0])`.** Both total
complexes are the termwise complexes `p ↦ 𝓟^p ⊗ 𝓘^n` and `p ↦ 𝓟^p|_Y ⊗ (𝓘|_Y)^n`
(`AlgebraicGeometry.idealPowerTotalSingleIso`), and the restriction of the first is the second
(`AlgebraicGeometry.restrictRowComplexIso`, with
`AlgebraicGeometry.restrictIdealPowerSheafIso`). -/
public def restrictIdealPowerResolutionTermIso (P : Stacks.Duality.TensorComplex X) (n : ℕ) :
    (restrictTensorComplexFunctor f).obj
        (Stacks.Duality.totalTensorComplex P (idealPowerSingle I n)) ≅
      Stacks.Duality.totalTensorComplex ((restrictTensorComplexFunctor f).obj P)
        (idealPowerSingle (I.comap f) n) :=
  (restrictTensorComplexFunctor f).mapIso (idealPowerTotalSingleIso I P n) ≪≫
    restrictRowComplexIso f P (idealPowerSheaf I n) (restrictIdealPowerSheafIso f I n) ≪≫
    (idealPowerTotalSingleIso (I.comap f) ((restrictTensorComplexFunctor f).obj P) n).symm

/-- `AlgebraicGeometry.restrictIdealPowerResolutionTermIso` is compatible with the transitions. -/
public lemma restrictIdealPowerResolutionTermIso_transition (P : Stacks.Duality.TensorComplex X)
    (n : ℕ) :
    (restrictTensorComplexFunctor f).map (idealPowerResolutionTransition I P n) ≫
        (restrictIdealPowerResolutionTermIso f I P n).hom =
      (restrictIdealPowerResolutionTermIso f I P (n + 1)).hom ≫
        idealPowerResolutionTransition (I.comap f) ((restrictTensorComplexFunctor f).obj P) n :=
  paste_transition (restrictTensorComplexFunctor f) (idealPowerTotalSingleIso_hom_transition I P n)
    (restrictRowComplexIso_naturality_right f P (idealPowerSheafTransition I n)
      (restrictIdealPowerSheafIso f I (n + 1)) (restrictIdealPowerSheafIso f I n)
      (idealPowerSheafTransition (I.comap f) n) (restrictIdealPowerSheafIso_transition f I n))
    (idealPowerTotalSingleIso_inv_transition (I.comap f) ((restrictTensorComplexFunctor f).obj P) n)

/-- **The restriction of the inverse system `(Tot(𝓟^• ⊗ 𝓘^n[0]))_n` is the system
`(Tot(𝓟^•|_Y ⊗ (𝓘|_Y)^n[0]))_n`**, with components
`AlgebraicGeometry.restrictIdealPowerResolutionTermIso`. -/
public def restrictIdealPowerResolutionSystemIso (P : Stacks.Duality.TensorComplex X) :
    idealPowerResolutionSystem I P ⋙ restrictTensorComplexFunctor f ≅
      idealPowerResolutionSystem (I.comap f) ((restrictTensorComplexFunctor f).obj P) :=
  let α : idealPowerResolutionSystem I P ⋙ restrictTensorComplexFunctor f ⟶
      idealPowerResolutionSystem (I.comap f) ((restrictTensorComplexFunctor f).obj P) :=
    NatTrans.ofOpSequence (fun n => (restrictIdealPowerResolutionTermIso f I P n).hom)
      (fun n => (congrArg (fun g => (restrictTensorComplexFunctor f).map g ≫
          (restrictIdealPowerResolutionTermIso f I P n).hom)
          (idealPowerResolutionSystem_map_succ I P n)).trans
        ((restrictIdealPowerResolutionTermIso_transition f I P n).trans
          (congrArg ((restrictIdealPowerResolutionTermIso f I P (n + 1)).hom ≫ ·)
            (idealPowerResolutionSystem_map_succ (I.comap f)
              ((restrictTensorComplexFunctor f).obj P) n).symm)))
  haveI : ∀ n, IsIso (α.app n) := fun n =>
    (restrictIdealPowerResolutionTermIso f I P n.unop).isIso_hom
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  asIso α

/-- The components of `AlgebraicGeometry.restrictIdealPowerResolutionSystemIso`. -/
public lemma restrictIdealPowerResolutionSystemIso_hom_app (P : Stacks.Duality.TensorComplex X)
    (n : ℕ) :
    (restrictIdealPowerResolutionSystemIso f I P).hom.app (op n) =
      (restrictIdealPowerResolutionTermIso f I P n).hom :=
  NatTrans.ofOpSequence_app (F := idealPowerResolutionSystem I P ⋙ restrictTensorComplexFunctor f)
    (G := idealPowerResolutionSystem (I.comap f) ((restrictTensorComplexFunctor f).obj P))
    (fun n => (restrictIdealPowerResolutionTermIso f I P n).hom)
    (fun _ => (restrictIdealPowerResolutionSystemIso f I P).hom.naturality _) (op n)

/-- **The restriction of the inverse system `(𝓘^n 𝓕^•)_n` is the system
`((𝓘|_Y)^n (𝓕^•|_Y))_n`**, for a complex `𝓕^•` with quasi-coherent terms. This is
`AlgebraicGeometry.restrictIdealPowerSystemIso`, stated at the spelling of the target of
`AlgebraicGeometry.idealPowerResolutionNatTrans`. -/
public def restrictIdealPowerTensorComplexSystemIso (F : CochainComplex X.Modules ℤ)
    (hF : ∀ i, (F.X i).IsQuasicoherent) :
    Functor.ofOpSequence (fun n => idealPowerTensorComplexTransition I n F) ⋙
        restrictTensorComplexFunctor f ≅
      Functor.ofOpSequence
        (fun n => idealPowerTensorComplexTransition (I.comap f) n (restrictComplex f F)) :=
  restrictIdealPowerSystemIso f I (idealPowerComplexSystem I F) hF

/-- The components of `AlgebraicGeometry.restrictIdealPowerTensorComplexSystemIso`. -/
public lemma restrictIdealPowerTensorComplexSystemIso_hom_app (F : CochainComplex X.Modules ℤ)
    (hF : ∀ i, (F.X i).IsQuasicoherent) (n : ℕ) :
    (restrictIdealPowerTensorComplexSystemIso f I F hF).hom.app (op n) =
      (restrictIdealPowerComplexIso f I (idealPowerComplexSystem I F) hF n).hom :=
  NatTrans.ofOpSequence_app
    (F := Functor.ofOpSequence (idealPowerComplexSystem I F).transition ⋙
      (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ))
    (G := Functor.ofOpSequence
      (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).transition)
    (fun n => (restrictIdealPowerComplexIso f I (idealPowerComplexSystem I F) hF n).hom)
    (fun _ => (restrictIdealPowerTensorComplexSystemIso f I F hF).hom.naturality _) (op n)

/-- The termwise multiplication maps `𝓕^p ⊗ 𝓘^n ⟶ 𝓘^n 𝓕^p` commute with restriction. -/
public lemma restrict_idealPowerRowMap (F : CochainComplex X.Modules ℤ)
    (hF : ∀ i, (F.X i).IsQuasicoherent) (n : ℕ) :
    (restrictTensorComplexFunctor f).map (idealPowerRowMap I n F) ≫
        (restrictIdealPowerComplexIso f I (idealPowerComplexSystem I F) hF n).hom =
      (restrictRowComplexIso f (show Stacks.Duality.TensorComplex X from F) (idealPowerSheaf I n)
          (restrictIdealPowerSheafIso f I n)).hom ≫
        idealPowerRowMap (I.comap f) n (restrictComplex f F) := by
  ext p : 1
  refine cancel_idealPowerComplexSystem_inclusion (I.comap f) n p _ _ ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (restrictIdealPowerTermIso_hom_comp_inclusion f I
    (idealPowerComplexSystem I F) hF n p)).trans ?_
  refine ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm.trans ?_
  refine (congrArg (Scheme.Modules.restrictFunctor f).map
    (idealPowerRowMap_inclusion_f I n F p)).trans ?_
  refine (restrict_idealPowerTensorMulAmbient f I n (F.X p)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (_ ≫ ·) (idealPowerRowMap_inclusion_f (I.comap f) n (restrictComplex f F) p).symm

/-- The restriction `𝓟^•|_Y ⟶ 𝓕^•|_Y` of a map of complexes `π : 𝓟^• ⟶ 𝓕^•`, typed with the
restricted complex `AlgebraicGeometry.restrictComplex f 𝓕^•` as target. -/
public abbrev restrictResolution {F : CochainComplex X.Modules ℤ}
    {P : Stacks.Duality.TensorComplex X} (π : P ⟶ (show Stacks.Duality.TensorComplex X from F)) :
    (restrictTensorComplexFunctor f).obj P ⟶
      (show Stacks.Duality.TensorComplex Y from restrictComplex f F) :=
  (restrictTensorComplexFunctor f).map π

/-- `AlgebraicGeometry.restrictRowComplexIso_naturality_left` for a map `π : 𝓟^• ⟶ 𝓕^•`, with
the restricted map typed as `AlgebraicGeometry.restrictResolution f π`. -/
public lemma restrictRowComplexIso_naturality_resolution {F : CochainComplex X.Modules ℤ}
    {P : Stacks.Duality.TensorComplex X} (π : P ⟶ (show Stacks.Duality.TensorComplex X from F))
    (n : ℕ) :
    (restrictTensorComplexFunctor f).map (CochainComplex.KFlatBifunctor.rowComplexMap
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) π (idealPowerSheaf I n)) ≫
        (restrictRowComplexIso f (show Stacks.Duality.TensorComplex X from F)
          (idealPowerSheaf I n) (restrictIdealPowerSheafIso f I n)).hom =
      (restrictRowComplexIso f P (idealPowerSheaf I n) (restrictIdealPowerSheafIso f I n)).hom ≫
        CochainComplex.KFlatBifunctor.rowComplexMap
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (restrictResolution f π)
          (idealPowerSheaf (I.comap f) n) :=
  restrictRowComplexIso_naturality_left f π (idealPowerSheaf I n)
    (restrictIdealPowerSheafIso f I n)

/-- **The comparison map on a resolution commutes with restriction**, componentwise: under the
identifications `AlgebraicGeometry.restrictIdealPowerResolutionTermIso` and
`AlgebraicGeometry.restrictIdealPowerComplexIso`, the restriction of
`Tot(𝓟^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•` is `Tot(𝓟^•|_Y ⊗ (𝓘|_Y)^n[0]) ⟶ (𝓘|_Y)^n (𝓕^•|_Y)`. -/
public lemma restrict_idealPowerResolutionMap {F : CochainComplex X.Modules ℤ}
    (hF : ∀ i, (F.X i).IsQuasicoherent) {P : Stacks.Duality.TensorComplex X}
    (π : P ⟶ (show Stacks.Duality.TensorComplex X from F)) (n : ℕ) :
    (restrictTensorComplexFunctor f).map (idealPowerResolutionMap I n π) ≫
        (restrictIdealPowerComplexIso f I (idealPowerComplexSystem I F) hF n).hom =
      (restrictIdealPowerResolutionTermIso f I P n).hom ≫
        idealPowerResolutionMap (I.comap f) n (restrictResolution f π) := by
  rw [idealPowerResolutionMap_eq, idealPowerResolutionMap_eq]
  exact paste_component (restrictTensorComplexFunctor f) (idealPowerTotalSingleIso_hom_left I π n)
    (idealPowerTotalSingleIso_hom_left (I.comap f) (restrictResolution f π) n)
    (restrictRowComplexIso_naturality_resolution f I π n) (restrict_idealPowerRowMap f I F hF n)

/-- **The comparison on a resolution is compatible with restriction to an open.** For an open
immersion `f : Y ⟶ X`, a complex `𝓕^•` with quasi-coherent terms and a map `π : 𝓟^• ⟶ 𝓕^•`, the
restriction of the map of inverse systems `(Tot(𝓟^• ⊗ 𝓘^n[0]))_n ⟶ (𝓘^n 𝓕^•)_n` of
`AlgebraicGeometry.idealPowerResolutionNatTrans` is, under the identifications
`AlgebraicGeometry.restrictIdealPowerResolutionSystemIso` and
`AlgebraicGeometry.restrictIdealPowerTensorComplexSystemIso`, the map of inverse systems attached
to `𝓘|_Y` and `π|_Y : 𝓟^•|_Y ⟶ 𝓕^•|_Y`. -/
public lemma idealPowerResolutionNatTrans_restrict {F : CochainComplex X.Modules ℤ}
    (hF : ∀ i, (F.X i).IsQuasicoherent) {P : Stacks.Duality.TensorComplex X}
    (π : P ⟶ (show Stacks.Duality.TensorComplex X from F)) :
    Functor.whiskerRight (idealPowerResolutionNatTrans I π) (restrictTensorComplexFunctor f) ≫
        (restrictIdealPowerTensorComplexSystemIso f I F hF).hom =
      (restrictIdealPowerResolutionSystemIso f I P).hom ≫
        idealPowerResolutionNatTrans (I.comap f) (restrictResolution f π) := by
  refine NatTrans.ext (funext fun n => ?_)
  obtain ⟨n⟩ := n
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app,
    idealPowerResolutionNatTrans_app, idealPowerResolutionNatTrans_app,
    restrictIdealPowerTensorComplexSystemIso_hom_app, restrictIdealPowerResolutionSystemIso_hom_app]
  exact restrict_idealPowerResolutionMap f I hF π n

/-- **The restriction of a K-flat complex to an open is K-flat** ([Stacks, Tag 06YC]):
restriction along an open immersion is pullback (`Scheme.Modules.restrictFunctorIsoPullback`),
and the termwise pullback of a K-flat complex is K-flat
(`Stacks.Duality.kFlatComplex_pullbackComplex`). -/
public lemma kFlatComplex_restrict {P : Stacks.Duality.TensorComplex X}
    (hP : Stacks.Duality.KFlatComplex P) :
    Stacks.Duality.KFlatComplex ((restrictTensorComplexFunctor f).obj P) :=
  CochainComplex.KFlatBifunctor.KFlat.of_iso _ (Stacks.Duality.kFlatComplex_pullbackComplex f hP)
    ((NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback f)
      (ComplexShape.up ℤ)).app P).symm

end AlgebraicGeometry
