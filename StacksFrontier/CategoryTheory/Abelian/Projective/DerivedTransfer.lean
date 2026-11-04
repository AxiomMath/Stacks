module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import StacksFrontier.CategoryTheory.Abelian.Projective.ResolutionLift

/-!
# Transferring a left derived functor along a resolution of the target

Let `G : A ⥤ T` be an additive functor out of an abelian category with projective resolutions,
let `X Y : A`, and let `t : X ⟶ Y`. A left derived functor `Lₙ G` is computed from a *projective*
resolution of its argument, but the morphism `t` need not be lifted into a projective resolution
of `Y`: by `CategoryTheory.ProjectiveResolution.lift'` it lifts into *any* resolution
`ε : K ⟶ Y[0]`, and by `CategoryTheory.ProjectiveResolution.liftHomotopy'` the lift is unique up
to homotopy, hence unique after `G` and homology.

This file packages that observation as `CategoryTheory.ProjectiveResolution.transferHomology`: a
morphism `(Lₙ G).obj X ⟶ Hₙ(L)` built from a resolution `ε : K ⟶ Y[0]` of `Y` and a chain map
`Θ : G(K) ⟶ L`. The point of the construction is `transferHomology_eq`, which says that *any*
chain map `R.complex ⟶ K` compatible with the augmentations computes it; this is what makes the
functoriality laws of such a transfer provable, since each of them exhibits a different
convenient lift.

The situation arises whenever a left derived functor on one abelian category is compared with a
left derived functor on another: the image of a projective resolution under an exact functor is a
resolution, but not a projective one. See
`CategoryTheory.Functor.mapAugmentation`.

## Main definitions

* `CategoryTheory.ProjectiveResolution.transferHomology`: the morphism
  `(Lₙ G).obj X ⟶ Hₙ(L)` determined by `t : X ⟶ Y`, a resolution `ε : K ⟶ Y[0]` and a chain map
  `Θ : G(K) ⟶ L`.

## Main results

* `CategoryTheory.ProjectiveResolution.transferHomology_eq`: any augmentation-compatible chain
  map into `K` computes `transferHomology`.
* `CategoryTheory.ProjectiveResolution.comp_single₀_map_eq_of_f_zero`: the compatibility
  hypothesis of `transferHomology_eq` may be checked in degree zero.

## Implementation notes

The target of `transferHomology` is spelled `(HomologicalComplex.homologyFunctor T c n).obj L`
rather than the equal `L.homology n`, and its second factor is
`(HomologicalComplex.homologyFunctor T c n).map _` rather than
`HomologicalComplex.homologyMap _ n`. That is the spelling in which Mathlib states
`CategoryTheory.ProjectiveResolution.isoLeftDerivedObj`, which the construction composes with;
with the other spelling the resulting composite is not type-correct at `implicit` transparency
and even `Category.assoc` fails to rewrite in it.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u vT uT

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] {T : Type uT} [Category.{vT} T] [Abelian T]

/-- Precomposing an augmented complex with a chain map and then applying an additive functor is
applying the functor to the composite augmentation. -/
lemma map_comp_mapAugmentation (W : A ⥤ T) [W.Additive] {Q₀ Q : ChainComplex A ℕ} {Z : A}
    (χ : Q₀ ⟶ Q) (ε : Q ⟶ (ChainComplex.single₀ A).obj Z) :
    (W.mapHomologicalComplex (ComplexShape.down ℕ)).map χ ≫ W.mapAugmentation ε =
      W.mapAugmentation (χ ≫ ε) := by
  simp [mapAugmentation]

/-- Postcomposing an augmentation with a morphism of the objects resolved commutes with applying
an additive functor. -/
lemma mapAugmentation_comp_single₀_map (W : A ⥤ T) [W.Additive] {Q : ChainComplex A ℕ} {Y Z : A}
    (ε : Q ⟶ (ChainComplex.single₀ A).obj Y) (t : Y ⟶ Z) :
    W.mapAugmentation (ε ≫ (ChainComplex.single₀ A).map t) =
      W.mapAugmentation ε ≫ (ChainComplex.single₀ T).map (W.map t) := by
  rw [mapAugmentation, mapAugmentation,
    (W.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp, assoc, assoc]
  exact congrArg (fun m => (W.mapHomologicalComplex (ComplexShape.down ℕ)).map ε ≫ m)
    ((HomologicalComplex.singleMapHomologicalComplex W (ComplexShape.down ℕ) 0).hom.naturality t)

end CategoryTheory.Functor

namespace CategoryTheory.ProjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A] {T : Type uT} [Category.{vT} T] [Abelian T]

/-- A morphism into a complex concentrated in degree zero is determined by its degree-zero
component, so the compatibility of a chain map `φ : R.complex ⟶ K` with the augmentations of `R`
and of `K` may be checked in degree zero. -/
lemma comp_single₀_map_eq_of_f_zero {X Y : A} (R : ProjectiveResolution X)
    {K : ChainComplex A ℕ} (ε : K ⟶ (ChainComplex.single₀ A).obj Y) (φ : R.complex ⟶ K)
    (t : X ⟶ Y) (h : φ.f 0 ≫ ε.f 0 = R.π.f 0 ≫ t) :
    φ ≫ ε = R.π ≫ (ChainComplex.single₀ A).map t := by
  ext
  simpa using h

variable [HasProjectiveResolutions A]

/-- Given an additive functor `G : A ⥤ T`, a morphism `t : X ⟶ Y` in `A`, a resolution
`ε : K ⟶ Y[0]` of `Y` which need not be projective, and a chain map `Θ : G(K) ⟶ L`, this is the
induced morphism `(Lₙ G).obj X ⟶ Hₙ(L)`: lift `t` to a chain map from a projective resolution of
`X` into `K`, apply `G`, compose with `Θ`, and take homology. -/
def transferHomology (G : A ⥤ T) [G.Additive] {X Y : A} (R : ProjectiveResolution X)
    {K : ChainComplex A ℕ} (ε : K ⟶ (ChainComplex.single₀ A).obj Y) [QuasiIso ε] (t : X ⟶ Y)
    {L : ChainComplex T ℕ} (Θ : (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶ L)
    (n : ℕ) :
    (G.leftDerived n).obj X ⟶
      (HomologicalComplex.homologyFunctor T (ComplexShape.down ℕ) n).obj L :=
  (R.isoLeftDerivedObj G n).hom ≫
    (HomologicalComplex.homologyFunctor T (ComplexShape.down ℕ) n).map
      ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map (lift' t R ε) ≫ Θ)

/-- `CategoryTheory.ProjectiveResolution.transferHomology` is computed by *any* chain map
`φ : R.complex ⟶ K` which is compatible with the augmentations, not only by the chosen lift: two
such chain maps are homotopic by `CategoryTheory.ProjectiveResolution.liftHomotopy'`, hence induce
the same map on the homology of their images under `G`. -/
theorem transferHomology_eq (G : A ⥤ T) [G.Additive] {X Y : A} (R : ProjectiveResolution X)
    {K : ChainComplex A ℕ} (ε : K ⟶ (ChainComplex.single₀ A).obj Y) [QuasiIso ε] (t : X ⟶ Y)
    {L : ChainComplex T ℕ} (Θ : (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶ L)
    (n : ℕ) (φ : R.complex ⟶ K) (hφ : φ ≫ ε = R.π ≫ (ChainComplex.single₀ A).map t) :
    transferHomology G R ε t Θ n =
      (R.isoLeftDerivedObj G n).hom ≫
        (HomologicalComplex.homologyFunctor T (ComplexShape.down ℕ) n).map
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map φ ≫ Θ) := by
  dsimp only [transferHomology]
  rw [Functor.map_comp, Functor.map_comp]
  congr 2
  exact homologyMap_map_eq_of_comp_eq ε G (lift' t R ε) φ (by rw [lift'_commutes, hφ]) n

end CategoryTheory.ProjectiveResolution

end
