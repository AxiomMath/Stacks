module

public import StacksFrontier.Deformation.Applications.TwoFibreProductDeformation
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Morphism
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensor
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace

/-!
# Tools for the six-term exact sequence of a 2-fibre product

Three universe-general tools that part (2) of Tag 06L5 needs and that the library does not
otherwise provide.  **Nothing here carries a tag**: the six-term exact sequence itself is not
in this file.

## Main results

* `Deformation.isLinearMap_of_natural_at`: a natural family of maps between the values of two
  linear functors on finitely generated modules is linear at every module.  This is
  `Deformation.isLinearMap_of_natural_on_fgModules` with the rank-one module `R` replaced by
  an arbitrary module and with the universe of the modules independent of the universe of the
  ring.
* `Deformation.squareZeroCross`: the square-zero extension by a finite-dimensional vector
  space, read as an algebra under an object `A` of `𝒞_Λ`, compared with the square-zero
  extension read directly in `𝒞_Λ`.  The two have the same carrier; the comparison is the
  identity on it, is an isomorphism, and is natural in the coordinate module.
* `Deformation.cocartesianCompare`: two strongly cocartesian lifts of the same arrow of the
  base out of the same object have canonically isomorphic codomains.

## Implementation notes

`Deformation.isLinearMap_of_natural_at` is the form in which linearity transfers between the
two canonical linear lifts a six-term sequence compares: the lift
`Deformation.infinitesimalAutomorphismLinearLift` of the infinitesimal-automorphism coordinate
functor and the lift `Deformation.associatedTangentSpaceModuleStructure` of the associated
square-zero functor.  Both are `Deformation.linearFunctorLiftOfProductConditions`, hence
`Deformation.fgModuleCatLinearFunctorLift`, on `FGModuleCat.{max v w} k` with rank-one module
`FGModuleCat.of k (ULift.{v} k)`; but they take values in different type universes, so Tag
06I7 (`Deformation.fgModuleCat_linearFunctorLift_natTrans`), which requires one common value
universe, does not apply, while this statement does.
-/

@[expose] public section

namespace Deformation

/-! ### Linearity from naturality, at an arbitrary module -/

section Linearity
open CategoryTheory
universe uR vM z₁ z₂

/-- A natural family of maps between the values of two linear functors on finitely generated
modules is linear at every module.

This is `Deformation.isLinearMap_of_natural_on_fgModules` with the rank-one module `R` replaced
by an arbitrary module and with the universe of the modules independent of the universe of the
ring; the six-term sequence needs it at the universe-lifted rank-one module
`FGModuleCat.of k (ULift k)`, which is the rank-one module of both linear lifts involved. -/
public theorem isLinearMap_of_natural_at
    (R : Type uR) [CommRing R]
    (F : FGModuleCat.{vM} R ⥤ ModuleCat.{z₁} R)
    (G : FGModuleCat.{vM} R ⥤ ModuleCat.{z₂} R)
    [F.Additive] [G.Additive] [F.Linear R] [G.Linear R]
    (t : ∀ X, F.obj X → G.obj X)
    (ht : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), t Y ((F.map f) x) = (G.map f) (t X x))
    (A : FGModuleCat.{vM} R) :
    IsLinearMap R (t A) := by
  let B : FGModuleCat.{vM} R := FGModuleCat.of R (↥A × ↥A)
  let p₁ : B ⟶ A := FGModuleCat.ofHom (LinearMap.fst R ↥A ↥A)
  let p₂ : B ⟶ A := FGModuleCat.ofHom (LinearMap.snd R ↥A ↥A)
  let i₁ : A ⟶ B := FGModuleCat.ofHom (LinearMap.inl R ↥A ↥A)
  let i₂ : A ⟶ B := FGModuleCat.ofHom (LinearMap.inr R ↥A ↥A)
  have hp₁i₁ : i₁ ≫ p₁ = 𝟙 A := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have hp₂i₂ : i₂ ≫ p₂ = 𝟙 A := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have hp₁i₂ : i₂ ≫ p₁ = 0 := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have hp₂i₁ : i₁ ≫ p₂ = 0 := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  constructor
  · intro x y
    let z : F.obj B := (F.map i₁) x + (F.map i₂) y
    have hF : ∀ {X Y W} (f : X ⟶ Y) (g : Y ⟶ W) (v : F.obj X),
        (F.map g) ((F.map f) v) = (F.map (f ≫ g)) v := fun f g v => by simp
    have hF₁ : (F.map p₁) z = x := by
      simp only [z, map_add, hF, hp₁i₁, hp₁i₂, F.map_id, F.map_zero]; simp
    have hF₂ : (F.map p₂) z = y := by
      simp only [z, map_add, hF, hp₂i₁, hp₂i₂, F.map_id, F.map_zero]; simp
    have hFadd : (F.map (p₁ + p₂)) z = x + y := by
      rw [F.map_add]
      change (F.map p₁) z + (F.map p₂) z = x + y
      rw [hF₁, hF₂]
    have hGadd (b : G.obj B) : (G.map (p₁ + p₂)) b = (G.map p₁) b + (G.map p₂) b := by
      rw [G.map_add]
      rfl
    calc
      _ = t A ((F.map (p₁ + p₂)) z) := by rw [hFadd]
      _ = (G.map (p₁ + p₂)) (t B z) := ht (p₁ + p₂) z
      _ = (G.map p₁) (t B z) + (G.map p₂) (t B z) := hGadd _
      _ = t A x + t A y := by rw [← ht p₁ z, ← ht p₂ z, hF₁, hF₂]
  · intro r x
    let f : A ⟶ A := r • (𝟙 A)
    simpa [f] using ht f x

end Linearity

/-! ### Square-zero extensions read over two different bases -/

section Crossing
open CategoryTheory IsLocalRing
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The square-zero extension by `M`, read as an algebra under `A`, compared with the
square-zero extension by `M` read directly in `𝒞_Λ`: the two have the same carrier, and the
comparison is the identity on it. -/
public noncomputable def squareZeroCross (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) :
    ((squareZeroAlgFunctor.{u, v, w} A).obj M).right ⟶
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M :=
  homOfRingHom (RingHom.id _)
    (fun t => congrArg TrivSqZeroExt.inl (A.residueEquiv.commutes t))
    (fun _ => rfl)

/-- The comparison `Deformation.squareZeroCross` is the identity on the common carrier. -/
public theorem squareZeroCross_hom (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) (a : ↥((squareZeroAlgFunctor.{u, v, w} A).obj M).right) :
    (squareZeroCross.{u, v, w} A M).hom a = a := rfl

/-- The comparison `Deformation.squareZeroCross` is an isomorphism. -/
public theorem isIso_squareZeroCross (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) : IsIso (squareZeroCross.{u, v, w} A M) :=
  ArtinianLocalAlgCat.isIso_of_bijective_hom _ Function.bijective_id

/-- The comparison is natural in the coordinate module. -/
public theorem squareZeroCross_naturality (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {M N : FGModuleCat.{max v w} k} (g : M ⟶ N) :
    ((squareZeroAlgFunctor.{u, v, w} A).map g).right ≫ squareZeroCross.{u, v, w} A N =
      squareZeroCross.{u, v, w} A M ≫ (squareZeroExtensionArtinian.{u, w, max v w} Λ k).map g :=
  ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

end Crossing

/-! ### Comparison of two cocartesian lifts of one arrow -/

section Cocartesian
open CategoryTheory CategoryTheory.Functor
universe u₁ v₁ u₂ v₂

/-- Two strongly cocartesian lifts of the same arrow of the base out of the same object have
canonically isomorphic codomains, by the universal property in both directions. -/
public noncomputable def cocartesianCompare {F : Type u₁} [Category.{v₁} F]
    {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C) {x b b' : F} {A B : C} (a : A ⟶ B)
    (u : x ⟶ b) (u' : x ⟶ b')
    [p.IsStronglyCocartesian a u] [p.IsStronglyCocartesian a u'] : b ≅ b' where
  hom := IsStronglyCocartesian.map p a u (Category.comp_id a).symm u'
  inv := IsStronglyCocartesian.map p a u' (Category.comp_id a).symm u
  hom_inv_id := by
    have : p.IsHomLift (𝟙 B)
        (IsStronglyCocartesian.map p a u (Category.comp_id a).symm u' ≫
          IsStronglyCocartesian.map p a u' (Category.comp_id a).symm u) := by
      simpa using IsHomLift.comp p (𝟙 B) (𝟙 B)
        (IsStronglyCocartesian.map p a u (Category.comp_id a).symm u')
        (IsStronglyCocartesian.map p a u' (Category.comp_id a).symm u)
    have : p.IsHomLift (𝟙 B) (𝟙 b) :=
      IsHomLift.id (IsHomLift.codomain_eq p a u)
    refine IsStronglyCocartesian.ext p a u (𝟙 B) ?_
    rw [← Category.assoc, IsStronglyCocartesian.fac, IsStronglyCocartesian.fac,
      Category.comp_id]
  inv_hom_id := by
    have : p.IsHomLift (𝟙 B)
        (IsStronglyCocartesian.map p a u' (Category.comp_id a).symm u ≫
          IsStronglyCocartesian.map p a u (Category.comp_id a).symm u') := by
      simpa using IsHomLift.comp p (𝟙 B) (𝟙 B)
        (IsStronglyCocartesian.map p a u' (Category.comp_id a).symm u)
        (IsStronglyCocartesian.map p a u (Category.comp_id a).symm u')
    have : p.IsHomLift (𝟙 B) (𝟙 b') :=
      IsHomLift.id (IsHomLift.codomain_eq p a u')
    refine IsStronglyCocartesian.ext p a u' (𝟙 B) ?_
    rw [← Category.assoc, IsStronglyCocartesian.fac, IsStronglyCocartesian.fac,
      Category.comp_id]

/-- The comparison `Deformation.cocartesianCompare` lies over the identity of the base. -/
public instance isHomLift_cocartesianCompare_hom {F : Type u₁} [Category.{v₁} F]
    {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C) {x b b' : F} {A B : C} (a : A ⟶ B)
    (u : x ⟶ b) (u' : x ⟶ b')
    [p.IsStronglyCocartesian a u] [p.IsStronglyCocartesian a u'] :
    p.IsHomLift (𝟙 B) (cocartesianCompare p a u u').hom := by
  dsimp [cocartesianCompare]
  infer_instance

/-- The inverse of the comparison `Deformation.cocartesianCompare` lies over the identity of
the base. -/
public instance isHomLift_cocartesianCompare_inv {F : Type u₁} [Category.{v₁} F]
    {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C) {x b b' : F} {A B : C} (a : A ⟶ B)
    (u : x ⟶ b) (u' : x ⟶ b')
    [p.IsStronglyCocartesian a u] [p.IsStronglyCocartesian a u'] :
    p.IsHomLift (𝟙 B) (cocartesianCompare p a u u').inv := by
  dsimp [cocartesianCompare]
  infer_instance

/-- The comparison `Deformation.cocartesianCompare` carries the first lift `u` to the second
lift `u'`. -/
@[reassoc]
public theorem comp_cocartesianCompare_hom {F : Type u₁} [Category.{v₁} F]
    {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C) {x b b' : F} {A B : C} (a : A ⟶ B)
    (u : x ⟶ b) (u' : x ⟶ b')
    [p.IsStronglyCocartesian a u] [p.IsStronglyCocartesian a u'] :
    u ≫ (cocartesianCompare p a u u').hom = u' :=
  IsStronglyCocartesian.fac p a u (Category.comp_id a).symm u'

/-- The inverse of the comparison `Deformation.cocartesianCompare` carries the second lift `u'`
to the first lift `u`. -/
@[reassoc]
public theorem comp_cocartesianCompare_inv {F : Type u₁} [Category.{v₁} F]
    {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C) {x b b' : F} {A B : C} (a : A ⟶ B)
    (u : x ⟶ b) (u' : x ⟶ b')
    [p.IsStronglyCocartesian a u] [p.IsStronglyCocartesian a u'] :
    u' ≫ (cocartesianCompare p a u u').inv = u :=
  IsStronglyCocartesian.fac p a u' (Category.comp_id a).symm u

end Cocartesian

end Deformation

