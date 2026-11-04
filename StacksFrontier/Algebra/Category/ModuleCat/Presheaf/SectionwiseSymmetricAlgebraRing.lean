module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras

/-!
# The sectionwise symmetric algebra of a presheaf of modules, as a presheaf of rings

Let `O` be a presheaf of commutative rings on a category `C` and `F` a presheaf of
`O`-modules.  This file records the presheaf of commutative rings

`X ↦ Sym_{O(X)}(F(X))`,

with restriction maps the semilinear base change `SymmetricAlgebra.mapₛₗ` of the restriction
maps of `F`, together with

* its structure map `O ⟶ Sym(F)`, sectionwise `algebraMap`;
* its functoriality in `F`;
* its universal property: a natural family of `O(X)`-linear maps from `F(X)` into a presheaf of
  commutative `O`-algebras `A` extends uniquely to a morphism of presheaves of rings
  `Sym(F) ⟶ A` compatible with the structure maps.

Unlike `PresheafOfModules.symPowInt`, which records the homogeneous pieces separately as
presheaves of modules, the object here is ungraded: its sections are the whole symmetric
algebra of the sections, and it is the presheaf whose sheafification is computed over affine
charts in `StacksFrontier.AlgebraicGeometry.Spaces.Limits.SymmetricSectionsAlgebra`.

## Main definitions

* `PresheafOfModules.sectionwiseSymAlg`: the presheaf `X ↦ Sym_{O(X)}(F(X))`.
* `PresheafOfModules.toSymAlg`: its structure map from `O`.
* `PresheafOfModules.symAlgMap`: the morphism induced by a morphism of presheaves of modules.
* `PresheafOfModules.symAlgLift`: the morphism into a presheaf of algebras extending a natural
  family of linear maps.
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ w

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **The sectionwise symmetric algebra `X ↦ Sym_{O(X)}(F(X))`**, as a presheaf of commutative
rings. -/
noncomputable def sectionwiseSymAlg (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)) :
    Cᵒᵖ ⥤ CommRingCat.{w} where
  obj X := CommRingCat.of (SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
  map {X Y} f := CommRingCat.ofHom
    (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f))
  map_id X := by
    ext x
    exact SymmetricAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 X))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj X => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_id X))
      (fun m => F.map_id_apply_ungraded X m) x
  map_comp {X _ Z} f g := by
    ext x
    exact SymmetricAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj Z => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_comp f g))
      (fun m => F.map_comp_apply f g m) x

variable (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- The sections of `sectionwiseSymAlg F` over `X` are the symmetric algebra of `F(X)` over
`O(X)`. -/
theorem sectionwiseSymAlg_obj (X : Cᵒᵖ) :
    (sectionwiseSymAlg F).obj X =
      CommRingCat.of (SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :=
  rfl

/-- The restriction maps of `sectionwiseSymAlg F` are the semilinear base changes of the
restriction maps of `F`. -/
@[simp]
theorem sectionwiseSymAlg_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (y : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    (sectionwiseSymAlg F).map f y =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) y :=
  rfl

/-- The restriction maps of `sectionwiseSymAlg F` send a generator `ι m` to `ι (F.map f m)`. -/
theorem sectionwiseSymAlg_map_ι {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X) :
    (sectionwiseSymAlg F).map f (SymmetricAlgebra.ι _ _ m) = SymmetricAlgebra.ι _ _ (F.map f m) :=
  SymmetricAlgebra.mapₛₗ_ι _ _ m

/-- **The structure map `O ⟶ Sym(F)`**, sectionwise the algebra map of the symmetric algebra. -/
noncomputable def toSymAlg : O ⟶ sectionwiseSymAlg F where
  app X := CommRingCat.ofHom
    (algebraMap ((O ⋙ forget₂ _ RingCat).obj X)
      (SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)))
  naturality {X Y} f := by
    ext r
    exact (SymmetricAlgebra.mapₛₗ_algebraMap ((O ⋙ forget₂ _ RingCat).map f).hom
      (F.restrictₛₗ f) r).symm

/-- On sections over `X`, `toSymAlg F` is the algebra map `O(X) → Sym_{O(X)}(F(X))`. -/
theorem toSymAlg_app_apply (X : Cᵒᵖ) (r : O.obj X) :
    (toSymAlg F).app X r =
      algebraMap ((O ⋙ forget₂ _ RingCat).obj X)
        (SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) r :=
  rfl

/-! ### Functoriality in the presheaf of modules -/

variable {F} in
/-- **The morphism `Sym(F) ⟶ Sym(G)` induced by `φ : F ⟶ G`.** -/
noncomputable def symAlgMap {G : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)} (φ : F ⟶ G) :
    sectionwiseSymAlg F ⟶ sectionwiseSymAlg G where
  app X := CommRingCat.ofHom
    (SymmetricAlgebra.mapₛₗ (RingHom.id _) (φ.app X).hom)
  naturality {X Y} f := by
    ext x
    change (SymmetricAlgebra.mapₛₗ (RingHom.id _) (φ.app Y).hom)
        ((SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)) x) =
      (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (G.restrictₛₗ f))
        ((SymmetricAlgebra.mapₛₗ (RingHom.id _) (φ.app X).hom) x)
    have h := SymmetricAlgebra.ringHom_ext
      (f := (SymmetricAlgebra.mapₛₗ (RingHom.id _) (φ.app Y).hom).comp
        (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)))
      (g := (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (G.restrictₛₗ f)).comp
        (SymmetricAlgebra.mapₛₗ (RingHom.id _) (φ.app X).hom))
      (fun r => by
        simp only [RingHom.comp_apply, SymmetricAlgebra.mapₛₗ_algebraMap, RingHom.id_apply])
      (fun m => by
        simp only [RingHom.comp_apply, SymmetricAlgebra.mapₛₗ_ι]
        congr 1
        exact PresheafOfModules.naturality_apply φ f m)
    exact congrArg (fun g => g x) h

/-- On sections over `X`, `symAlgMap φ` sends a generator `ι m` to `ι (φ.app X m)`. -/
theorem symAlgMap_app_ι {G : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)} (φ : F ⟶ G)
    (X : Cᵒᵖ) (m : F.obj X) :
    (symAlgMap φ).app X (SymmetricAlgebra.ι _ _ m) = SymmetricAlgebra.ι _ _ (φ.app X m) :=
  SymmetricAlgebra.mapₛₗ_ι _ _ m

/-- On sections over `X`, `symAlgMap φ` carries the image of `r` under `toSymAlg F` to its
image under `toSymAlg G`. -/
theorem symAlgMap_app_algebraMap {G : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)}
    (φ : F ⟶ G) (X : Cᵒᵖ) (r : O.obj X) :
    (symAlgMap φ).app X ((toSymAlg F).app X r) = (toSymAlg G).app X r :=
  SymmetricAlgebra.mapₛₗ_algebraMap _ _ r

/-- `symAlgMap φ` is compatible with the structure maps:
`toSymAlg F ≫ symAlgMap φ = toSymAlg G`. -/
theorem toSymAlg_symAlgMap {G : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)} (φ : F ⟶ G) :
    toSymAlg F ≫ symAlgMap φ = toSymAlg G := by
  ext X r
  exact symAlgMap_app_algebraMap F φ X r

/-! ### The universal property -/

variable {F} {A : Cᵒᵖ ⥤ CommRingCat.{w}} (α : O ⟶ A)

/-- The `O(X)`-algebra structure on `A(X)` given by a morphism of presheaves of rings
`α : O ⟶ A`.  Not an instance: it depends on `α`. -/
@[instance_reducible]
noncomputable def algebraOfHom (X : Cᵒᵖ) :
    Algebra ((O ⋙ forget₂ _ RingCat).obj X) (A.obj X) :=
  (α.app X).hom.toAlgebra

/-- **The morphism `Sym(F) ⟶ A` extending a natural family of linear maps `F(X) ⟶ A(X)`**, where
`A(X)` is an `O(X)`-algebra through `α`. -/
noncomputable def symAlgLift
    (u : ∀ X : Cᵒᵖ, letI := algebraOfHom α X; F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] A.obj X)
    (hu : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X), A.map f (u X m) = u Y (F.map f m)) :
    sectionwiseSymAlg F ⟶ A where
  app X := letI := algebraOfHom α X
    CommRingCat.ofHom (SymmetricAlgebra.lift (u X)).toRingHom
  naturality {X Y} f := by
    let := algebraOfHom α X
    let := algebraOfHom α Y
    ext x
    change (SymmetricAlgebra.lift (u Y))
        ((SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)) x) =
      A.map f ((SymmetricAlgebra.lift (u X)) x)
    have h := SymmetricAlgebra.ringHom_ext
      (f := (SymmetricAlgebra.lift (u Y)).toRingHom.comp
        (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)))
      (g := (A.map f).hom.comp (SymmetricAlgebra.lift (u X)).toRingHom)
      (fun r => by
        change (SymmetricAlgebra.lift (u Y)) (SymmetricAlgebra.mapₛₗ _ _ (algebraMap _ _ r)) =
          A.map f ((SymmetricAlgebra.lift (u X)) (algebraMap _ _ r))
        rw [AlgHom.commutes, SymmetricAlgebra.mapₛₗ_algebraMap, AlgHom.commutes]
        exact ConcreteCategory.congr_hom (α.naturality f) r)
      (fun m => by
        change (SymmetricAlgebra.lift (u Y))
            (SymmetricAlgebra.mapₛₗ _ _ (SymmetricAlgebra.ι _ _ m)) =
          A.map f ((SymmetricAlgebra.lift (u X)) (SymmetricAlgebra.ι _ _ m))
        rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.mapₛₗ_ι,
          SymmetricAlgebra.lift_ι_apply]
        exact (hu f m).symm)
    exact congrArg (fun g => g x) h

/-- On sections over `X`, `symAlgLift α u hu` sends a generator `ι m` to `u X m`. -/
theorem symAlgLift_app_ι
    (u : ∀ X : Cᵒᵖ, letI := algebraOfHom α X; F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] A.obj X)
    (hu : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X), A.map f (u X m) = u Y (F.map f m))
    (X : Cᵒᵖ) (m : F.obj X) :
    (symAlgLift α u hu).app X (SymmetricAlgebra.ι _ _ m) = u X m := by
  let := algebraOfHom α X
  exact SymmetricAlgebra.lift_ι_apply (u X) m

/-- `symAlgLift α u hu` is compatible with the structure maps:
`toSymAlg F ≫ symAlgLift α u hu = α`. -/
theorem toSymAlg_symAlgLift
    (u : ∀ X : Cᵒᵖ, letI := algebraOfHom α X; F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] A.obj X)
    (hu : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X), A.map f (u X m) = u Y (F.map f m)) :
    toSymAlg F ≫ symAlgLift α u hu = α := by
  refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun r => ?_))
  let := algebraOfHom α X
  exact (SymmetricAlgebra.lift (u X)).commutes r

/-- **Two morphisms out of `Sym(F)` agree as soon as they agree after the structure map and on
the degree-one generators.** -/
theorem sectionwiseSymAlg_hom_ext {g g' : sectionwiseSymAlg F ⟶ A}
    (h₁ : toSymAlg F ≫ g = toSymAlg F ≫ g')
    (h₂ : ∀ (X : Cᵒᵖ) (m : F.obj X),
      g.app X (SymmetricAlgebra.ι _ _ m) = g'.app X (SymmetricAlgebra.ι _ _ m)) : g = g' := by
  refine NatTrans.ext (funext fun X => CommRingCat.hom_ext ?_)
  refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun m => h₂ X m)
  exact congrArg (fun k : O ⟶ A => (k.app X).hom r) h₁

end PresheafOfModules

end
