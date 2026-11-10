module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModuleLinearIso
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing

/-!
# `𝓕 ⊗_R (-)` from a morphism of presheaves of rings: linearity, and gluing a comparison in

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it, let `R` be a commutative
ring, let `θ : constantRingPresheaf R ⟶ O` be a morphism of presheaves of commutative rings and
let `𝓕` be a sheaf of `O`-modules.  `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` is the
functor `M ↦ 𝓕 ⊗_R M : ModuleCat R ⥤ SheafOfModules O`, built as the sheafification of the
presheaf `U ↦ 𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`.  This file supplies for it the two things that
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorByBaseModuleLinearIso.lean` supplies for the
form taking a terminal object `U₀` of the site and a ring homomorphism `α : R → O(U₀)`.

**It is `R`-linear.**  A scalar `r : R` gives the compatible family `U ↦ θ_U(r)` of local
sections of `O`, hence a point of the ring `Γ(C, O)` of global sections
(`Stacks.TensorByBaseModule.globalSectionRingHomOfHom`); multiplying by that family is the
`Γ(C, O)`-linear structure `Stacks.Cohomology.SiteModules.linearSheafOfModules` on sheaves of
`O`-modules, and restricting it along `globalSectionRingHomOfHom` makes those sheaves `R`-linear.
The functor then carries `r • φ` to `r • 𝓕 ⊗ φ`, which is what an `R`-linear dévissage along
`Stacks.FlatDevissage.isIso_tensorComparisonUniv_app_of_flat` asks of it.  Linearity is proved
from the single identity `r • φ = φ ≫ (r • 𝟙)` in `ModuleCat R` and the fact that each of the
three presheaf-level factors carries multiplication by a scalar to multiplication by its image
(`Stacks.TensorByBaseModule.presheafMultOfHom`).

**A locally bijective comparison into a sheaf of modules identifies that sheaf with
`𝓕 ⊗_R M`.**  `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfHom` turns a morphism of
presheaves of `O`-modules `Φ : 𝓕 ⊗_{O} (O ⊗_R M) ⟶ G.val` whose underlying morphism of presheaves
of abelian groups is locally bijective into an isomorphism
`(tensorByBaseModuleOfHom R J O 𝓕 θ).obj M ≅ G`, and
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom` reduces local bijectivity to
bijectivity of `Φ` on the sections over a family of objects whose arrows generate covering
sieves — the affine objects of a site of charts, say.  This is the gluing step of the second part
of [Stacks Project, Tag 073K]: `g'_*ℱ' = ℱ ⊗_A B` is checked over affine charts and glued.

The small étale site of an algebraic space has a terminal object only when the space is
representable, so these are the forms a consumer on a general algebraic space uses; the terminal
forms are their values at `Stacks.TensorByBaseModule.coefficientMap`, as
`Stacks.TensorByBaseModule.presheafMultOfHom_coefficientMap` records for the multiplication
endomorphism.

## Main definitions

* `Stacks.TensorByBaseModule.presheafMultOfHom`: multiplication by the image of a scalar under
  `θ`, as an endomorphism of a presheaf of `O`-modules.
* `Stacks.TensorByBaseModule.globalSectionRingHomOfHom`: the ring homomorphism from `R` to the
  global sections of `O` that `θ` is.
* `Stacks.TensorByBaseModule.linearOfHom`: the `R`-linear structure on sheaves of `O`-modules
  attached to `θ`.

## Main results

* `Stacks.TensorByBaseModule.presheafMultOfHom_comp`: multiplication by the image of a scalar is
  central — it commutes with every morphism of presheaves of `O`-modules.
* `Stacks.TensorByBaseModule.tensorByBaseModulePresheafOfHom_map_smul`: the presheaf-level tensor
  functor carries `r • φ` to multiplication by the image of `r` followed by `𝓕 ⊗ φ`.
* `Stacks.TensorByBaseModule.sheafify_map_presheafMultOfHom`: sheafification carries
  multiplication by the image of a scalar to multiplication by the corresponding global section.
* `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom_linear`: **`𝓕 ⊗_R (-)` is `R`-linear.**
* `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfHom` and
  `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom`: **a locally bijective
  comparison exhibits a sheaf of `O`-modules as `𝓕 ⊗_R M`.**

## Implementation notes

*Where the naturality of `θ` enters.*  Every restriction map of `constantRingPresheaf R` is the
identity of `R` (`Stacks.TensorByBaseModule.constantRingPresheaf_map`), so naturality of `θ`
collapses to `θ_Y = θ_X ≫ O(f)` for every `f : X ⟶ Y`, which is
`Stacks.TensorByBaseModule.app_eq_comp_map`.  This single identity is what makes
`presheafMultOfHom` a morphism of presheaves and what makes the family `U ↦ θ_U(r)` a global
section of `O`; nothing else about `θ` is used.

*Why linearity is proved through `r • 𝟙` and not through `r • φ` directly.*  The three factors
of `tensorByBaseModulePresheafOfHom` are the constant presheaf of modules, extension of scalars
along `θ` and the sectionwise tensor product with `𝓕`.  For the middle factor the identity
`(1 ⊗ (r • x)) = θ(r) • (1 ⊗ x)` is a statement about a *single* pure tensor and is reached
through the change-of-rings hom-set bijection
`Stacks.PresheafOfModules.ChangeOfRings.homEquivCore`, which turns an equality of morphisms out
of `O ⊗_R M` into an equality on the elements `1 ⊗ x`; at `r • φ` for a general `φ` the same
computation needs an induction over the tensor product, and there the module instances on
`Stacks.PresheafOfModules.ChangeOfRings.cofObj` are no longer determined by unification.
Factoring `r • φ = φ ≫ (r • 𝟙)` first removes the general `φ` from the computation.

*The scalar is introduced as a `let`, not a `have`.*  The ring of sections of
`Stacks.TensorByBaseModule.constantRingPresheaf R` over an object is `R` itself, but not
syntactically, and the tensor products of the change of rings are formed over the first
spelling.  A scalar of the second spelling is therefore reintroduced at the first; with `have`
the reintroduction is opaque and the definitional checks below fail, so `let` is used.

*Sheafification is applied to `presheafMultOfHom` through the adjunction, not computed.*  The
sheafification of a presheaf of modules has no description on sections, so
`Stacks.TensorByBaseModule.sheafify_map_presheafMultOfHom` is proved by transposing both sides
along `PresheafOfModules.sheafificationAdjunction`: the transpose of the sheafified
multiplication is the multiplication followed by the unit, by naturality of the unit, and the
transpose of the multiplication on the sheafification is the unit followed by the multiplication,
which is the same morphism because multiplication by the image of a scalar is central.

*The gluing is stated for the comparison, not for an abstract isomorphism.*  An isomorphism of
the sections over each object of a covering family cannot be glued: the gluing is the assertion
that one morphism of presheaves is locally bijective, and a family of unrelated isomorphisms
carries no compatibility.  What the statements below ask for is therefore bijectivity of a given
`Φ` over the objects of the family, which is exactly what a canonical comparison provides.

No declaration here carries a `stacks` tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits MonoidalCategory TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings
open scoped IsMulCommutative

universe v u w

namespace Stacks.TensorByBaseModule

open Stacks.Presheaf (isLocallyInjective_of_injective_app isLocallySurjective_of_surjective_app)

variable {C : Type u} [Category.{v} C]

section MultOfHom

variable (R : Type w) [CommRing R] (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Naturality of a morphism of presheaves of rings out of `constantRingPresheaf R`, in the
collapsed form it takes there: every restriction map of the constant presheaf is the identity,
so the component over `Y` is the component over `X` followed by restriction along `f`. -/
theorem app_eq_comp_map (θ : constantRingPresheaf (C := C) R ⟶ O) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    θ.app Y = θ.app X ≫ O.map f :=
  (Category.id_comp (θ.app Y)).symm.trans (θ.naturality f)

/-- On an element, `Stacks.TensorByBaseModule.app_eq_comp_map`: the image of a scalar over `Y` is
the restriction of its image over `X`. -/
theorem map_app_apply (θ : constantRingPresheaf (C := C) R ⟶ O) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R) :
    (O.map f).hom ((θ.app X).hom r) = (θ.app Y).hom r := by
  rw [app_eq_comp_map R O θ f]
  rfl

/-- Multiplication by the image of a scalar under `θ`, on a presheaf of modules. -/
def presheafMultOfHom (θ : constantRingPresheaf (C := C) R ⟶ O) (r : R) (N : PMod O) : N ⟶ N where
  app X := ModuleCat.ofHom
    { toFun := fun x => ((θ.app X).hom r) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => by
        dsimp
        rw [smul_comm] }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change ((θ.app Y).hom r) • N.map f x = N.map f (((θ.app X).hom r) • x)
    rw [PresheafOfModules.map_smul]
    congr 1
    change _ = ((ringPresheaf O).map f).hom _
    exact (map_app_apply R O θ f r).symm

/-- The component of `presheafMultOfHom R O θ r N` over `X` sends `x` to `θ.app X r • x`. -/
@[simp]
theorem presheafMultOfHom_app_apply (θ : constantRingPresheaf (C := C) R ⟶ O) (r : R) (N : PMod O)
    (X : Cᵒᵖ) (x : N.obj X) :
    ((presheafMultOfHom R O θ r N).app X).hom x = ((θ.app X).hom r) • x :=
  rfl

/-- Multiplication by the image of a scalar commutes with every morphism. -/
theorem presheafMultOfHom_comp (θ : constantRingPresheaf (C := C) R ⟶ O) (r : R)
    {N N' : PMod O} (f : N ⟶ N') :
    presheafMultOfHom R O θ r N ≫ f = f ≫ presheafMultOfHom R O θ r N' := by
  ext X x
  change (f.app X).hom (((θ.app X).hom r) • x) = ((θ.app X).hom r) • (f.app X).hom x
  exact (f.app X).hom.map_smul _ x

/-- Tensoring on the left with a fixed presheaf of modules commutes with multiplication by the
image of a scalar. -/
theorem tensorLeft_map_presheafMultOfHom (θ : constantRingPresheaf (C := C) R ⟶ O) (r : R)
    (F : PMod O) (N : PMod O) :
    (tensorLeft F).map (presheafMultOfHom R O θ r N)
      = presheafMultOfHom R O θ r ((tensorLeft F).obj N) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  refine ModuleCat.hom_ext (TensorProduct.ext' fun s t => ?_)
  change s ⊗ₜ[O.obj X] (((θ.app X).hom r) • t) = ((θ.app X).hom r) • (s ⊗ₜ[O.obj X] t)
  exact TensorProduct.tmul_smul _ s t

/-- At a coefficient map, multiplication by the image of a scalar is multiplication by the
section `α r` over the terminal object: the two endomorphisms are the same morphism. -/
theorem presheafMultOfHom_coefficientMap {U₀ : C} (hU₀ : IsTerminal U₀)
    (α : R →+* O.obj (op U₀)) (r : R) (N : PMod O) :
    presheafMultOfHom R O (coefficientMap R hU₀ α) r N = presheafMult hU₀ O (α r) N :=
  rfl

end MultOfHom

section Site

variable (R : Type w) [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})
  (𝓕 : SheafOfModules.{w} (ringSheaf J O)) (θ : constantRingPresheaf (C := C) R ⟶ O.obj)

-- The rings of sections of `ringSheaf J O` are commutative (instance search no longer sees
-- through the composite with `forget₂`); the instance is declared, locally, upstream.
attribute [local instance] isMulCommutativeRingSheafObj

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Extension of scalars along `θ` carries the action of a scalar on the identity to
multiplication by the image of that scalar. -/
theorem changeOfRings_constantModulePresheaf_map_smul_id_ofHom (N : ModuleCat.{w} R) (r : R) :
    (changeOfRings θ).map ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))
      = presheafMultOfHom R O.obj θ r
          ((changeOfRings θ).obj ((constantModulePresheaf (C := C) R).obj N)) := by
  refine (homEquivCore θ _ _).injective ?_
  ext X x
  let := (θ.app X).hom.toAlgebra
  let r' : ((constantRingPresheaf (C := C) R).obj X : Type w) := r
  have hc : ((θ.app X).hom r : O.obj.obj X) = r' • (1 : O.obj.obj X) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  have h1 : ((θ.app X).hom r) •
        ((1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] x)
      = (1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] (r' • x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hc, TensorProduct.smul_tmul]
  change (unitApp θ ((changeOfRings θ).map
      ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))) X).hom x
    = (unitApp θ (presheafMultOfHom R O.obj θ r _) X).hom x
  rw [unitApp_apply, unitApp_apply]
  change (((changeOfRings θ).map
      ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))).app X).hom
        ((1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] x)
    = ((θ.app X).hom r) •
      ((1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] x)
  rw [h1, show (((changeOfRings θ).map
          ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))).app X).hom
            ((1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] x)
        = (1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X]
          ((((constantModulePresheaf (C := C) R).map (r • 𝟙 N)).app X).hom x) from
      cofHom_app_tmul _ _ X _ x]
  refine congrArg (fun y => (1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] y) ?_
  change (r • 𝟙 N).hom x = r' • x
  rw [ModuleCat.hom_smul]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The presheaf-level tensor functor carries the action of a scalar on the identity to
multiplication by the image of that scalar. -/
theorem tensorByBaseModulePresheafOfHom_map_smul_id (N : ModuleCat.{w} R) (r : R) :
    (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (r • 𝟙 N)
      = presheafMultOfHom R O.obj θ r
          ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj N) := by
  change (tensorLeft 𝓕.val).map ((changeOfRings θ).map
      ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))) = _
  rw [changeOfRings_constantModulePresheaf_map_smul_id_ofHom,
    tensorLeft_map_presheafMultOfHom]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The presheaf-level tensor functor carries the action of a scalar on a morphism of modules
to multiplication by the image of that scalar.** -/
theorem tensorByBaseModulePresheafOfHom_map_smul {M N : ModuleCat.{w} R} (r : R) (φ : M ⟶ N) :
    (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (r • φ) =
      presheafMultOfHom R O.obj θ r ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M) ≫
        (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map φ := by
  have key : r • φ = φ ≫ (r • 𝟙 N) := by
    rw [Linear.comp_smul, Category.comp_id]
  rw [key, Functor.map_comp, tensorByBaseModulePresheafOfHom_map_smul_id,
    presheafMultOfHom_comp]

/-- **The ring homomorphism from `R` to the global sections of `O` that `θ` is**: a scalar goes
to the family of its images, which is compatible with restriction by naturality of `θ`. -/
def globalSectionRingHomOfHom :
    R →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (ringSheaf J O)) where
  toFun r := ⟨fun X => (θ.app X).hom r, fun {_ _} f => map_app_apply R O.obj θ f r⟩
  map_one' := Subtype.ext (funext fun X => map_one (θ.app X).hom)
  map_mul' r s := Subtype.ext (funext fun X => map_mul (θ.app X).hom r s)
  map_zero' := Subtype.ext (funext fun X => map_zero (θ.app X).hom)
  map_add' r s := Subtype.ext (funext fun X => map_add (θ.app X).hom r s)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The global section attached to a scalar takes the value `θ_X(r)` over `X`. -/
@[simp]
theorem globalSectionRingHomOfHom_val (r : R) (X : Cᵒᵖ) :
    (globalSectionRingHomOfHom R J O θ r).val X = (θ.app X).hom r :=
  rfl

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Multiplication by the global section attached to a scalar, on a sheaf of modules, is
multiplication by the image of that scalar on the underlying presheaf. -/
theorem forget_map_globalSmulOfHom (r : R) (G : SheafOfModules.{w} (ringSheaf J O)) :
    (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map
        (Stacks.Cohomology.SiteModules.globalSmul (ringSheaf J O)
          (globalSectionRingHomOfHom R J O θ r) G)
      = presheafMultOfHom R O.obj θ r
        ((SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj G) := by
  ext X x
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Sheafification carries multiplication by the image of a scalar to multiplication by the
corresponding global section.** -/
theorem sheafify_map_presheafMultOfHom (r : R) (N : PMod O.obj) :
    (sheafify J O).map (presheafMultOfHom R O.obj θ r N)
      = Stacks.Cohomology.SiteModules.globalSmul (ringSheaf J O)
        (globalSectionRingHomOfHom R J O θ r) ((sheafify J O).obj N) := by
  change (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map
      (presheafMultOfHom R O.obj θ r N)
    = Stacks.Cohomology.SiteModules.globalSmul (ringSheaf J O)
      (globalSectionRingHomOfHom R J O θ r)
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).obj N)
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf J O).obj)).homEquiv N _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, forget_map_globalSmulOfHom]
  exact Eq.trans
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).unit.naturality
      (presheafMultOfHom R O.obj θ r N)).symm)
    (presheafMultOfHom_comp R O.obj θ r
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).unit.app N))

/-- The `R`-linear structure on sheaves of `O`-modules attached to `θ`: a scalar acts by
multiplication by the global section of `O` that is its family of images, which is the
`Γ(C, O)`-linear structure of `Stacks.Cohomology.SiteModules.linearSheafOfModules` restricted
along `Stacks.TensorByBaseModule.globalSectionRingHomOfHom`. -/
@[instance_reducible]
def linearOfHom : Linear R (SheafOfModules.{w} (ringSheaf J O)) :=
  letI : Linear ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (ringSheaf J O))
      (SheafOfModules.{w} (ringSheaf J O)) :=
    Stacks.Cohomology.SiteModules.linearSheafOfModules (ringSheaf J O)
  Linear.ofRingHom (globalSectionRingHomOfHom R J O θ)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **`𝓕 ⊗_R (-)` is `R`-linear**, in the form taking a morphism of presheaves of rings. -/
theorem tensorByBaseModuleOfHom_linear :
    letI := linearOfHom R J O θ
    Functor.Linear R (tensorByBaseModuleOfHom R J O 𝓕 θ) := by
  let := linearOfHom R J O θ
  refine ⟨fun {M N} φ r => ?_⟩
  change (sheafify J O).map ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (r • φ)) = _
  rw [tensorByBaseModulePresheafOfHom_map_smul, Functor.map_comp,
    sheafify_map_presheafMultOfHom]
  rfl

/-! ### Gluing a comparison into the tensor product -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A locally bijective comparison out of the presheaf-level tensor product sheafifies to an
isomorphism.** -/
theorem isIso_sheafificationHomEquiv_symm_ofHom (M : ModuleCat.{w} R)
    (G : SheafOfModules.{w} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    [Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)]
    [Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)] :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ) := by
  have hiso : IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)) :=
    (J.W_iff _).mp (J.W_of_isLocallyBijective _)
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{w} (ringSheaf J O)),
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  change IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ) ≫
    (sheafificationAdjunction J AddCommGrpCat.{w}).counit.app
      ((SheafOfModules.toSheaf (ringSheaf J O)).obj G))
  exact IsIso.comp_isIso' hiso (isIso_sheafificationAdjunction_counit _)

/-- **`𝓕 ⊗_R M ≅ G`**: a sheaf of `O`-modules receiving a locally bijective comparison from the
presheaf `U ↦ 𝓕(U) ⊗_R M` *is* the value of
`Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` at `M`.  This is the gluing step: the
comparison itself need only be locally bijective — no isomorphism of sections over a single
object is asked for, and conversely a chart-wise isomorphism that is not the comparison cannot be
used. -/
noncomputable def tensorByBaseModuleIsoOfHom (M : ModuleCat.{w} R)
    (G : SheafOfModules.{w} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    [Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)]
    [Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)] :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).obj M ≅ G :=
  @asIso _ _ _ _ ((PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ)
    (isIso_sheafificationHomEquiv_symm_ofHom R J O 𝓕 θ M G Φ)

/-- **`𝓕 ⊗_R M ≅ G` from bijectivity on the sections over a covering family of objects.**  This
is the form in which the geometric chain uses the gluing step: the comparison is checked on the
*affine* objects of the site, which generate covering sieves of every object. -/
noncomputable def tensorByBaseModuleIsoOfBijectiveAppOfHom (M : ModuleCat.{w} R)
    (G : SheafOfModules.{w} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    (P : C → Prop)
    (hcov : ∀ X : C, Sieve.generate (fun {W : C} (_ : W ⟶ X) => P W) ∈ J X)
    (hbij : ∀ W : C, P W → Function.Bijective (Φ.app (op W)).hom) :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).obj M ≅ G :=
  haveI := isLocallyInjective_of_injective_app J
    ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ) P hcov
    (fun W hW => (hbij W hW).1)
  haveI := isLocallySurjective_of_surjective_app J
    ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ) P hcov
    (fun W hW => (hbij W hW).2)
  tensorByBaseModuleIsoOfHom R J O 𝓕 θ M G Φ

end Sheafify

end Site

end Stacks.TensorByBaseModule

end
