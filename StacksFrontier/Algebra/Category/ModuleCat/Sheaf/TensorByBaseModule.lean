module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring a fixed sheaf of modules by a module over a base ring

Let `(C, J)` be a site with a terminal object `U₀`, let `O` be a sheaf of commutative rings on
it, let `R` be a commutative ring equipped with a ring homomorphism `α : R → O(U₀)`, and let
`𝓕` be a sheaf of `O`-modules.  This file builds the functor

  `M ↦ 𝓕 ⊗_R M : ModuleCat R ⥤ SheafOfModules O`

and shows that it preserves colimits and carries the free module of rank one back to `𝓕`.  It
is the engine of the second part of [Stacks Project, Tag 073K]: there `𝓕` is a quasi-coherent
module on an algebraic space, `R` is the coordinate ring of an affine base, and the colimit
preservation is what turns a presentation of `M` into a presentation of `𝓕 ⊗_R M`.

The functor is a composite of four functors, each of which is already known to preserve
colimits:

  `constantModulePresheaf R ⋙ changeOfRings (coefficientMap α) ⋙ tensorLeft 𝓕 ⋙ sheafification`

The first sends `M` to the constant presheaf with value `M`; it is left adjoint to evaluation
at the terminal object, which is the only place terminality of `U₀` is used.  The second is
extension of scalars along the morphism of presheaves of rings induced by `α`, which is
[Stacks Project, Tag 01BH] in the affine case and is taken from
`Stacks.PresheafOfModules.ChangeOfRings`.  The third is the sectionwise tensor product with
`𝓕`, and the fourth is sheafification.

## Main definitions

* `Stacks.TensorByBaseModule.constantRingPresheaf`: the constant presheaf of commutative rings
  with value `R`.
* `Stacks.TensorByBaseModule.constantModulePresheaf`: the constant presheaf of `R`-modules, as
  a functor `ModuleCat R ⥤ PresheafOfModules (constantRingPresheaf R)`.
* `Stacks.TensorByBaseModule.coefficientMap`: the morphism of presheaves of commutative rings
  `constantRingPresheaf R ⟶ O` induced by `α` and restriction from the terminal object.
* `Stacks.TensorByBaseModule.coefficientAlgebra`, `Stacks.TensorByBaseModule.sectionsModule`:
  the `R`-algebra structure on `O(U)` and the `R`-module structure on the sections of a
  presheaf of `O`-modules that `coefficientMap` defines.
* `Stacks.TensorByBaseModule.ringSheaf`: `O` read as a sheaf of not necessarily commutative
  rings, spelled so that its underlying presheaf is `ringPresheaf O.val` on the nose.
* `Stacks.TensorByBaseModule.tensorByBaseModulePresheaf`: the presheaf-level functor
  `M ↦ 𝓕 ⊗_R M`, the composite of the first three factors.
* `Stacks.TensorByBaseModule.tensorByBaseModule`: the functor `M ↦ 𝓕 ⊗_R M` with values in
  sheaves of modules, obtained by sheafifying the previous one.

## Main results

* `Stacks.TensorByBaseModule.constantModulePresheafHomEquiv` and
  `Stacks.TensorByBaseModule.constantModulePresheafAdjunction`: the constant presheaf of
  modules is left adjoint to evaluation at the terminal object.
* `Stacks.TensorByBaseModule.constantModulePresheaf_preservesColimitsOfSize`: the constant
  presheaf of modules preserves colimits of size `{w, w}` on any site, with no terminal object
  needed — a cocone of presheaves of modules is colimit as soon as it is so after evaluation at
  every object, and evaluating the constant presheaf returns the diagram one started with.  This
  is what makes `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom`, the form taking a morphism
  of presheaves of rings, preserve colimits on a site with no terminal object.
* `Stacks.TensorByBaseModule.tensorByBaseModulePresheaf_obj_obj` and
  `Stacks.TensorByBaseModule.sectionsEquiv`: the sections of `𝓕 ⊗_R M` over `U` are
  `𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`, canonically `𝓕(U) ⊗_R M` as an `O(U)`-module.
* `Stacks.TensorByBaseModule.tensorByBaseModule` is additive and preserves colimits of size
  `{w, w}`, where `w` is the universe of the sections.
* `Stacks.TensorByBaseModule.tensorByBaseModuleUnitIso`: the value of the functor at the free
  module of rank one is `𝓕` itself.

## Implementation notes

Mathlib's monoidal structure on presheaves of modules lives on
`PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)` for `O : Cᵒᵖ ⥤ CommRingCat.{u}`, so
it identifies the universe of the module sections with the universe of the ring sections.  The
third factor of the composite is `MonoidalCategory.tensorLeft`, so this file works in a single
universe `w` for both; the `w` of `ModuleCat.{w} R` and the `r` of `O : Sheaf J CommRingCat.{r}`
cannot be kept apart here.

The sheaf of rings indexing the target is `ringSheaf`, which re-spells
`AlgebraicGeometry.SheafOfModules.underlyingRingSheafOfSite` (reusing its sheaf condition, so
there is one proof) with `ringPresheaf O.val` as its underlying presheaf *syntactically*.  Both
halves of that matter.  Without it the module instances at each object do not synthesize,
because the underlying ring of `(sheafCompose J _).obj O` at an object is reachable only by
unfolding `sheafCompose`; and `PresheafOfModules.sheafification` is applied to the identity of
the underlying presheaf, so if the two spellings differed the identity morphism would have
distinct source and target and its `IsIso` instance — hence the local bijectivity hypotheses of
sheafification — would not be found.

`coefficientRingHom` is `α` followed by restriction along the unique map to `U₀`, taken with
target type `R →+* O(U)` rather than `↑((constantRingPresheaf R).obj U) →+* O(U)`.  The two are
definitionally equal, but only the first makes `Algebra R (O(U))` and therefore the tensor
product `O(U) ⊗_R M` available to instance search.

Additivity of the four factors is assembled from the adjunctions, by
`Adjunction.left_adjoint_additive`, except for `tensorLeft`, which is
`MonoidalPreadditive.whiskerLeft_add` sectionwise.  An
`R`-linear structure on the composite is *not* provided: already at the first factor, the
scalar action of `R` on morphisms of presheaves of modules over `constantRingPresheaf R` needs
`Linear R (ModuleCat ↑((ringPresheaf (constantRingPresheaf R)).obj U))`, and the ring there is
`R` only up to unfolding, so the sectionwise linear structure of `ModuleCat R` does not apply.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits MonoidalCategory TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe v u w

namespace Stacks.TensorByBaseModule

variable {C : Type u} [Category.{v} C]

/-- The constant presheaf of commutative rings with value `R`. -/
@[sga "4 IV 13.8"]
def constantRingPresheaf (R : Type w) [CommRing R] : Cᵒᵖ ⥤ CommRingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (CommRingCat.of R)

variable (R : Type w) [CommRing R]

/-- Every object of `C` carries `R` itself as its ring of sections of `constantRingPresheaf R`. -/
@[simp]
theorem constantRingPresheaf_obj (X : Cᵒᵖ) :
    (constantRingPresheaf (C := C) R).obj X = CommRingCat.of R :=
  rfl

/-- Every restriction map of `constantRingPresheaf R` is the identity of `R`. -/
@[simp]
theorem constantRingPresheaf_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (constantRingPresheaf (C := C) R).map f = 𝟙 (CommRingCat.of R) :=
  rfl

/-- The constant presheaf of `R`-modules with value `M`: the module of sections over every
object is `M` itself, and every restriction map is the identity.  This is a presheaf of modules
over `constantRingPresheaf R`, whose restriction maps are identities of `R`. -/
def constantModulePresheafObj (M : ModuleCat.{w} R) :
    PMod (constantRingPresheaf (C := C) R) where
  obj _ := M
  map _ := 𝟙 _

/-- The constant presheaf of modules, as a functor into presheaves of modules over the constant
presheaf of rings.  It is left adjoint to evaluation at a terminal object, hence preserves all
colimits; see `constantModulePresheafAdjunction`. -/
def constantModulePresheaf : ModuleCat.{w} R ⥤ PMod (constantRingPresheaf (C := C) R) where
  obj M := constantModulePresheafObj R M
  map φ := { app _ := φ }

/-- The sections of `(constantModulePresheaf R).obj M` over any object are `M`. -/
@[simp]
theorem constantModulePresheaf_obj_obj (M : ModuleCat.{w} R) (X : Cᵒᵖ) :
    ((constantModulePresheaf (C := C) R).obj M).obj X = M :=
  rfl

/-- `constantModulePresheaf R` acts on a morphism by that same morphism over every object. -/
@[simp]
theorem constantModulePresheaf_map_app {M N : ModuleCat.{w} R} (φ : M ⟶ N) (X : Cᵒᵖ) :
    ((constantModulePresheaf (C := C) R).map φ).app X = φ :=
  rfl

/-- **The constant presheaf of modules preserves all colimits**, on any site whatever and with
no terminal object in sight.

A cocone of presheaves of modules is colimit as soon as it is so after evaluation at every
object, by `PresheafOfModules.evaluationJointlyReflectsColimits`; and evaluating
`constantModulePresheaf R` at an object gives back the diagram of `R`-modules one started with,
the sections over every object being that module and every restriction map the identity.  So the
image of a colimit cocone is evaluated at each object to that same colimit cocone.

The side condition of the joint reflection — that restriction of scalars along each restriction
map of `constantRingPresheaf R` preserve the colimits in question — is
`ModuleCat.preservesColimit_restrictScalars`, those restriction maps being identities of `R`. -/
instance constantModulePresheaf_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w, w} (constantModulePresheaf (C := C) R) :=
  ⟨⟨⟨fun hc => ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ fun _ => hc⟩⟩⟩⟩

section Terminal

variable {U₀ : C} (hU₀ : IsTerminal U₀)

/-- The maps to a terminal object, read in the opposite category, are compatible with
composition: the unique map `op U₀ ⟶ X` followed by `f : X ⟶ Y` is the unique map
`op U₀ ⟶ Y`. -/
theorem op_from_comp {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (hU₀.from X.unop).op ≫ f = (hU₀.from Y.unop).op :=
  Quiver.Hom.unop_inj (hU₀.comp_from f.unop)

/-- **The constant presheaf of modules is left adjoint to evaluation at a terminal object**, in
hom-set form: a morphism from the constant presheaf with value `M` to `N` is the same thing as a
morphism `M ⟶ N(U₀)`.  One direction evaluates at `U₀`; the other restricts a map into the
sections over the terminal object along the unique map `U ⟶ U₀`. -/
def constantModulePresheafHomEquiv (M : ModuleCat.{w} R)
    (N : PMod (constantRingPresheaf (C := C) R)) :
    ((constantModulePresheaf (C := C) R).obj M ⟶ N) ≃ (M ⟶ N.obj (op U₀)) where
  toFun f := f.app (op U₀)
  invFun g :=
    { app X := g ≫ (N.map (hU₀.from X.unop).op : N.obj (op U₀) ⟶ N.obj X)
      naturality {X Y} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        change N.map (hU₀.from Y.unop).op (g.hom x)
          = N.map f (N.map (hU₀.from X.unop).op (g.hom x))
        rw [← PresheafOfModules.map_comp_apply, op_from_comp hU₀ f] }
  left_inv f := by
    refine PresheafOfModules.hom_ext fun X => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change N.map (hU₀.from X.unop).op (f.app (op U₀) x) = f.app X x
    exact (PresheafOfModules.naturality_apply f (hU₀.from X.unop).op x).symm
  right_inv g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change N.map (hU₀.from U₀).op (g.hom x) = g.hom x
    rw [PresheafOfModules.congr_map_apply N
      (show (hU₀.from U₀).op = 𝟙 (op U₀) from Quiver.Hom.unop_inj hU₀.from_self),
      N.map_id]
    rfl

/-- **The constant presheaf of modules is left adjoint to evaluation at a terminal object.**
This is where terminality of `U₀` is used, and it is the reason the first factor of
`tensorByBaseModule` preserves all colimits. -/
def constantModulePresheafAdjunction :
    constantModulePresheaf (C := C) R ⊣
      PresheafOfModules.evaluation (ringPresheaf (constantRingPresheaf (C := C) R)) (op U₀) :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N := constantModulePresheafHomEquiv R hU₀ M N
      homEquiv_naturality_left_symm {_ _ _} f g :=
        PresheafOfModules.hom_ext fun _ => Category.assoc f g _
      homEquiv_naturality_right {_ _ _} _ _ := rfl }

section Coefficients

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The morphism of presheaves of commutative rings `constantRingPresheaf R ⟶ O` induced by a
ring homomorphism `α : R →+* O(U₀)` into the sections over a terminal object: over an object `U`
it is `α` followed by restriction along the unique map `U ⟶ U₀`. -/
def coefficientMap (α : R →+* O.obj (op U₀)) : constantRingPresheaf (C := C) R ⟶ O where
  app X := CommRingCat.ofHom α ≫ O.map (hU₀.from X.unop).op
  naturality {X Y} f := by
    have h : (CommRingCat.ofHom α ≫ O.map (hU₀.from X.unop).op) ≫ O.map f
        = CommRingCat.ofHom α ≫ O.map (hU₀.from Y.unop).op := by
      rw [Category.assoc, ← O.map_comp, op_from_comp hU₀ f]
    exact (Category.id_comp _).trans h.symm

/-- Over an object `U`, `coefficientMap α` is `α` followed by restriction from `U₀` to `U`. -/
@[simp]
theorem coefficientMap_app (α : R →+* O.obj (op U₀)) (X : Cᵒᵖ) :
    (coefficientMap R hU₀ α).app X = CommRingCat.ofHom α ≫ O.map (hU₀.from X.unop).op :=
  rfl

/-- The ring homomorphism `R →+* O(U)` carried by `coefficientMap α`, with `R` as its source
type rather than the sections of `constantRingPresheaf R` over `U`.  The two are definitionally
equal; only this spelling lets instance search find `Algebra R (O(U))`. -/
def coefficientRingHom (α : R →+* O.obj (op U₀)) (X : Cᵒᵖ) : R →+* O.obj X :=
  (O.map (hU₀.from X.unop).op).hom.comp α

/-- `coefficientRingHom` is the ring homomorphism underlying `coefficientMap`. -/
theorem coefficientRingHom_eq (α : R →+* O.obj (op U₀)) (X : Cᵒᵖ) :
    coefficientRingHom R hU₀ α X = ((coefficientMap R hU₀ α).app X).hom :=
  rfl

/-- The sections of `O` over `U` as an `R`-algebra, via `α` and restriction from `U₀`. -/
@[instance_reducible]
def coefficientAlgebra (α : R →+* O.obj (op U₀)) (X : Cᵒᵖ) : Algebra R (O.obj X) :=
  (coefficientRingHom R hU₀ α X).toAlgebra

/-- The sections of a presheaf of `O`-modules over `U` as an `R`-module, by restriction of
scalars along `coefficientRingHom`. -/
@[instance_reducible]
def sectionsModule (α : R →+* O.obj (op U₀)) (F : PMod O) (X : Cᵒᵖ) :
    Module R (F.obj X) :=
  Module.compHom (F.obj X) (coefficientRingHom R hU₀ α X)

/-- The scalar actions of `R` and of `O(U)` on the sections of a presheaf of `O`-modules over
`U` form a tower, the first being the second restricted along `coefficientRingHom`. -/
theorem isScalarTower_coefficient (α : R →+* O.obj (op U₀)) (F : PMod O) (X : Cᵒᵖ) :
    letI := coefficientAlgebra R hU₀ α X
    letI := sectionsModule R hU₀ α F X
    IsScalarTower R (O.obj X) (F.obj X) :=
  let := coefficientAlgebra R hU₀ α X
  let := sectionsModule R hU₀ α F X
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

end Coefficients

section Site

variable (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})

/-- A sheaf of commutative rings read as a sheaf of not necessarily commutative rings, in the
spelling whose underlying presheaf is `ringPresheaf O.val` on the nose.  The sheaf condition is
that of `Stacks.SheafOfModules.Tensor.ringSheaf O`, of which this is a
re-spelling and not a second object. -/
abbrev ringSheaf : Sheaf J RingCat.{w} :=
  ⟨ringPresheaf O.val, (Stacks.SheafOfModules.Tensor.ringSheaf O).property⟩

/-- **Tensoring `𝓕` by a module over the base ring, at the level of presheaves**: the composite
of the constant presheaf of modules, extension of scalars along `coefficientMap α`, and the
sectionwise tensor product with `𝓕`.  Over an object `U` it is
`M ↦ 𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`; see `tensorByBaseModulePresheaf_obj_obj`. -/
def tensorByBaseModulePresheaf (𝓕 : SheafOfModules.{w} (ringSheaf J O))
    (α : R →+* O.val.obj (op U₀)) :
    ModuleCat.{w} R ⥤ PMod O.val :=
  constantModulePresheaf (C := C) R ⋙
    changeOfRings (coefficientMap R hU₀ (O := O.val) α) ⋙ tensorLeft 𝓕.val

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafification of presheaves of `O`-modules, which is `PresheafOfModules.sheafification`
applied to the identity of `ringPresheaf O.val`. -/
def sheafify : PMod O.val ⥤ SheafOfModules.{w} (ringSheaf J O) :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)

/-- **Tensoring `𝓕` by a module over the base ring.**  This is the functor `M ↦ 𝓕 ⊗_R M` of
the second part of [Stacks Project, Tag 073K]: the presheaf-level tensor product, sheafified. -/
def tensorByBaseModule (𝓕 : SheafOfModules.{w} (ringSheaf J O))
    (α : R →+* O.val.obj (op U₀)) :
    ModuleCat.{w} R ⥤ SheafOfModules.{w} (ringSheaf J O) :=
  tensorByBaseModulePresheaf R hU₀ J O 𝓕 α ⋙ sheafify J O

/-- The constant presheaf of modules is additive: it acts on morphisms by the identity over
every object. -/
instance constantModulePresheaf_additive :
    (constantModulePresheaf (C := C) R).Additive where
  map_add := PresheafOfModules.hom_ext fun _ => rfl

/-- Tensoring presheaves of modules on the left by a fixed one is additive, because it is so
sectionwise. -/
instance tensorLeft_additive (F : PMod O.val) : (tensorLeft F).Additive where
  map_add {_ _ f g} := PresheafOfModules.hom_ext fun X =>
    MonoidalPreadditive.whiskerLeft_add (X := F.obj X) (f.app X) (g.app X)

/-- Sheafification of presheaves of modules is additive, being left adjoint to the forgetful
functor, which is additive. -/
instance sheafify_additive : (sheafify J O).Additive :=
  have : (SheafOfModules.forget (ringSheaf J O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).Additive :=
    { map_add := PresheafOfModules.hom_ext fun _ => rfl }
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).left_adjoint_additive

variable (𝓕 : SheafOfModules.{w} (ringSheaf J O)) (α : R →+* O.val.obj (op U₀))

/-- The presheaf-level tensor functor is additive, each of its three factors being so. -/
instance tensorByBaseModulePresheaf_additive :
    (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).Additive := by
  have h₁ : (restrictScalars (coefficientMap R hU₀ (O := O.obj) α)).Additive :=
    { map_add := PresheafOfModules.hom_ext fun _ => rfl }
  have h₂ : (changeOfRings (coefficientMap R hU₀ (O := O.obj) α)).Additive :=
    (changeOfRingsAdjunction (coefficientMap R hU₀ (O := O.obj) α)).left_adjoint_additive
  dsimp only [tensorByBaseModulePresheaf]
  infer_instance

/-- **`𝓕 ⊗_R (-)` is additive.** -/
instance tensorByBaseModule_additive :
    (tensorByBaseModule R hU₀ J O 𝓕 α).Additive := by
  dsimp only [tensorByBaseModule]
  infer_instance

/-- The presheaf-level tensor functor preserves colimits: its first two factors are left
adjoints and its third has the sectionwise colimit-preservation instance of Mathlib. -/
instance tensorByBaseModulePresheaf_preservesColimits :
    PreservesColimitsOfSize.{w, w} (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α) := by
  have h₁ : PreservesColimitsOfSize.{w, w} (constantModulePresheaf (C := C) R) :=
    (constantModulePresheafAdjunction R hU₀).leftAdjoint_preservesColimits
  have h₂ : PreservesColimitsOfSize.{w, w}
      (changeOfRings (coefficientMap R hU₀ (O := O.obj) α)) :=
    (changeOfRingsAdjunction (coefficientMap R hU₀ (O := O.obj) α)).leftAdjoint_preservesColimits
  dsimp only [tensorByBaseModulePresheaf]
  infer_instance

/-- **`𝓕 ⊗_R (-)` preserves colimits**, sheafification being a left adjoint as well.  This is
what turns a presentation of `M` into a presentation of `𝓕 ⊗_R M`. -/
instance tensorByBaseModule_preservesColimits :
    PreservesColimitsOfSize.{w, w} (tensorByBaseModule R hU₀ J O 𝓕 α) := by
  have h : PreservesColimitsOfSize.{w, w} (sheafify J O) :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O).obj)).leftAdjoint_preservesColimits
  dsimp only [tensorByBaseModule]
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The sections of the presheaf-level tensor product**: over an object `U` they are
`𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`, the two tensor products being the ones of the third and second
factor of the composite.  This holds by construction. -/
theorem tensorByBaseModulePresheaf_obj_obj (M : ModuleCat.{w} R) (X : Cᵒᵖ) :
    letI := coefficientAlgebra R hU₀ α X
    ((tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj M).obj X
      = ModuleCat.of (O.val.obj X) (𝓕.val.obj X ⊗[O.val.obj X] (O.val.obj X ⊗[R] M)) :=
  rfl

/-- **The sections of the presheaf-level tensor product, in closed form**: over an object `U`
they are canonically `𝓕(U) ⊗_R M` as an `O(U)`-module.  This is the cancellation of the base
change `O(U) ⊗_R (-)` against the tensor product over `O(U)`, and is the description a consumer
of `tensorByBaseModule` needs. -/
def sectionsEquiv (M : ModuleCat.{w} R) (X : Cᵒᵖ) :
    letI := coefficientAlgebra R hU₀ α X
    letI := sectionsModule R hU₀ α 𝓕.val X
    letI := isScalarTower_coefficient R hU₀ α 𝓕.val X
    ((tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj M).obj X ≃ₗ[O.val.obj X]
      (𝓕.val.obj X ⊗[R] M) :=
  let := coefficientAlgebra R hU₀ α X
  let := sectionsModule R hU₀ α 𝓕.val X
  let := isScalarTower_coefficient R hU₀ α 𝓕.val X
  TensorProduct.AlgebraTensorModule.cancelBaseChange R (O.val.obj X) (O.val.obj X)
    (𝓕.val.obj X) M

/-- The constant presheaf of modules sends the free module of rank one to the unit of the
monoidal structure on presheaves of modules over the constant presheaf of rings: both have `R`
as their sections over every object and identities as their restriction maps. -/
def constantModuleUnitIso :
    (constantModulePresheaf (C := C) R).obj (ModuleCat.of R R) ≅
      𝟙_ (PMod (constantRingPresheaf (C := C) R)) :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)
    (fun {_ _} _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- Extension of scalars sends the unit to the unit: `O(U) ⊗_R R ≅ O(U)`.  This is the
base-change unitor of `Stacks.PresheafOfModules.ChangeOfRings`, applied to the change-of-rings
adjunction. -/
def changeOfRingsUnitIso (θ : constantRingPresheaf (C := C) R ⟶ O.val) :
    (changeOfRings θ).obj (𝟙_ (PMod (constantRingPresheaf (C := C) R))) ≅ 𝟙_ (PMod O.val) :=
  baseChangeUnitor _ (changeOfRingsAdjunction θ)

/-- **The presheaf-level tensor product with the free module of rank one is `𝓕`.**  The three
factors in turn carry `R` to the unit, the unit to the unit, and `𝓕 ⊗ 𝟙` to `𝓕` by the right
unitor. -/
def tensorByBaseModulePresheafUnitIso :
    (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj (ModuleCat.of R R) ≅ 𝓕.val :=
  (tensorLeft 𝓕.val).mapIso
      ((changeOfRings (coefficientMap R hU₀ (O := O.val) α)).mapIso (constantModuleUnitIso R) ≪≫
        changeOfRingsUnitIso R J O (coefficientMap R hU₀ (O := O.val) α)) ≪≫
    ρ_ 𝓕.val

/-- **`𝓕 ⊗_R R ≅ 𝓕`.**  The value of `tensorByBaseModule` at the free module of rank one is
`𝓕` itself: the presheaf-level value is `𝓕.val` by `tensorByBaseModulePresheafUnitIso`, and
sheafifying the underlying presheaf of a sheaf of modules gives it back, the counit of the
sheafification adjunction being an isomorphism. -/
def tensorByBaseModuleUnitIso :
    (tensorByBaseModule R hU₀ J O 𝓕 α).obj (ModuleCat.of R R) ≅ 𝓕 :=
  (sheafify J O).mapIso (tensorByBaseModulePresheafUnitIso R hU₀ J O 𝓕 α) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).counit).app 𝓕

end Site

end Terminal


section OfHom

/-! ### The construction from a morphism of presheaves of rings

`Stacks.TensorByBaseModule.tensorByBaseModule` takes a terminal object of the site and a ring
homomorphism into its sections, and uses them only to build the morphism of presheaves of rings
`Stacks.TensorByBaseModule.coefficientMap`.  The small étale site of an algebraic space has a
terminal object only when the space is representable, so a consumer on a general algebraic space
cannot supply that data.  The versions below take the morphism of presheaves of rings directly,
and the terminal ones are their values at `coefficientMap`.
-/

variable (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})

/-- The ring homomorphism `R →+* O(U)` carried by a morphism of presheaves of rings
`θ : constantRingPresheaf R ⟶ O`, with `R` as its source type rather than the sections of
`constantRingPresheaf R` over `U`.  The two are definitionally equal; only this spelling lets
instance search find `Algebra R (O(U))`. -/
def coefficientRingHomOfHom (θ : constantRingPresheaf (C := C) R ⟶ O.val) (X : Cᵒᵖ) :
    R →+* O.val.obj X :=
  (θ.app X).hom

/-- The sections of `O` over `U` as an `R`-algebra, via `θ`. -/
@[instance_reducible]
def coefficientAlgebraOfHom (θ : constantRingPresheaf (C := C) R ⟶ O.val) (X : Cᵒᵖ) :
    Algebra R (O.val.obj X) :=
  (coefficientRingHomOfHom R J O θ X).toAlgebra

/-- The sections of a presheaf of `O`-modules over `U` as an `R`-module, by restriction of
scalars along `θ`. -/
@[instance_reducible]
def sectionsModuleOfHom (θ : constantRingPresheaf (C := C) R ⟶ O.val) (F : PMod O.val)
    (X : Cᵒᵖ) : Module R (F.obj X) :=
  Module.compHom (F.obj X) (coefficientRingHomOfHom R J O θ X)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The scalar actions of `R` and of `O(U)` on the sections of a presheaf of `O`-modules over
`U` form a tower. -/
theorem isScalarTowerOfHom (θ : constantRingPresheaf (C := C) R ⟶ O.val) (F : PMod O.val)
    (X : Cᵒᵖ) :
    letI := coefficientAlgebraOfHom R J O θ X
    letI := sectionsModuleOfHom R J O θ F X
    IsScalarTower R (O.val.obj X) (F.obj X) :=
  let := coefficientAlgebraOfHom R J O θ X
  let := sectionsModuleOfHom R J O θ F X
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **Tensoring `𝓕` by a module over the base ring, at the level of presheaves**, from a
morphism of presheaves of rings.  Over an object `U` it is `M ↦ 𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`. -/
def tensorByBaseModulePresheafOfHom (𝓕 : SheafOfModules.{w} (ringSheaf J O))
    (θ : constantRingPresheaf (C := C) R ⟶ O.val) :
    ModuleCat.{w} R ⥤ PMod O.val :=
  constantModulePresheaf (C := C) R ⋙ changeOfRings θ ⋙ tensorLeft 𝓕.val

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Tensoring `𝓕` by a module over the base ring**, from a morphism of presheaves of rings:
the presheaf-level tensor product, sheafified. -/
def tensorByBaseModuleOfHom (𝓕 : SheafOfModules.{w} (ringSheaf J O))
    (θ : constantRingPresheaf (C := C) R ⟶ O.val) :
    ModuleCat.{w} R ⥤ SheafOfModules.{w} (ringSheaf J O) :=
  tensorByBaseModulePresheafOfHom R J O 𝓕 θ ⋙ sheafify J O

variable (𝓕 : SheafOfModules.{w} (ringSheaf J O))
  (θ : constantRingPresheaf (C := C) R ⟶ O.val)

/-- The presheaf-level tensor functor is additive, each of its three factors being so. -/
instance tensorByBaseModulePresheafOfHom_additive :
    (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).Additive := by
  have h₁ : (restrictScalars θ).Additive :=
    { map_add := PresheafOfModules.hom_ext fun _ => rfl }
  have h₂ : (changeOfRings θ).Additive := (changeOfRingsAdjunction θ).left_adjoint_additive
  dsimp only [tensorByBaseModulePresheafOfHom]
  infer_instance

/-- **`𝓕 ⊗_R (-)` is additive**, in the form taking a morphism of presheaves of rings. -/
instance tensorByBaseModuleOfHom_additive :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).Additive := by
  dsimp only [tensorByBaseModuleOfHom]
  infer_instance

/-- The presheaf-level tensor functor preserves colimits: its first factor is
`constantModulePresheaf R`, which preserves all colimits by
`constantModulePresheaf_preservesColimitsOfSize`, and the other two are a left adjoint and a
functor with Mathlib's sectionwise colimit-preservation instance. -/
instance preservesColimitsOfSize_tensorByBaseModulePresheafOfHom :
    PreservesColimitsOfSize.{w, w} (tensorByBaseModulePresheafOfHom R J O 𝓕 θ) := by
  have h : PreservesColimitsOfSize.{w, w} (changeOfRings θ) :=
    (changeOfRingsAdjunction θ).leftAdjoint_preservesColimits
  dsimp only [tensorByBaseModulePresheafOfHom]
  infer_instance

/-- **`𝓕 ⊗_R (-)` preserves colimits**, sheafification being a left adjoint as well.  Nothing
is assumed: this is unconditional on the site and on the morphism of presheaves of rings. -/
instance preservesColimitsOfSize_tensorByBaseModuleOfHom :
    PreservesColimitsOfSize.{w, w} (tensorByBaseModuleOfHom R J O 𝓕 θ) := by
  have h : PreservesColimitsOfSize.{w, w} (sheafify J O) :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O).obj)).leftAdjoint_preservesColimits
  dsimp only [tensorByBaseModuleOfHom]
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The sections of the presheaf-level tensor product**: over an object `U` they are
`𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`.  This holds by construction. -/
theorem tensorByBaseModulePresheafOfHom_obj_obj (M : ModuleCat.{w} R) (X : Cᵒᵖ) :
    letI := coefficientAlgebraOfHom R J O θ X
    ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M).obj X
      = ModuleCat.of (O.val.obj X) (𝓕.val.obj X ⊗[O.val.obj X] (O.val.obj X ⊗[R] M)) :=
  rfl

/-- **The sections of the presheaf-level tensor product, in closed form**: over an object `U`
they are canonically `𝓕(U) ⊗_R M` as an `O(U)`-module, by cancellation of the base change. -/
def sectionsEquivOfHom (M : ModuleCat.{w} R) (X : Cᵒᵖ) :
    letI := coefficientAlgebraOfHom R J O θ X
    letI := sectionsModuleOfHom R J O θ 𝓕.val X
    letI := isScalarTowerOfHom R J O θ 𝓕.val X
    ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M).obj X ≃ₗ[O.val.obj X]
      (𝓕.val.obj X ⊗[R] M) :=
  let := coefficientAlgebraOfHom R J O θ X
  let := sectionsModuleOfHom R J O θ 𝓕.val X
  let := isScalarTowerOfHom R J O θ 𝓕.val X
  TensorProduct.AlgebraTensorModule.cancelBaseChange R (O.val.obj X) (O.val.obj X)
    (𝓕.val.obj X) M

/-- **The presheaf-level tensor product with the free module of rank one is `𝓕`.** -/
def tensorByBaseModulePresheafOfHomUnitIso :
    (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj (ModuleCat.of R R) ≅ 𝓕.val :=
  (tensorLeft 𝓕.val).mapIso
      ((changeOfRings θ).mapIso (constantModuleUnitIso R) ≪≫
        changeOfRingsUnitIso R J O θ) ≪≫
    ρ_ 𝓕.val

/-- **`𝓕 ⊗_R R ≅ 𝓕`**, in the form taking a morphism of presheaves of rings. -/
def tensorByBaseModuleOfHomUnitIso :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).obj (ModuleCat.of R R) ≅ 𝓕 :=
  (sheafify J O).mapIso (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).counit).app 𝓕

end OfHom

end Stacks.TensorByBaseModule
