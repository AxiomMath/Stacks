module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModule

/-!
# `𝓕 ⊗_R (-)` as an `R`-linear functor, and gluing a comparison into it

Let `(C, J)` be a site with a terminal object `U₀`, let `O` be a sheaf of commutative rings on
it, let `R` be a commutative ring with a ring homomorphism `α : R → O(U₀)` and let `𝓕` be a
sheaf of `O`-modules.  `Stacks.TensorByBaseModule.tensorByBaseModule` is the functor
`M ↦ 𝓕 ⊗_R M : ModuleCat R ⥤ SheafOfModules O`, built as the sheafification of the presheaf
`U ↦ 𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`.  This file supplies the two things a consumer of that functor
needs and which its own file declines to provide.

**It is `R`-linear.**  The scalar action of `R` on morphisms of sheaves of `O`-modules is
multiplication by the image of the scalar in `O(U₀)`, which is the `R`-linear structure
`Stacks.SheafOfModules.linearOfTerminalSection` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BaseRingLinear.lean`; and the functor carries
`r • φ` to `r • 𝓕 ⊗ φ`.  This is what an `R`-linear dévissage along
`Stacks.FlatDevissage.isIso_tensorComparisonUniv_app_of_flat` asks of the functor, and the
implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorByBaseModule.lean` record it as absent:
"An `R`-linear structure on the composite is *not* provided".  The obstruction recorded there —
that the action of `R` on morphisms of presheaves of modules over the *constant* presheaf of
rings is not reachable by instance search — is avoided by not asking for it: linearity is proved
directly, from the single identity `r • φ = φ ≫ (r • 𝟙)` in `ModuleCat R` and the fact that each
of the three presheaf-level factors carries multiplication by a scalar to multiplication by its
image (`Stacks.TensorByBaseModule.presheafMult`).

**A locally bijective comparison into a sheaf of modules identifies that sheaf with
`𝓕 ⊗_R M`.**  `Stacks.TensorByBaseModule.tensorByBaseModuleIso` turns a morphism of presheaves
of `O`-modules `Φ : 𝓕 ⊗_{O} (O ⊗_R M) ⟶ G.val` whose underlying morphism of presheaves of
abelian groups is locally bijective into an isomorphism
`(tensorByBaseModule R hU₀ J O 𝓕 α).obj M ≅ G`, and
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveApp` reduces local bijectivity to
bijectivity of `Φ` on the sections over a family of objects whose arrows generate covering
sieves — the affine objects of a site of charts, say.  This is the gluing step of the second
part of [Stacks Project, Tag 073K]: `g'_*ℱ' = ℱ ⊗_A B` is checked over affine charts and glued.

## Main definitions

* `Stacks.Presheaf.isLocallyInjective_of_injective_app` and
  `Stacks.Presheaf.isLocallySurjective_of_surjective_app`: a morphism of presheaves of abelian
  groups which is injective (resp. surjective) on the sections over the objects of a family
  whose arrows generate covering sieves is locally injective (resp. locally surjective).
* `Stacks.TensorByBaseModule.presheafMult`: multiplication by a section of `O` over the
  terminal object, as an endomorphism of a presheaf of `O`-modules.
* `Stacks.TensorByBaseModule.linearOfCoefficientMap`: the `R`-linear structure on sheaves of
  `O`-modules attached to `α`.

## Main results

* `Stacks.TensorByBaseModule.presheafMult_comp`: multiplication by a section over the terminal
  object is central — it commutes with every morphism of presheaves of `O`-modules.
* `Stacks.TensorByBaseModule.tensorByBaseModulePresheaf_map_smul`: the presheaf-level tensor
  functor carries `r • φ` to multiplication by `α r` followed by `𝓕 ⊗ φ`.
* `Stacks.TensorByBaseModule.sheafify_map_presheafMult`: sheafification carries multiplication
  by a section over the terminal object to multiplication by that section.
* `Stacks.TensorByBaseModule.tensorByBaseModule_linear`: **`𝓕 ⊗_R (-)` is `R`-linear.**
* `Stacks.TensorByBaseModule.tensorByBaseModuleIso` and
  `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveApp`: **a locally bijective
  comparison exhibits a sheaf of `O`-modules as `𝓕 ⊗_R M`.**

## Implementation notes

*Why linearity is proved through `r • 𝟙` and not through `r • φ` directly.*  The three factors
of `tensorByBaseModulePresheaf` are the constant presheaf of modules, extension of scalars along
`Stacks.TensorByBaseModule.coefficientMap` and the sectionwise tensor product with `𝓕`.  For the
middle factor the identity `(1 ⊗ (r • x)) = α(r) • (1 ⊗ x)` is a statement about a *single* pure
tensor and is reached through the change-of-rings hom-set bijection
`Stacks.PresheafOfModules.ChangeOfRings.homEquivCore`, which turns an equality of morphisms out
of `O ⊗_R M` into an equality on the elements `1 ⊗ x`; at `r • φ` for a general `φ` the same
computation needs an induction over the tensor product, and there the module instances on
`Stacks.PresheafOfModules.ChangeOfRings.cofObj` are no longer determined by unification — the
goal is not type-correct at `implicit` transparency after the induction and `rw` refuses it.
Factoring `r • φ = φ ≫ (r • 𝟙)` first removes the general `φ` from the computation.

*The scalar is introduced as a `let`, not a `have`.*  The ring of sections of
`Stacks.TensorByBaseModule.constantRingPresheaf R` over an object is `R` itself, but not
syntactically, and the tensor products of the change of rings are formed over the first
spelling.  A scalar of the second spelling is therefore reintroduced at the first; with `have`
the reintroduction is opaque and the definitional checks below fail, so `let` is used.

*Sheafification is applied to `presheafMult` through the adjunction, not computed.*  The
sheafification of a presheaf of modules has no description on sections, so
`Stacks.TensorByBaseModule.sheafify_map_presheafMult` is proved by transposing both sides along
`PresheafOfModules.sheafificationAdjunction`: the transpose of the sheafified multiplication is
the multiplication followed by the unit, by naturality of the unit, and the transpose of the
multiplication on the sheafification is the unit followed by the multiplication, which is the
same morphism because multiplication by a section over the terminal object is central.

*The gluing is stated for the comparison, not for an abstract isomorphism.*  An isomorphism of
the sections over each object of a covering family cannot be glued: the gluing is the assertion
that one morphism of presheaves is locally bijective, and a family of unrelated isomorphisms
carries no compatibility.  What the statements below ask for is therefore bijectivity of a given
`Φ` over the objects of the family, which is exactly what a canonical comparison provides.

No declaration here carries a `stacks` tag: this is the linear and the gluing input to the
second part of Tag 073K rather than an assertion of any tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits MonoidalCategory TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe v u w

namespace Stacks.Presheaf

variable {C : Type u} [Category.{v} C]

section LocalBijectivity

variable (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : F ⟶ G)
  (P : C → Prop)
  (hcov : ∀ X : C, Sieve.generate (fun {W : C} (_ : W ⟶ X) => P W) ∈ J X)

include hcov

/-- **A morphism of presheaves of abelian groups injective on the sections over a family of
objects whose arrows generate covering sieves is locally injective.** -/
theorem isLocallyInjective_of_injective_app
    (hinj : ∀ W : C, P W → Function.Injective (φ.app (op W))) :
    Presheaf.IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := by
    refine J.superset_covering ?_ (hcov X.unop)
    rintro Z g ⟨W, i, f, hW, rfl⟩
    show F.map (i ≫ f).op x = F.map (i ≫ f).op y
    rw [op_comp, F.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    refine congrArg (F.map i.op) (hinj W hW ?_)
    rw [NatTrans.naturality_apply φ, NatTrans.naturality_apply φ, h]

/-- **A morphism of presheaves of abelian groups surjective on the sections over a family of
objects whose arrows generate covering sieves is locally surjective.** -/
theorem isLocallySurjective_of_surjective_app
    (hsurj : ∀ W : C, P W → Function.Surjective (φ.app (op W))) :
    Presheaf.IsLocallySurjective J φ where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (hcov U)
    rintro Z g ⟨W, i, f, hW, rfl⟩
    obtain ⟨t, ht⟩ := hsurj W hW (G.map f.op s)
    refine ⟨F.map i.op t, ?_⟩
    rw [NatTrans.naturality_apply φ, ht, op_comp, G.map_comp, ConcreteCategory.comp_apply]

end LocalBijectivity

end Stacks.Presheaf

namespace Stacks.TensorByBaseModule

open Stacks.Presheaf (isLocallyInjective_of_injective_app isLocallySurjective_of_surjective_app)

variable {C : Type u} [Category.{v} C]

section Mult

variable {U₀ : C} (hU₀ : IsTerminal U₀) (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Multiplication by a section over a terminal object, on a presheaf of modules. -/
def presheafMult (a : O.obj (op U₀)) (N : PMod O) : N ⟶ N where
  app X := ModuleCat.ofHom
    { toFun := fun x => (O.map (hU₀.from X.unop).op a) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => by
        dsimp
        rw [smul_comm] }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (O.map (hU₀.from Y.unop).op a) • N.map f x
      = N.map f ((O.map (hU₀.from X.unop).op a) • x)
    rw [PresheafOfModules.map_smul]
    congr 1
    change _ = ((ringPresheaf O).map f).hom _
    rw [← op_from_comp hU₀ f]
    change _ = ((O.map (hU₀.from X.unop).op) ≫ (O.map f)).hom a
    rw [← O.map_comp]

/-- On sections over `X`, `presheafMult hU₀ O a N` is scalar multiplication by the restriction
of `a` to `X`. -/
@[simp]
theorem presheafMult_app_apply (a : O.obj (op U₀)) (N : PMod O) (X : Cᵒᵖ) (x : N.obj X) :
    ((presheafMult hU₀ O a N).app X).hom x = (O.map (hU₀.from X.unop).op a) • x :=
  rfl

/-- Multiplication by a section over the terminal object commutes with every morphism. -/
theorem presheafMult_comp (a : O.obj (op U₀)) {N N' : PMod O} (f : N ⟶ N') :
    presheafMult hU₀ O a N ≫ f = f ≫ presheafMult hU₀ O a N' := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show (f.app X).hom ((O.map (hU₀.from X.unop).op a) • x)
    = (O.map (hU₀.from X.unop).op a) • (f.app X).hom x
  exact (f.app X).hom.map_smul _ x

end Mult


section Site

variable (R : Type w) [CommRing R] {U₀ : C} (hU₀ : IsTerminal U₀)
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})
  (𝓕 : SheafOfModules.{w} (ringSheaf J O)) (α : R →+* O.val.obj (op U₀))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sections of the presheaf-level tensor functor on a morphism, on a pure tensor. -/
theorem tensorByBaseModulePresheaf_map_app_tmul {M N : ModuleCat.{w} R} (ψ : M ⟶ N) (X : Cᵒᵖ)
    (s : 𝓕.val.obj X) (b : O.val.obj X)
    (m : ((constantModulePresheaf (C := C) R).obj M).obj X) :
    letI := ((coefficientMap R hU₀ (O := O.val) α).app X).hom.toAlgebra
    (((tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).map ψ).app X).hom
        (s ⊗ₜ[O.val.obj X] (b ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] m))
      = s ⊗ₜ[O.val.obj X] (b ⊗ₜ[(constantRingPresheaf (C := C) R).obj X]
          (((constantModulePresheaf (C := C) R).map ψ).app X).hom m) := by
  let := ((coefficientMap R hU₀ (O := O.obj) α).app X).hom.toAlgebra
  show (𝓕.val.obj X ◁ ((changeOfRings (coefficientMap R hU₀ (O := O.obj) α)).map
      ((constantModulePresheaf (C := C) R).map ψ)).app X).hom _ = _
  exact congrArg (fun y => s ⊗ₜ[O.obj.obj X] y) (cofHom_app_tmul _ _ X b m)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Tensoring on the left with a fixed presheaf of modules commutes with multiplication by a
section over the terminal object. -/
theorem tensorLeft_map_presheafMult (F : PMod O.val) (a : O.val.obj (op U₀)) (N : PMod O.val) :
    (tensorLeft F).map (presheafMult hU₀ O.val a N)
      = presheafMult hU₀ O.val a ((tensorLeft F).obj N) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  refine ModuleCat.hom_ext (TensorProduct.ext' fun s t => ?_)
  show s ⊗ₜ[O.obj.obj X] ((O.obj.map (hU₀.from X.unop).op a) • t)
    = (O.obj.map (hU₀.from X.unop).op a) • (s ⊗ₜ[O.obj.obj X] t)
  exact TensorProduct.tmul_smul _ s t

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Extension of scalars along the coefficient map carries the action of a scalar on the
identity to multiplication by the image of that scalar. -/
theorem changeOfRings_constantModulePresheaf_map_smul_id (N : ModuleCat.{w} R) (r : R) :
    (changeOfRings (coefficientMap R hU₀ (O := O.val) α)).map
        ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))
      = presheafMult hU₀ O.val (α r)
          ((changeOfRings (coefficientMap R hU₀ (O := O.val) α)).obj
            ((constantModulePresheaf (C := C) R).obj N)) := by
  refine (homEquivCore (coefficientMap R hU₀ (O := O.obj) α) _ _).injective ?_
  refine PresheafOfModules.hom_ext fun X => ?_
  let := ((coefficientMap R hU₀ (O := O.obj) α).app X).hom.toAlgebra
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let r' : ((constantRingPresheaf (C := C) R).obj X : Type w) := r
  have hc : (O.obj.map (hU₀.from X.unop).op (α r) : O.obj.obj X)
      = r' • (1 : O.obj.obj X) := by
    rw [Algebra.smul_def, mul_one,
      show algebraMap ((constantRingPresheaf (C := C) R).obj X : Type w) (O.obj.obj X)
          = ((coefficientMap R hU₀ (O := O.obj) α).app X).hom from rfl,
      coefficientMap_app]
    rfl
  have h1 : (O.obj.map (hU₀.from X.unop).op (α r)) •
        ((1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] x)
      = (1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] (r' • x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hc, TensorProduct.smul_tmul]
  show (unitApp (coefficientMap R hU₀ (O := O.obj) α)
      ((changeOfRings (coefficientMap R hU₀ (O := O.obj) α)).map
        ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))) X).hom x
    = (unitApp (coefficientMap R hU₀ (O := O.obj) α)
      (presheafMult hU₀ O.obj (α r) _) X).hom x
  rw [unitApp_apply, unitApp_apply]
  show _ = (O.obj.map (hU₀.from X.unop).op (α r)) •
      ((1 : O.obj.obj X) ⊗ₜ[(constantRingPresheaf (C := C) R).obj X] x)
  rw [h1]
  refine (cofHom_app_tmul _ _ X 1 x).trans (congrArg _ ?_)
  show (r • 𝟙 N).hom x = r' • x
  rw [ModuleCat.hom_smul]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The presheaf-level tensor functor carries the action of a scalar on the identity to
multiplication by the image of that scalar. -/
theorem tensorByBaseModulePresheaf_map_smul_id (N : ModuleCat.{w} R) (r : R) :
    (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).map (r • 𝟙 N)
      = presheafMult hU₀ O.val (α r) ((tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj N) := by
  show (tensorLeft 𝓕.val).map ((changeOfRings (coefficientMap R hU₀ (O := O.obj) α)).map
      ((constantModulePresheaf (C := C) R).map (r • 𝟙 N))) = _
  rw [changeOfRings_constantModulePresheaf_map_smul_id, tensorLeft_map_presheafMult]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The presheaf-level tensor functor carries the action of a scalar on a morphism of modules
to multiplication by the image of that scalar.** -/
theorem tensorByBaseModulePresheaf_map_smul {M N : ModuleCat.{w} R} (r : R) (φ : M ⟶ N) :
    (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).map (r • φ) =
      presheafMult hU₀ O.val (α r) ((tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj M) ≫
        (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).map φ := by
  have key : r • φ = φ ≫ (r • 𝟙 N) := by
    rw [Linear.comp_smul, Category.comp_id]
  rw [key, Functor.map_comp, tensorByBaseModulePresheaf_map_smul_id, presheafMult_comp]

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Multiplication by a section over the terminal object, on a sheaf of modules, is
multiplication by that section on the underlying presheaf. -/
theorem forget_map_terminalSectionToEnd (a : O.val.obj (op U₀))
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map
        ((Stacks.SheafOfModules.terminalSectionToEnd (ringSheaf J O) U₀ hU₀ a).app G)
      = presheafMult hU₀ O.val a
        ((SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj G) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Sheafification carries multiplication by a section over the terminal object to
multiplication by that section.** -/
theorem sheafify_map_presheafMult (a : O.val.obj (op U₀)) (N : PMod O.val) :
    (sheafify J O).map (presheafMult hU₀ O.val a N)
      = (Stacks.SheafOfModules.terminalSectionToEnd (ringSheaf J O) U₀ hU₀ a).app
        ((sheafify J O).obj N) := by
  show (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map
      (presheafMult hU₀ O.obj a N)
    = (Stacks.SheafOfModules.terminalSectionToEnd (ringSheaf J O) U₀ hU₀ a).app
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).obj N)
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf J O).obj)).homEquiv N _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, forget_map_terminalSectionToEnd]
  exact Eq.trans
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).unit.naturality
      (presheafMult hU₀ O.obj a N)).symm)
    (presheafMult_comp hU₀ O.obj a
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).unit.app N))

/-- The `R`-linear structure on sheaves of `O`-modules attached to the coefficient map `α`:
a scalar acts by multiplication by its image, a section of `O` over the terminal object. -/
@[instance_reducible]
def linearOfCoefficientMap : Linear R (SheafOfModules.{w} (ringSheaf J O)) :=
  Stacks.SheafOfModules.linearOfTerminalSection (ringSheaf J O) R U₀ hU₀ α

/-- **`𝓕 ⊗_R (-)` is `R`-linear.** -/
@[instance_reducible]
def tensorByBaseModule_linear :
    letI := linearOfCoefficientMap R hU₀ J O α
    Functor.Linear R (tensorByBaseModule R hU₀ J O 𝓕 α) := by
  let := linearOfCoefficientMap R hU₀ J O α
  refine ⟨fun {M N} φ r => ?_⟩
  change (sheafify J O).map ((tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).map (r • φ)) = _
  rw [tensorByBaseModulePresheaf_map_smul, Functor.map_comp, sheafify_map_presheafMult]
  rfl

/-! ### Gluing a comparison into the tensor product -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A locally bijective comparison out of the presheaf-level tensor product sheafifies to an
isomorphism.** -/
theorem isIso_sheafificationHomEquiv_symm (M : ModuleCat.{w} R)
    (G : SheafOfModules.{w} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj M ⟶
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
  show IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ) ≫
    (sheafificationAdjunction J AddCommGrpCat.{w}).counit.app
      ((SheafOfModules.toSheaf (ringSheaf J O)).obj G))
  exact IsIso.comp_isIso' hiso (isIso_sheafificationAdjunction_counit _)

/-- **`𝓕 ⊗_R M ≅ G`**: a sheaf of `O`-modules receiving a locally bijective comparison from the
presheaf `U ↦ 𝓕(U) ⊗_R M` *is* the value of `Stacks.TensorByBaseModule.tensorByBaseModule` at
`M`.  This is the gluing step: the comparison itself need only be locally bijective — no
isomorphism of sections over a single object is asked for, and conversely a chart-wise
isomorphism that is not the comparison cannot be used. -/
noncomputable def tensorByBaseModuleIso (M : ModuleCat.{w} R)
    (G : SheafOfModules.{w} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    [Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)]
    [Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)] :
    (tensorByBaseModule R hU₀ J O 𝓕 α).obj M ≅ G :=
  @asIso _ _ _ _ ((PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ)
    (isIso_sheafificationHomEquiv_symm R hU₀ J O 𝓕 α M G Φ)

/-- **`𝓕 ⊗_R M ≅ G` from bijectivity on the sections over a covering family of objects.**  This
is the form in which the geometric chain uses the gluing step: the comparison is checked on the
*affine* objects of the site, which generate covering sieves of every object. -/
noncomputable def tensorByBaseModuleIsoOfBijectiveApp (M : ModuleCat.{w} R)
    (G : SheafOfModules.{w} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheaf R hU₀ J O 𝓕 α).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    (P : C → Prop)
    (hcov : ∀ X : C, Sieve.generate (fun {W : C} (_ : W ⟶ X) => P W) ∈ J X)
    (hbij : ∀ W : C, P W → Function.Bijective (Φ.app (op W)).hom) :
    (tensorByBaseModule R hU₀ J O 𝓕 α).obj M ≅ G :=
  haveI := isLocallyInjective_of_injective_app J
    ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ) P hcov
    (fun W hW => (hbij W hW).1)
  haveI := isLocallySurjective_of_surjective_app J
    ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ) P hcov
    (fun W hW => (hbij W hW).2)
  tensorByBaseModuleIso R hU₀ J O 𝓕 α M G Φ

end Sheafify

end Site

end Stacks.TensorByBaseModule

end
