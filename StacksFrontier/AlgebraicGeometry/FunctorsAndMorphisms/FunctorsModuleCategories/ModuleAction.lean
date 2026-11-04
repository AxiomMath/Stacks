module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.FinitelyPresented
public import StacksCore.Tactic.StacksAttribute

/-!
# Finitely presented right modules, and objects with a ring action

A right exact functor from finitely presented right `A`-modules to an additive category with
cokernels is determined by its value on the rank-one free module together with the action of
`A` on that value. This file sets up the two categories involved and the evaluation functor
between them, and records that right exactness forces additivity here.

## Main definitions

* `ModuleCat.FPModule` is the category of finitely presented right `A`-modules.
* `ModuleCat.ModuleAction` is the category of objects of `B` equipped with an action of `A`.
* `ModuleCat.regularModule`, `ModuleCat.regularEnd` and `ModuleCat.regularAction` are the
  rank-one free right module, multiplication by a scalar on it, and the resulting action.
* `ModuleCat.evaluationFunctor` evaluates a right exact functor on the rank-one free module,
  with its natural action.

## Main results

* `ModuleCat.rightExactFunctor_additive`: a right exact functor out of `FPModule A` is additive.
* `ModuleCat.finitePresentation_closedUnderFiniteCoproducts`,
  `ModuleCat.finitePresentation_closedUnderCokernels` and
  `ModuleCat.fpModuleInclusion_preservesFiniteColimits`: the finitely presented modules are
  closed under finite coproducts and cokernels, so their inclusion is right exact.

## Implementation notes

The Stacks Project's category `Mod_A^{fp}` of finitely presented right `A`-modules is
represented as the full subcategory `ModuleCat.FinitelyPresentedModuleCat` of left
`Aᵐᵒᵖ`-modules, which allows arbitrary, not necessarily commutative, rings. Right exact
functors are Mathlib's `CategoryTheory.RightExactFunctor`. The category of pairs `(K, κ)` is
presented directly, including its equivariant morphisms, so that the comparison with right
exact functors can be the canonical evaluation functor rather than an unspecified equivalence.

## References

* [Stacks Project, Tag 0GNN](https://stacks.math.columbia.edu/tag/0GNN)
-/

@[expose] public section

namespace ModuleCat

universe w v u

open CategoryTheory CategoryTheory.Limits

/-- The category of finitely presented `A`-modules. -/
public abbrev FPModule (A : Type u) [Ring A] :=
  FinitelyPresentedModuleCat.{u, u} Aᵐᵒᵖ

/-- An object of `B` endowed with an action of the ring `A`. -/
public structure ModuleAction (A : Type u) (B : Type v) [Ring A] [Category.{w} B]
    [Preadditive B] where
  /-- The underlying object. -/
  carrier : B
  /-- The ring action on the underlying object. -/
  action : A →+* End carrier

namespace ModuleAction

variable {A : Type u} {B : Type v} [Ring A] [Category.{w} B] [Preadditive B]

/-- An equivariant morphism between objects with `A`-action. -/
@[ext]
public structure Hom (X Y : ModuleAction A B) where
  /-- The underlying morphism. -/
  hom : X.carrier ⟶ Y.carrier
  comm : ∀ a : A, X.action a ≫ hom = hom ≫ Y.action a := by aesop_cat

/-- Objects with `A`-action form a category, with equivariant morphisms as morphisms. -/
public instance : Category.{w} (ModuleAction A B) where
  Hom := Hom
  id X := ⟨𝟙 X.carrier, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    intro a
    rw [← Category.assoc, f.comm a, Category.assoc, g.comm a, ← Category.assoc]⟩
  id_comp := by intros; ext; simp
  comp_id := by intros; ext; simp
  assoc := by intros; apply Hom.ext; apply Category.assoc

end ModuleAction

/-- The finite product `∀ i, M i` of modules, as a cofan whose inclusions are the maps
`LinearMap.single`. -/
public def modulePiCofan {R : Type u} [Ring R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ModuleCat.{u} R) : Cofan M :=
  Cofan.mk (ModuleCat.of R (∀ i, M i))
    (fun i ↦ ModuleCat.ofHom (LinearMap.single R (fun j ↦ M j) i))

/-- A finite product of modules, with its `LinearMap.single` inclusions, is a coproduct. -/
public def modulePiCofanIsColimit {R : Type u} [Ring R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (M : ι → ModuleCat.{u} R) :
    IsColimit (modulePiCofan M) := by
  refine Cofan.IsColimit.mk _
    (fun t ↦ ModuleCat.ofHom (∑ i, (t.inj i).hom.comp (LinearMap.proj i))) ?_ ?_
  · intro t i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp [modulePiCofan, Pi.single, Function.update, apply_dite]
  · intro t m hm
    apply ModuleCat.hom_ext
    apply LinearMap.pi_ext (φ := fun i ↦ M i)
    intro i a
    have hi : m.hom (Pi.single i a) = (t.inj i).hom a :=
      congrArg (fun f ↦ f.hom a) (hm i)
    change m.hom (Pi.single i a) =
      (∑ j, (t.inj j).hom.comp (LinearMap.proj j)) (Pi.single i a)
    simpa [LinearMap.sum_apply, Pi.single, Function.update, apply_dite] using hi

/-- A colimit of a diagram with a finitely presented colimit is finitely presented. -/
private theorem finitelyPresentedModule_of_isColimit {R : Type u} [Ring R] {J : Type*}
    [Category J] {F : J ⥤ ModuleCat.{u} R} {c c' : Cocone F} (hc : IsColimit c)
    (hc' : IsColimit c') [Module.FinitePresentation R c.pt] :
    finitelyPresentedModule.{u, u} R c'.pt :=
  (finitelyPresentedModule_iff R _).2
    (Module.FinitePresentation.of_equiv (Iso.toLinearEquiv (hc.coconePointUniqueUpToIso hc')))

/-- Finitely presented right `A`-modules are closed under finite coproducts. -/
public lemma finitePresentation_closedUnderFiniteCoproducts (A : Type u) [Ring A] :
    ObjectProperty.IsClosedUnderFiniteCoproducts
      (finitelyPresentedModule.{u, u} Aᵐᵒᵖ) where
  isClosedUnderColimitsOfShape J _ := by
    classical
    let := Fintype.ofFinite J
    refine ⟨?_⟩
    rintro X ⟨p⟩
    let (j : J) : Module.FinitePresentation Aᵐᵒᵖ (p.diag.obj ⟨j⟩) :=
      (finitelyPresentedModule_iff Aᵐᵒᵖ _).1 (p.prop_diag_obj ⟨j⟩)
    have hc : IsColimit (Cofan.mk X (fun j : J ↦ p.ι.app ⟨j⟩)) := by
      refine Cofan.IsColimit.mk _ (fun s ↦ p.isColimit.desc
        ⟨s.pt, Discrete.natTrans (fun j ↦ s.inj j.as)⟩) ?_ ?_
      · intro s j
        exact p.isColimit.fac _ ⟨j⟩
      · intro s m hm
        apply p.isColimit.hom_ext
        rintro ⟨j⟩
        exact (hm j).trans (p.isColimit.fac
          ⟨s.pt, Discrete.natTrans (fun j ↦ s.inj j.as)⟩ ⟨j⟩).symm
    let : Module.FinitePresentation Aᵐᵒᵖ
        (modulePiCofan (fun j : J ↦ p.diag.obj ⟨j⟩)).pt := by
      show Module.FinitePresentation Aᵐᵒᵖ (∀ j : J, p.diag.obj ⟨j⟩)
      infer_instance
    exact finitelyPresentedModule_of_isColimit
      (modulePiCofanIsColimit (fun j : J ↦ p.diag.obj ⟨j⟩)) hc

/-- Finitely presented right `A`-modules are closed under cokernels. -/
public lemma finitePresentation_closedUnderCokernels (A : Type u) [Ring A] :
    ObjectProperty.IsClosedUnderCokernels
      (finitelyPresentedModule.{u, u} Aᵐᵒᵖ) where
  cokernels_le := by
    rintro Z ⟨f, k, hk, hX, hY⟩
    let : Module.FinitePresentation Aᵐᵒᵖ _ := (finitelyPresentedModule_iff Aᵐᵒᵖ _).1 hX
    let : Module.FinitePresentation Aᵐᵒᵖ _ := (finitelyPresentedModule_iff Aᵐᵒᵖ _).1 hY
    have hQ : Module.FinitePresentation Aᵐᵒᵖ (_ ⧸ f.hom.range) :=
      Module.finitePresentation_of_surjective f.hom.range.mkQ f.hom.range.mkQ_surjective
        (by simp)
    let : Module.FinitePresentation Aᵐᵒᵖ (ModuleCat.cokernelCocone f).pt := hQ
    exact finitelyPresentedModule_of_isColimit (ModuleCat.cokernelIsColimit f) hk

/-- The inclusion of finitely presented right `A`-modules into all right `A`-modules
preserves finite colimits. -/
public lemma fpModuleInclusion_preservesFiniteColimits (A : Type u) [Ring A] :
    PreservesFiniteColimits (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι := by
  let := finitePresentation_closedUnderCokernels A
  let := finitePresentation_closedUnderFiniteCoproducts A
  let : HasFiniteBiproducts (FPModule A) := HasFiniteBiproducts.of_hasFiniteCoproducts
  let : HasBinaryBiproducts (FPModule A) := HasBinaryBiproducts.of_hasBinaryCoproducts
  let : HasCoequalizers (FPModule A) := Preadditive.hasCoequalizers_of_hasCokernels
  let {X Y : FPModule A} (f : X ⟶ Y) :
      PreservesColimit (parallelPair f 0) (ObjectProperty.ι _) :=
    ObjectProperty.preservesCokernels_ι _ f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

/-- The rank-one free module, regarded as a finitely presented module. -/
public abbrev regularModule (A : Type u) [Ring A] : FPModule A := by
  let e : Aᵐᵒᵖ ≃ₗ[Aᵐᵒᵖ] A :=
    { toFun := MulOpposite.unop
      invFun := MulOpposite.op
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact ⟨ModuleCat.of Aᵐᵒᵖ A, Module.FinitePresentation.of_equiv e⟩

/-- Multiplication by an element of `A` on the rank-one free module. -/
public def regularEnd (A : Type u) [Ring A] (a : A) : End (regularModule A) :=
  InducedCategory.homMk (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a))

/-- The natural action of `A` on its rank-one free module. -/
public def regularAction (A : Type u) [Ring A] : A →+* End (regularModule A) where
  toFun := regularEnd A
  map_one' := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    ext
    simp [regularEnd]
  map_mul' a b := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    ext
    simp [regularEnd]
  map_zero' := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    ext
    simp [regularEnd]
  map_add' a b := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact add_mul a b x

/-- A right exact functor on finitely presented modules is automatically additive. -/
@[stacks 0GNN "automatic additivity"]
public lemma rightExactFunctor_additive (A : Type u) (B : Type v) [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B]
    (F : FPModule A ⥤ᵣ B) : F.obj.Additive := by
  let := finitePresentation_closedUnderFiniteCoproducts A
  let : HasFiniteCoproducts (FPModule A) := inferInstance
  let : HasZeroObject (FPModule A) :=
    Preadditive.hasZeroObject_of_hasCoproduct.{u, u, u + 1} (C := FPModule A)
  let : HasBinaryBiproducts (FPModule A) := HasBinaryBiproducts.of_hasBinaryCoproducts
  exact (rightExactFunctor_le_additiveFunctor (FPModule A) B F.obj) F.property

/-- Evaluation at `A`, with its natural `A`-action, is an equivalence from right exact functors
on finitely presented `A`-modules to objects equipped with an `A`-action.  Its action on a
natural transformation is its component at `A`. -/
public def evaluationFunctor (A : Type u) (B : Type v) [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] :
    Functor (FPModule A ⥤ᵣ B) (ModuleAction A B) where
  obj F :=
    let G : Functor (FPModule A) B := F.obj
    letI : G.Additive := rightExactFunctor_additive A B F
    { carrier := G.obj (regularModule A)
      action :=
        ({ G.mapEnd (regularModule A) with
            map_zero' := G.map_zero _ _
            map_add' := fun _ _ ↦ G.map_add } :
          End (regularModule A) →+* End (G.obj (regularModule A))).comp
            (regularAction A) }
  map η :=
    { hom := η.hom.app (regularModule A)
      comm := fun a ↦ by
        dsimp
        exact η.hom.naturality (regularEnd A a) }
  map_id F := by
    apply ModuleAction.Hom.ext
    rfl
  map_comp f g := by
    apply ModuleAction.Hom.ext
    rfl

end ModuleCat
