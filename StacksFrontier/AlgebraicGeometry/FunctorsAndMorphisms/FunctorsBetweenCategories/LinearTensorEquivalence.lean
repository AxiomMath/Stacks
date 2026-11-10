module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.BimoduleTensor
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.TensorFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Linear right exact functors between module categories are bimodules

Let `A` and `B` be algebras over a commutative ring `R`. The category of `R`-linear right exact
functors from `A`-modules to `B`-modules which preserve arbitrary direct sums is equivalent to
the category of modules over `A ⊗[R] B`.

## Main definitions

* `ModuleCat.IsLinearRightExactAndPreservesDirectSums` cuts out the relevant full subcategory of
  the functor category.
* `ModuleCat.moduleTensorFunctor` sends an `A ⊗[R] B`-module to its tensor functor, and
  `ModuleCat.moduleTensorFunctorLift` lifts it to that full subcategory.
* `ModuleCat.tensorFunctorEquivalence` is the resulting equivalence.

## Main results

* `ModuleCat.tensorFunctorEquivalence_functorIso` identifies the functor underlying the
  equivalence with tensoring by a module.

## Implementation notes

Right exactness is preservation of finite colimits, and preservation of arbitrary direct sums
is preservation of colimits of discrete diagrams indexed by every type in the ambient universe.
The target of the equivalence is a full subcategory of the functor category, and the
identification of its underlying functor with `ModuleCat.moduleTensorFunctor` is an isomorphism
of functors, so it includes naturality in the module.

The inverse sends a functor `F` to `F` applied to the rank-one free module, with the
`A ⊗[R] B`-module structure assembled from the right `B`-action it already has and the left
`A`-action of `ModuleCat.imageAction`; `R`-linearity of `F` is exactly what makes the two
actions agree on `R`, which is `ModuleCat.imageAction_algebraMap`.

## References

* [Stacks Project, Tag 0GNV](https://stacks.math.columbia.edu/tag/0GNV)
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct MonoidalCategory

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

private def categoryScalarMul (M : ModuleCat.{u} A) (r : R) : M ⟶ M := by
  letI := CategoryTheory.Linear.homModule (R := R) M M
  exact r • 𝟙 M

private lemma scalarMul_algebraMap (M : ModuleCat.{u} A) (r : R) :
    scalarMul A M (algebraMap R A r) = categoryScalarMul R A M r := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private lemma imageAction_algebraMap
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] (M : ModuleCat.{u} A) (r : R) :
    imageAction A B F M (algebraMap R A r) =
      algebraMap B (Module.End B (F.obj M)) (algebraMap R B r) := by
  let : F.Additive :=
    rightExactFunctor_le_additiveFunctor (ModuleCat.{u} A) (ModuleCat.{u} B)
      F (show PreservesFiniteColimits F from inferInstance)
  apply LinearMap.ext
  intro x
  have hmap : F.map (scalarMul A M (algebraMap R A r)) =
      categoryScalarMul R B (F.obj M) r := by
    calc
      _ = F.map (categoryScalarMul R A M r) :=
        congrArg F.map (scalarMul_algebraMap (R := R) (A := A) M r)
      _ = categoryScalarMul R B (F.obj M) r := by
        simp [categoryScalarMul, Functor.map_smul (F := F) r (𝟙 M)]
  simpa [imageAction, scalarMul, categoryScalarMul] using
    congrArg (fun f : (F.obj M ⟶ F.obj M) => f.hom x) hmap

private noncomputable abbrev functorValueModule
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] (M : ModuleCat.{u} A) :
    ModuleCat.{u} (A ⊗[R] B) := by
  let K := F.obj M
  letI : Module A K := Module.compHom K (imageAction A B F M)
  letI : SMulCommClass A B K := ⟨fun a b x => by
    change (imageAction A B F M a) (b • x) =
      b • (imageAction A B F M a) x
    exact map_smul (imageAction A B F M a) b x⟩
  letI : IsScalarTower R A K := ⟨fun r a x => by
    rw [Algebra.smul_def, mul_smul]
    change (imageAction A B F M (algebraMap R A r))
        ((imageAction A B F M a) x) = _
    rw [imageAction_algebraMap R A B F M r]
    rfl⟩
  letI : IsScalarTower R B K := inferInstance
  letI : Module (A ⊗[R] B) K := TensorProduct.Algebra.module
  exact ModuleCat.of (A ⊗[R] B) K

private lemma functorValueModule_smul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] (M : ModuleCat.{u} A)
    (a : A) (b : B) (x : F.obj M) :
    (functorValueModule R A B F M).isModule.smul (a ⊗ₜ[R] b) x =
      b • (F.map (scalarMul A M a)) x := by
  dsimp [functorValueModule]
  change (imageAction A B F M a) (b • x) =
    b • (imageAction A B F M a) x
  exact map_smul (imageAction A B F M a) b x

/-- A `B`-linear map between values of two functors which commutes with the `A`-actions is
`A ⊗[R] B`-linear. -/
private noncomputable def functorValueModuleHom
    (F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F]
    [PreservesFiniteColimits G] [Functor.Linear R G]
    {M N : ModuleCat.{u} A} (φ : F.obj M ⟶ G.obj N)
    (h : ∀ a, F.map (scalarMul A M a) ≫ φ = φ ≫ G.map (scalarMul A N a)) :
    functorValueModule R A B F M ⟶ functorValueModule R A B G N := by
  letI : Module (A ⊗[R] B) (F.obj M) := (functorValueModule R A B F M).isModule
  letI : Module (A ⊗[R] B) (G.obj N) := (functorValueModule R A B G N).isModule
  refine ConcreteCategory.ofHom (C := ModuleCat (A ⊗[R] B)) {
    toFun := fun x => φ x
    map_add' := fun x y => φ.hom.map_add x y
    map_smul' := ?_ }
  intro c x
  change F.obj M at x
  induction c using TensorProduct.inductionOn with
  | tmul a b =>
      change φ ((functorValueModule R A B F M).isModule.smul (a ⊗ₜ[R] b) x) =
        (functorValueModule R A B G N).isModule.smul (a ⊗ₜ[R] b) (φ x)
      rw [functorValueModule_smul, functorValueModule_smul, map_smul]
      congr 1
      exact congrArg (fun g => g x) (congrArg ModuleCat.Hom.hom (h a))
  | add c d hc hd =>
      change φ.hom ((c + d) • x) = (c + d) • φ.hom x
      change φ.hom (c • x) = c • φ.hom x at hc
      change φ.hom (d • x) = d • φ.hom x at hd
      rw [add_smul, φ.hom.map_add, hc, hd, add_smul]

/-- The property of an `R`-linear functor between module categories being right exact and
preserving arbitrary direct sums. -/
@[ega "III 7.2.6"]
public abbrev IsLinearRightExactAndPreservesDirectSums :
    ObjectProperty (ModuleCat.{u} A ⥤ ModuleCat.{u} B) := fun F ↦
  F.Linear R ∧ PreservesFiniteColimits F ∧
    ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F

private noncomputable def freeEvaluation (M : ModuleCat.{u} A) :
    (ModuleCat.free A).obj M ⟶ M :=
  ModuleCat.freeDesc (↾fun x : M => x)

private lemma freeEvaluation_surjective (M : ModuleCat.{u} A) :
    Function.Surjective (freeEvaluation A M) := by
  intro x
  exact ⟨ModuleCat.freeMk x, ModuleCat.freeDesc_apply (↾fun y : M => y) x⟩

private lemma natTrans_ext_of_app_regular
    (F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [Functor.PreservesEpimorphisms F]
    (hcoprod : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F)
    (η θ : F ⟶ G)
    (hA : η.app (ModuleCat.of A A) = θ.app (ModuleCat.of A A)) : η = θ := by
  apply NatTrans.ext
  funext M
  let : Epi (freeEvaluation A M) :=
    (ModuleCat.epi_iff_surjective _).2 (freeEvaluation_surjective A M)
  have hfree : η.app ((ModuleCat.free A).obj M) = θ.app ((ModuleCat.free A).obj M) := by
    let : PreservesColimitsOfShape (Discrete (↑M)) F := hcoprod (↑M)
    let c := ModuleCat.finsuppCocone A A (↑M)
    let hc : IsColimit (F.mapCocone c) :=
      isColimitOfPreserves F (ModuleCat.finsuppCoconeIsColimit A A (↑M))
    apply hc.hom_ext
    intro m
    have hA' : η.app (ModuleCat.of A A) ≫ G.map (c.ι.app ⟨m.as⟩) =
        θ.app (ModuleCat.of A A) ≫ G.map (c.ι.app ⟨m.as⟩) :=
      congrArg (fun f : F.obj (ModuleCat.of A A) ⟶ G.obj (ModuleCat.of A A) =>
        f ≫ G.map (c.ι.app ⟨m.as⟩)) hA
    have hA'' : η.app ((Discrete.functor fun _ => ModuleCat.of A A).obj m) ≫
        G.map (c.ι.app m) =
        θ.app ((Discrete.functor fun _ => ModuleCat.of A A).obj m) ≫
        G.map (c.ι.app m) := hA'
    have hη := η.naturality (c.ι.app m)
    have hθ := θ.naturality (c.ι.app m)
    change (F.mapCocone c).ι.app m ≫ η.app ((ModuleCat.free A).obj M) =
      η.app ((Discrete.functor fun _ => ModuleCat.of A A).obj m) ≫ G.map (c.ι.app m) at hη
    change (F.mapCocone c).ι.app m ≫ θ.app ((ModuleCat.free A).obj M) =
      θ.app ((Discrete.functor fun _ => ModuleCat.of A A).obj m) ≫ G.map (c.ι.app m) at hθ
    exact hη.trans (hA''.trans hθ.symm)
  let : Epi (F.map (freeEvaluation A M)) := inferInstance
  apply (cancel_epi (F.map (freeEvaluation A M))).mp
  calc
    F.map (freeEvaluation A M) ≫ η.app M =
        η.app ((ModuleCat.free A).obj M) ≫ G.map (freeEvaluation A M) := η.naturality _
    _ = θ.app ((ModuleCat.free A).obj M) ≫ G.map (freeEvaluation A M) := by rw [hfree]
    _ = F.map (freeEvaluation A M) ≫ θ.app M := (θ.naturality _).symm

private noncomputable def reconstructFunctor :
    ObjectProperty.FullSubcategory
        (IsLinearRightExactAndPreservesDirectSums R A B) ⥤
      ModuleCat.{u} (A ⊗[R] B) where
  obj F := by
    letI := F.property.1
    letI := F.property.2.1
    exact functorValueModule R A B F.obj (ModuleCat.of A A)
  map {F G} η := by
    letI := F.property.1
    letI := F.property.2.1
    letI := G.property.1
    letI := G.property.2.1
    exact functorValueModuleHom R A B F.obj G.obj (η.hom.app _) fun a ↦ η.hom.naturality _
  map_id F := by
    let := F.property.1
    let := F.property.2.1
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp {F G H} f g := by
    let := F.property.1
    let := F.property.2.1
    let := G.property.1
    let := G.property.2.1
    let := H.property.1
    let := H.property.2.1
    apply ModuleCat.hom_ext
    ext x
    rfl

private lemma functorValueModule_restrict_smul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] (M : ModuleCat.{u} A)
    (b : B) (x : F.obj M) :
    (((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).obj
      (functorValueModule R A B F M)).isModule).smul b x = b • x := by
  change (functorValueModule R A B F M).isModule.smul
    ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)) b) x = b • x
  rw [Algebra.TensorProduct.includeRight_apply, functorValueModule_smul]
  rw [scalarMul_one, F.map_id]
  rfl

private noncomputable def functorValueModule_restrictIso
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] (M : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).obj
        (functorValueModule R A B F M) ≅ F.obj M := by
  let X := (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).obj
      (functorValueModule R A B F M)
  letI : Module B X := X.isModule
  letI : Module B (F.obj M) := (F.obj M).isModule
  let e : X ≃ₗ[B] F.obj M := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro b x
      exact functorValueModule_restrict_smul R A B F M b x }
  exact LinearEquiv.toModuleIso e

/-- Tensoring by a module over `A ⊗[R] B`, functorially in that module. -/
public noncomputable def moduleTensorFunctor :
    ModuleCat.{u} (A ⊗[R] B) ⥤ (ModuleCat.{u} A ⥤ ModuleCat.{u} B) :=
  MonoidalCategory.tensoringRight (ModuleCat.{u} (A ⊗[R] B)) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)))


private noncomputable def extendScalarsRegularIso :
    (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj
        (ModuleCat.of A A) ≅ ModuleCat.of (A ⊗[R] B) (A ⊗[R] B) := by
  letI : Algebra A (A ⊗[R] B) :=
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)).toAlgebra
  letI : Module A (A ⊗[R] B) :=
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)).toModule
  exact LinearEquiv.toModuleIso
    (TensorProduct.AlgebraTensorModule.rid A (A ⊗[R] B) (A ⊗[R] B))

private noncomputable def tensorFunctorRegularIso
    (K : ModuleCat.{u} (A ⊗[R] B)) :
    ((moduleTensorFunctor R A B).obj K).obj (ModuleCat.of A A) ≅
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).obj K :=
  (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).mapIso
    (((MonoidalCategory.tensoringRight (ModuleCat.{u} (A ⊗[R] B))).obj K).mapIso
        (extendScalarsRegularIso R A B) ≪≫
      MonoidalCategory.leftUnitor K)

private lemma tensorFunctorRegularIso_hom_tmul
    (K : ModuleCat.{u} (A ⊗[R] B))
    (t : A ⊗[R] B) (z : A) (k : K) :
    (tensorFunctorRegularIso R A B K).hom
        ((t ⊗ₜ[A] z) ⊗ₜ[A ⊗[R] B] k) =
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B) z * t) • k := by
  dsimp [tensorFunctorRegularIso, extendScalarsRegularIso]
  rfl

private noncomputable def tensorFunctorRegularValueIso
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] :
    (tensorFunctor R A B
      (functorValueModule R A B F (ModuleCat.of A A))).obj (ModuleCat.of A A) ≅
      F.obj (ModuleCat.of A A) :=
  tensorFunctorRegularIso R A B
      (functorValueModule R A B F (ModuleCat.of A A)) ≪≫
    (functorValueModule_restrictIso R A B F (ModuleCat.of A A))

private lemma functorValueModule_includeLeft_smul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] (a : A)
    (k : functorValueModule R A B F (ModuleCat.of A A)) :
    (functorValueModule R A B F (ModuleCat.of A A)).isModule.smul
      ((Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) a) k =
        F.map (regularMul A a) k := by
  change (functorValueModule R A B F (ModuleCat.of A A)).isModule.smul
    (a ⊗ₜ[R] (1 : B)) k = F.map (regularMul A a) k
  rw [functorValueModule_smul, regularMul_eq_scalarMul]
  simp

private lemma tensorFunctorRegularValueIso_hom_tmul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F]
    (t : A ⊗[R] B) (z : A)
    (k : functorValueModule R A B F (ModuleCat.of A A)) :
    (tensorFunctorRegularValueIso R A B F).hom
        ((t ⊗ₜ[A] z) ⊗ₜ[A ⊗[R] B] k) =
      (functorValueModule R A B F (ModuleCat.of A A)).isModule.smul
        ((Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) z * t) k := by
  dsimp [tensorFunctorRegularValueIso, tensorFunctorRegularIso,
    functorValueModule_restrictIso, extendScalarsRegularIso]
  rfl

private lemma tensorFunctorRegularValueIso_natural
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F] (a : A) :
    (tensorFunctor R A B
      (functorValueModule R A B F (ModuleCat.of A A))).map (regularMul A a) ≫
        (tensorFunctorRegularValueIso R A B F).hom =
      (tensorFunctorRegularValueIso R A B F).hom ≫ F.map (regularMul A a) := by
  apply ModuleCat.hom_ext
  let T := tensorFunctor R A B
    (functorValueModule R A B F (ModuleCat.of A A))
  let e := tensorFunctorRegularValueIso R A B F
  let L : T.obj (ModuleCat.of A A) →ₗ[B] F.obj (ModuleCat.of A A) :=
    ((T.map (regularMul A a) ≫ e.hom).hom)
  let R' : T.obj (ModuleCat.of A A) →ₗ[B] F.obj (ModuleCat.of A A) :=
    ((e.hom ≫ F.map (regularMul A a)).hom)
  change L = R'
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul s k =>
    induction s using TensorProduct.inductionOn with
    | tmul t z =>
      change A ⊗[R] B at t
      change A at z
      let : Module (A ⊗[R] B) (F.obj (ModuleCat.of A A)) :=
        (functorValueModule R A B F (ModuleCat.of A A)).isModule
      change e.hom
          (((ModuleCat.extendScalars
              (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).map
                (regularMul A a) (t ⊗ₜ[A] z)) ⊗ₜ[A ⊗[R] B] k) =
        (F.map (regularMul A a)).hom
          (e.hom ((t ⊗ₜ[A] z) ⊗ₜ[A ⊗[R] B] k))
      change e.hom ((t ⊗ₜ[A] (a * z)) ⊗ₜ[A ⊗[R] B] k) =
        (F.map (regularMul A a)).hom
          (e.hom ((t ⊗ₜ[A] z) ⊗ₜ[A ⊗[R] B] k))
      rw [tensorFunctorRegularValueIso_hom_tmul,
        tensorFunctorRegularValueIso_hom_tmul]
      change (functorValueModule R A B F (ModuleCat.of A A)).isModule.smul
          ((Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) (a * z) * t) k =
        (F.map (regularMul A a)).hom
          ((functorValueModule R A B F (ModuleCat.of A A)).isModule.smul
            ((Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) z * t) k)
      let iL := Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)
      change (iL (a * z) * t) • k =
        (F.map (regularMul A a)).hom ((iL z * t) • k)
      calc
        (iL (a * z) * t) • k = (iL z * t) • (iL a • k) := by
          rw [← mul_smul, map_mul]
          congr 1
          ring
        _ = (iL z * t) • ((F.map (regularMul A a)).hom k) := by
          have h := functorValueModule_includeLeft_smul R A B F a k
          change iL a • k = (F.map (regularMul A a)).hom k at h
          exact congrArg (fun v => (iL z * t) • v) h
        _ = (F.map (regularMul A a)).hom ((iL z * t) • k) :=
          ((functorValueModuleHom R A B F F (F.map (regularMul A a)) fun a' => by
            rw [← F.map_comp, ← F.map_comp, scalarMul_natural]).hom.map_smul
            (iL z * t) k).symm
    | add s t hs ht =>
      let E := (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj
          (ModuleCat.of A A)
      let : Module (A ⊗[R] B)
          (((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj
              (ModuleCat.of (A ⊗[R] B) (A ⊗[R] B))) ⊗[A] (ModuleCat.of A A)) :=
        E.isModule
      have hadd : (((s : E) + (t : E)) ⊗ₜ[A ⊗[R] B] k : T.obj (ModuleCat.of A A)) =
          ((s : E) ⊗ₜ[A ⊗[R] B] k : T.obj (ModuleCat.of A A)) +
            ((t : E) ⊗ₜ[A ⊗[R] B] k : T.obj (ModuleCat.of A A)) :=
        TensorProduct.add_tmul (s : E) (t : E) k
      calc
        L ((s + t) ⊗ₜ[A ⊗[R] B] k) =
            L (s ⊗ₜ[A ⊗[R] B] k + t ⊗ₜ[A ⊗[R] B] k) := congrArg L hadd
        _ = L (s ⊗ₜ[A ⊗[R] B] k) + L (t ⊗ₜ[A ⊗[R] B] k) := L.map_add _ _
        _ = R' (s ⊗ₜ[A ⊗[R] B] k) + R' (t ⊗ₜ[A ⊗[R] B] k) :=
          congrArg₂ (· + ·) hs ht
        _ = R' (s ⊗ₜ[A ⊗[R] B] k + t ⊗ₜ[A ⊗[R] B] k) :=
          (R'.map_add _ _).symm
        _ = R' ((s + t) ⊗ₜ[A ⊗[R] B] k) := congrArg R' hadd.symm
  | add x y hx hy =>
    calc
      L (x + y) = L x + L y := L.map_add x y
      _ = R' x + R' y := congrArg₂ (· + ·) hx hy
      _ = R' (x + y) := (R'.map_add x y).symm

/-- A right exact functor preserving direct sums preserves all colimits. -/
private lemma preservesColimits_of_directSums
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F]
    (hcoprod : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) : PreservesColimits F := by
  have h := (tfae_iso_tensorFunctor_preserves_colimits_isLeftAdjoint A B F).out 2 3
  exact h.mp ⟨inferInstance, hcoprod⟩

private noncomputable def representedFunctorIso
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F]
    (hcoprod : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) :
    (moduleTensorFunctor R A B).obj
      (functorValueModule R A B F (ModuleCat.of A A)) ≅ F := by
  haveI := preservesColimits_of_directSums A B F hcoprod
  let T := tensorFunctor R A B
    (functorValueModule R A B F (ModuleCat.of A A))
  haveI : PreservesColimits T :=
    tensorFunctor_preservesColimits R A B
      (functorValueModule R A B F (ModuleCat.of A A))
  change T ≅ F
  exact isoOfRegularAction A B T F (tensorFunctorRegularValueIso R A B F)
    (tensorFunctorRegularValueIso_natural R A B F)

private lemma representedFunctorIso_app_regular
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] [Functor.Linear R F]
    (hcoprod : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) :
    (representedFunctorIso R A B F hcoprod).hom.app (ModuleCat.of A A) =
      (tensorFunctorRegularValueIso R A B F).hom := by
  have := preservesColimits_of_directSums A B F hcoprod
  have : PreservesColimits
      (tensorFunctor R A B
        (functorValueModule R A B F (ModuleCat.of A A))) :=
    tensorFunctor_preservesColimits R A B
      (functorValueModule R A B F (ModuleCat.of A A))
  exact isoOfRegularAction_hom_app A B
    (tensorFunctor R A B (functorValueModule R A B F (ModuleCat.of A A))) F
    (tensorFunctorRegularValueIso R A B F)
    (tensorFunctorRegularValueIso_natural R A B F)

private lemma moduleTensorFunctor_property (K : ModuleCat.{u} (A ⊗[R] B)) :
    IsLinearRightExactAndPreservesDirectSums R A B ((moduleTensorFunctor R A B).obj K) :=
  ⟨tensorFunctor_linear R A B K, tensorFunctor_preservesFiniteColimits R A B K,
    tensorFunctor_preservesDirectSums R A B K⟩

private noncomputable def reconstructedTensorModuleIso
    (K : ModuleCat.{u} (A ⊗[R] B)) :
    (reconstructFunctor R A B).obj
      ⟨(moduleTensorFunctor R A B).obj K,
        moduleTensorFunctor_property R A B K⟩ ≅ K := by
  let F := (moduleTensorFunctor R A B).obj K
  letI : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (tensorFunctor R A B K)
    exact tensorFunctor_preservesFiniteColimits R A B K
  letI : Functor.Linear R F := by
    change Functor.Linear R (tensorFunctor R A B K)
    exact tensorFunctor_linear R A B K
  let X := functorValueModule R A B F (ModuleCat.of A A)
  letI : Module (A ⊗[R] B) X := X.isModule
  letI : Module (A ⊗[R] B) K := K.isModule
  let iL := Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)
  let iR := Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)
  let KB := (ModuleCat.restrictScalars iR.toRingHom).obj K
  letI : Module (A ⊗[R] B) KB := K.isModule
  letI : Module A KB := Module.compHom KB iL
  let e := tensorFunctorRegularIso R A B K
  let E := (ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj
      (ModuleCat.of A A)
  letI : Module (A ⊗[R] B)
      (((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj
          (ModuleCat.of (A ⊗[R] B) (A ⊗[R] B))) ⊗[A] (ModuleCat.of A A)) := E.isModule
  have hA (a : A) (x : F.obj (ModuleCat.of A A)) :
      e.hom ((F.map (scalarMul A (ModuleCat.of A A) a)).hom x) =
        iL a • e.hom x := by
    change E ⊗[A ⊗[R] B] K at x
    induction x using TensorProduct.inductionOn with
    | tmul s k =>
      change E at s
      induction s using TensorProduct.inductionOn with
      | tmul t z =>
        change A ⊗[R] B at t
        change e.hom
            (((ModuleCat.extendScalars
                (Algebra.TensorProduct.includeLeftRingHom
                  (R := R) (A := A) (B := B))).map (regularMul A a)
                (t ⊗ₜ[A] z)) ⊗ₜ[A ⊗[R] B] k) = _
        change e.hom ((t ⊗ₜ[A] (a * z)) ⊗ₜ[A ⊗[R] B] k) = _
        change (tensorFunctorRegularIso R A B K).hom
            ((t ⊗ₜ[A] (a * z)) ⊗ₜ[A ⊗[R] B] k) = _
        rw [tensorFunctorRegularIso_hom_tmul, tensorFunctorRegularIso_hom_tmul]
        change (iL (a * z) * (t : A ⊗[R] B)) • k =
          iL a • ((iL z * (t : A ⊗[R] B)) • k)
        rw [map_mul, mul_assoc, ← mul_smul]
      | add s t hs ht =>
        change E at s
        change E at t
        change e.hom ((F.map (scalarMul A (ModuleCat.of A A) a)).hom
          ((s + t : E) ⊗ₜ[A ⊗[R] B] k)) = _
        have hst : (s + t : E) ⊗ₜ[A ⊗[R] B] k =
            s ⊗ₜ[A ⊗[R] B] k + t ⊗ₜ[A ⊗[R] B] k := TensorProduct.add_tmul s t k
        refine (congrArg _ (congrArg _ hst)).trans ?_
        refine (congrArg _ (map_add _ _ _)).trans ?_
        refine (map_add _ _ _).trans ?_
        refine (congrArg₂ (· + ·) hs ht).trans ?_
        refine (smul_add (iL a) _ _).symm.trans ?_
        refine (congrArg _ (map_add _ _ _).symm).trans ?_
        exact congrArg _ (congrArg _ hst).symm
    | add x y hx hy =>
      refine (congrArg _ (map_add _ x y)).trans ?_
      refine (map_add _ _ _).trans ?_
      refine (congrArg₂ (· + ·) hx hy).trans ?_
      refine (smul_add (iL a) _ _).symm.trans ?_
      exact congrArg _ (map_add _ x y).symm
  let eLin : X →ₗ[A ⊗[R] B] KB := {
    toFun := e.hom.hom
    map_add' := e.hom.hom.map_add
    map_smul' := by
      intro c x
      induction c using TensorProduct.inductionOn with
      | tmul a b =>
        change e.hom.hom
          ((functorValueModule R A B F (ModuleCat.of A A)).isModule.smul
            (a ⊗ₜ[R] b) x) = _
        rw [functorValueModule_smul, e.hom.hom.map_smul, hA]
        change b • (a • e.hom.hom x) = (a ⊗ₜ[R] b) • e.hom.hom x
        calc
          _ = (iR b * iL a) • e.hom.hom x := by
            change (iR b) • ((iL a) • e.hom.hom x) = _
            rw [← mul_smul]
          _ = (a ⊗ₜ[R] b) • e.hom.hom x := by
            congr 1
            simp [iL, iR, Algebra.TensorProduct.includeRight_apply, mul_comm]
      | add c d hc hd =>
        change e.hom.hom ((c + d) • x) = (c + d) • e.hom.hom x
        rw [add_smul, e.hom.hom.map_add, hc, hd, add_smul]
        simp only [RingHom.id_apply]
  }
  let eEquiv : X ≃ₗ[A ⊗[R] B] KB := {
    toFun := eLin
    invFun := e.inv.hom
    left_inv := fun x => congrArg (fun φ => (ConcreteCategory.hom φ) x) e.hom_inv_id
    right_inv := fun x => congrArg (fun φ => (ConcreteCategory.hom φ) x) e.inv_hom_id
    map_add' := eLin.map_add
    map_smul' := eLin.map_smul }
  exact LinearEquiv.toModuleIso eEquiv

private lemma tensorFunctorRegularIso_natural {K L : ModuleCat.{u} (A ⊗[R] B)}
    (f : K ⟶ L) :
    ((moduleTensorFunctor R A B).map f).app (ModuleCat.of A A) ≫
        (tensorFunctorRegularIso R A B L).hom =
      (tensorFunctorRegularIso R A B K).hom ≫
      (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).map f := by
  dsimp [moduleTensorFunctor, tensorFunctorRegularIso]
  rw [← Functor.map_comp, ← Functor.map_comp]
  let e := extendScalarsRegularIso R A B
  have h :
      (MonoidalCategory.whiskerLeft
          ((ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj
              (ModuleCat.of A A)) f) ≫
          (MonoidalCategory.whiskerRight e.hom L) ≫ (λ_ L).hom =
        (MonoidalCategory.whiskerRight e.hom K) ≫ (λ_ K).hom ≫ f := by
    calc
      _ = (MonoidalCategory.whiskerRight e.hom K) ≫
            (MonoidalCategory.whiskerLeft
              (ModuleCat.of (A ⊗[R] B) (A ⊗[R] B)) f) ≫ (λ_ L).hom := by
          simpa only [Category.assoc] using congrArg
            (fun g => g ≫ (λ_ L).hom)
            (MonoidalCategory.whisker_exchange e.hom f)
      _ = (MonoidalCategory.whiskerRight e.hom K) ≫
            (λ_ K).hom ≫ f := by
          calc
            _ = (MonoidalCategory.whiskerRight e.hom K) ≫
                ((𝟙_ (ModuleCat (A ⊗[R] B)) ◁ f) ≫ (λ_ L).hom) := rfl
            _ = (MonoidalCategory.whiskerRight e.hom K) ≫ ((λ_ K).hom ≫ f) := by
                  rw [MonoidalCategory.leftUnitor_naturality]
            _ = _ := rfl
  exact congrArg (fun g => (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).map g) h

/-- The tensor functor, lifted to the full subcategory of linear, right exact,
direct-sum-preserving functors. -/
@[ega "III 7.2.6" "special case"]
public noncomputable def moduleTensorFunctorLift :
    ModuleCat.{u} (A ⊗[R] B) ⥤
      ObjectProperty.FullSubcategory
        (IsLinearRightExactAndPreservesDirectSums R A B) :=
  (IsLinearRightExactAndPreservesDirectSums R A B).lift
    (moduleTensorFunctor R A B) fun K ↦
      ⟨tensorFunctor_linear R A B K,
        tensorFunctor_preservesFiniteColimits R A B K,
        tensorFunctor_preservesDirectSums R A B K⟩

private lemma reconstructedTensorModuleIso_natural
    {K L : ModuleCat.{u} (A ⊗[R] B)} (f : K ⟶ L) :
    (reconstructFunctor R A B).map ((moduleTensorFunctorLift R A B).map f) ≫
        (let eL : (reconstructFunctor R A B).obj
            ((moduleTensorFunctorLift R A B).obj L) ≅ L := by
          dsimp [moduleTensorFunctorLift]
          exact reconstructedTensorModuleIso R A B L
         eL.hom) =
      (let eK : (reconstructFunctor R A B).obj
          ((moduleTensorFunctorLift R A B).obj K) ≅ K := by
        dsimp [moduleTensorFunctorLift]
        exact reconstructedTensorModuleIso R A B K
       eK.hom) ≫ f := by
  apply ModuleCat.hom_ext
  ext x
  convert congrArg (fun g => g.hom x) (tensorFunctorRegularIso_natural R A B f) using 1 <;> rfl

private noncomputable def tensorFunctorReconstructUnitIso :
    𝟭 (ModuleCat.{u} (A ⊗[R] B)) ≅
      moduleTensorFunctorLift R A B ⋙ reconstructFunctor R A B := by
  refine NatIso.ofComponents (fun K => ?_) ?_
  · change K ≅ (reconstructFunctor R A B).obj
      ⟨(moduleTensorFunctor R A B).obj K,
        moduleTensorFunctor_property R A B K⟩
    exact (reconstructedTensorModuleIso R A B K).symm
  · intro K L f
    let eK : (reconstructFunctor R A B).obj
        ((moduleTensorFunctorLift R A B).obj K) ≅ K := by
      dsimp [moduleTensorFunctorLift]
      exact reconstructedTensorModuleIso R A B K
    let eL : (reconstructFunctor R A B).obj
        ((moduleTensorFunctorLift R A B).obj L) ≅ L := by
      dsimp [moduleTensorFunctorLift]
      exact reconstructedTensorModuleIso R A B L
    let g := (reconstructFunctor R A B).map ((moduleTensorFunctorLift R A B).map f)
    have h : g ≫ eL.hom = eK.hom ≫ f := by
      simpa [eK, eL, g] using reconstructedTensorModuleIso_natural R A B f
    calc
      f ≫ eL.inv = eK.inv ≫ (eK.hom ≫ f) ≫ eL.inv := by simp [Category.assoc]
      _ = eK.inv ≫ (g ≫ eL.hom) ≫ eL.inv := by rw [← h]
      _ = eK.inv ≫ g := by simp

private noncomputable def tensorFunctorReconstructCounitIso :
    reconstructFunctor R A B ⋙ moduleTensorFunctorLift R A B ≅
      𝟭 (IsLinearRightExactAndPreservesDirectSums R A B).FullSubcategory := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  · letI : Functor.Linear R F.obj := F.property.1
    letI : PreservesFiniteColimits F.obj := F.property.2.1
    exact ObjectProperty.isoMk
      (IsLinearRightExactAndPreservesDirectSums R A B)
      (representedFunctorIso R A B F.obj F.property.2.2)
  · intro F G η
    let : Functor.Linear R F.obj := F.property.1
    let : PreservesFiniteColimits F.obj := F.property.2.1
    let : Functor.Linear R G.obj := G.property.1
    let : PreservesFiniteColimits G.obj := G.property.2.1
    let TF := (moduleTensorFunctorLift R A B).obj ((reconstructFunctor R A B).obj F)
    let : PreservesFiniteColimits TF.obj := TF.property.2.1
    let : PreservesColimitsOfShape WalkingSpan TF.obj := inferInstance
    let : Functor.PreservesEpimorphisms TF.obj := inferInstance
    apply ObjectProperty.hom_ext
    apply natTrans_ext_of_app_regular A B TF.obj G.obj
      TF.property.2.2 _ _
    let m := (reconstructFunctor R A B).map η
    change ((moduleTensorFunctor R A B).map m).app (ModuleCat.of A A) ≫
        (representedFunctorIso R A B G.obj G.property.2.2).hom.app
          (ModuleCat.of A A) =
      (representedFunctorIso R A B F.obj F.property.2.2).hom.app
          (ModuleCat.of A A) ≫ η.hom.app (ModuleCat.of A A)
    rw [representedFunctorIso_app_regular, representedFunctorIso_app_regular]
    have hrestr :
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).map m ≫
            (functorValueModule_restrictIso R A B G.obj (ModuleCat.of A A)).hom =
          (functorValueModule_restrictIso R A B F.obj (ModuleCat.of A A)).hom ≫
            η.hom.app (ModuleCat.of A A) := by
      apply ModuleCat.hom_ext
      ext x
      rfl
    calc
      _ = (((moduleTensorFunctor R A B).map m).app (ModuleCat.of A A) ≫
          (tensorFunctorRegularIso R A B ((reconstructFunctor R A B).obj G)).hom) ≫
            (functorValueModule_restrictIso R A B G.obj (ModuleCat.of A A)).hom :=
        rfl
      _ = ((tensorFunctorRegularIso R A B ((reconstructFunctor R A B).obj F)).hom ≫
          (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).map m) ≫
            (functorValueModule_restrictIso R A B G.obj (ModuleCat.of A A)).hom :=
        congrArg
          (fun q => q ≫
            (functorValueModule_restrictIso R A B G.obj (ModuleCat.of A A)).hom)
          (tensorFunctorRegularIso_natural R A B m)
      _ = (tensorFunctorRegularIso R A B ((reconstructFunctor R A B).obj F)).hom ≫
          ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom).map m ≫
            (functorValueModule_restrictIso R A B G.obj (ModuleCat.of A A)).hom) :=
        -- `simp` and `rw` cannot act on these two steps: the objects of the composite are
        -- spelled through `reconstructFunctor`, whose unfolding the elaborator will not perform
        -- at the transparency those tactics use. Applied as terms they go through.
        Category.assoc _ _ _
      _ = (tensorFunctorRegularIso R A B ((reconstructFunctor R A B).obj F)).hom ≫
          ((functorValueModule_restrictIso R A B F.obj (ModuleCat.of A A)).hom ≫
            η.hom.app (ModuleCat.of A A)) :=
        congrArg
          (fun q => (tensorFunctorRegularIso R A B ((reconstructFunctor R A B).obj F)).hom ≫ q)
          hrestr
      _ = _ := rfl

/-- The functor `moduleTensorFunctorLift R A B` is an equivalence of categories, with
quasi-inverse `reconstructFunctor R A B`. -/
public theorem tensorFunctorEquivalence_isEquivalence :
    (moduleTensorFunctorLift R A B).IsEquivalence :=
  (CategoryTheory.Equivalence.mk
    (F := moduleTensorFunctorLift R A B) (G := reconstructFunctor R A B)
    (tensorFunctorReconstructUnitIso R A B)
    (tensorFunctorReconstructCounitIso R A B)).isEquivalence_functor

/-- Modules over `A ⊗[R] B` are equivalent to `R`-linear right exact functors from
`A`-modules to `B`-modules which preserve arbitrary direct sums. -/
@[stacks 0GNV "the equivalence", ega "III 7.2.6" "commutative rings"]
public noncomputable def tensorFunctorEquivalence :
    ModuleCat.{u} (A ⊗[R] B) ≌
      ObjectProperty.FullSubcategory
        (IsLinearRightExactAndPreservesDirectSums R A B) := by
  letI : (moduleTensorFunctorLift R A B).IsEquivalence :=
    tensorFunctorEquivalence_isEquivalence R A B
  exact (moduleTensorFunctorLift R A B).asEquivalence

/-- The functor underlying `tensorFunctorEquivalence` is naturally isomorphic to the functor
which sends a module `K` to tensoring with `K`. -/
@[stacks 0GNV "given by tensoring", ega "III 7.2.6" "N ↦ T_N"]
public lemma tensorFunctorEquivalence_functorIso :
    Nonempty
      ((tensorFunctorEquivalence R A B).functor ≅ moduleTensorFunctorLift R A B) := ⟨Iso.refl _⟩

end ModuleCat
