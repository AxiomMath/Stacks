module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute

/-!
# Adequacy under base change

Restriction of an adequate module-valued functor from commutative `A`-algebras to
commutative `A'`-algebras remains adequate for any homomorphism `A → A'`.

## Main definitions

* `AdequateFunctor.restrictAlgebras` forgets an `A'`-algebra to an `A`-algebra.
* `AdequateFunctor.restrictFunctor` restricts a module-valued functor along this forgetful functor.

## Main results

* `AdequateFunctor.IsAdequate.restrict` states that adequacy survives restriction to `A'`-algebras.

## Implementation notes

The scalar ring of the functor at an `A'`-algebra is unchanged by restriction. The restriction
is expressed through Mathlib's pushforward of presheaves of modules. The algebra universe contains
both base rings, whose universes remain independent. We lift the restricted functor's values to
include the source ring universe, so its adequate presentation can use the base-changed modules,
whose universe also includes both base rings. This lift changes neither the values as modules nor
their transition maps, up to the canonical linear equivalences.

## References

* [Stacks Project, Tag 06V9](https://stacks.math.columbia.edu/tag/06V9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe w v u u'

namespace AdequateFunctor


variable {A : Type u} {A' : Type u'} [CommRing A] [CommRing A']

/-- Regard a commutative `A'`-algebra as a commutative `A`-algebra. -/
public def restrictAlgebras (f : A →+* A') :
    CommAlgCat.{max u u' v} A' ⥤ CommAlgCat.{max u u' v} A where
  obj B :=
    letI : Algebra A B := Algebra.compHom B f
    CommAlgCat.of A B
  map {B C} g :=
    letI : Algebra A B := Algebra.compHom B f
    letI : Algebra A C := Algebra.compHom C f
    letI : Algebra A A' := f.toAlgebra
    haveI : IsScalarTower A A' B := .of_algebraMap_eq' rfl
    haveI : IsScalarTower A A' C := .of_algebraMap_eq' rfl
    CommAlgCat.ofHom (g.hom.restrictScalars A)

/-- The identity map of the underlying ring diagrams induced by restriction of algebras. -/
public def restrictRingDiagram (f : A →+* A') :
    algebraRingDiagram.{max u u' v} A' ⟶
      (restrictAlgebras.{v} f).op.op ⋙ algebraRingDiagram.{max u u' v} A where
  app X := RingCat.ofHom (RingHom.id X.unop.unop)
  naturality := by
    intro X Y g
    ext x
    rfl

/-- Restrict a module-valued functor to commutative `A'`-algebras. -/
public noncomputable def restrictFunctor (f : A →+* A') :
    ModuleValuedFunctor.{w, max u u' v} A ⥤ ModuleValuedFunctor.{w, max u u' v} A' :=
  PresheafOfModules.pushforward (restrictRingDiagram.{v} f)

/-- A functor of presheaves of modules preserves the kernel of `e` as soon as it does so after
evaluating at every object. -/
private theorem preservesLimit_kernel_of_evaluation
    {C : Type*} [Category C] {D : Type*} [Category D] {R : Cᵒᵖ ⥤ RingCat} {S : Dᵒᵖ ⥤ RingCat}
    {F G : PresheafOfModules R} (e : F ⟶ G) (P : PresheafOfModules R ⥤ PresheafOfModules S)
    (h : ∀ X, PreservesLimit (parallelPair e 0) (P ⋙ PresheafOfModules.evaluation S X)) :
    PreservesLimit (parallelPair e 0) P := by
  let c : Fork e 0 := Fork.ofι (kernel.ι e) (kernel.condition e)
  have hc : IsLimit c := kernelIsKernel e
  apply preservesLimit_of_preserves_limit_cone hc
  exact PresheafOfModules.evaluationJointlyReflectsLimits _ _
    fun X => isLimitOfPreserves (P ⋙ PresheafOfModules.evaluation S X) hc

/-- Restriction of the base ring, read as a pushforward of presheaves of modules, preserves the
kernel of a given morphism. -/
private theorem pushforward_preserves_kernel
    (f : A →+* A')
    {F G : ModuleValuedFunctor.{w, max u u' v} A} (e : F ⟶ G) :
    PreservesLimit (parallelPair e 0)
      (PresheafOfModules.pushforward (restrictRingDiagram.{max u u' v} f)) :=
  preservesLimit_kernel_of_evaluation e _ fun X =>
    inferInstanceAs (PreservesLimit (parallelPair e 0)
      (PresheafOfModules.evaluation (algebraRingDiagram.{max u u' v} A)
        ((restrictAlgebras.{max u u' v} f).op.op.obj X) ⋙
      ModuleCat.restrictScalars ((restrictRingDiagram.{max u u' v} f).app X).hom))

set_option linter.checkUnivs false in
/-- The universe lift of presheaves of modules preserves the kernel of a given morphism. -/
private theorem ulift_preserves_kernel
    {F G : ModuleValuedFunctor.{w, max u u' v} A} (e : F ⟶ G) :
    PreservesLimit (parallelPair e 0)
      (presheafOfModulesUliftFunctor.{u} (algebraRingDiagram.{max u u' v} A)) :=
  preservesLimit_kernel_of_evaluation e _ fun X =>
    inferInstanceAs (PreservesLimit (parallelPair e 0)
      (PresheafOfModules.evaluation (algebraRingDiagram.{max u u' v} A) X ⋙
      ModuleCat.uliftFunctor.{u} ((algebraRingDiagram.{max u u' v} A).obj X)))


universe z

/-- Restricting the module-valued functor of an `A`-module to `A'`-algebras gives the
module-valued functor of the base-changed `A'`-module. -/
private noncomputable def moduleExtensionRestrictIso (f : A →+* A')
    (M : ModuleCat.{z} A) :
    (PresheafOfModules.pushforward (restrictRingDiagram.{max u u' v} f)).obj
        (moduleExtension.{z, max u u' v} A M) ≅
      moduleExtension.{max u' z, max u u' v} A'
        ((ModuleCat.extendScalars.{u, u', z} f).obj M) := by
  classical
  letI : Algebra A A' := f.toAlgebra
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · let B := (X.unop.unop : CommAlgCat.{max u u' v} A')
    letI : Algebra A B := Algebra.compHom B f
    letI : IsScalarTower A A' B := .of_algebraMap_eq' rfl
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' B B M).symm.toModuleIso
  · intro X Y g
    let B := (X.unop.unop : CommAlgCat.{max u u' v} A')
    let C := (Y.unop.unop : CommAlgCat.{max u u' v} A')
    let : Algebra A B := Algebra.compHom B f
    let : Algebra A C := Algebra.compHom C f
    let : IsScalarTower A A' B := .of_algebraMap_eq' rfl
    let : IsScalarTower A A' C := .of_algebraMap_eq' rfl
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => convert congrArg₂ (· + ·) hx hy using 1 <;> apply map_add

/-- The identification of `AdequateFunctor.moduleExtensionRestrictIso` is natural in the
module. -/
private theorem moduleExtensionRestrictIso_naturality (f : A →+* A')
    {M N : ModuleCat.{z} A} (g : M ⟶ N) :
    ((PresheafOfModules.pushforward.{max (max u u' v) z}
      (restrictRingDiagram.{max u u' v} f)).map
      ((moduleExtensionFunctor.{z, max u u' v} A).map g)) ≫
        (moduleExtensionRestrictIso f N).hom =
    (moduleExtensionRestrictIso f M).hom ≫
      (moduleExtensionFunctor.{max u' z, max u u' v} A').map
        ((ModuleCat.extendScalars.{u, u', z} f).map g) := by
  classical
  ext X
  rename_i x
  induction x using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy => convert congrArg₂ (· + ·) hx hy using 1 <;> apply map_add

/-- The value of the restriction of a module-valued functor at an `A'`-algebra is its value at
the underlying `A`-algebra. -/
private noncomputable def pushforwardObjIso (f : A →+* A')
    (G : ModuleValuedFunctor.{z, max u u' v} A) (X) :
    ((PresheafOfModules.pushforward.{z} (restrictRingDiagram.{max u u' v} f)).obj G).obj X ≅
      G.obj ((restrictAlgebras.{v} f).op.op.obj X) := by
  change (ModuleCat.restrictScalars (RingHom.id _)).obj (G.obj _) ≅ _
  exact ModuleCat.restrictScalarsId'App (RingHom.id _) rfl _

/-- Restriction of the base ring commutes with the universe lift of module-valued
functors. -/
private noncomputable def pushforwardUliftIso (f : A →+* A')
    (G : ModuleValuedFunctor.{z, max u u' v} A) :
    (PresheafOfModules.pushforward.{max u z}
      (restrictRingDiagram.{max u u' v} f)).obj
        ((presheafOfModulesUliftFunctor.{u}
          (algebraRingDiagram.{max u u' v} A)).obj G) ≅
      (presheafOfModulesUliftFunctor.{u}
        (algebraRingDiagram.{max u u' v} A')).obj
        ((PresheafOfModules.pushforward.{z}
          (restrictRingDiagram.{max u u' v} f)).obj G) := by
  classical
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · exact pushforwardObjIso f _ X ≪≫
      (ModuleCat.uliftFunctor.{u} ((algebraRingDiagram.{max u u' v} A').obj X)).mapIso
        (pushforwardObjIso f G X).symm
  · intro X Y g; ext x; rfl

/-- The identification of `AdequateFunctor.pushforwardUliftIso` is natural in the functor. -/
private theorem pushforwardUliftIso_naturality (f : A →+* A')
    {G H : ModuleValuedFunctor.{z, max u u' v} A} (η : G ⟶ H) :
    ((PresheafOfModules.pushforward.{max u z}
      (restrictRingDiagram.{max u u' v} f)).map
      (((presheafOfModulesUliftFunctor.{u}
        (algebraRingDiagram.{max u u' v} A)).map η))) ≫
        (pushforwardUliftIso f H).hom =
    (pushforwardUliftIso f G).hom ≫
      (presheafOfModulesUliftFunctor.{u}
        (algebraRingDiagram.{max u u' v} A')).map
        ((PresheafOfModules.pushforward.{z}
          (restrictRingDiagram.{max u u' v} f)).map η) := by
  ext X; rfl

/-- Restriction of the base ring commutes with the universe lift, on a module-valued functor
whose values are lifted to contain the source ring universe. -/
private noncomputable def restrictLiftIso (f : A →+* A')
    (F : ModuleValuedFunctor.{w, max u u' v} A) :
    (PresheafOfModules.pushforward.{max u (max (max u u' v) w)}
      (restrictRingDiagram.{max u u' v} f)).obj
        ((presheafOfModulesUliftFunctor.{u}
          (algebraRingDiagram.{max u u' v} A)).obj
          ((presheafOfModulesUliftFunctor.{max u u' v}
            (algebraRingDiagram.{max u u' v} A)).obj F)) ≅
      (presheafOfModulesUliftFunctor.{max u u' v}
        (algebraRingDiagram.{max u u' v} A')).obj
        ((presheafOfModulesUliftFunctor.{u}
          (algebraRingDiagram.{max u u' v} A')).obj
          ((PresheafOfModules.pushforward.{w}
            (restrictRingDiagram.{max u u' v} f)).obj F)) := by
  classical
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · let X₀ := (restrictAlgebras.{v} f).op.op.obj X
    let R := (algebraRingDiagram.{max u u' v} A).obj X₀
    let e : ULift.{u} (ULift.{max u u' v} (F.obj X₀)) ≃ₗ[R]
        ULift.{max u u' v} (ULift.{u} (F.obj X₀)) :=
      (ULift.moduleEquiv.{max u u' v, max (max u u' v) w, u}).trans
        ((ULift.moduleEquiv.{max u u' v, w, max u u' v}).trans
          ((ULift.moduleEquiv.{max u u' v, w, u}).symm.trans
            (ULift.moduleEquiv.{max u u' v, max u w, max u u' v}).symm))
    exact pushforwardObjIso f _ X ≪≫ e.toModuleIso ≪≫
      (ModuleCat.uliftFunctor.{max u u' v} ((algebraRingDiagram.{max u u' v} A').obj X)).mapIso
        ((ModuleCat.uliftFunctor.{u} ((algebraRingDiagram.{max u u' v} A').obj X)).mapIso
          (pushforwardObjIso f F X).symm)
  · intro X Y g
    ext x
    rfl

/-- An adequate functor stays adequate after restriction along a ring homomorphism,
with its values lifted to include the source ring universe. -/
@[stacks 06V9]
public theorem IsAdequate.restrict (f : A →+* A')
    (F : ModuleValuedFunctor.{w, max u u' v} A)
    (hF : IsAdequate.{w, max u u' v} (𝟭 _) F) :
    IsAdequate.{max u w, max u u' v} (𝟭 _)
      ((presheafOfModulesUliftFunctor.{u} (algebraRingDiagram.{max u u' v} A')).obj
        ((restrictFunctor.{w, v} f).obj F)) := by
  classical
  obtain ⟨M, N, g, ⟨e⟩⟩ := hF
  let M' := (ModuleCat.extendScalars f).obj M
  let N' := (ModuleCat.extendScalars f).obj N
  let g' := (ModuleCat.extendScalars f).map g
  let U := presheafOfModulesUliftFunctor.{u, max (max u u' v) w}
    (algebraRingDiagram.{max u u' v} A)
  let U' := presheafOfModulesUliftFunctor.{u, max (max u u' v) w}
    (algebraRingDiagram.{max u u' v} A')
  let P := PresheafOfModules.pushforward.{max u (max (max u u' v) w)}
    (restrictRingDiagram.{max u u' v} f)
  let q := (moduleExtensionFunctor.{max u (max u' v) w, max u u' v} A).map g
  let q' := (moduleExtensionFunctor.{max u' (max u (max u' v) w), max u u' v} A').map g'
  let : PreservesLimit (parallelPair q 0) U :=
    ulift_preserves_kernel.{max (max u u' v) w, v, u, u'} q
  let : PreservesLimit (parallelPair (U.map q) 0) P :=
    pushforward_preserves_kernel.{max u (max (max u u' v) w), v, u, u'} f (U.map q)
  let : P.PreservesZeroMorphisms := ⟨by intro X Y; ext Z x; rfl⟩
  let targetIso := restrictLiftIso f F
  let liftIso := PreservesKernel.iso U q
  let pushIso := PreservesKernel.iso P (U.map q)
  let dM := pushforwardUliftIso f
    (moduleExtension.{max u (max u' v) w, max u u' v} A M)
  let dN := pushforwardUliftIso f
    (moduleExtension.{max u (max u' v) w, max u u' v} A N)
  let eM := moduleExtensionRestrictIso f M
  let eN := moduleExtensionRestrictIso f N
  let uM := presheafOfModulesUliftIso.{u, max u u' v w}
    (algebraRingDiagram.{max u u' v} A')
    (moduleExtension.{max u' (max u (max u' v) w), max u u' v} A' M')
  let uN := presheafOfModulesUliftIso.{u, max u u' v w}
    (algebraRingDiagram.{max u u' v} A')
    (moduleExtension.{max u' (max u (max u' v) w), max u u' v} A' N')
  let sM := dM ≪≫ U'.mapIso eM ≪≫ uM
  let sN := dN ≪≫ U'.mapIso eN ≪≫ uN
  have hD := pushforwardUliftIso_naturality f q
  have hE := moduleExtensionRestrictIso_naturality f g
  have hD' : P.map (U.map q) ≫ dN.hom = dM.hom ≫ U'.map (P.map q) := by
    change (PresheafOfModules.pushforward (restrictRingDiagram.{max u u' v} f)).map
        ((presheafOfModulesUliftFunctor.{u}
          (algebraRingDiagram.{max u u' v} A)).map q) ≫ dN.hom = _
    exact hD
  have hU : U'.map q' ≫ uN.hom = uM.hom ≫ q' := by
    ext X x
    rfl
  have hsq : P.map (U.map q) ≫ sN.hom = sM.hom ≫ q' := by
    dsimp [sM, sN]
    calc
      P.map (U.map q) ≫ dN.hom ≫ U'.map eN.hom ≫ uN.hom =
          (dM.hom ≫ U'.map (P.map q)) ≫ U'.map eN.hom ≫ uN.hom := by
              change (P.map (U.map q) ≫ dN.hom) ≫ U'.map eN.hom ≫ uN.hom = _
              rw [hD']
      _ = dM.hom ≫ U'.map (P.map q ≫ eN.hom) ≫ uN.hom := by
              simp only [Functor.map_comp, Category.assoc]
      _ = dM.hom ≫ U'.map (eM.hom ≫ q') ≫ uN.hom := by rw [hE]
      _ = dM.hom ≫ U'.map eM.hom ≫ (uM.hom ≫ q') := by
            rw [← hU]
            simp only [Functor.map_comp, Category.assoc]
      _ = sM.hom ≫ q' := by simp [sM, Category.assoc]
  have kIso := kernel.mapIso (P.map (U.map q)) q' sM sN hsq
  exact ⟨M', N', g', ⟨targetIso.symm ≪≫ P.mapIso (U.mapIso e) ≪≫ P.mapIso liftIso ≪≫
    pushIso ≪≫ kIso⟩⟩


end AdequateFunctor
