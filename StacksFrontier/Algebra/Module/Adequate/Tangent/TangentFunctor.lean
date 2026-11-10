module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksCore.Tactic.StacksAttribute

/-!
# The tangent functor of a module-valued functor

Evaluating a module-valued functor on the square-zero extension `B ⊕ M` and taking the kernel
of the augmentation produces the *tangent module* of the functor at `(B, M)`.  This file builds
the category of algebra-module pairs, the square-zero extension, the tangent functor with its
decomposition and multiplication maps, the second scalar action, the tangent functor at a fixed
algebra and the right exactness property `(*)`.

## References

* [Stacks Project, Tag 06Z8](https://stacks.math.columbia.edu/tag/06Z8)
* [Stacks Project, Tag 06ZB](https://stacks.math.columbia.edu/tag/06ZB)
* [Stacks Project, Tag 06ZF](https://stacks.math.columbia.edu/tag/06ZF)
-/

@[expose] public section

namespace AdequateFunctor

section

open CategoryTheory


/-- The ring-valued presheaf whose modules are module-valued functors on `A`-algebras. -/
abbrev algebraStructurePresheaf.{v, u} (A : Type u) [CommRing A] :
    ((CommAlgCat.{v} A)ᵒᵖ)ᵒᵖ ⥤ RingCat.{v} :=
  unopUnop (CommAlgCat.{v} A) ⋙ forget₂ (CommAlgCat.{v} A) CommRingCat ⋙
    forget₂ CommRingCat RingCat

/-- A pair of an `A`-algebra and a module over it. -/
structure AlgebraModulePair.{v, u} (A : Type u) [CommRing A] where
  /-- The algebra. -/
  algebra : Type v
  [commRing : CommRing algebra]
  [algebraStructure : Algebra A algebra]
  /-- The module. -/
  module : Type v
  [addCommGroup : AddCommGroup module]
  [moduleStructure : Module algebra module]

universe u v w

namespace AlgebraModulePair

attribute [instance] commRing algebraStructure addCommGroup moduleStructure

/-- A morphism of pairs, semilinear over its algebra homomorphism. -/
structure Hom {A : Type u} [CommRing A] (X Y : AlgebraModulePair.{v} A) where
  /-- The algebra homomorphism. -/
  base : X.algebra →ₐ[A] Y.algebra
  /-- The semilinear module map. -/
  linear : X.module →ₛₗ[base.toRingHom] Y.module

/-- Two morphisms of pairs are equal when their algebra homomorphisms and module maps agree. -/
@[ext]
lemma Hom.ext {A : Type u} [CommRing A] {X Y : AlgebraModulePair.{v} A} (f g : Hom X Y)
    (hbase : f.base = g.base) (hlinear : ∀ x, f.linear x = g.linear x) : f = g := by
  cases f with
  | mk fb fl =>
    cases g with
    | mk gb gl =>
      dsimp at hbase hlinear
      cases hbase
      congr
      exact LinearMap.ext hlinear

/-- The identity of a pair. -/
def id {A : Type u} [CommRing A] (X : AlgebraModulePair.{v} A) : Hom X X where
  base := AlgHom.id A X.algebra
  linear :=
    { toFun := _root_.id
      map_add' := by simp
      map_smul' := by simp }

/-- Composition of morphisms of pairs. -/
def comp {A : Type u} [CommRing A] {X Y Z : AlgebraModulePair.{v} A}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := g.base.comp f.base
  linear := g.linear.comp f.linear

/-- The category of algebra-module pairs and semilinear morphisms of pairs. -/
instance {A : Type u} [CommRing A] : Category (AlgebraModulePair.{v} A) where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := by ext <;> rfl
  comp_id f := by ext <;> rfl
  assoc f g h := by ext <;> rfl

end AlgebraModulePair

variable (A : Type u) [CommRing A]

/-- Evaluation of a module-valued functor at an algebra. -/
abbrev moduleValue (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))
    (B : Type v) [CommRing B] [Algebra A B] : Type w :=
  F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))

/-- The value of `F` at `B` is a `B`-module. -/
instance moduleValue.module (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))
    (B : Type v) [CommRing B] [Algebra A B] : Module B (moduleValue A F B) :=
  (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))).isModule

/-- The semilinear map on values induced by an algebra homomorphism. -/
noncomputable abbrev moduleValueMap
    (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))
    {B C : Type v} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) : moduleValue A F B →ₛₗ[f.toRingHom] moduleValue A F C :=
  F.restrictₛₗ ((CommAlgCat.ofHom f).op.op)

/-- The module of a pair is a module over the opposite of its algebra. -/
instance pairModuleOp (X : AlgebraModulePair.{v} A) : Module X.algebraᵐᵒᵖ X.module :=
  Module.compHom _ ((RingHom.id X.algebra).fromOpposite mul_comm)

/-- The action of the algebra of a pair on its module is central. -/
instance pairModuleCentral (X : AlgebraModulePair.{v} A) :
    IsCentralScalar X.algebra X.module := ⟨fun _ _ => rfl⟩

/-- The module of a pair is an `A`-module by restriction of scalars along `A → B`. -/
instance pairModuleBase (X : AlgebraModulePair.{v} A) : Module A X.module :=
  Module.compHom X.module (algebraMap A X.algebra)

/-- The actions of `A` and of the algebra on the module of a pair form a scalar tower. -/
instance pairModuleTower (X : AlgebraModulePair.{v} A) :
    IsScalarTower A X.algebra X.module :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The actions of `A` and of the opposite algebra on the module of a pair form a scalar
tower. -/
instance pairModuleOpTower (X : AlgebraModulePair.{v} A) :
    IsScalarTower A X.algebraᵐᵒᵖ X.module :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The square-zero extension of a pair. -/
def squareZeroAlgebra (X : AlgebraModulePair.{v} A) : CommAlgCat.{v} A :=
  CommAlgCat.of A (TrivSqZeroExt X.algebra X.module)

/-- The square-zero extension `B ⊕ N` is a `B`-algebra. -/
instance squareZeroAlgebra.algebra (X : AlgebraModulePair.{v} A) :
    Algebra X.algebra (squareZeroAlgebra A X) :=
  inferInstanceAs (Algebra X.algebra (TrivSqZeroExt X.algebra X.module))

/-- The inclusion of the square-zero ideal `N → B[N]`. -/
def squareZeroInr (X : AlgebraModulePair.{v} A) :
    X.module →ₗ[X.algebra] squareZeroAlgebra A X :=
  TrivSqZeroExt.inrHom X.algebra X.module

/-- The zero section of the square-zero extension. -/
abbrev squareZeroSection (X : AlgebraModulePair.{v} A) :
    X.algebra →ₐ[A] squareZeroAlgebra A X :=
  TrivSqZeroExt.inlAlgHom A X.algebra X.module

/-- The augmentation of the square-zero extension. -/
abbrev squareZeroAugmentation (X : AlgebraModulePair.{v} A) :
    squareZeroAlgebra A X →ₐ[A] X.algebra :=
  TrivSqZeroExt.fstHom A X.algebra X.module

/-- A morphism of pairs induces the coordinatewise homomorphism of square-zero extensions. -/
@[simps! apply]
def squareZeroMap {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y) :
    squareZeroAlgebra A X →ₐ[A] squareZeroAlgebra A Y where
  toFun x := ⟨f.base x.fst, f.linear x.snd⟩
  map_zero' := TrivSqZeroExt.ext (map_zero f.base) (map_zero f.linear)
  map_one' := TrivSqZeroExt.ext (map_one f.base) (map_zero f.linear)
  map_add' x y :=
    TrivSqZeroExt.ext (map_add f.base x.fst y.fst) (map_add f.linear x.snd y.snd)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul f.base x.fst y.fst
    · change f.linear (x.fst • y.snd + y.fst • x.snd) =
        f.base x.fst • f.linear y.snd + f.base y.fst • f.linear x.snd
      rw [map_add, f.linear.map_smulₛₗ, f.linear.map_smulₛₗ]
      rfl
  commutes' a := TrivSqZeroExt.ext (f.base.commutes a) (map_zero f.linear)

variable (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))

/-- The value of `F` on the square-zero extension. -/
abbrev extensionValue (X : AlgebraModulePair.{v} A) : Type w :=
  moduleValue A F (squareZeroAlgebra A X)

/-- The value of `F` on `B ⊕ N` is a `B`-module by restriction along the zero section. -/
instance extensionValue.module (X : AlgebraModulePair.{v} A) :
    Module X.algebra (extensionValue A F X) :=
  Module.compHom _ (squareZeroSection A X).toRingHom

/-- The actions of `B` and of `B ⊕ N` on the value of `F` on `B ⊕ N` form a scalar tower. -/
instance extensionValue.isScalarTower (X : AlgebraModulePair.{v} A) :
    IsScalarTower X.algebra (squareZeroAlgebra A X) (extensionValue A F X) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The tangent kernel, with scalars restricted along the zero section `B → B[N]`. -/
@[stacks 06Z8 "parts (1) and (2): the kernel with its restricted module structure"]
noncomputable def tangentKernel (X : AlgebraModulePair.{v} A) :
    Submodule X.algebra (extensionValue A F X) :=
  (LinearMap.ker (moduleValueMap A F (squareZeroAugmentation A X))).restrictScalars X.algebra

/-- The tangent module `TF(B,N)`. -/
abbrev tangentModule (X : AlgebraModulePair.{v} A) : Type w := tangentKernel A F X

/-- The canonical decomposition together with the formula for its inverse. -/
abbrev TangentDecompositionData (X : AlgebraModulePair.{v} A) : Type w :=
  {e : extensionValue A F X ≃ₗ[X.algebra]
      (moduleValue A F X.algebra × tangentModule A F X) //
    ∀ (y : moduleValue A F X.algebra) (t : tangentModule A F X),
      e.symm (y, t) = moduleValueMap A F (squareZeroSection A X) y +
        (t : extensionValue A F X)}

/-- Functorial semilinear maps on the tangent kernels, characterized by their inclusions into
the values on square-zero extensions. -/
structure TangentFunctorData where
  /-- The induced map on tangent modules. -/
  map : ∀ {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y),
    tangentModule A F X →ₛₗ[f.base.toRingHom] tangentModule A F Y
  /-- The tangent map is the restriction of the map on the square-zero extensions. -/
  map_coe : ∀ {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y) (x : tangentModule A F X),
    (map f x : extensionValue A F Y) = moduleValueMap A F (squareZeroMap A f) x
  /-- Identity law. -/
  map_id : ∀ (X : AlgebraModulePair.{v} A) (x : tangentModule A F X), map (𝟙 X) x = x
  /-- Composition law. -/
  map_comp : ∀ {X Y Z : AlgebraModulePair.{v} A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : tangentModule A F X), map (f ≫ g) x = map g (map f x)

/-- The map on values induced by a composite of algebra homomorphisms is the composite of the
induced maps. -/
lemma moduleValueMap_comp
    {B C D : Type v} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D]
    (f : B →ₐ[A] C) (g : C →ₐ[A] D) (x : moduleValue A F B) :
    moduleValueMap A F (g.comp f) x =
      moduleValueMap A F g (moduleValueMap A F f x) := by
  change F.map (CommAlgCat.ofHom (g.comp f)).op.op x =
    F.map (CommAlgCat.ofHom g).op.op (F.map (CommAlgCat.ofHom f).op.op x)
  rw [show (CommAlgCat.ofHom (g.comp f)).op.op =
      (CommAlgCat.ofHom f).op.op ≫ (CommAlgCat.ofHom g).op.op by rfl]
  exact F.map_comp_apply ((CommAlgCat.ofHom f).op.op) ((CommAlgCat.ofHom g).op.op) x

/-- Equal composites of algebra homomorphisms induce equal composites on values. -/
private lemma moduleValueMap_comp_congr
    {B C D E : Type v} [CommRing B] [CommRing C] [CommRing D] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra A E]
    {f : B →ₐ[A] C} {g : C →ₐ[A] E} {f' : B →ₐ[A] D} {g' : D →ₐ[A] E}
    (h : g.comp f = g'.comp f') (x : moduleValue A F B) :
    moduleValueMap A F g (moduleValueMap A F f x) =
      moduleValueMap A F g' (moduleValueMap A F f' x) := by
  rw [← moduleValueMap_comp, h, moduleValueMap_comp]

/-- The canonical tangent functor on pairs of algebras and modules. -/
@[stacks 06Z8 "part (3): the canonical tangent functor"]
noncomputable def tangentFunctor : TangentFunctorData A F := by
  let map : ∀ {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y),
      tangentModule A F X →ₛₗ[f.base.toRingHom] tangentModule A F Y := fun {X Y} f =>
    { toFun := fun x =>
        ⟨moduleValueMap A F (squareZeroMap A f) x, by
          change moduleValueMap A F (squareZeroAugmentation A _) _ = 0
          rw [← moduleValueMap_comp, show (squareZeroAugmentation A _).comp (squareZeroMap A f) =
              f.base.comp (squareZeroAugmentation A _) by ext z; rfl, moduleValueMap_comp]
          have hx := x.property
          change moduleValueMap A F (squareZeroAugmentation A X)
            (x : extensionValue A F X) = 0 at hx
          rw [hx, map_zero]⟩
      map_add' := fun x y => by ext; exact map_add _ _ _
      map_smul' := fun r x => by
        ext
        change moduleValueMap A F (squareZeroMap A f)
            (squareZeroSection A X r • (x : extensionValue A F X)) =
          squareZeroSection A Y (f.base r) • moduleValueMap A F (squareZeroMap A f) x
        rw [(moduleValueMap A F (squareZeroMap A f)).map_smulₛₗ]
        congr 1
        apply TrivSqZeroExt.ext
        · rfl
        · exact map_zero f.linear }
  refine { map := map, map_coe := ?_, map_id := ?_, map_comp := ?_ }
  · intro X Y f x
    rfl
  · intro X x
    apply Subtype.ext
    dsimp only [map]
    change F.map (CommAlgCat.ofHom (squareZeroMap A (𝟙 X))).op.op
      (x : extensionValue A F X) = (x : extensionValue A F X)
    have hAlg : CommAlgCat.ofHom (squareZeroMap A (𝟙 X)) = 𝟙 _ := by
      ext z
      rfl
    have h := congrArg (fun q => q.op.op) hAlg
    rw [F.congr_map_apply h (x : extensionValue A F X)]
    exact congrArg (fun g => g (x : extensionValue A F X)) (F.map_id _)
  · intro X Y Z f g x
    apply Subtype.ext
    dsimp only [map]
    change moduleValueMap A F (squareZeroMap A (f ≫ g)) (x : extensionValue A F X) =
      moduleValueMap A F (squareZeroMap A g)
        (moduleValueMap A F (squareZeroMap A f) (x : extensionValue A F X))
    rw [show squareZeroMap A (f ≫ g) =
        (squareZeroMap A g).comp (squareZeroMap A f) by ext z; rfl]
    exact moduleValueMap_comp A F _ _ _

/-- The underlying functor to abelian groups of the tangent functor. -/
noncomputable def TangentFunctorData.toFunctor (T : TangentFunctorData A F) :
    AlgebraModulePair.{v} A ⥤ Ab.{w} where
  obj X := AddCommGrpCat.of (tangentModule A F X)
  map f := AddCommGrpCat.ofHom (T.map f).toAddMonoidHom
  map_id X := by ext x; exact congrArg Subtype.val (T.map_id X x)
  map_comp f g := by ext x; exact congrArg Subtype.val (T.map_comp f g x)

/-- The canonical decomposition, specified by the sum of the zero section and the kernel
inclusion as its inverse. -/
@[stacks 06Z8 "the canonical direct-sum decomposition"]
noncomputable def tangentDecompositionData (X : AlgebraModulePair.{v} A) :
    TangentDecompositionData A F X := by
  let p : extensionValue A F X →ₗ[X.algebra] moduleValue A F X.algebra :=
    { toFun := moduleValueMap A F (squareZeroAugmentation A X)
      map_add' := map_add _
      map_smul' := fun r x => by
        change moduleValueMap A F (squareZeroAugmentation A X)
          (squareZeroSection A X r • x) =
            r • moduleValueMap A F (squareZeroAugmentation A X) x
        rw [(moduleValueMap A F (squareZeroAugmentation A X)).map_smulₛₗ]
        rfl }
  let s : moduleValue A F X.algebra →ₗ[X.algebra] extensionValue A F X :=
    { toFun := moduleValueMap A F (squareZeroSection A X)
      map_add' := map_add _
      map_smul' := fun r x => (moduleValueMap A F (squareZeroSection A X)).map_smulₛₗ r x }
  have hps (x : moduleValue A F X.algebra) : p (s x) = x := by
    change moduleValueMap A F (squareZeroAugmentation A X)
      (moduleValueMap A F (squareZeroSection A X) x) = x
    rw [← moduleValueMap_comp]
    have hAlg : (squareZeroAugmentation A X).comp (squareZeroSection A X) =
        AlgHom.id A X.algebra := by ext z; rfl
    rw [hAlg]
    change F.map (𝟙 _) x = x
    exact congrArg (fun g => g x) (F.map_id _)
  let e : extensionValue A F X →ₗ[X.algebra]
      (moduleValue A F X.algebra × tangentModule A F X) :=
    { toFun := fun x => (p x, ⟨x - s (p x), by
          change p (x - s (p x)) = 0
          simp [hps]⟩)
      map_add' := fun x y => by
        apply Prod.ext
        · exact p.map_add x y
        · apply Subtype.ext
          dsimp
          rw [p.map_add, s.map_add]
          abel
      map_smul' := fun r x => by
        apply Prod.ext
        · exact p.map_smul r x
        · apply Subtype.ext
          dsimp
          rw [p.map_smul, s.map_smul, smul_sub] }
  let inv : (moduleValue A F X.algebra × tangentModule A F X) →ₗ[X.algebra]
      extensionValue A F X :=
    { toFun := fun z => s z.1 + z.2
      map_add' := fun x y => by dsimp; rw [s.map_add]; abel
      map_smul' := fun r x => by dsimp; rw [s.map_smul, smul_add] }
  refine ⟨LinearEquiv.ofLinearMap e inv ?_ ?_, ?_⟩
  · apply LinearMap.ext
    intro z
    rcases z with ⟨y, t⟩
    apply Prod.ext
    · change p (s y + (t : extensionValue A F X)) = y
      rw [p.map_add, hps]
      have ht : p (t : extensionValue A F X) = 0 := t.property
      rw [ht, add_zero]
    · apply Subtype.ext
      dsimp [e, inv]
      rw [p.map_add, hps]
      rw [show p (t : extensionValue A F X) = 0 by exact t.property]
      rw [add_zero]
      abel
  · apply LinearMap.ext
    intro x
    dsimp [e, inv]
    abel
  · intro y t
    rfl

/-- The linear equivalence in the tangent decomposition. -/
noncomputable abbrev tangentDecomposition (X : AlgebraModulePair.{v} A) :
    extensionValue A F X ≃ₗ[X.algebra]
      (moduleValue A F X.algebra × tangentModule A F X) :=
  (tangentDecompositionData A F X).val

/-- Multiplication by the square-zero ideal, specified on pure tensors. -/
@[stacks 06Z8 "part (4): the canonical multiplication map"]
noncomputable def tangentMultiplicationData (X : AlgebraModulePair.{v} A) :
    {μ : TensorProduct X.algebra X.module (moduleValue A F X.algebra) →ₗ[X.algebra]
        tangentModule A F X //
      ∀ (n : X.module) (y : moduleValue A F X.algebra),
        (μ (TensorProduct.tmul X.algebra n y) : extensionValue A F X) =
          squareZeroInr A X n •
            moduleValueMap A F (squareZeroSection A X) y} := by
  let b : X.module →ₗ[X.algebra]
      moduleValue A F X.algebra →ₗ[X.algebra] tangentModule A F X :=
    { toFun := fun n =>
        { toFun := fun y => ⟨squareZeroInr A X n •
              moduleValueMap A F (squareZeroSection A X) y, by
              change moduleValueMap A F (squareZeroAugmentation A X)
                (squareZeroInr A X n • moduleValueMap A F (squareZeroSection A X) y) = 0
              rw [(moduleValueMap A F (squareZeroAugmentation A X)).map_smulₛₗ]
              change (0 : X.algebra) • _ = 0
              exact zero_smul _ _⟩
          map_add' := fun y z => by
            apply Subtype.ext
            change squareZeroInr A X n •
                moduleValueMap A F (squareZeroSection A X) (y + z) =
              squareZeroInr A X n • moduleValueMap A F (squareZeroSection A X) y +
                squareZeroInr A X n • moduleValueMap A F (squareZeroSection A X) z
            rw [map_add, smul_add]
          map_smul' := fun r y => by
            apply Subtype.ext
            change squareZeroInr A X n •
                moduleValueMap A F (squareZeroSection A X) (r • y) =
              r • (squareZeroInr A X n • moduleValueMap A F (squareZeroSection A X) y)
            rw [(moduleValueMap A F (squareZeroSection A X)).map_smulₛₗ]
            change squareZeroInr A X n •
                (squareZeroSection A X r • moduleValueMap A F (squareZeroSection A X) y) =
              squareZeroSection A X r •
                (squareZeroInr A X n • moduleValueMap A F (squareZeroSection A X) y)
            simp only [smul_smul]
            rw [mul_comm] }
      map_add' := fun n m => by
        apply LinearMap.ext
        intro y
        rw [LinearMap.add_apply]
        apply Subtype.ext
        change squareZeroInr A X (n + m) •
            moduleValueMap A F (squareZeroSection A X) y =
          squareZeroInr A X n • moduleValueMap A F (squareZeroSection A X) y +
            squareZeroInr A X m • moduleValueMap A F (squareZeroSection A X) y
        rw [map_add, add_smul]
      map_smul' := fun r n => by
        apply LinearMap.ext
        intro y
        rw [LinearMap.smul_apply]
        apply Subtype.ext
        change squareZeroInr A X (r • n) • _ =
          r • (squareZeroInr A X n • _)
        rw [map_smul]
        exact smul_assoc r (squareZeroInr A X n)
          (moduleValueMap A F (squareZeroSection A X) y) }
  refine ⟨TensorProduct.lift b, ?_⟩
  intro n y
  rfl

/-- The canonical linear map `N ⊗[B] F(B) → TF(B,N)`. -/
noncomputable abbrev tangentMultiplication (X : AlgebraModulePair.{v} A) :
    TensorProduct X.algebra X.module (moduleValue A F X.algebra) →ₗ[X.algebra]
      tangentModule A F X :=
  (tangentMultiplicationData A F X).val

/-- The tangent kernel is precisely the vanishing locus of the augmentation map. -/
@[simp]
lemma mem_tangentKernel (X : AlgebraModulePair.{v} A) (x : extensionValue A F X) :
    x ∈ tangentKernel A F X ↔ moduleValueMap A F (squareZeroAugmentation A X) x = 0 :=
  Iff.rfl

/-- The first coordinate of the canonical decomposition is the augmentation. -/
@[stacks 06Z8 "the augmentation coordinate of the decomposition", simp]
lemma tangentDecomposition_fst (X : AlgebraModulePair.{v} A) (x : extensionValue A F X) :
    (tangentDecomposition A F X x).1 =
      moduleValueMap A F (squareZeroAugmentation A X) x := by
  unfold tangentDecomposition tangentDecompositionData; rfl

/-- The map on square-zero extensions commutes with the zero sections. -/
private lemma squareZeroMap_comp_section {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y) :
    (squareZeroMap A f).comp (squareZeroSection A X) = (squareZeroSection A Y).comp f.base := by
  ext z
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero f.linear

/-- The decomposition is natural for morphisms of pairs, including changes of base algebra. -/
@[stacks 06Z8 "naturality of the decomposition"]
lemma tangentDecomposition_naturality {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y)
    (x : extensionValue A F X) :
    tangentDecomposition A F Y (moduleValueMap A F (squareZeroMap A f) x) =
      (moduleValueMap A F f.base (tangentDecomposition A F X x).1,
        (tangentFunctor A F).map f (tangentDecomposition A F X x).2) := by
  have hfst : moduleValueMap A F (squareZeroAugmentation A Y)
      (moduleValueMap A F (squareZeroMap A f) x) =
      moduleValueMap A F f.base (moduleValueMap A F (squareZeroAugmentation A X) x) :=
    moduleValueMap_comp_congr A F (by ext z; rfl) x
  unfold tangentDecomposition tangentDecompositionData
  apply Prod.ext
  · exact hfst
  · apply Subtype.ext
    rw [(tangentFunctor A F).map_coe]
    change moduleValueMap A F (squareZeroMap A f) x -
        moduleValueMap A F (squareZeroSection A Y)
          (moduleValueMap A F (squareZeroAugmentation A Y)
            (moduleValueMap A F (squareZeroMap A f) x)) =
      moduleValueMap A F (squareZeroMap A f)
        (x - moduleValueMap A F (squareZeroSection A X)
          (moduleValueMap A F (squareZeroAugmentation A X) x))
    rw [map_sub, hfst]
    congr 1
    exact (moduleValueMap_comp_congr A F (squareZeroMap_comp_section A f) _).symm

/-- The multiplication maps form a natural transformation on the category of pairs. -/
@[stacks 06Z8 "part (4): naturality of multiplication"]
lemma tangentMultiplication_naturality {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y)
    (t : TensorProduct X.algebra X.module (moduleValue A F X.algebra)) :
    (tangentFunctor A F).map f (tangentMultiplication A F X t) =
      tangentMultiplication A F Y
        (TensorProduct.map f.linear (moduleValueMap A F f.base) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul n y =>
      apply Subtype.ext
      rw [(tangentFunctor A F).map_coe]
      change moduleValueMap A F (squareZeroMap A f)
          (squareZeroInr A X n • moduleValueMap A F (squareZeroSection A X) y) =
        squareZeroInr A Y (f.linear n) •
          moduleValueMap A F (squareZeroSection A Y) (moduleValueMap A F f.base y)
      rw [(moduleValueMap A F (squareZeroMap A f)).map_smulₛₗ]
      congr 1
      · apply TrivSqZeroExt.ext
        · change f.base 0 = 0
          exact map_zero f.base
        · rfl
      · exact moduleValueMap_comp_congr A F (squareZeroMap_comp_section A f) y
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]

/-- The tangent module of a zero module is zero. -/
@[stacks 06Z8 "part (5): vanishing at the zero module", instance]
lemma tangentModule_subsingleton (X : AlgebraModulePair.{v} A) [Subsingleton X.module] :
    Subsingleton (tangentModule A F X) := by
  constructor; intro x y
  apply Subtype.ext
  have vanish (z : tangentModule A F X) : (z : extensionValue A F X) = 0 := by
    have hAlg : (squareZeroSection A X).comp (squareZeroAugmentation A X) =
        AlgHom.id A (squareZeroAlgebra A X) := by
      apply AlgHom.ext
      intro q
      apply TrivSqZeroExt.ext
      · rfl
      · exact Subsingleton.elim _ _
    have hz : moduleValueMap A F (squareZeroAugmentation A X)
        (z : extensionValue A F X) = 0 := z.property
    have h := moduleValueMap_comp A F (squareZeroAugmentation A X)
      (squareZeroSection A X) (z : extensionValue A F X)
    rw [hAlg] at h
    have hid : moduleValueMap A F (AlgHom.id A (squareZeroAlgebra A X))
        (z : extensionValue A F X) = (z : extensionValue A F X) := by
      change F.map (CommAlgCat.ofHom (AlgHom.id A (squareZeroAlgebra A X))).op.op
        (z : extensionValue A F X) = (z : extensionValue A F X)
      have hId : CommAlgCat.ofHom (AlgHom.id A (squareZeroAlgebra A X)) = 𝟙 _ := by rfl
      have hCat := congrArg (fun q => q.op.op) hId
      rw [F.congr_map_apply hCat (z : extensionValue A F X)]
      exact congrArg (fun g => g (z : extensionValue A F X)) (F.map_id _)
    calc
      (z : extensionValue A F X) =
          moduleValueMap A F (AlgHom.id A (squareZeroAlgebra A X)) z := hid.symm
      _ = moduleValueMap A F (squareZeroSection A X)
          (moduleValueMap A F (squareZeroAugmentation A X) z) := h
      _ = 0 := by rw [hz, map_zero]
  rw [vanish x, vanish y]

/-- A morphism of pairs whose module map is zero induces the zero tangent map. -/
@[stacks 06Z8 "part (5): zero module maps induce zero tangent maps"]
lemma tangentFunctor_map_eq_zero {X Y : AlgebraModulePair.{v} A} (f : X ⟶ Y)
    (hf : f.linear = 0) : (tangentFunctor A F).map f = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [(tangentFunctor A F).map_coe]
  change moduleValueMap A F (squareZeroMap A f)
    (x : extensionValue A F X) = 0
  have hAlg : squareZeroMap A f =
      (squareZeroSection A Y).comp (f.base.comp (squareZeroAugmentation A X)) := by
    apply AlgHom.ext
    intro z
    apply TrivSqZeroExt.ext
    · rfl
    · change f.linear z.snd = 0
      rw [hf]
      rfl
  rw [hAlg, moduleValueMap_comp, moduleValueMap_comp,
    show moduleValueMap A F (squareZeroAugmentation A X)
      (x : extensionValue A F X) = 0 from x.property, map_zero, map_zero]

end

section

open AdequateFunctor

universe u v w

variable (A : Type u) [CommRing A]
variable (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))

/-- The second scalar operation on a tangent module, induced by multiplication
on the module variable. -/
@[stacks 06ZB "second_scalar_action"]
noncomputable def secondScalarAction (X : AlgebraModulePair.{v} A)
    (x : tangentModule A F X) (b : X.algebra) : tangentModule A F X :=
  (tangentFunctor A F).map
    { base := AlgHom.id A X.algebra
      linear := LinearMap.lsmul X.algebra X.module b }
    x

end

section

open CategoryTheory


open AdequateFunctor AdequateFunctor.AlgebraModulePair

universe u v w

variable (A : Type u) [CommRing A]
variable (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))

/-- Regard modules over a fixed `A`-algebra as algebra-module pairs. -/
@[implicit_reducible]
def fixedAlgebraModuleFunctor (B : Type v) [CommRing B] [Algebra A B] :
    ModuleCat.{v} B ⥤ AlgebraModulePair.{v} A where
  obj M :=
    { algebra := B
      module := M }
  map {M N} f :=
    { base := AlgHom.id A B
      linear :=
        { toFun := f.hom
          map_add' := f.hom.map_add
          map_smul' := by simp } }
  map_id M := by
    apply Hom.ext
    · rfl
    · intro x
      rfl
  map_comp f g := by
    apply Hom.ext
    · rfl
    · intro x
      rfl

/-- The tangent functor in the module variable, with the `A`-algebra `B` fixed. -/
@[implicit_reducible]
noncomputable def tangentFunctorAt (B : Type v) [CommRing B] [Algebra A B] :
    ModuleCat.{v} B ⥤ Ab.{w} :=
  fixedAlgebraModuleFunctor A B ⋙ (tangentFunctor A F).toFunctor

/-- The tangent functor at a fixed algebra preserves zero morphisms. -/
instance tangentFunctorAt_preservesZeroMorphisms (B : Type v) [CommRing B] [Algebra A B] :
    (tangentFunctorAt A F B).PreservesZeroMorphisms where
  map_zero M N := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact DFunLike.congr_fun
      (tangentFunctor_map_eq_zero A F ((fixedAlgebraModuleFunctor A B).map 0) rfl) x

/-- Property `(*)`: over every `A`-algebra, the tangent functor sends a short exact
sequence of modules to an exact sequence ending in an epimorphism. -/
@[stacks 06ZF "property"]
abbrev HasRightExactTangentFunctor : Prop :=
  ∀ (B : Type v) [CommRing B] [Algebra A B] (S : ShortComplex (ModuleCat.{v} B)),
    S.ShortExact →
      (S.map (tangentFunctorAt A F B)).Exact ∧ Epi ((tangentFunctorAt A F B).map S.g)

end

section

open CategoryTheory


universe u v w

/-- The standing situation in which the tangent functor of a module-valued
functor preserves right exactness at every algebra. -/
public structure RightExactTangentFunctor where
  /-- The base ring. -/
  A : Type u
  [commRing : CommRing A]
  /-- The module-valued functor. -/
  F : PresheafOfModules.{w} (AdequateFunctor.algebraStructurePresheaf.{v} A)
  /-- Every fixed-algebra tangent functor sends short exact sequences to
  right exact sequences. -/
  rightExact : AdequateFunctor.HasRightExactTangentFunctor A F

attribute [instance] RightExactTangentFunctor.commRing

end

end AdequateFunctor

end
