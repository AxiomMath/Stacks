module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Pull and push for sheaves of graded modules

Let `f : (C, J, R) ⟶ (C', J', R')` be a morphism of ringed sites, presented as a functor
`u : C' ⥤ C` in the direction opposite to `f` together with the structure map
`σ : R' ⟶ f_*R` of its sheaves of rings. Let `A` be a sheaf of graded `R`-algebras on the
source, let `B` be a sheaf of graded `R'`-algebras on the target and let `φ : B ⟶ f_*A` be a
homomorphism of sheaves of graded algebras. The direct image

`f_* : Mod(A) ⥤ Mod(B)`

is constructed here: the degree-`n` piece of `f_*M` is the direct image `f_*M^n` of the
degree-`n` piece of `M`, and the multiplication

`f_*M^n × B^m --(id, φ^m)--> f_*M^n × f_*A^m --f_*μ_{n,m}--> f_*M^{n+m}`

is the one induced by the multiplication `μ_{n,m}` of `M` through `φ`. The same assignment
upgrades to the graded categories: it carries a homomorphism homogeneous of degree `n` to one
homogeneous of degree `n`.

## Main definitions

* `SheafOfModules.GradedAlgebra.SemilinearHom` is a homomorphism `φ : B ⟶ f_*A` of sheaves of
  graded algebras along a morphism of ringed sites, written out on local sections, and
  `SheafOfModules.DifferentialGradedAlgebra.SemilinearHom.toGradedAlgebraHom` is the one
  underlying a homomorphism of sheaves of differential graded algebras.
* `SheafOfModules.GradedModule.pushforwardObj` is the direct image `f_*M` of a right graded
  `A`-module, `SheafOfModules.GradedModule.pushforwardMap` is its action on homomorphisms and
  `SheafOfModules.GradedModule.pushforwardFunctor` is the functor `f_* : Mod(A) ⥤ Mod(B)`.
* `SheafOfModules.GradedModule.pushforwardHomOfDegree` is the direct image of a homomorphism
  homogeneous of degree `n`, i.e. the functor `f_* : Mod^gr(A) ⥤ Mod^gr(B)` of graded
  categories on morphisms.
* `SheafOfModules.GradedModule.SemilinearHom` is a `φ`-semilinear homomorphism `P ⟶ M` of right
  graded modules.

## Main results

* `SheafOfModules.GradedModule.semilinearHomEquiv`: a `φ`-semilinear homomorphism `P ⟶ M` is
  exactly a homomorphism `P ⟶ f_*M` of right graded `B`-modules, which is what makes the
  reading of the multiplication of `f_*M` above a theorem rather than a definition.
* `SheafOfModules.GradedModule.ofDifferentialGraded_pushforwardObj` and
  `SheafOfModules.GradedModule.ofDifferentialGraded_pushforwardMap`: the right graded module
  underlying the direct image of a right differential graded module **is** the direct image of
  the right graded module underlying it, so the graded and differential graded direct images
  are one construction.

## Implementation notes

The direct image is **constructed**, not pinned by a universal property: the direct image of a
sheaf of modules along a morphism of ringed sites is restriction of sections along `u` with
scalars restricted along `σ`, which is `SheafOfModules.sitePushforward`, so the sections of
`f_*M^n` over `V` are the sections of `M^n` over `u V` on the nose. Every law of a right graded
`B`-module is then inherited from the corresponding law of `M` at `u V` together with the laws
of `φ`, and every statement below is proved on sections.

The pullback and the adjunction `f^* ⊣ f_*` are not here but in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullback.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullbackConstruction.lean`, the latter
obtaining the pullback as the left adjoint of the direct image. Its identification with the
composite `f^*N = f^{-1}N ⊗_{f^{-1}B, φ} A` of the source is out of reach of this development,
which has no inverse image of a sheaf of graded modules, and whose relative tensor product
`SheafOfModules.RelativeTensor.gradedTensor` of a right graded `A`-module with a left graded
`A`-module is a graded sheaf of `O`-modules carrying no residual module structure, so neither
factor of that composite is available.

The homomorphisms homogeneous of degree `n` are `SheafOfModules.GradedHomOfDegree`, the
degreewise action-linear families of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedInternalHom.lean`; they are the morphisms
of the graded category `Mod^gr(A)`, so the direct image on them is the graded enhancement of
`f_*`.

Everything is stated for an arbitrary sheaf of rings on an arbitrary site, with the universes of
the two sites, their morphisms, the two algebras and the module sections independent, as in the
neighbouring graded files. The two sheaves of rings share the universe `t` because the structure
map relates them, and the module sections of a sheaf and of its direct image share the universe
`m` because `SheafOfModules.pushforward` preserves it.

## References

* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory

universe t a m v u a' v' u'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

namespace GradedAlgebra

/-- A homomorphism of sheaves of graded algebras along a morphism of ringed sites: a map
`B ⟶ f_*A`, given on local sections as a degreewise additive map from the sections of `B` over
`V` to the sections of `A` over `u V` which is compatible with restriction, semilinear over the
structure map `σ`, and a unital homomorphism of graded algebras. -/
structure SemilinearHom (u : C' ⥤ C) (σ : R'.obj ⟶ u.op ⋙ R.obj)
    (B : GradedAlgebra.{t, a'} R') (A : GradedAlgebra.{t, a} R) where
  /-- The map on local sections, from the sections of `B` over `V` to those of `A` over `u V`. -/
  app (i : ℤ) (V : C'ᵒᵖ) : (B.piece i).val.obj V →+ (A.piece i).val.obj (u.op.obj V)
  /-- The maps are semilinear over the structure map of the morphism of ringed sites. -/
  map_smul (i : ℤ) (V : C'ᵒᵖ) (s : R'.obj.obj V) (x : (B.piece i).val.obj V) :
    app i V (s • x) = (σ.app V).hom s • app i V x
  /-- The maps commute with restriction along a morphism of the site. -/
  naturality (i : ℤ) {V W : C'ᵒᵖ} (k : V ⟶ W) (x : (B.piece i).val.obj V) :
    app i W ((B.piece i).val.map k x) = (A.piece i).val.map (u.op.map k) (app i V x)
  /-- The maps respect the graded multiplication. -/
  map_mul (i j : ℤ) (V : C'ᵒᵖ) (x : (B.piece i).val.obj V) (y : (B.piece j).val.obj V) :
    app (i + j) V ((B.mul i j).app V x y) =
      (A.mul i j).app (u.op.obj V) (app i V x) (app j V y)
  /-- The maps carry the unit to the unit. -/
  map_one (V : C'ᵒᵖ) : app 0 V (B.one.eval V) = A.one.eval (u.op.obj V)

namespace SemilinearHom

variable {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {A : GradedAlgebra.{t, a} R}
  {B : GradedAlgebra.{t, a'} R'}

/-- A homomorphism of sheaves of graded algebras along a morphism of ringed sites is determined
by its values on local sections. -/
@[ext]
theorem ext {φ ψ : SemilinearHom u σ B A}
    (h : ∀ (i : ℤ) (V : C'ᵒᵖ) (x : (B.piece i).val.obj V), φ.app i V x = ψ.app i V x) :
    φ = ψ := by
  cases φ with
  | mk app smul nat mul one =>
    cases ψ with
    | mk app' smul' nat' mul' one' =>
      have happ : app = app' := by
        funext i V
        exact AddMonoidHom.ext fun x => h i V x
      subst happ
      rfl

end SemilinearHom

end GradedAlgebra

namespace DifferentialGradedAlgebra

/-- The homomorphism of sheaves of graded algebras along a morphism of ringed sites underlying a
homomorphism of sheaves of differential graded algebras along it, obtained by forgetting
compatibility with the differentials. -/
def SemilinearHom.toGradedAlgebraHom {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
    {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}
    (φ : SemilinearHom u σ A' A) :
    GradedAlgebra.SemilinearHom u σ A'.toGradedAlgebra A.toGradedAlgebra where
  app := φ.app
  map_smul := φ.map_smul
  naturality := φ.naturality
  map_mul := φ.map_mul
  map_one := φ.map_one

/-- The underlying homomorphism of sheaves of graded algebras has the same values on local
sections. -/
@[simp]
theorem SemilinearHom.toGradedAlgebraHom_app {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
    {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}
    (φ : SemilinearHom u σ A' A) (i : ℤ) (V : C'ᵒᵖ) :
    φ.toGradedAlgebraHom.app i V = φ.app i V :=
  rfl

end DifferentialGradedAlgebra

namespace GradedModule

variable {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : GradedAlgebra.{t, a} R} {B : GradedAlgebra.{t, a'} R'}

/-- The direct image `f_*M` of a right graded `A`-module along a morphism of ringed sites and a
homomorphism `φ : B ⟶ f_*A` of sheaves of graded algebras: its degree-`n` piece is the direct
image of the degree-`n` piece of `M`, and a homogeneous section `b` of `B` acts through
`φ b`. -/
@[stacks 0FR7 "the direct image f_*M of a graded module, with multiplication f_*μ ∘ (id, φ)"]
noncomputable def pushforwardObj (φ : GradedAlgebra.SemilinearHom u σ B A)
    (M : GradedModule.{t, a, m} A) : GradedModule.{t, a', m} B where
  piece n := (sitePushforward u σ).obj (M.piece n)
  smul n i V := (AddMonoidHom.compHom' (φ.app i V)).comp (M.smul n i (u.op.obj V))
  smul_smul_left n i V r x y := M.smul_smul_left n i (u.op.obj V) _ x (φ.app i V y)
  smul_smul_right n i V r x y := by
    change M.smul n i (u.op.obj V) x (φ.app i V (r • y)) = _
    rw [φ.map_smul]
    exact M.smul_smul_right n i (u.op.obj V) _ x (φ.app i V y)
  smul_naturality n i {V W} k x y := by
    change (M.piece (n + i)).val.map (u.op.map k) (M.smul n i (u.op.obj V) x (φ.app i V y)) =
      M.smul n i (u.op.obj W) ((M.piece n).val.map (u.op.map k) x)
        (φ.app i W ((B.piece i).val.map k y))
    rw [M.smul_naturality n i (u.op.map k) x (φ.app i V y), φ.naturality]
  smul_mul n i j V x y z := by
    have h := M.smul_mul n i j (u.op.obj V) x (φ.app i V y) (φ.app j V z)
    rw [← φ.map_mul] at h
    exact h
  smul_one n V x := by
    have h := M.smul_one n (u.op.obj V) x
    rw [← φ.map_one] at h
    exact h

/-- The degree-`n` piece of `f_*M` is the direct image of the degree-`n` piece of `M`. -/
@[simp]
theorem pushforwardObj_piece (φ : GradedAlgebra.SemilinearHom u σ B A)
    (M : GradedModule.{t, a, m} A) (n : ℤ) :
    (pushforwardObj φ M).piece n = (sitePushforward u σ).obj (M.piece n) :=
  rfl

/-- A homogeneous section `b` of `B` acts on `f_*M` as `φ b` acts on `M`. -/
@[simp]
theorem pushforwardObj_smul (φ : GradedAlgebra.SemilinearHom u σ B A)
    (M : GradedModule.{t, a, m} A) (n i : ℤ) (V : C'ᵒᵖ)
    (x : ((pushforwardObj φ M).piece n).val.obj V) (b : (B.piece i).val.obj V) :
    (pushforwardObj φ M).smul n i V x b = M.smul n i (u.op.obj V) x (φ.app i V b) :=
  rfl

/-- The direct image of a homomorphism of right graded `A`-modules is its degreewise direct
image. -/
@[stacks 0FR7 "the direct image is functorial in the graded module"]
noncomputable def pushforwardMap (φ : GradedAlgebra.SemilinearHom u σ B A)
    {M N : GradedModule.{t, a, m} A} (g : M ⟶ N) :
    pushforwardObj φ M ⟶ pushforwardObj φ N where
  app n := (sitePushforward u σ).map (g.app n)
  map_smul n i V x b := g.map_smul n i (u.op.obj V) x (φ.app i V b)

/-- The degree-`n` component of the direct image of `g` is the direct image of the degree-`n`
component of `g`. -/
@[simp]
theorem pushforwardMap_app (φ : GradedAlgebra.SemilinearHom u σ B A)
    {M N : GradedModule.{t, a, m} A} (g : M ⟶ N) (n : ℤ) :
    (pushforwardMap φ g).app n = (sitePushforward u σ).map (g.app n) :=
  rfl

/-- The direct image functor `f_* : Mod(A) ⥤ Mod(B)` on sheaves of graded modules. -/
@[stacks 0FR7 "the functor f_* : Mod(A) ⥤ Mod(B)"]
noncomputable def pushforwardFunctor (φ : GradedAlgebra.SemilinearHom u σ B A) :
    GradedModule.{t, a, m} A ⥤ GradedModule.{t, a', m} B where
  obj M := pushforwardObj φ M
  map g := pushforwardMap φ g
  map_id M := Hom.ext fun n => (sitePushforward u σ).map_id (M.piece n)
  map_comp g g' := Hom.ext fun n => (sitePushforward u σ).map_comp (g.app n) (g'.app n)

/-- The direct image functor sends `M` to `f_*M`. -/
@[simp]
theorem pushforwardFunctor_obj (φ : GradedAlgebra.SemilinearHom u σ B A)
    (M : GradedModule.{t, a, m} A) :
    (pushforwardFunctor φ).obj M = pushforwardObj φ M :=
  rfl

/-- The degree-`n` component of the image of `g` under the direct image functor is the direct
image of the degree-`n` component of `g`. -/
@[simp]
theorem pushforwardFunctor_map_app (φ : GradedAlgebra.SemilinearHom u σ B A)
    {M N : GradedModule.{t, a, m} A} (g : M ⟶ N) (n : ℤ) :
    ((pushforwardFunctor φ).map g).app n = (sitePushforward u σ).map (g.app n) :=
  rfl

section GradedCategory

/-- The direct image of a homomorphism of right graded `A`-modules homogeneous of degree `n`:
the degreewise direct image again, which is homogeneous of degree `n`. This is the action on
morphisms of the induced functor `f_* : Mod^gr(A) ⥤ Mod^gr(B)` of graded categories, whose
action on objects is `SheafOfModules.GradedModule.pushforwardObj`. -/
@[stacks 0FR7 "f_* as a functor of graded categories, on homogeneous morphisms of degree n"]
noncomputable def pushforwardHomOfDegree (φ : GradedAlgebra.SemilinearHom u σ B A)
    {M L : GradedModule.{t, a, m} A} {n : ℤ} (g : GradedHomOfDegree M L n) :
    GradedHomOfDegree (pushforwardObj φ M) (pushforwardObj φ L) n where
  app i j hij := (sitePushforward u σ).map (g.app i j hij)
  map_mul i j hij p V x b := g.map_mul i j hij p (u.op.obj V) x (φ.app p V b)

/-- The components of the direct image of a homomorphism homogeneous of degree `n` are the
direct images of its components. -/
@[simp]
theorem pushforwardHomOfDegree_app (φ : GradedAlgebra.SemilinearHom u σ B A)
    {M L : GradedModule.{t, a, m} A} {n : ℤ} (g : GradedHomOfDegree M L n) (i j : ℤ)
    (hij : i + n = j) :
    (pushforwardHomOfDegree φ g).app i j hij = (sitePushforward u σ).map (g.app i j hij) :=
  rfl

end GradedCategory

section Semilinear

/-- A `φ`-semilinear homomorphism of right graded modules along a morphism of ringed sites `f`
and a homomorphism `φ : B ⟶ f_*A` of sheaves of graded algebras: a degreewise additive map from
the sections of `P` over `V` to the sections of `M` over `u V`, compatible with restriction,
semilinear over the structure map, and carrying the action of a homogeneous section `b` of `B`
to the action of `φ b`. -/
structure SemilinearHom (φ : GradedAlgebra.SemilinearHom u σ B A)
    (P : GradedModule.{t, a', m} B) (M : GradedModule.{t, a, m} A) where
  /-- The map on local sections, from the sections of `P` over `V` to those of `M` over
  `u V`. -/
  app (i : ℤ) (V : C'ᵒᵖ) : (P.piece i).val.obj V →+ (M.piece i).val.obj (u.op.obj V)
  /-- The maps are semilinear over the structure map of the morphism of ringed sites. -/
  map_smul (i : ℤ) (V : C'ᵒᵖ) (s : R'.obj.obj V) (x : (P.piece i).val.obj V) :
    app i V (s • x) = (σ.app V).hom s • app i V x
  /-- The maps commute with restriction along a morphism of the site. -/
  naturality (i : ℤ) {V W : C'ᵒᵖ} (k : V ⟶ W) (x : (P.piece i).val.obj V) :
    app i W ((P.piece i).val.map k x) = (M.piece i).val.map (u.op.map k) (app i V x)
  /-- The maps carry the action of a homogeneous section `b` of `B` to the action of `φ b`. -/
  map_smul_right (n i : ℤ) (V : C'ᵒᵖ) (x : (P.piece n).val.obj V)
      (b : (B.piece i).val.obj V) :
    app (n + i) V (P.smul n i V x b) =
      M.smul n i (u.op.obj V) (app n V x) (φ.app i V b)

variable {φ : GradedAlgebra.SemilinearHom u σ B A} {P : GradedModule.{t, a', m} B}
  {M : GradedModule.{t, a, m} A}

omit [u.IsContinuous J' J] in
/-- A `φ`-semilinear homomorphism of right graded modules is determined by its values on local
sections. -/
@[ext]
theorem SemilinearHom.ext {θ θ' : SemilinearHom φ P M}
    (h : ∀ (i : ℤ) (V : C'ᵒᵖ) (x : (P.piece i).val.obj V), θ.app i V x = θ'.app i V x) :
    θ = θ' := by
  cases θ with
  | mk app smul nat mul =>
    cases θ' with
    | mk app' smul' nat' mul' =>
      have happ : app = app' := by
        funext i V
        exact AddMonoidHom.ext fun x => h i V x
      subst happ
      rfl

/-- The degree-`i` component of the homomorphism `P ⟶ f_*M` attached to a `φ`-semilinear
homomorphism. -/
noncomputable def semilinearComponent (θ : SemilinearHom φ P M) (i : ℤ) :
    P.piece i ⟶ (sitePushforward u σ).obj (M.piece i) :=
  semilinearSheafHom (fun V => θ.app i V) (θ.map_smul i) fun _ _ k x => θ.naturality i k x

/-- On local sections, the degree-`i` component attached to `θ` is the map `θ.app i V`. -/
@[simp]
theorem semilinearComponent_app (θ : SemilinearHom φ P M) (i : ℤ) (V : C'ᵒᵖ)
    (x : (P.piece i).val.obj V) :
    (semilinearComponent θ i).val.app V x = θ.app i V x :=
  rfl

/-- **A `φ`-semilinear homomorphism `P ⟶ M` is exactly a homomorphism `P ⟶ f_*M` of right graded
`B`-modules.** -/
@[stacks 0FR7 "f_*M corepresents the φ-semilinear homomorphisms into M"]
noncomputable def semilinearHomEquiv (φ : GradedAlgebra.SemilinearHom u σ B A)
    (P : GradedModule.{t, a', m} B) (M : GradedModule.{t, a, m} A) :
    SemilinearHom φ P M ≃ (P ⟶ pushforwardObj φ M) where
  toFun θ :=
    { app := fun i => semilinearComponent θ i
      map_smul := fun n i V x b => θ.map_smul_right n i V x b }
  invFun h :=
    { app := fun i V => homSections (h.app i) V
      map_smul := fun i V s x => (h.app i).val.app V |>.hom.map_smul s x
      naturality := fun i {V W} k x => PresheafOfModules.naturality_apply (h.app i).val k x
      map_smul_right := fun n i V x b => h.map_smul n i V x b }
  left_inv θ := SemilinearHom.ext fun _ _ _ => rfl
  right_inv h := Hom.ext fun i => by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- On local sections, the homomorphism `P ⟶ f_*M` attached to a `φ`-semilinear homomorphism
`θ` is given by `θ`. -/
@[simp]
theorem semilinearHomEquiv_apply_app (θ : SemilinearHom φ P M) (i : ℤ) (V : C'ᵒᵖ)
    (x : (P.piece i).val.obj V) :
    ((semilinearHomEquiv φ P M θ).app i).val.app V x = θ.app i V x :=
  rfl

/-- On local sections, the `φ`-semilinear homomorphism attached to a homomorphism
`h : P ⟶ f_*M` is given by `h`. -/
@[simp]
theorem semilinearHomEquiv_symm_apply_app (h : P ⟶ pushforwardObj φ M) (i : ℤ) (V : C'ᵒᵖ)
    (x : (P.piece i).val.obj V) :
    ((semilinearHomEquiv φ P M).symm h).app i V x = (h.app i).val.app V x :=
  rfl

end Semilinear

section DifferentialGraded

variable {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}

/-- **The graded direct image and the differential graded direct image are one construction**:
the right graded module underlying `f_*M` is the direct image of the right graded module
underlying `M`. -/
theorem ofDifferentialGraded_pushforwardObj
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (M : DifferentialGradedModule.{t, a, m} A) :
    ofDifferentialGraded (DifferentialGradedModule.pushforwardObj φ M) =
      pushforwardObj φ.toGradedAlgebraHom (ofDifferentialGraded M) :=
  rfl

/-- The homomorphism of right graded modules underlying the direct image of a morphism of right
differential graded modules is the direct image of the underlying homomorphism. -/
theorem ofDifferentialGraded_pushforwardMap
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    {M N : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ N) :
    ofDifferentialGradedMap (DifferentialGradedModule.pushforwardMap φ g) =
      pushforwardMap φ.toGradedAlgebraHom (ofDifferentialGradedMap g) :=
  rfl

end DifferentialGraded

end GradedModule

end SheafOfModules
