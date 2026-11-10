module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionSystemEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeSquare
public import StacksFrontier.Algebra.DifferentialGraded.Module.FilteredColimit

/-!
# Extension of differential graded modules from a subcategory of a chaotic site

Let `F : C' ⥤ C` be a functor of categories, both viewed as sites with the chaotic topology, such
that for every object `U` of `C` the category `U/F` of arrows `U → F U'` is cofiltered. Let `O` be
a sheaf of commutative rings on `C`, let `(A, d)` be a sheaf of differential graded `O`-algebras
and let `(A', d)` be its restriction to `C'`, whose sections over `U'` are those of `A` over
`F U'`. A presheaf of section modules along `F` — a differential graded `A(F U')`-module `X(U')`
for every object `U'` of `C'`, with restriction homomorphisms — extends to a presheaf of section
modules over `A` by the rule

`E(X)(U) = colim_{U → F U' ∈ U/F} X(U') ⊗_{A(F U')} A(U)`,

a filtered colimit of differential graded `A(U)`-modules, together with the restriction
`Y ↦ (U' ↦ Y(F U'))` in the other direction.

## Implementation notes

Presheaves of section modules along `F` are those over `A'`, read through `A'(U') = A(F U')`;
working along `F` avoids comparing the two algebras of sections, which are equal only after
unfolding both.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.AlongSystem`: presheaves of section
  modules along `F`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.arrowHom`: the homomorphism
  `A(F U') ⟶ A(U)` of differential graded algebras of sections attached to an arrow `U → F U'`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.diagram`: the filtered diagram
  `U → F U' ↦ X(U') ⊗_{A(F U')} A(U)`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.extSystem`: the extension `E(X)`, a
  presheaf of section modules over `A`, and `extFunctor` its functoriality in `X`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.restrictSystem`: the restriction
  `U' ↦ Y(F U')` of a presheaf of section modules over `A`, and `restrictFunctor`.

## References

* [Stacks Project, Lemma 24.34.1 (Tag 0GZE)](https://stacks.math.columbia.edu/tag/0GZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits
open DifferentialGradedModule (restrictScalarsFunctor restrictScalarsIdHom restrictScalarsIdInv)
open DifferentialGraded.Bimodule (tensorCompFunctor regular tensorPure plainTranspose
  tensorSquareMap)

universe u

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace DifferentialGradedModule.ChaoticExtension

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] (F : C' ⥤ C)
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-! ### Restriction homomorphisms of the algebra of sections -/

/-- Restriction of sections along an identity is the identity. -/
theorem sectionRestriction_id_apply (U : Cᵒᵖ) (x : (A.sectionAlgebra U).A) :
    (A.sectionRestriction (𝟙 U)).toAlgebraHom x = x :=
  DifferentialGradedAlgebra.sectionRestrictRing_id A U x

/-- Restriction of sections along a composite is the composite of the restrictions. -/
theorem sectionRestriction_comp_apply {U V W : Cᵒᵖ} (a : V ⟶ U) (b : W ⟶ V)
    (x : (A.sectionAlgebra W).A) :
    (A.sectionRestriction (b ≫ a)).toAlgebraHom x =
      (A.sectionRestriction a).toAlgebraHom ((A.sectionRestriction b).toAlgebraHom x) :=
  DifferentialGradedAlgebra.sectionRestrictRing_comp A a b x

/-! ### The homomorphism of sections along an arrow into the image of `F` -/

/-- **The homomorphism `A(F U') ⟶ A(U)` attached to an arrow `U → F U'`**: restriction of
sections along the arrow. -/
abbrev arrowHom {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    (A.sectionAlgebra (F.op.obj (Opposite.op b.right))).Hom (A.sectionAlgebra U) :=
  A.sectionRestriction b.hom.op

/-- The homomorphisms of sections along the arrows of `U/F` are compatible with the morphisms
of `U/F`. -/
theorem arrowHom_map {U : Cᵒᵖ} {b b' : StructuredArrow U.unop F} (g : b' ⟶ b)
    (y : (A.sectionAlgebra (F.op.obj (Opposite.op b.right))).A) :
    (_root_.DifferentialGradedAlgebra.Hom.id (A.sectionAlgebra U)).toAlgebraHom
        ((arrowHom F A b).toAlgebraHom y) =
      (arrowHom F A b').toAlgebraHom
        ((A.sectionRestriction (F.op.map g.right.op)).toAlgebraHom y) := by
  change (A.sectionRestriction b.hom.op).toAlgebraHom y =
    (A.sectionRestriction b'.hom.op).toAlgebraHom
      ((A.sectionRestriction (F.op.map g.right.op)).toAlgebraHom y)
  rw [← sectionRestriction_comp_apply]
  have hw : F.op.map g.right.op ≫ b'.hom.op = b.hom.op :=
    congrArg Quiver.Hom.op (StructuredArrow.w g)
  rw [hw]

/-- Precomposition of an arrow `V → F U'` with `U → V`. -/
abbrev pre {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F) : StructuredArrow U.unop F :=
  (StructuredArrow.map a.unop).obj b

/-- The homomorphisms of sections along the arrows of `U/F` are compatible with precomposition. -/
theorem arrowHom_pre {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F)
    (y : (A.sectionAlgebra (F.op.obj (Opposite.op b.right))).A) :
    (A.sectionRestriction a).toAlgebraHom ((arrowHom F A b).toAlgebraHom y) =
      (arrowHom F A (pre F a b)).toAlgebraHom
        ((_root_.DifferentialGradedAlgebra.Hom.id _).toAlgebraHom y) := by
  change (A.sectionRestriction a).toAlgebraHom ((A.sectionRestriction b.hom.op).toAlgebraHom y) =
    (A.sectionRestriction (b.hom.op ≫ a)).toAlgebraHom y
  rw [sectionRestriction_comp_apply]

/-! ### Extensionality on pure tensors -/

/-- **Two homomorphisms out of `X ⊗_B C` agreeing on the homogeneous pure tensors are equal.** -/
theorem tensor_hom_ext {B B' : _root_.DifferentialGradedAlgebra.{u, u} (ULift.{u} ℤ)}
    (ψ : B.Hom B') {X : _root_.DifferentialGradedModule.{u, u, u} B}
    {Y : _root_.DifferentialGradedModule.{u, u, u} B'}
    {f g : (tensorCompFunctor (regular ψ)).obj X ⟶ Y}
    (h : ∀ (p : ℤ) (x : X.grading p) (c : B'.A),
      f.toFun ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c) =
        g.toFun ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c)) : f = g :=
  _root_.DifferentialGradedModule.Hom.ext
    (@DifferentialGraded.Bimodule.tensorObj_linearMap_ext_homogeneous _ _ _ _ (regular ψ) X Y.M _
      Y.module f.toFun g.toFun fun p x y => h p x y)

/-- **Two additive maps out of `X ⊗_B C` agreeing on the homogeneous pure tensors are equal.** -/
theorem tensor_addHom_ext {B B' : _root_.DifferentialGradedAlgebra.{u, u} (ULift.{u} ℤ)}
    (ψ : B.Hom B') {X : _root_.DifferentialGradedModule.{u, u, u} B} {P : Type*}
    [AddCommGroup P] {f g : ((tensorCompFunctor (regular ψ)).obj X).M →+ P}
    (h : ∀ (p : ℤ) (x : X.grading p) (c : B'.A),
      f ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c) =
        g ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c)) : f = g := by
  refine tensorObj_addHom_ext (regular ψ) X f g fun x c => ?_
  induction x using DirectSum.Decomposition.inductionOn X.grading with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply]
    exact (map_zero f).trans (map_zero g).symm
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply]
    exact (map_add f _ _).trans ((congrArg₂ (· + ·) hx hx').trans (map_add g _ _).symm)
  | @homogeneous p x => exact h p x c

/-! ### Presheaves of section modules along `F` -/

/-- **A presheaf of section modules along `F`**: for every object `U'` of `C'` a differential
graded `A(F U')`-module `X(U')`, with restriction homomorphisms along the restriction
homomorphisms of `A` along `F`. -/
structure AlongSystem where
  /-- The differential graded `A(F U')`-module over `U'`. -/
  obj (U' : C'ᵒᵖ) : _root_.DifferentialGradedModule.{u, u, u} (A.sectionAlgebra (F.op.obj U'))
  /-- The restriction homomorphism along a morphism of `C'ᵒᵖ`. -/
  restr {U' V' : C'ᵒᵖ} (a : V' ⟶ U') :
    (obj V').Hom (_root_.DifferentialGradedModule.restrictScalars
      (A.sectionRestriction (F.op.map a)) (obj U'))
  /-- Restriction along an identity is the identity. -/
  restr_id (U' : C'ᵒᵖ) (x : (obj U').M) : (restr (𝟙 U')).toFun x = x
  /-- Restriction along a composite is the composite of the restrictions. -/
  restr_comp {U' V' W' : C'ᵒᵖ} (a : V' ⟶ U') (b : W' ⟶ V') (x : (obj W').M) :
    (restr (b ≫ a)).toFun x = (restr a).toFun ((restr b).toFun x)

namespace AlongSystem

variable {F A}

/-- The restriction homomorphism, as a map into `X(U')` itself. -/
abbrev restrFun (X : AlongSystem F A) {U' V' : C'ᵒᵖ} (a : V' ⟶ U') (x : (X.obj V').M) :
    (X.obj U').M :=
  (X.restr a).toFun x

/-- A morphism of presheaves of section modules along `F`. -/
@[ext]
structure Hom (X Y : AlongSystem F A) where
  /-- The homomorphism over `U'`. -/
  app (U' : C'ᵒᵖ) : X.obj U' ⟶ Y.obj U'
  /-- The homomorphisms commute with restriction. -/
  naturality {U' V' : C'ᵒᵖ} (a : V' ⟶ U') (x : (X.obj V').M) :
    Y.restrFun a ((app V').toFun x) = (app U').toFun (X.restrFun a x)

/-- The category of presheaves of section modules along `F`. -/
instance : Category (AlongSystem F A) where
  Hom := Hom
  id X := ⟨fun U' => 𝟙 (X.obj U'), fun _ _ => rfl⟩
  comp f g := ⟨fun U' => f.app U' ≫ g.app U', fun a x => by
    change _ = (g.app _).toFun ((f.app _).toFun _)
    rw [← f.naturality, ← g.naturality]
    rfl⟩

/-- Two morphisms of presheaves of section modules along `F` with the same components are
equal. -/
@[ext]
theorem hom_ext {X Y : AlongSystem F A} {f g : X ⟶ Y} (h : ∀ U', f.app U' = g.app U') : f = g :=
  Hom.ext (funext h)

/-- The component of the identity morphism is the identity. -/
@[simp] theorem id_app (X : AlongSystem F A) (U' : C'ᵒᵖ) :
    (𝟙 X : X ⟶ X).app U' = 𝟙 (X.obj U') := rfl

/-- The component of a composite is the composite of the components. -/
@[simp] theorem comp_app {X Y Z : AlongSystem F A} (f : X ⟶ Y) (g : Y ⟶ Z) (U' : C'ᵒᵖ) :
    (f ≫ g).app U' = f.app U' ≫ g.app U' := rfl

end AlongSystem

/-! ### The diagram defining the extension -/

variable {F A} (X : AlongSystem F A)

/-- **The term of the colimit at an arrow `b : U → F U'`**: `X(U') ⊗_{A(F U')} A(U)`. -/
abbrev term {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    _root_.DifferentialGradedModule.{u, u, u} (A.sectionAlgebra U) :=
  (tensorCompFunctor (regular (arrowHom F A b))).obj (X.obj (Opposite.op b.right))

/-- The pure tensor `x ⊗ c` of the term at `b`. -/
abbrev pure {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :=
  (tensorPure (regular (arrowHom F A b)) (X.obj (Opposite.op b.right))).toLinearMap

/-- **The transition map of the diagram** along a morphism `g : b' ⟶ b` of `U/F`:
`x ⊗ c ↦ x|_{g} ⊗ c`. -/
def transition {U : Cᵒᵖ} {b b' : StructuredArrow U.unop F} (g : b' ⟶ b) :
    term X b ⟶ term X b' :=
  tensorSquareMap (A.sectionRestriction (F.op.map g.right.op)) (arrowHom F A b)
      (arrowHom F A b') (_root_.DifferentialGradedAlgebra.Hom.id (A.sectionAlgebra U))
      (arrowHom_map F A g) (X.restr g.right.op) ≫
    restrictScalarsIdHom _

/-- The transition map along `g` sends `x ⊗ c` to `x|_{g} ⊗ c`. -/
theorem transition_pure {U : Cᵒᵖ} {b b' : StructuredArrow U.unop F} (g : b' ⟶ b) (p : ℤ)
    (x : (X.obj (Opposite.op b.right)).grading p) (c : (A.sectionAlgebra U).A) :
    (transition X g).toFun (pure X b (x : (X.obj (Opposite.op b.right)).M) c) =
      pure X b' (X.restrFun g.right.op x) c :=
  DifferentialGraded.Bimodule.tensorSquareMap_pure _ _ _ _ (arrowHom_map F A g)
    (X.restr g.right.op) p x c

/-- The transition map along a morphism that is the identity on `U'` fixes pure tensors. -/
private theorem transition_pure_homMk_id {U : Cᵒᵖ} {b : StructuredArrow U.unop F}
    {f : U.unop ⟶ F.obj b.right} (w) (p : ℤ) (x : (X.obj (Opposite.op b.right)).grading p)
    (c : (A.sectionAlgebra U).A) :
    (transition X (StructuredArrow.homMk (𝟙 b.right) w : StructuredArrow.mk f ⟶ b)).toFun
        (pure X b (x : (X.obj (Opposite.op b.right)).M) c) =
      pure X (StructuredArrow.mk f) (x : (X.obj (Opposite.op b.right)).M) c :=
  (transition_pure X _ p x c).trans (congrArg (pure X _ · c) (X.restr_id _ _))

/-- The restriction of a homogeneous element is homogeneous of the same degree. -/
def restrPiece {U V : C'ᵒᵖ} (a : V ⟶ U) {p : ℤ} (x : (X.obj V).grading p) :
    (X.obj U).grading p :=
  ⟨X.restrFun a x, (X.restr a).map_grading p x x.2⟩

variable (U : Cᵒᵖ)

/-- **The diagram `U → F U' ↦ X(U') ⊗_{A(F U')} A(U)`**, indexed by the opposite of `U/F`. -/
abbrev diagram : (StructuredArrow U.unop F)ᵒᵖ ⥤
    _root_.DifferentialGradedModule.{u, u, u} (A.sectionAlgebra U) where
  obj j := term X j.unop
  map g := transition X g.unop
  map_id j := tensor_hom_ext _ fun p x c => by
    refine (transition_pure X (𝟙 j.unop) p x c).trans ?_
    change pure X j.unop (X.restrFun (𝟙 (Opposite.op j.unop.right)) x) c = _
    rw [AlongSystem.restrFun, X.restr_id]
    rfl
  map_comp {i j k} f g := tensor_hom_ext _ fun p x c => by
    refine (transition_pure X (g.unop ≫ f.unop) p x c).trans ?_
    refine Eq.trans ?_ (congrArg (transition X g.unop).toFun
      (transition_pure X f.unop p x c)).symm
    refine Eq.trans ?_ (transition_pure X g.unop p (restrPiece X f.unop.right.op x) c).symm
    change pure X k.unop (X.restrFun (f.unop.right.op ≫ g.unop.right.op) x) c =
      pure X k.unop (X.restrFun g.unop.right.op (X.restrFun f.unop.right.op x)) c
    rw [AlongSystem.restrFun, X.restr_comp]

/-- The diagram sends a morphism of `(U/F)ᵒᵖ` to the transition map along it. -/
@[simp] theorem diagram_map {U : Cᵒᵖ} {i j : (StructuredArrow U.unop F)ᵒᵖ} (g : i ⟶ j) :
    (diagram X U).map g = transition X g.unop := rfl

section Extension

variable [∀ U : C, IsCofiltered (StructuredArrow U F)]

/-- **The extension over `U`**: `colim_{U → F U'} X(U') ⊗_{A(F U')} A(U)`. -/
abbrev extObj : _root_.DifferentialGradedModule.{u, u, u} (A.sectionAlgebra U) :=
  _root_.DifferentialGradedModule.FilteredColimit.colimitModule (diagram X U)

/-- The germ in the extension over `U` of an element of the term at `b`. -/
abbrev germ {U : Cᵒᵖ} (b : StructuredArrow U.unop F) (z : (term X b).M) : (extObj X U).M :=
  _root_.DifferentialGradedModule.FilteredColimit.germ (diagram X U) (Opposite.op b) z

open _root_.DifferentialGradedModule.FilteredColimit in
/-- The germ of an element is the germ of its image under a transition map. -/
theorem germ_transition {U : Cᵒᵖ} {b b' : StructuredArrow U.unop F} (g : b' ⟶ b)
    (z : (term X b).M) : germ X b' ((transition X g).toFun z) = germ X b z :=
  _root_.DifferentialGradedModule.FilteredColimit.germ_map (diagram X U) g.op z

/-! ### Restriction of the extension -/

/-- **The leg of the restriction map at `b`**: `x ⊗ c ↦ x ⊗ c|_U`, from the term at `b : V → F U'`
to the term at the composite `U → V → F U'`. -/
def restrLeg {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F) :
    term X b ⟶ (restrictScalarsFunctor (A.sectionRestriction a)).obj (term X (pre F a b)) :=
  tensorSquareMap (_root_.DifferentialGradedAlgebra.Hom.id _) (arrowHom F A b)
    (arrowHom F A (pre F a b)) (A.sectionRestriction a) (arrowHom_pre F A a b)
    (restrictScalarsIdInv _)

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The leg of the restriction map sends `x ⊗ c` to `x ⊗ c|_U`. -/
theorem restrLeg_pure {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F) (p : ℤ)
    (x : (X.obj (Opposite.op b.right)).grading p) (c : (A.sectionAlgebra V).A) :
    (restrLeg X a b).toFun (pure X b (x : (X.obj (Opposite.op b.right)).M) c) =
      pure X (pre F a b) (x : (X.obj (Opposite.op b.right)).M)
        ((A.sectionRestriction a).toAlgebraHom c) :=
  DifferentialGraded.Bimodule.tensorSquareMap_pure _ _ _ _ (arrowHom_pre F A a b) _ p x c

/-- The morphism of `U/F` from the composite `U → V → F U'` along `g : b' ⟶ b`. -/
abbrev preMap {U V : Cᵒᵖ} (a : V ⟶ U) {b b' : StructuredArrow V.unop F} (g : b' ⟶ b) :
    pre F a b' ⟶ pre F a b :=
  (StructuredArrow.map a.unop).map g

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The legs of the restriction map commute with the transition maps. -/
theorem restrLeg_transition {U V : Cᵒᵖ} (a : V ⟶ U) {b b' : StructuredArrow V.unop F}
    (g : b' ⟶ b) (z : (term X b).M) :
    (restrLeg X a b').toFun ((transition X g).toFun z) =
      (transition X (preMap a g)).toFun ((restrLeg X a b).toFun z) := by
  have key : transition X g ≫ restrLeg X a b' =
      restrLeg X a b ≫ (restrictScalarsFunctor (A.sectionRestriction a)).map
        (transition X (preMap a g)) :=
    tensor_hom_ext _ fun p x c => by
      change (restrLeg X a b').toFun ((transition X g).toFun (pure X b x c)) =
        (transition X (preMap a g)).toFun ((restrLeg X a b).toFun (pure X b x c))
      refine (congrArg (restrLeg X a b').toFun (transition_pure X g p x c)).trans ?_
      refine (restrLeg_pure X a b' p (restrPiece X g.right.op x) c).trans ?_
      refine Eq.trans ?_
        (congrArg (transition X (preMap a g)).toFun (restrLeg_pure X a b p x c)).symm
      exact (transition_pure X (preMap a g) p x _).symm
  exact congrArg (fun f => f.toFun z) key

/-- The cocone over the diagram at `V` whose legs are the restriction legs followed by the
coprojections of the extension over `U`. -/
def restrCocone {V : Cᵒᵖ} (a : V ⟶ U) : Cocone (diagram X V) where
  pt := (restrictScalarsFunctor (A.sectionRestriction a)).obj (extObj X U)
  ι :=
    { app j := restrLeg X a j.unop ≫ (restrictScalarsFunctor (A.sectionRestriction a)).map
        (_root_.DifferentialGradedModule.FilteredColimit.ι (diagram X U)
          (Opposite.op (pre F a j.unop)))
      naturality {i j} g := _root_.DifferentialGradedModule.Hom.ext
        (DFunLike.ext _ _ fun (z : (term X i.unop).M) =>
          (congrArg (germ X (pre F a j.unop)) (restrLeg_transition X a g.unop z)).trans
            (germ_transition X (preMap a g.unop) _)) }

/-- **The restriction map of the extension** along `a : V ⟶ U`: on the germ of `x ⊗ c` at
`b : V → F U'` it is the germ of `x ⊗ c|_U` at `U → V → F U'`. -/
def restr {U V : Cᵒᵖ} (a : V ⟶ U) :
    extObj X V ⟶ (restrictScalarsFunctor (A.sectionRestriction a)).obj (extObj X U) :=
  _root_.DifferentialGradedModule.FilteredColimit.desc (diagram X V) (restrCocone X U a)

/-- The restriction map of the extension sends the germ of `z` at `b` to the germ of its
image under the leg at `b`. -/
theorem restr_germ {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F) (z : (term X b).M) :
    (restr X a).toFun (germ X b z) = germ X (pre F a b) ((restrLeg X a b).toFun z) :=
  _root_.DifferentialGradedModule.FilteredColimit.desc_germ (diagram X V) _ _ z

/-- The identification of `b` with its precomposition with an identity. -/
abbrev preIdHom {V : Cᵒᵖ} (b : StructuredArrow V.unop F) : pre F (𝟙 V) b ⟶ b :=
  StructuredArrow.homMk (𝟙 b.right) (by simp)

/-- The identification of a twice precomposed arrow with its precomposition with the
composite. -/
abbrev preCompHom {U V W : Cᵒᵖ} (a : V ⟶ U) (a' : W ⟶ V) (b : StructuredArrow W.unop F) :
    pre F (a' ≫ a) b ⟶ pre F a (pre F a' b) :=
  StructuredArrow.homMk (𝟙 b.right) (by simp)

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The leg of the restriction map along an identity is the transition map along
`preIdHom b`. -/
theorem restrLeg_id {V : Cᵒᵖ} (b : StructuredArrow V.unop F) (z : (term X b).M) :
    (restrLeg X (𝟙 V) b).toFun z = (transition X (preIdHom b)).toFun z := by
  have key : (restrLeg X (𝟙 V) b).toFun.toAddMonoidHom =
      (transition X (preIdHom b)).toFun.toAddMonoidHom := by
    refine tensor_addHom_ext _ fun p x c => ?_
    change (restrLeg X (𝟙 V) b).toFun (pure X b x c) =
      (transition X (preIdHom b)).toFun (pure X b x c)
    refine (restrLeg_pure X (𝟙 V) b p x c).trans ?_
    rw [transition_pure_homMk_id X _ p x c]
    exact congrArg (pure X _ _) (sectionRestriction_id_apply A V c)
  exact DFunLike.congr_fun key z

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The leg of the restriction map along a composite is the composite of the legs, followed by
the transition map along `preCompHom a a' b`. -/
theorem restrLeg_comp {U V W : Cᵒᵖ} (a : V ⟶ U) (a' : W ⟶ V) (b : StructuredArrow W.unop F)
    (z : (term X b).M) :
    (restrLeg X (a' ≫ a) b).toFun z =
      (transition X (preCompHom a a' b)).toFun
        ((restrLeg X a (pre F a' b)).toFun ((restrLeg X a' b).toFun z)) := by
  have key : (restrLeg X (a' ≫ a) b).toFun.toAddMonoidHom =
      (transition X (preCompHom a a' b)).toFun.toAddMonoidHom.comp
        ((restrLeg X a (pre F a' b)).toFun.toAddMonoidHom.comp
          (restrLeg X a' b).toFun.toAddMonoidHom) := by
    refine tensor_addHom_ext _ fun p x c => ?_
    change (restrLeg X (a' ≫ a) b).toFun (pure X b x c) =
      (transition X (preCompHom a a' b)).toFun
        ((restrLeg X a (pre F a' b)).toFun ((restrLeg X a' b).toFun (pure X b x c)))
    refine (restrLeg_pure X (a' ≫ a) b p x c).trans ?_
    refine Eq.trans ?_ (congrArg (fun w => (transition X (preCompHom a a' b)).toFun
      ((restrLeg X a (pre F a' b)).toFun w)) (restrLeg_pure X a' b p x c)).symm
    refine Eq.trans ?_ (congrArg (transition X (preCompHom a a' b)).toFun
      (restrLeg_pure X a (pre F a' b) p x _)).symm
    refine Eq.trans ?_ (transition_pure_homMk_id (b := pre F a (pre F a' b)) X _ p x _).symm
    exact congrArg (pure X _ _) (sectionRestriction_comp_apply A a a' c)
  exact DFunLike.congr_fun key z

/-- **The extension `E(X)`**, a presheaf of section modules over `A`: over `U` it is
`colim_{U → F U'} X(U') ⊗_{A(F U')} A(U)`. -/
def extSystem : SectionSystem A where
  obj U := extObj X U
  restr a := restr X a
  restr_id V z := by
    obtain ⟨j, w, rfl⟩ := _root_.DifferentialGradedModule.FilteredColimit.exists_germ _ z
    exact (restr_germ X (𝟙 V) j.unop w).trans
      ((congrArg (germ X (pre F (𝟙 V) j.unop)) (restrLeg_id X j.unop w)).trans
        (germ_transition X (preIdHom j.unop) w))
  restr_comp a a' z := by
    obtain ⟨j, w, rfl⟩ := _root_.DifferentialGradedModule.FilteredColimit.exists_germ _ z
    refine (restr_germ X (a' ≫ a) j.unop w).trans ?_
    refine Eq.trans ?_ (congrArg (restr X a).toFun (restr_germ X a' j.unop w)).symm
    refine Eq.trans ?_ (restr_germ X a (pre F a' j.unop) _).symm
    exact (congrArg (germ X (pre F (a' ≫ a) j.unop)) (restrLeg_comp X a a' j.unop w)).trans
      (germ_transition X (preCompHom a a' j.unop) _)

/-- The extension over `U` is `extObj X U`. -/
@[simp] theorem extSystem_obj : (extSystem X).obj U = extObj X U := rfl

/-- The restriction map of `E(X)` sends the germ of `z` at `b` to the germ of its image under
the leg at `b`. -/
theorem extSystem_restrFun_germ {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F)
    (z : (term X b).M) :
    (extSystem X).restrFun a (germ X b z) = germ X (pre F a b) ((restrLeg X a b).toFun z) :=
  restr_germ X a b z

/-! ### Functoriality -/

variable {X} {Y Z : AlongSystem F A}

/-- A morphism of presheaves of section modules, on the term at `b`: `x ⊗ c ↦ f(x) ⊗ c`. -/
abbrev termMap (f : X ⟶ Y) {U : Cᵒᵖ} (b : StructuredArrow U.unop F) : term X b ⟶ term Y b :=
  (tensorCompFunctor (regular (arrowHom F A b))).map (f.app (Opposite.op b.right))

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The map on the term at `b` sends `x ⊗ c` to `f(x) ⊗ c`. -/
theorem termMap_pure (f : X ⟶ Y) {U : Cᵒᵖ} (b : StructuredArrow U.unop F)
    (x : (X.obj (Opposite.op b.right)).M) (c : (A.sectionAlgebra U).A) :
    (termMap f b).toFun (pure X b x c) = pure Y b ((f.app (Opposite.op b.right)).toFun x) c :=
  DifferentialGraded.Bimodule.tensorCompFunctor_map_pure' (regular (arrowHom F A b))
    (f.app (Opposite.op b.right)) x c

/-- A morphism of presheaves of section modules, as a natural transformation of diagrams. -/
def diagramMap (f : X ⟶ Y) (U : Cᵒᵖ) : diagram X U ⟶ diagram Y U where
  app j := termMap f j.unop
  naturality {i j} g := tensor_hom_ext _ fun p x c => by
    change (termMap f j.unop).toFun ((transition X g.unop).toFun (pure X i.unop x c)) =
      (transition Y g.unop).toFun ((termMap f i.unop).toFun (pure X i.unop x c))
    rw [transition_pure, termMap_pure, termMap_pure]
    refine Eq.trans ?_ (transition_pure Y g.unop p
      ⟨_, (f.app _).map_grading p x x.2⟩ c).symm
    exact congrArg (fun w => pure Y j.unop w c) (f.naturality g.unop.right.op x).symm

/-- **A morphism of presheaves of section modules, on the extensions.** -/
def extMap (f : X ⟶ Y) : extSystem X ⟶ extSystem Y where
  app U := _root_.DifferentialGradedModule.FilteredColimit.map (diagramMap f U)
  naturality {U V} a z := by
    obtain ⟨j, w, rfl⟩ := _root_.DifferentialGradedModule.FilteredColimit.exists_germ _ z
    change (extSystem Y).restrFun a
        ((_root_.DifferentialGradedModule.FilteredColimit.map (diagramMap f V)).toFun
          (germ X j.unop w)) =
      (_root_.DifferentialGradedModule.FilteredColimit.map (diagramMap f U)).toFun
        ((extSystem X).restrFun a (germ X j.unop w))
    rw [extSystem_restrFun_germ]
    refine (congrArg ((extSystem Y).restrFun a)
      (_root_.DifferentialGradedModule.FilteredColimit.map_germ (diagramMap f V) j w)).trans ?_
    refine (extSystem_restrFun_germ Y a j.unop _).trans ?_
    refine Eq.trans ?_
      (_root_.DifferentialGradedModule.FilteredColimit.map_germ (diagramMap f U) _ _).symm
    congr 1
    have key : termMap f j.unop ≫ restrLeg Y a j.unop =
        restrLeg X a j.unop ≫ (restrictScalarsFunctor (A.sectionRestriction a)).map
          (termMap f (pre F a j.unop)) :=
      tensor_hom_ext _ fun p x c => by
        change (restrLeg Y a j.unop).toFun ((termMap f j.unop).toFun (pure X j.unop x c)) =
          (termMap f (pre F a j.unop)).toFun ((restrLeg X a j.unop).toFun (pure X j.unop x c))
        rw [termMap_pure, restrLeg_pure, termMap_pure]
        exact restrLeg_pure Y a j.unop p ⟨_, (f.app _).map_grading p x x.2⟩ c
    exact congrArg (fun g => g.toFun w) key

/-- The map on extensions sends the germ of `z` at `b` to the germ of its image under the map
on the term at `b`. -/
theorem extMap_germ (f : X ⟶ Y) {U : Cᵒᵖ} (b : StructuredArrow U.unop F) (z : (term X b).M) :
    ((extMap f).app U).toFun (germ X b z) = germ Y b ((termMap f b).toFun z) :=
  _root_.DifferentialGradedModule.FilteredColimit.map_germ (diagramMap f U) _ z

variable (F A) in
/-- **The extension functor** from presheaves of section modules along `F` to presheaves of
section modules over `A`. -/
def extFunctor : AlongSystem F A ⥤ SectionSystem A where
  obj X := extSystem X
  map f := extMap f
  map_id X₀ := SectionSystem.hom_ext fun U => by
    refine _root_.DifferentialGradedModule.FilteredColimit.hom_ext _ fun j z => ?_
    refine (extMap_germ (𝟙 X₀) j.unop z).trans ?_
    congr 1
    exact congrArg (fun g => g.toFun z)
      ((tensorCompFunctor (regular (arrowHom F A j.unop))).map_id _)
  map_comp f g := SectionSystem.hom_ext fun U => by
    refine _root_.DifferentialGradedModule.FilteredColimit.hom_ext _ fun j z => ?_
    refine (extMap_germ (f ≫ g) j.unop z).trans ?_
    change _ = ((extMap g).app U).toFun (((extMap f).app U).toFun (germ _ j.unop z))
    rw [extMap_germ, extMap_germ]
    congr 1
    exact congrArg (fun h => h.toFun z)
      ((tensorCompFunctor (regular (arrowHom F A j.unop))).map_comp
        (f.app (Opposite.op j.unop.right)) (g.app (Opposite.op j.unop.right)))

/-- The extension functor sends `X` to `E(X)`. -/
@[simp] theorem extFunctor_obj : (extFunctor F A).obj X = extSystem X := rfl

/-- The extension functor sends `f` to `extMap f`. -/
@[simp] theorem extFunctor_map (f : X ⟶ Y) : (extFunctor F A).map f = extMap f := rfl

end Extension

/-! ### Restriction of presheaves of section modules -/

section Restrict

variable (Y Y' Y'' : SectionSystem A)

/-- Restriction along the image under `F` of an identity is the identity. -/
theorem restr_map_id (U' : C'ᵒᵖ) (y : (Y.obj (F.op.obj U')).M) :
    (Y.restr (F.op.map (𝟙 U'))).toFun y = y := by
  have hy := Y.restr_id (F.op.obj U') y
  rwa [← F.op.map_id] at hy

/-- Restriction along the image under `F` of a composite is the composite of the
restrictions. -/
theorem restr_map_comp {U' V' W' : C'ᵒᵖ} (a : V' ⟶ U') (b : W' ⟶ V')
    (y : (Y.obj (F.op.obj W')).M) :
    (Y.restr (F.op.map (b ≫ a))).toFun y =
      (Y.restr (F.op.map a)).toFun ((Y.restr (F.op.map b)).toFun y) := by
  have hy := Y.restr_comp (F.op.map a) (F.op.map b) y
  rwa [← F.op.map_comp] at hy

variable (F) in
/-- **The restriction `U' ↦ Y(F U')` of a presheaf of section modules over `A`**, a presheaf of
section modules along `F`. -/
def restrictSystem : AlongSystem F A where
  obj U' := Y.obj (F.op.obj U')
  restr a := Y.restr (F.op.map a)
  restr_id U' x := restr_map_id Y U' x
  restr_comp a b x := restr_map_comp Y a b x

variable {Y Y' Y''}

variable (F) in
/-- A morphism of presheaves of section modules over `A`, restricted along `F`. -/
def restrictMap (g : Y ⟶ Y') : restrictSystem F Y ⟶ restrictSystem F Y' where
  app U' := g.app (F.op.obj U')
  naturality a x := g.naturality (F.op.map a) x

variable (F A) in
/-- **The restriction functor** from presheaves of section modules over `A` to presheaves of
section modules along `F`. -/
def restrictFunctor : SectionSystem A ⥤ AlongSystem F A where
  obj Y := restrictSystem F Y
  map g := restrictMap F g
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction functor sends `Y` to `U' ↦ Y(F U')`. -/
@[simp] theorem restrictFunctor_obj : (restrictFunctor F A).obj Y = restrictSystem F Y := rfl

/-- The component at `U'` of the restriction of `g` is the component of `g` at `F U'`. -/
@[simp] theorem restrictFunctor_map_app (g : Y ⟶ Y') (U' : C'ᵒᵖ) :
    ((restrictFunctor F A).map g).app U' = g.app (F.op.obj U') := rfl

end Restrict

end DifferentialGradedModule.ChaoticExtension

end SheafOfModules

end
