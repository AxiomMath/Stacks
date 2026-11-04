module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback commutes with the exterior algebra of a sheaf of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces and `M` a sheaf of `𝒪_Y`-modules. Stacks 01CI
asserts `f^*⋀(M) = ⋀(f^*M)`. This file proves that: the canonical comparison
`SheafOfModules.GradedAlgebra.pullbackComparison` is an **isomorphism in every degree**, and the
degreewise and direct-sum comparisons, with their three compatibilities, are the unique such
family.

Both exterior algebras enter through their universal property
(`SheafOfModules.GradedAlgebra.IsExteriorAlgebra`: a square-zero degree-one generator, initial
among such) rather than through a construction, so nothing here depends on an unconstructed
exterior algebra.

## The three things the proof needs, and where each comes from

The comparison `c_n : f^*(A_n) ⟶ B_n` is the adjoint transpose of the unique unital homomorphism
`A ⟶ f_*B`, and it exists with no hypotheses
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback`). Inverting it means
producing a map back out of the universal property of `B = ⋀(f^*M)`, and that needs exactly
three things.

1. **A graded-algebra structure on `f^*A`.** It is built here as `comparisonGradedAlgebra`, by
   conjugating the multiplication of `A` with the comparison of Stacks 01CD. The algebra axioms
   are the coherences of that comparison, proved in
   `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` and transported by
   `Stacks.MonoidalGraded`.
2. **Multiplicativity of the unit of `f^* ⊣ f_*`**, i.e. that `A ⟶ f_*(f^*A)` is a homomorphism
   of sheaves of graded algebras (`pullbackUnitalHom`). Because the multiplication of `f^*A` was
   conjugated with the comparison of Stacks 01CD, and that comparison has a section formula on
   the pullback-unit images, this is immediate: `comparisonGradedAlgebra_mul_pullbackUnit`.
3. **Square-zero-ness of the pulled-back generator on _all_ local sections of `f^*M`**, not only
   on the pullback-unit images (`squareZero_pullbackGenerator`). This is the one genuinely
   non-formal step. It is a polarization argument: the family of pullback-unit sections is closed
   under addition after restriction
   (`Stacks.PullbackUnitGenerators.add_mem_unitSections`), so square-zero-ness on the family
   gives anticommutativity on the family; both extend to the `𝒪_X`-span by bilinearity
   (`Submodule.span_induction`, twice); and every local section of `f^*M` restricts into that
   span along a covering sieve
   (`Stacks.PullbackUnitGenerators.spanSieve_mem`), so separatedness of the degree-two piece
   finishes it.

With those, `descUnitalHom : B ⟶ f^*A` exists, and the two composites are identities: one by the
universal property of `B`, the other by the universal property of `A` applied to the two unital
homomorphisms `A ⟶ f_*(f^*A)` of item 2.

**No density argument is needed for multiplicativity of the comparison itself.**
`pullbackComparison_mul` gives it on the pullback-unit sections only, and the upgrade to all
local sections — which is what makes the comparison a `UnitalHom` and is where one would expect a
second span induction — is free: both sides of the identity are morphisms out of a *pullback*
once the comparison of Stacks 01CD is peeled off, so the adjunction reduces it to the adjoint
transposes, which are morphisms out of the tensor product sheaf and are determined by their
values on local pure tensors. See `map_mulHom_comp_comparisonHom`.

## Main definitions

* `Stacks.PullbackExteriorAlgebra.comparisonMul` and `comparisonOne`: the multiplication and the
  unit of `f^*A`, conjugated by the comparisons of Stacks 01CD and `f^*𝒪_Y ≅ 𝒪_X`.
* `Stacks.PullbackExteriorAlgebra.comparisonGradedAlgebra`: **the sheaf of graded algebras
  `f^*A`.**
* `Stacks.PullbackExteriorAlgebra.pullbackUnitalHom`: **the unit of `f^* ⊣ f_*` as a homomorphism
  of sheaves of graded algebras `A ⟶ f_*(f^*A)`**, and `pushforwardUnitalHom`, the pushforward of
  a homomorphism of sheaves of graded algebras.
* `Stacks.PullbackExteriorAlgebra.pullbackGenerator` and `genBilinear`: the pulled-back
  degree-one generator and the bilinear map `(x, y) ↦ ι(x) · ι(y)` whose diagonal the square-zero
  condition is about.
* `Stacks.PullbackExteriorAlgebra.comparisonHom`: `pullbackComparison`, retyped at the
  `Stacks.RingedSpace.structureRingSheaf` spelling, and `comparisonUnitalHom`, the comparison as
  a homomorphism of sheaves of graded algebras.
* `Stacks.PullbackExteriorAlgebra.descUnitalHom`: **the homomorphism `B ⟶ f^*A`** out of the
  universal property of `B`.
* `Stacks.PullbackExteriorAlgebra.pieceIso` and `sheafIso`: **Stacks 01CI for the exterior
  algebra**, degreewise and on the underlying direct-sum sheaf.
* `Stacks.PullbackExteriorAlgebra.ExteriorAlgebraPullbackIso`: the comparison packaged with its
  three compatibilities, which is the form Stacks 01CI is used in.

## Main results

* `comparisonGradedAlgebra_mul_pullbackUnit` and `comparisonGradedAlgebra_one_eval_pullbackUnit`:
  **the unit of `f^* ⊣ f_*` is multiplicative and unital.**
* `squareZero_pullbackGenerator`: **a pulled-back square-zero degree-one generator is
  square-zero**, on all local sections.
* `map_mulHom_comp_comparisonHom`, `comparisonMul_comp_comparisonHom` and
  `comparisonOne_comp_comparisonHom`: **the comparison is multiplicative and unital at every
  local section.**
* `isIso_comparisonHom` and `isIso_pullbackComparison`: **the comparison is an isomorphism in
  every degree.**
* `exteriorAlgebraPullbackIso` and `exteriorAlgebraPullbackIso_unique`: **Stacks 01CI for the
  exterior algebra and its canonicality.**

## Implementation notes

**What is forced and what is chosen.** No mathematical choice is made. The multiplication of `f^*A`
is the one the comparison of Stacks 01CD supplies, the map back is the one the universal property
of `B` supplies, and the comparison itself is the pre-existing
`SheafOfModules.GradedAlgebra.pullbackComparison`. The one presentational choice is that this file
works with `Stacks.PullbackExteriorAlgebra.comparisonHom` rather than with `pullbackComparison`
directly: they are equal by `rfl`, but the former's type is written with
`Stacks.RingedSpace.structureRingSheaf X` where the latter's is written with
`structureSheafRing X`, and only the first spelling finds the monoidal structure of Tag 01CA by
instance search (`structureSheafRing` is not reducible). Every statement below is in one
spelling, as the discipline of this directory requires.

**A second graded-algebra structure on `f^*A`.**
`Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra` is already a graded-algebra structure on
`f^*A`, built from the tensorator of
`Stacks.PullbackMonoidalSheaf.pullbackMonoidal`. `comparisonGradedAlgebra` is a *different term*
for what ought to be the same structure, built from `Stacks.RingedSpace.comparison` instead, and
it is the one used here because **its multiplication has a formula on local sections** —
`comparisonGradedAlgebra_mul_pullbackUnit`, which is item 2 above and without which the proof
does not close. No such formula is available for the older one: it would require computing the
tensorator of the localized monoidal structure on local sections. Identifying the two structures
is open, and it is exactly the identification
`Stacks.PullbackTensorCoherence` records as open. `comparisonGradedAlgebra` also takes **no**
sheaf-condition hypothesis, where `pullbackGradedAlgebra` takes `hY`: the hypothesis is
recoverable from the ringed space (`(structureSheafRing X).property`), so it is supplied rather
than assumed.

**Why `genBilinear` is a `Stacks.BilinearMap` and not a plain function.** The square-zero
extension is an induction over a span, and its induction hypotheses are statements about
`(x, y) ↦ ι(x) · ι(y)`. Packaging that as a bilinear map makes its additivity, its
`𝒪_X`-linearity and its compatibility with restriction structure fields rather than lemmas; the
three `Submodule.span_induction` calls use all of them.

**Universes.** Everything is at a single universe `u`, forced by
`RingedSpaceModuleAdjunction.modulePullback`, which exists only for `RingedSpace.{u, u}` with
modules in `u`. Nothing is narrowed relative to the imports.

**Tag 01CI, and what the two tagged declarations do not assert.** The `@[stacks 01CI]`
attributes carry clause comments saying so: this file proves the **exterior**-algebra clause.
The tensor-algebra clause is
`Stacks.PullbackAlgebra.pullbackTensorPieceIso`/`pullbackTensorSheafIso` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso`, whose own tag comments record
that they cover the tensor algebra only. The **symmetric**-algebra clause is proved nowhere: the
argument here uses that the exterior ideal is generated by squares of degree-one sections, and
its symmetric counterpart needs commutators, for which the polarization step of
`squareZero_pullbackGenerator` has no analogue as written.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI) — pullback and the
  tensor, exterior and symmetric algebras of a sheaf of modules.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace PresheafOfModules
open Stacks.PullbackTensorCoherence SheafOfModules.GradedAlgebra

open scoped TensorProduct

universe u

namespace Stacks.PullbackExteriorAlgebra

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))

/-- **The multiplication of `f^*A`**, conjugated by the comparison of Stacks 01CD. -/
noncomputable def comparisonMul (i j : ℤ) :
    (pullbackFunctor f).obj (A.piece i) ⊗ (pullbackFunctor f).obj (A.piece j) ⟶
      (pullbackFunctor f).obj (A.piece (i + j)) :=
  letI := pullbackComparisonMonoidal f
  Stacks.MonoidalGraded.mapMul (F := pullbackFunctor f) (X := A.piece i) (Y := A.piece j)
    (Z := A.piece (i + j)) (mulHom A i j)

/-- **The global unit of `f^*A`**, conjugated by the structure-sheaf comparison. -/
noncomputable def comparisonOne : 𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) ⟶
    (pullbackFunctor f).obj (A.piece 0) :=
  letI := pullbackComparisonMonoidal f
  Stacks.MonoidalGraded.mapOne (F := pullbackFunctor f) (X := A.piece 0) (oneHom A)

/-- `comparisonMul` is the inverse of the comparison followed by the pullback of the
multiplication of `A`. -/
theorem comparisonMul_eq (i j : ℤ) :
    comparisonMul f A i j =
      inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
        (pullbackFunctor f).map (mulHom A i j) :=
  rfl

/-- `comparisonOne` is the inverse of the structure-sheaf comparison followed by the pullback of
the unit of `A`. -/
theorem comparisonOne_eq :
    comparisonOne f A =
      inv (pullbackUnitComparison f) ≫ (pullbackFunctor f).map (oneMorphism A) :=
  rfl

/-- **The multiplication of `f^*A` on pullback-unit sections is the pullback-unit image of the
multiplication of `A`**: the unit of `f^* ⊣ f_*` is multiplicative. This is the section formula
that the comparison of Stacks 01CD supplies and that no formula for the tensorator of the
localized monoidal structure is needed for. -/
theorem comparisonMul_tmul_pullbackUnit (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (comparisonMul f A i j).val.app ((opensMap f).op.obj U)
        (tmul X ((pullbackFunctor f).obj (A.piece i)) ((pullbackFunctor f).obj (A.piece j))
          ((opensMap f).op.obj U) (pullbackUnit f (A.piece i) U x)
          (pullbackUnit f (A.piece j) U y)) =
      pullbackUnit f (A.piece (i + j)) U ((A.mul i j).app U x y) := by
  rw [comparisonMul_eq, SheafOfModules.comp_val_app_apply,
    ← pullbackTensorComparison_pullbackUnit, inv_val_app_apply, pullbackUnit_naturality,
    mulHom_tmul]

/-- **The global unit of `f^*A` over an inverse image is the pullback-unit image of the global
unit of `A`.** -/
theorem comparisonOne_val_app_oneSec (U : (Opens Y.carrier)ᵒᵖ) :
    (comparisonOne f A).val.app ((opensMap f).op.obj U)
        (oneSec X ((opensMap f).op.obj U)) =
      pullbackUnit f (A.piece 0) U (A.one.eval U) := by
  rw [comparisonOne_eq, SheafOfModules.comp_val_app_apply, ← pullbackUnitComparison_oneSec,
    inv_val_app_apply, pullbackUnit_naturality]
  exact congrArg (pullbackUnit f (A.piece 0) U) (oneMorphism_val_app_oneSec A U)

/-- **The multiplication of `f^*A` is associative**, as an equality of morphisms. -/
theorem comparisonMul_assoc (i j k : ℤ) :
    comparisonMul f A i j ▷ (pullbackFunctor f).obj (A.piece k) ≫ comparisonMul f A (i + j) k =
      (α_ ((pullbackFunctor f).obj (A.piece i)) ((pullbackFunctor f).obj (A.piece j))
            ((pullbackFunctor f).obj (A.piece k))).hom ≫
        (pullbackFunctor f).obj (A.piece i) ◁ comparisonMul f A j k ≫
          comparisonMul f A i (j + k) ≫
            eqToHom (congrArg (fun n ↦ (pullbackFunctor f).obj (A.piece n))
              (add_assoc i j k).symm) := by
  let _ := pullbackComparisonMonoidal f
  refine (Stacks.MonoidalGraded.mapMul_assoc (pullbackFunctor f) (mulHom A i j)
    (mulHom A j k) (mulHom A (i + j) k)
    (mulHom A i (j + k) ≫ eqToHom (congrArg A.piece (add_assoc i j k).symm))
    (mulHom_assoc A i j k)).trans ?_
  refine congrArg (fun ϑ ↦ (α_ ((pullbackFunctor f).obj (A.piece i))
      ((pullbackFunctor f).obj (A.piece j)) ((pullbackFunctor f).obj (A.piece k))).hom ≫
    (pullbackFunctor f).obj (A.piece i) ◁ comparisonMul f A j k ≫ ϑ) ?_
  exact (Stacks.MonoidalGraded.mapMul_comp (pullbackFunctor f) (mulHom A i (j + k))
    (eqToHom (congrArg A.piece (add_assoc i j k).symm))).trans
    (congrArg (fun ϑ ↦ comparisonMul f A i (j + k) ≫ ϑ)
      (eqToHom_map (pullbackFunctor f) (congrArg A.piece (add_assoc i j k).symm)))

/-- **The global unit of `f^*A` is a left identity**, as an equality of morphisms. -/
theorem comparisonOne_mul (i : ℤ) :
    comparisonOne f A ▷ (pullbackFunctor f).obj (A.piece i) ≫ comparisonMul f A 0 i =
      (λ_ ((pullbackFunctor f).obj (A.piece i))).hom ≫
        eqToHom (congrArg (fun n ↦ (pullbackFunctor f).obj (A.piece n)) (zero_add i).symm) := by
  let _ := pullbackComparisonMonoidal f
  refine (Stacks.MonoidalGraded.mapOne_mul (pullbackFunctor f) (oneMorphism A) (mulHom A 0 i)
    (eqToHom (congrArg A.piece (zero_add i).symm)) (oneMorphism_mulHom A i)).trans ?_
  rw [eqToHom_map]

/-- **The global unit of `f^*A` is a right identity**, as an equality of morphisms. -/
theorem comparisonMul_one (i : ℤ) :
    (pullbackFunctor f).obj (A.piece i) ◁ comparisonOne f A ≫ comparisonMul f A i 0 =
      (ρ_ ((pullbackFunctor f).obj (A.piece i))).hom ≫
        eqToHom (congrArg (fun n ↦ (pullbackFunctor f).obj (A.piece n)) (add_zero i).symm) := by
  let _ := pullbackComparisonMonoidal f
  refine (Stacks.MonoidalGraded.mapMul_one (pullbackFunctor f) (oneMorphism A) (mulHom A i 0)
    (eqToHom (congrArg A.piece (add_zero i).symm)) (mulHom_oneMorphism A i)).trans ?_
  rw [eqToHom_map]

/-- **The pullback of a sheaf of graded algebras, with the multiplication conjugated by the
comparison of Stacks 01CD.** -/
noncomputable def comparisonGradedAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X) :=
  ofMorphismData (Osharp := X.sheaf)
    (structureSheafRing X).property
    (fun n ↦ (pullbackFunctor f).obj (A.piece n)) (comparisonMul f A) (comparisonOne f A)
    (comparisonMul_assoc f A) (comparisonOne_mul f A) (comparisonMul_one f A)

/-- The homogeneous pieces of `f^*A` are the pullbacks of those of `A`. -/
theorem comparisonGradedAlgebra_piece (n : ℤ) :
    (comparisonGradedAlgebra f A).piece n = (pullbackFunctor f).obj (A.piece n) :=
  rfl

/-- The multiplication of `f^*A` on a local pure tensor of sections of the pullbacks. -/
theorem comparisonGradedAlgebra_mul_app (i j : ℤ) (W : (Opens X.carrier)ᵒᵖ)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj W)
    (y : ((pullbackFunctor f).obj (A.piece j)).val.obj W) :
    ((comparisonGradedAlgebra f A).mul i j).app W x y =
      (comparisonMul f A i j).val.app W
        (tmul X ((pullbackFunctor f).obj (A.piece i)) ((pullbackFunctor f).obj (A.piece j))
          W x y) :=
  rfl

/-- The global unit of `f^*A`, as a local section. -/
theorem comparisonGradedAlgebra_one_eval (W : (Opens X.carrier)ᵒᵖ) :
    (comparisonGradedAlgebra f A).one.eval W = (comparisonOne f A).val.app W (oneSec X W) :=
  rfl

/-- The unit of `f^*A` read as a morphism out of the unit object is `comparisonOne`. -/
theorem oneMorphism_comparisonGradedAlgebra :
    oneMorphism (comparisonGradedAlgebra f A) = comparisonOne f A :=
  ((comparisonGradedAlgebra f A).piece 0).unitHomEquiv.symm_apply_apply (comparisonOne f A)

/-- **The multiplication of `f^*A` on pullback-unit sections.** -/
theorem comparisonGradedAlgebra_mul_pullbackUnit (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    ((comparisonGradedAlgebra f A).mul i j).app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece i) U x) (pullbackUnit f (A.piece j) U y) =
      pullbackUnit f (A.piece (i + j)) U ((A.mul i j).app U x y) :=
  (comparisonGradedAlgebra_mul_app f A i j _ _ _).trans
    (comparisonMul_tmul_pullbackUnit f A i j U x y)

/-- **The global unit of `f^*A` over an inverse image.** -/
theorem comparisonGradedAlgebra_one_eval_pullbackUnit (U : (Opens Y.carrier)ᵒᵖ) :
    (comparisonGradedAlgebra f A).one.eval ((opensMap f).op.obj U) =
      pullbackUnit f (A.piece 0) U (A.one.eval U) :=
  comparisonOne_val_app_oneSec f A U

/-- The multiplication of `f^*A` as a morphism out of the tensor product sheaf is the
conjugated multiplication it was built from. -/
theorem mulHom_comparisonGradedAlgebra (i j : ℤ) :
    mulHom (comparisonGradedAlgebra f A) i j = comparisonMul f A i j :=
  tensor_hom_ext fun W x y ↦
    (mulHom_tmul (comparisonGradedAlgebra f A) i j W x y).trans
      (comparisonGradedAlgebra_mul_app f A i j W x y)

/-! ### The unit of `f^* ⊣ f_*` as a homomorphism of sheaves of graded algebras -/

/-- **The unit of `f^* ⊣ f_*` is a homomorphism of sheaves of graded algebras**
`A ⟶ f_*(f^*A)`. Its multiplicativity is `comparisonGradedAlgebra_mul_pullbackUnit`: the
multiplication of `f^*A` was conjugated from that of `A` by the comparison of Stacks 01CD, and
the comparison carries a pullback-unit pure tensor to the pure tensor of the pullback-unit
images. -/
noncomputable def pullbackUnitalHom :
    UnitalHom A (pushforwardRingedSpace f (comparisonGradedAlgebra f A)) where
  app n := (pullbackAdjunction f).unit.app (A.piece n)
  map_mul i j U x y := (comparisonGradedAlgebra_mul_pullbackUnit f A i j U x y).symm
  map_one U := (comparisonGradedAlgebra_one_eval_pullbackUnit f A U).symm

/-- The degree-`n` component of `pullbackUnitalHom f A` is the unit of `f^* ⊣ f_*` at `A_n`. -/
@[simp] theorem pullbackUnitalHom_app (n : ℤ) :
    (pullbackUnitalHom f A).app n = (pullbackAdjunction f).unit.app (A.piece n) :=
  rfl

/-- **Pushforward of a homomorphism of sheaves of graded algebras.** -/
noncomputable def pushforwardUnitalHom
    {B D : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)} (g : UnitalHom B D) :
    UnitalHom (pushforwardRingedSpace f B) (pushforwardRingedSpace f D) where
  app n := (pushforwardFunctor f).map (g.app n)
  map_mul i j U x y := g.map_mul i j ((opensMap f).op.obj U) x y
  map_one U := g.map_one ((opensMap f).op.obj U)

/-- The degree-`n` component of `pushforwardUnitalHom f g` is the pushforward of `g_n`. -/
@[simp] theorem pushforwardUnitalHom_app
    {B D : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)} (g : UnitalHom B D)
    (n : ℤ) :
    (pushforwardUnitalHom f g).app n = (pushforwardFunctor f).map (g.app n) :=
  rfl

/-! ### Square-zero-ness of a pulled-back degree-one generator -/

section SquareZero

open Stacks.SheafOfModules Stacks.PullbackUnitGenerators

variable {M : SheafOfModules.{u} (structureRingSheaf Y)} (ι : M ⟶ A.piece 1)

/-- **The pulled-back degree-one generator** `f^*M ⟶ (f^*A)_1`. -/
noncomputable def pullbackGenerator :
    (pullbackFunctor f).obj M ⟶ (comparisonGradedAlgebra f A).piece 1 :=
  (pullbackFunctor f).map ι

/-- The bilinear map `(x, y) ↦ ι(x) · ι(y)` on local sections of `f^*M`, with values in the
degree-two piece of `f^*A`. `SquareZero (pullbackGenerator f A ι)` says that its diagonal
vanishes, and the extension of that from a generating family to all local sections is an
induction over a span, whose induction hypotheses are statements about this map; having it as a
`Stacks.BilinearMap` is what makes its additivity, linearity and naturality available without
proof. -/
noncomputable def genBilinear : SheafOfModules.BilinearMap ((pullbackFunctor f).obj M)
    ((pullbackFunctor f).obj M) ((comparisonGradedAlgebra f A).piece (1 + 1)) :=
  (((comparisonGradedAlgebra f A).mul 1 1).compLeft (pullbackGenerator f A ι).val).compRight
    (pullbackGenerator f A ι).val

/-- On local sections, `genBilinear f A ι` sends `(x, y)` to the product of `ι(x)` and `ι(y)`. -/
@[simp] theorem genBilinear_app (W : (Opens X.carrier)ᵒᵖ)
    (x y : ((pullbackFunctor f).obj M).val.obj W) :
    (genBilinear f A ι).app W x y =
      ((comparisonGradedAlgebra f A).mul 1 1).app W
        ((pullbackGenerator f A ι).val.app W x) ((pullbackGenerator f A ι).val.app W y) :=
  rfl

variable {W W' : (Opens X.carrier)ᵒᵖ}

/-- `genBilinear f A ι` vanishes when its first argument is zero. -/
theorem genBilinear_zero_left (y : ((pullbackFunctor f).obj M).val.obj W) :
    (genBilinear f A ι).app W 0 y = 0 :=
  (DFunLike.congr_fun (map_zero ((genBilinear f A ι).app W)) y).trans
    (AddMonoidHom.zero_apply y)

/-- `genBilinear f A ι` vanishes when its second argument is zero. -/
theorem genBilinear_zero_right (x : ((pullbackFunctor f).obj M).val.obj W) :
    (genBilinear f A ι).app W x 0 = 0 :=
  map_zero ((genBilinear f A ι).app W x)

/-- `genBilinear f A ι` is additive in its second argument. -/
theorem genBilinear_add_right (x y y' : ((pullbackFunctor f).obj M).val.obj W) :
    (genBilinear f A ι).app W x (y + y') =
      (genBilinear f A ι).app W x y + (genBilinear f A ι).app W x y' :=
  map_add ((genBilinear f A ι).app W x) y y'

/-- The bilinear map on two pullback-unit sections is the pullback-unit image of the product in
`A` of the images of the two sections under the degree-one generator. -/
theorem genBilinear_pullbackUnit (V : (Opens Y.carrier)ᵒᵖ) (t t' : M.val.obj V) :
    (genBilinear f A ι).app ((opensMap f).op.obj V) (pullbackUnit f M V t)
        (pullbackUnit f M V t') =
      pullbackUnit f (A.piece (1 + 1)) V ((A.mul 1 1).app V (ι.val.app V t) (ι.val.app V t')) :=
  (congrArg₂ (fun a b ↦ ((comparisonGradedAlgebra f A).mul 1 1).app ((opensMap f).op.obj V) a b)
      (pullbackUnit_naturality f ι V t) (pullbackUnit_naturality f ι V t')).trans
    (comparisonGradedAlgebra_mul_pullbackUnit f A 1 1 V (ι.val.app V t) (ι.val.app V t'))

/-- A member of the generating set of the span of the pullback-unit sections is itself a
restriction of a pullback-unit section, hence a member of the family. -/
theorem mem_unitSections_of_mem_generators {x : ((pullbackFunctor f).obj M).val.obj W}
    (hx : x ∈ {z | ∃ (Z : (Opens X.carrier)ᵒᵖ) (g : Z ⟶ W)
      (w : ((pullbackFunctor f).obj M).val.obj Z),
      w ∈ unitSections f M Z ∧ ((pullbackFunctor f).obj M).val.map g w = z}) :
    x ∈ unitSections f M W := by
  obtain ⟨Z, g, w, hw, rfl⟩ := hx
  exact map_mem_unitSections f M g hw

variable (hι : SquareZero ι)

include hι

/-- A member of the family of pullback-unit sections has square zero. -/
theorem genBilinear_self_eq_zero_of_mem_unitSections
    {x : ((pullbackFunctor f).obj M).val.obj W} (hx : x ∈ unitSections f M W) :
    (genBilinear f A ι).app W x x = 0 := by
  obtain ⟨V, g, t, rfl⟩ := hx
  refine ((genBilinear f A ι).naturality g (pullbackUnitSection f M V t)
    (pullbackUnitSection f M V t)).symm.trans ?_
  refine (congrArg (((comparisonGradedAlgebra f A).piece (1 + 1)).val.map g) ?_).trans
    (map_zero _)
  refine (genBilinear_pullbackUnit f A ι V t t).trans ?_
  rw [hι V t]
  exact map_zero _

/-- **The polarization step.** Two members of the family of pullback-unit sections
anticommute, because the family is closed under addition
(`Stacks.PullbackUnitGenerators.add_mem_unitSections`) and every member has square zero. -/
theorem genBilinear_add_eq_zero_of_mem_unitSections
    {x y : ((pullbackFunctor f).obj M).val.obj W} (hx : x ∈ unitSections f M W)
    (hy : y ∈ unitSections f M W) :
    (genBilinear f A ι).app W x y + (genBilinear f A ι).app W y x = 0 := by
  have h := genBilinear_self_eq_zero_of_mem_unitSections f A ι hι
    (add_mem_unitSections f M hx hy)
  rw [Stacks.BilinearMap.map_add_left, genBilinear_add_right, genBilinear_add_right,
    genBilinear_self_eq_zero_of_mem_unitSections f A ι hι hx,
    genBilinear_self_eq_zero_of_mem_unitSections f A ι hι hy, zero_add, add_zero] at h
  exact h

/-- **Anticommutativity extends from the pullback-unit sections to their span.** -/
theorem genBilinear_add_eq_zero_of_mem_span {x y : ((pullbackFunctor f).obj M).val.obj W}
    (hx : x ∈ (spanSubmodule ((pullbackFunctor f).obj M) (unitSections f M)).obj W)
    (hy : y ∈ (spanSubmodule ((pullbackFunctor f).obj M) (unitSections f M)).obj W) :
    (genBilinear f A ι).app W x y + (genBilinear f A ι).app W y x = 0 := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦
      (genBilinear f A ι).app W x y + (genBilinear f A ι).app W y x = 0)
    (fun x y hx hy ↦ genBilinear_add_eq_zero_of_mem_unitSections f A ι hι
      (mem_unitSections_of_mem_generators f hx) (mem_unitSections_of_mem_generators f hy))
    ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro y _
    rw [genBilinear_zero_left, genBilinear_zero_right, add_zero]
  · intro x _
    rw [genBilinear_zero_left, genBilinear_zero_right, add_zero]
  · intro x x' z _ _ _ h1 h2
    rw [Stacks.BilinearMap.map_add_left, genBilinear_add_right, add_add_add_comm, h1, h2, add_zero]
  · intro x y y' _ _ _ h1 h2
    rw [genBilinear_add_right, Stacks.BilinearMap.map_add_left, add_add_add_comm, h1, h2, add_zero]
  · intro r x y _ _ h
    rw [(genBilinear f A ι).map_smul_left, (genBilinear f A ι).map_smul_right, ← smul_add, h,
      smul_zero]
  · intro r x y _ _ h
    rw [(genBilinear f A ι).map_smul_right, (genBilinear f A ι).map_smul_left, ← smul_add, h,
      smul_zero]

/-- **Square-zero-ness extends from the pullback-unit sections to their span.** -/
theorem genBilinear_self_eq_zero_of_mem_span {x : ((pullbackFunctor f).obj M).val.obj W}
    (hx : x ∈ (spanSubmodule ((pullbackFunctor f).obj M) (unitSections f M)).obj W) :
    (genBilinear f A ι).app W x x = 0 := by
  refine Submodule.span_induction (p := fun x _ ↦ (genBilinear f A ι).app W x x = 0)
    ?_ ?_ ?_ ?_ hx
  · intro x hxm
    exact genBilinear_self_eq_zero_of_mem_unitSections f A ι hι
      (mem_unitSections_of_mem_generators f hxm)
  · exact genBilinear_zero_left f A ι 0
  · intro x y hx' hy' h1 h2
    rw [Stacks.BilinearMap.map_add_left, genBilinear_add_right, genBilinear_add_right, h1, h2,
      zero_add, add_zero]
    exact genBilinear_add_eq_zero_of_mem_span f A ι hι hx' hy'
  · intro r x _ h
    rw [(genBilinear f A ι).map_smul_left, (genBilinear f A ι).map_smul_right, h, smul_zero,
      smul_zero]

/-- **A pulled-back square-zero degree-one generator is square-zero.** Every local section of
`f^*M` lies, after restriction along a covering sieve, in the span of the pullback-unit sections
(`Stacks.PullbackUnitGenerators.spanSieve_mem`); square-zero-ness holds there by
`genBilinear_self_eq_zero_of_mem_span`, commutes with restriction, and the degree-two piece of
`f^*A` is a sheaf, so it holds outright.

This is the step that the quantification over *all* local sections genuinely needs:
square-zero-ness on the pullback-unit images alone is strictly weaker, and what bridges the gap
is that the family of pullback-unit sections is closed under addition after restriction. -/
theorem squareZero_pullbackGenerator : SquareZero (pullbackGenerator f A ι) := by
  intro W s
  refine ((comparisonGradedAlgebra f A).piece (1 + 1)).isSheaf.isSeparated W.unop
    (spanSieve ((pullbackFunctor f).obj M) (unitSections f M) s)
    (spanSieve_mem f M W s) _ 0 fun W' i hi ↦ ?_
  exact ((genBilinear f A ι).naturality i.op s s).trans
    ((genBilinear_self_eq_zero_of_mem_span f A ι hι hi).trans (map_zero _).symm)

end SquareZero

/-! ### The comparison morphism as a homomorphism of sheaves of graded algebras -/

section Comparison

variable {M : SheafOfModules.{u} (structureRingSheaf Y)} {ι : M ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj M ⟶ B.piece 1}
  (hA : IsExteriorAlgebra A ι) (hκ : SquareZero κ)

/-- **The canonical comparison morphism `f^*(A_n) ⟶ B_n`** of
`SheafOfModules.GradedAlgebra.pullbackComparison`, with its source ascribed at the
`Stacks.RingedSpace.structureRingSheaf` spelling of the structure sheaf of `X`.

`structureSheafRing X` and `structureRingSheaf X` are equal by `rfl`, and
`structureSheafRing` is not reducible, so the monoidal structure of Tag 01CA — named at the second
spelling — is not found for a morphism whose type is written at the first. The ascription is
what lets `⊗ₘ` be applied to the comparison. -/
noncomputable def comparisonHom (n : ℤ) :
    (pullbackFunctor f).obj (A.piece n) ⟶ B.piece n :=
  pullbackComparison f hA hκ n

/-- Equal morphisms of sheaves of modules agree on every local section. -/
private theorem congr_val_app {P Q : SheafOfModules.{u} (structureRingSheaf X)} {φ ψ : P ⟶ Q}
    (h : φ = ψ) (W : (Opens X.carrier)ᵒᵖ) (x : P.val.obj W) :
    φ.val.app W x = ψ.val.app W x := by
  rw [h]

/-- The comparison morphism is multiplicative on the pullback-unit sections. -/
theorem comparisonHom_mul (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    (comparisonHom f A hA hκ (i + j)).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece (i + j)) U ((A.mul i j).app U x y)) =
      (B.mul i j).app ((opensMap f).op.obj U)
        ((comparisonHom f A hA hκ i).val.app ((opensMap f).op.obj U)
          (pullbackUnit f (A.piece i) U x))
        ((comparisonHom f A hA hκ j).val.app ((opensMap f).op.obj U)
          (pullbackUnit f (A.piece j) U y)) :=
  pullbackComparison_mul f hA hκ i j U x y

/-- The comparison morphism carries the pulled-back unit to the unit. -/
theorem comparisonHom_one (U : (Opens Y.carrier)ᵒᵖ) :
    (comparisonHom f A hA hκ 0).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece 0) U (A.one.eval U)) =
      B.one.eval ((opensMap f).op.obj U) :=
  pullbackComparison_one f hA hκ U

/-- The comparison morphism matches the two degree-one generators. -/
theorem comparisonHom_generator (U : (Opens Y.carrier)ᵒᵖ) (s : M.val.obj U) :
    (comparisonHom f A hA hκ 1).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece 1) U (ι.val.app U s)) =
      κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U s) :=
  pullbackComparison_generator f hA hκ U s

/-- The comparison morphism computes the chosen unital homomorphism on pulled-back sections. -/
theorem comparisonHom_unit (n : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece n).val.obj U) :
    (comparisonHom f A hA hκ n).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece n) U x) =
      ((pushforwardDesc f hA hκ).app n).val.app U x :=
  pullbackComparison_unit f hA hκ n U x

/-- **The comparison morphism is multiplicative at every local section**, as an equality of
morphisms out of `f^*(A_i ⊗ A_j)`.

`SheafOfModules.GradedAlgebra.pullbackComparison_mul` gives multiplicativity on the
pullback-unit sections only, and the upgrade to all local sections needs no density argument:
both sides here are morphisms out of a **pullback**, so the adjunction reduces the equality to
the adjoint transposes, which are morphisms out of the tensor product sheaf `A_i ⊗ A_j` and are
therefore determined by their values on the local pure tensors. -/
theorem map_mulHom_comp_comparisonHom (i j : ℤ) :
    (pullbackFunctor f).map (mulHom A i j) ≫ comparisonHom f A hA hκ (i + j) =
      pullbackTensorComparison f (A.piece i) (A.piece j) ≫
        (comparisonHom f A hA hκ i ⊗ₘ comparisonHom f A hA hκ j) ≫ mulHom B i j :=
  pullback_tensor_hom_ext f fun U x y ↦ by
    rw [SheafOfModules.comp_val_app_apply ((pullbackFunctor f).map (mulHom A i j))
        (comparisonHom f A hA hκ (i + j)), pullbackUnit_naturality, mulHom_tmul,
      SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      pullbackTensorComparison_pullbackUnit, tensorHom_tmul, mulHom_tmul]
    exact comparisonHom_mul f A hA hκ i j U x y

/-- **The comparison morphism is multiplicative**, as an equality of morphisms out of
`(f^*A)_i ⊗ (f^*A)_j`. -/
theorem comparisonMul_comp_comparisonHom (i j : ℤ) :
    comparisonMul f A i j ≫ comparisonHom f A hA hκ (i + j) =
      (comparisonHom f A hA hκ i ⊗ₘ comparisonHom f A hA hκ j) ≫ mulHom B i j := by
  rw [comparisonMul_eq, Category.assoc, IsIso.inv_comp_eq, map_mulHom_comp_comparisonHom]

/-- **The comparison morphism carries the pulled-back unit of `A` to the unit of `B`**, as an
equality of morphisms out of `f^*𝒪_Y`. -/
theorem map_oneMorphism_comp_comparisonHom :
    (pullbackFunctor f).map (oneMorphism A) ≫ comparisonHom f A hA hκ 0 =
      pullbackUnitComparison f ≫ oneMorphism B :=
  pullback_hom_ext f fun U r ↦
    (congrArg ((comparisonHom f A hA hκ 0).val.app ((opensMap f).op.obj U))
          ((pullbackUnit_naturality f (oneMorphism A) U r).trans
            ((congrArg (pullbackUnit f (A.piece 0) U)
                (SheafOfModules.GradedAlgebra.oneHom_val_app A U r)).trans
              (pullbackUnit_smul f (A.piece 0) U r (A.one.eval U))))).trans
      ((((comparisonHom f A hA hκ 0).val.app ((opensMap f).op.obj U)).hom.map_smul
            (sharp f U r) (pullbackUnit f (A.piece 0) U (A.one.eval U))).trans
        ((congrArg (fun z ↦ sharp f U r • z) (comparisonHom_one f A hA hκ U)).trans
          ((SheafOfModules.GradedAlgebra.oneHom_val_app B ((opensMap f).op.obj U)
              (sharp f U r)).symm.trans
            (congrArg ((oneMorphism B).val.app ((opensMap f).op.obj U))
              (pullbackUnitComparison_pullbackUnit f U r).symm))))

/-- **The comparison morphism is unital**, as an equality of morphisms out of `𝟙_`. -/
theorem comparisonOne_comp_comparisonHom :
    comparisonOne f A ≫ comparisonHom f A hA hκ 0 = oneMorphism B := by
  rw [comparisonOne_eq, Category.assoc, IsIso.inv_comp_eq, map_oneMorphism_comp_comparisonHom]

/-- **The comparison morphism is a homomorphism of sheaves of graded algebras** `f^*A ⟶ B`. -/
noncomputable def comparisonUnitalHom : UnitalHom (comparisonGradedAlgebra f A) B where
  app n := comparisonHom f A hA hκ n
  map_mul i j W x y :=
    (congrArg ((comparisonHom f A hA hκ (i + j)).val.app W)
          (comparisonGradedAlgebra_mul_app f A i j W x y)).trans
      ((congrArg (fun φ : (pullbackFunctor f).obj (A.piece i) ⊗
            (pullbackFunctor f).obj (A.piece j) ⟶ B.piece (i + j) ↦
          φ.val.app W (tmul X ((pullbackFunctor f).obj (A.piece i))
            ((pullbackFunctor f).obj (A.piece j)) W x y))
          (comparisonMul_comp_comparisonHom f A hA hκ i j)).trans
        ((congrArg ((mulHom B i j).val.app W)
            (tensorHom_tmul (comparisonHom f A hA hκ i) (comparisonHom f A hA hκ j)
              W x y)).trans
          (mulHom_tmul B i j W _ _)))
  map_one W :=
    (congrArg ((comparisonHom f A hA hκ 0).val.app W)
          (comparisonGradedAlgebra_one_eval f A W)).trans
      ((congrArg (fun φ : 𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) ⟶ B.piece 0 ↦
            φ.val.app W (oneSec X W))
          (comparisonOne_comp_comparisonHom f A hA hκ)).trans
        (oneMorphism_val_app_oneSec B W))

/-- The degree-`n` component of `comparisonUnitalHom f A hA hκ` is `comparisonHom f A hA hκ n`. -/
@[simp] theorem comparisonUnitalHom_app (n : ℤ) :
    (comparisonUnitalHom f A hA hκ).app n = comparisonHom f A hA hκ n :=
  rfl

/-- **The comparison morphism extends the pulled-back degree-one generator**, as an equality of
morphisms out of `f^*M`. -/
theorem pullbackGenerator_comp_comparisonHom :
    pullbackGenerator f A ι ≫ comparisonHom f A hA hκ 1 = κ :=
  pullback_hom_ext f fun U s ↦
    (congrArg ((comparisonHom f A hA hκ 1).val.app ((opensMap f).op.obj U))
        (pullbackUnit_naturality f ι U s)).trans
      (comparisonHom_generator f A hA hκ U s)

end Comparison

/-! ### Invertibility of the comparison morphism -/

section Invertibility

variable {M : SheafOfModules.{u} (structureRingSheaf Y)} {ι : M ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj M ⟶ B.piece 1}
  (hA : IsExteriorAlgebra A ι) (hκ : SquareZero κ) (hB : IsExteriorAlgebra B κ)

/-- The chosen unital homomorphism `A ⟶ f_*B` extends the pushed-forward generator. -/
theorem pushforwardDesc_extends :
    ι ≫ (pushforwardDesc f hA hκ).app 1 = pushforwardGenerator f κ :=
  hA.desc_extends _ (pushforwardGenerator f κ) (squareZero_pushforwardGenerator f hκ)

/-- **The homomorphism `B ⟶ f^*A` out of the exterior algebra of `f^*M`**, given by the
universal property of `B` applied to the pulled-back degree-one generator, which is square-zero
by `squareZero_pullbackGenerator`. -/
noncomputable def descUnitalHom : UnitalHom B (comparisonGradedAlgebra f A) :=
  hB.desc (comparisonGradedAlgebra f A) (pullbackGenerator f A ι)
    (squareZero_pullbackGenerator f A ι hA.1)

/-- The homomorphism `descUnitalHom f A hA hB` extends the pulled-back degree-one generator. -/
theorem descUnitalHom_extends :
    κ ≫ (descUnitalHom f A hA hB).app 1 = pullbackGenerator f A ι :=
  hB.desc_extends _ (pullbackGenerator f A ι) (squareZero_pullbackGenerator f A ι hA.1)

include hA in
/-- The unit of `f^* ⊣ f_*`, composed with a degree-one generator of `A`, is a square-zero
degree-one generator of `f_*(f^*A)`. -/
theorem squareZero_comp_pullbackUnitalHom :
    SquareZero (ι ≫ (pullbackUnitalHom f A).app 1) := fun U s ↦
  (comparisonGradedAlgebra_mul_pullbackUnit f A 1 1 U (ι.val.app U s) (ι.val.app U s)).trans
    ((congrArg (pullbackUnit f (A.piece (1 + 1)) U) (hA.1 U s)).trans (map_zero _))

/-- **One composite is the identity of `B`.** The composite `B ⟶ f^*A ⟶ B` is a unital
endomorphism of `B` fixing its degree-one generator, hence the identity by the universal
property of `B`. -/
theorem descUnitalHom_comp_comparisonUnitalHom :
    (descUnitalHom f A hA hB).comp (comparisonUnitalHom f A hA hκ) = UnitalHom.id B :=
  hB.eq_id ((Category.assoc κ ((descUnitalHom f A hA hB).app 1)
        (comparisonHom f A hA hκ 1)).symm.trans
    ((congrArg (fun φ : (pullbackFunctor f).obj M ⟶ (comparisonGradedAlgebra f A).piece 1 ↦
          φ ≫ comparisonHom f A hA hκ 1) (descUnitalHom_extends f A hA hB)).trans
      (pullbackGenerator_comp_comparisonHom f A hA hκ)))

/-- The comparison morphism is a split epimorphism in every degree. -/
theorem descUnitalHom_app_comp_comparisonHom (n : ℤ) :
    (descUnitalHom f A hA hB).app n ≫ comparisonHom f A hA hκ n = 𝟙 (B.piece n) :=
  congrArg (fun g : UnitalHom B B ↦ g.app n)
    (descUnitalHom_comp_comparisonUnitalHom f A hA hκ hB)

/-- **The two unital homomorphisms `A ⟶ f_*(f^*A)` agree.** One is the unit of `f^* ⊣ f_*`
(`pullbackUnitalHom`), the other is the chosen homomorphism `A ⟶ f_*B` followed by the
pushforward of `descUnitalHom`. Both extend the degree-one generator `ι` to `ι ≫ η`, so the
universal property of `A` identifies them. This is what makes the other composite the
identity. -/
theorem pushforwardDesc_comp_eq_pullbackUnitalHom :
    (pushforwardDesc f hA hκ).comp (pushforwardUnitalHom f (descUnitalHom f A hA hB)) =
      pullbackUnitalHom f A := by
  have hgen : ι ≫ ((pushforwardDesc f hA hκ).comp
        (pushforwardUnitalHom f (descUnitalHom f A hA hB))).app 1 =
      ι ≫ (pullbackUnitalHom f A).app 1 := by
    ext U s
    have h1 : ((pushforwardDesc f hA hκ).app 1).val.app U (ι.val.app U s) =
        κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U s) :=
      (congr_val_app (pushforwardDesc_extends f A hA hκ) U s).trans
        (pushforwardGenerator_val_app f κ U s)
    have h2 : ((descUnitalHom f A hA hB).app 1).val.app ((opensMap f).op.obj U)
          (κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U s)) =
        pullbackUnit f (A.piece 1) U (ι.val.app U s) :=
      (congr_val_app (descUnitalHom_extends f A hA hB) _ _).trans (pullbackUnit_naturality f ι U s)
    exact (congrArg (((descUnitalHom f A hA hB).app 1).val.app ((opensMap f).op.obj U)) h1).trans h2
  exact (hA.desc_unique _ _ (squareZero_comp_pullbackUnitalHom f A hA) hgen).trans
    (hA.desc_unique _ _ (squareZero_comp_pullbackUnitalHom f A hA) rfl).symm

/-- **The other composite is the identity of `f^*A`.** -/
theorem comparisonHom_comp_descUnitalHom_app (n : ℤ) :
    comparisonHom f A hA hκ n ≫ (descUnitalHom f A hA hB).app n =
      𝟙 ((pullbackFunctor f).obj (A.piece n)) :=
  pullback_hom_ext f fun U x ↦
    (congrArg (((descUnitalHom f A hA hB).app n).val.app ((opensMap f).op.obj U))
        (comparisonHom_unit f A hA hκ n U x)).trans
      (congr_val_app (congrArg (·.app n)
        (pushforwardDesc_comp_eq_pullbackUnitalHom f A hA hκ hB)) U x)

include hB in
/-- **The comparison morphism `f^*(A_n) ⟶ B_n` is an isomorphism in every degree.** This is
Stacks 01CI for the exterior algebra, degreewise: `f^*A` carries a graded-algebra structure
(`comparisonGradedAlgebra`) whose degree-one generator `f^*ι` is square-zero
(`squareZero_pullbackGenerator`), so the universal property of `B = ⋀(f^*M)` produces a map back,
and the two composites are identities by the universal properties of `B` and of `A`. -/
theorem isIso_comparisonHom (n : ℤ) : IsIso (comparisonHom f A hA hκ n) :=
  ⟨(descUnitalHom f A hA hB).app n, comparisonHom_comp_descUnitalHom_app f A hA hκ hB n,
    descUnitalHom_app_comp_comparisonHom f A hA hκ hB n⟩

include hB in
/-- **The comparison morphism of `SheafOfModules.GradedAlgebra.pullbackComparison` is an
isomorphism in every degree.** -/
theorem isIso_pullbackComparison (n : ℤ) : IsIso (pullbackComparison f hA hκ n) :=
  isIso_comparisonHom f A hA hκ hB n

include hB in
/-- **Stacks 01CI for the exterior algebra, degreewise**: the pullback of the degree-`n` piece
of the exterior algebra of `M` is the degree-`n` piece of the exterior algebra of `f^*M`. -/
noncomputable def pieceIso (n : ℤ) : (pullbackFunctor f).obj (A.piece n) ≅ B.piece n :=
  @asIso _ _ _ _ (comparisonHom f A hA hκ n) (isIso_comparisonHom f A hA hκ hB n)

/-- The forward map of `pieceIso f A hA hκ hB n` is `comparisonHom f A hA hκ n`. -/
@[simp] theorem pieceIso_hom (n : ℤ) :
    (pieceIso f A hA hκ hB n).hom = comparisonHom f A hA hκ n :=
  rfl

include hB in
/-- **Stacks 01CI for the exterior algebra, on the underlying direct-sum sheaves.** -/
noncomputable def sheafIso :
    (pullbackFunctor f).obj (∐ fun n : ℕ ↦ A.piece (n : ℤ)) ≅ ∐ fun n : ℕ ↦ B.piece (n : ℤ) :=
  @asIso _ _ _ _ (pullbackComparisonSigma f hA hκ)
    (isIso_pullbackComparisonSigma f hA hκ fun n ↦ isIso_pullbackComparison f A hA hκ hB (n : ℤ))

/-- The forward map of `sheafIso f A hA hκ hB` is `pullbackComparisonSigma f hA hκ`. -/
@[simp] theorem sheafIso_hom :
    (sheafIso f A hA hκ hB).hom = pullbackComparisonSigma f hA hκ :=
  rfl

end Invertibility

/-! ### Stacks 01CI for the exterior algebra -/

section Statement

/-- **The comparison between the pullback of an exterior algebra and the exterior algebra of the
pulled-back module**, on homogeneous pieces and on the underlying direct-sum sheaf, compatible
with the graded algebra structures and with the degree-one generators.

The two exterior algebras enter through their universal properties: `A` with its degree-one
generator `ι` and `B` with its degree-one generator `κ`. Compatibility with the product, with
the unit and with the generator is expressed on the pullback-unit images of local sections, as
in the source; those images generate the pullback locally
(`Stacks.PullbackUnitGenerators.spanSieve_mem`), which is what makes the three clauses determine
the comparison. -/
structure ExteriorAlgebraPullbackIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))
    {M : SheafOfModules.{u} (structureRingSheaf Y)} (ι : M ⟶ A.piece 1)
    (B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X))
    (κ : (pullbackFunctor f).obj M ⟶ B.piece 1) where
  /-- The comparison in each integer degree. -/
  app (n : ℤ) : (pullbackFunctor f).obj (A.piece n) ≅ B.piece n
  /-- The comparison of the underlying direct-sum sheaves. -/
  sheafIso : (pullbackFunctor f).obj (∐ fun n : ℕ ↦ A.piece (n : ℤ)) ≅
    ∐ fun n : ℕ ↦ B.piece (n : ℤ)
  /-- The underlying sheaf comparison restricts to the comparison of each homogeneous
  summand. -/
  sheafIso_ι (n : ℕ) :
    (pullbackFunctor f).map (Sigma.ι (fun m : ℕ ↦ A.piece (m : ℤ)) n) ≫ sheafIso.hom =
      (app n).hom ≫ Sigma.ι (fun m : ℕ ↦ B.piece (m : ℤ)) n
  /-- Multiplication is preserved on the pulled-back local sections. -/
  map_mul (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj U)
      (b : (A.piece j).val.obj U) :
    (app (i + j)).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece (i + j)) U ((A.mul i j).app U a b)) =
      (B.mul i j).app ((opensMap f).op.obj U)
        ((app i).hom.val.app ((opensMap f).op.obj U) (pullbackUnit f (A.piece i) U a))
        ((app j).hom.val.app ((opensMap f).op.obj U) (pullbackUnit f (A.piece j) U b))
  /-- The degree-zero unit is preserved. -/
  map_one (U : (Opens Y.carrier)ᵒᵖ) :
    (app 0).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece 0) U (A.one.eval U)) = B.one.eval ((opensMap f).op.obj U)
  /-- The comparison restricts to the canonical pullback of the degree-one generator. -/
  map_generator (U : (Opens Y.carrier)ᵒᵖ) (s : M.val.obj U) :
    (app 1).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece 1) U (ι.val.app U s)) =
      κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U s)

variable {f : X ⟶ Y} {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)}
  {M : SheafOfModules.{u} (structureRingSheaf Y)} {ι : M ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj M ⟶ B.piece 1}

/-- Two comparisons agree as soon as their degreewise components and their underlying sheaf
components do: the remaining fields are propositions. -/
@[ext]
theorem ExteriorAlgebraPullbackIso.ext {e₁ e₂ : ExteriorAlgebraPullbackIso f A ι B κ}
    (happ : ∀ n, e₁.app n = e₂.app n) (hsheaf : e₁.sheafIso = e₂.sheafIso) : e₁ = e₂ := by
  obtain ⟨app₁, sheaf₁, _, _, _, _⟩ := e₁
  obtain ⟨app₂, sheaf₂, _, _, _, _⟩ := e₂
  have h : app₁ = app₂ := funext happ
  subst h
  subst hsheaf
  rfl

variable (f A ι B κ)

/-- **Stacks 01CI for the exterior algebra of a sheaf of modules.** For a morphism of ringed
spaces `f : X ⟶ Y` and a sheaf of `𝒪_Y`-modules `M`, the pullback of the exterior algebra of `M`
is canonically isomorphic to the exterior algebra of `f^*M`, degreewise and on the underlying
direct-sum sheaf, compatibly with the products, the units and the degree-one generators.

This covers the **exterior algebra** clause of Tag 01CI only. The tensor-algebra clause is
`Stacks.PullbackAlgebra.pullbackTensorPieceIso` and `pullbackTensorSheafIso`; the
symmetric-algebra clause is **not** proved here. Both exterior algebras are given by their
universal properties (`SheafOfModules.GradedAlgebra.IsExteriorAlgebra`) rather than by a
construction, so nothing here depends on an unconstructed exterior algebra. -/
@[stacks 01CI
  "pullback_exterior_algebra: the EXTERIOR algebra clause only; symmetric NOT proved"]
noncomputable def exteriorAlgebraPullbackIso (hA : IsExteriorAlgebra A ι)
    (hB : IsExteriorAlgebra B κ) : ExteriorAlgebraPullbackIso f A ι B κ where
  app n := pieceIso f A hA hB.1 hB n
  sheafIso := sheafIso f A hA hB.1 hB
  sheafIso_ι n := pullbackComparisonSigma_ι f hA hB.1 n
  map_mul i j U a b := comparisonHom_mul f A hA hB.1 i j U a b
  map_one U := comparisonHom_one f A hA hB.1 U
  map_generator U s := comparisonHom_generator f A hA hB.1 U s

/-- **The comparison of Stacks 01CI is unique.** Compatibility with multiplication, with the
unit and with the degree-one generators on the pullback-unit sections determines the comparison
in every degree, and the restriction to the homogeneous summands then determines the comparison
of the underlying direct-sum sheaves. -/
@[stacks 01CI
  "pullback_exterior_algebra: canonicality of the EXTERIOR algebra comparison only"]
theorem exteriorAlgebraPullbackIso_unique (hA : IsExteriorAlgebra A ι)
    (hB : IsExteriorAlgebra B κ) (e : ExteriorAlgebraPullbackIso f A ι B κ) :
    e = exteriorAlgebraPullbackIso f A ι B κ hA hB := by
  have happ : ∀ n, (e.app n).hom = comparisonHom f A hA hB.1 n :=
    pullbackComparison_unique f hA hB.1 (fun n ↦ (e.app n).hom) e.map_mul e.map_one
      e.map_generator
  refine ExteriorAlgebraPullbackIso.ext (fun n ↦ Iso.ext (happ n)) (Iso.ext ?_)
  exact pullbackComparisonSigma_unique f hA hB.1 fun n ↦
    (e.sheafIso_ι n).trans
      (congrArg (fun φ : (pullbackFunctor f).obj (A.piece (n : ℤ)) ⟶ B.piece (n : ℤ) ↦
        φ ≫ Sigma.ι (fun m : ℕ ↦ B.piece (m : ℤ)) n) (happ (n : ℤ)))

end Statement

end Stacks.PullbackExteriorAlgebra

end
