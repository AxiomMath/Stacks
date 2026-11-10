module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WhiskerTensorCoherence

/-!
# The fourth normalisation of the restriction tensorator, and multiplicativity

`Stacks.SheafOfModules.TensorPower.map_coherentMulIso_tensorPowerComparison` takes six
normalisations of a tensorator `β M N : R(M ⊗ N) ≅ R M ⊗ R N` as inputs. For restriction along a
continuous and cocontinuous functor of sites,
`Stacks.SheafOfModules.TensorPower.whiskerRestriction`,
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/WhiskerTensorNaturality.lean` supplied
`IsNaturalLeft` and `IsNaturalRight`, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/WhiskerTensorCoherence.lean` supplied
`IsSymmetric`, `IsLeftUnital` and `IsRightUnital`, recording `IsAssociative` as the one still
missing. This file supplies it, and draws the consequence the other five were collected for:
**the comparison of integral tensor powers along a restriction of sites is multiplicative.**

## The extra comparison layer

The three normalisations of `WhiskerTensorCoherence` are transports of a presheaf-level identity
through sheafification: restriction of *presheaves* of modules along `H` is Mathlib's monoidal
functor `PresheafOfModules.pushforward₀OfCommRingCat`, and a morphism out of the restriction of a
tensor product sheaf is pinned by its value on the restricted sheafification unit
`whiskerTensorUnit`, by `whiskerTensorSheafIso_hom`.

The associativity constraint `Stacks.SheafOfModules.tensorSheafAssociator` is not of that shape.
It is the sheafified presheaf associator conjugated by `tensorSheafAssocLeft` and
`tensorSheafAssocRight`, and the first of those enters **inverted**, so the value of
`R.map (α_ M N P).hom` on `whiskerTensorUnit O hO H (M ⊗ N) P` is not computable from the
transport calculus. The identity is therefore first precomposed with
`(whiskerRestriction O hO H).map (tensorSheafAssocLeft O hO M N P).hom`, which is invertible, and
then tested on `whiskerSheafifyUnit O hO H ((M.val ⊗ N.val) ⊗ P.val)` — the restricted
sheafification unit at the *triple objectwise* tensor product, one layer below
`whiskerTensorUnit`. That is the whole of the extra work; there is no new coherence theory.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.whiskerPresheafDelta`: the tensorator of the restriction of
  presheaves of modules, at arbitrary presheaves of modules rather than at the underlying
  presheaves of a pair of sheaves. It is the comultiplication of the oplax monoidal structure of
  `whiskerPresheafRestriction`, and carrying it at this generality is what lets the presheaf-level
  coherences below be stated at the spellings the transport produces.

## Main results

* `Stacks.SheafOfModules.sheafificationUnit_whiskerRight_comp_associator`: **the associativity
  constraint of the tensor product sheaf, read through the sheafification units of the objectwise
  tensor products.** This is the one-site statement the extra layer is for, and it holds on any
  site; the restriction enters only afterwards.
* `…whiskerSheafifyUnit_comp_associative_left` and `…whiskerSheafifyUnit_comp_associative_right`:
  the two sides of the normalisation, each evaluated on the restricted sheafification unit of the
  triple objectwise tensor product and reduced to a composite with the same tail.
* `…isAssociative_whiskerTensorator`: **the fourth normalisation**, hence the last of the six.
* `…map_coherentMulIso_whiskerTensorPowerIso`: **the payoff.** The comparison
  `R(L^{⊗ n}) ≅ (R L)^{⊗ n}` of `whiskerTensorPowerIso` carries the coherent multiplication of
  Tag 01CU for `L` to the one for `R L`, in every pair of integer degrees. In the slice case this
  is multiplicativity of `Stacks.SheafOfModules.TensorPower.overTensorPowerIso`.

## Implementation notes

The two chases are **term-mode**, through the combinator
`Stacks.SheafOfModules.chase_step`, and not `rw` chains. The reason is the one
`WhiskerTensorCoherence` records for its own proofs, in its sharpest form: the source category of
`whiskerPresheafRestriction O H` is `PresheafOfModules (structureRingPresheaf O)` while `M.val`
lives in `PresheafOfModules (structureSheaf O hO).obj`, and the two index presheaves of rings are
equal only by unfolding the semireducible `structureSheaf`. So a goal mentioning both — which
every step of these chases does — is **not type-correct at `implicit` transparency**, and
`rewrite`'s motive check is refused even when the pattern is present. An `exact` is checked at
default transparency and is accepted. `chase_step` is stated in an abstract category, where `rw`
is unproblematic, and every step equation is fed to it by application.

For the same reason each step is *stated* at the spelling the next step consumes and *proved* by
`exact` from the existing lemma at its own spelling: `TensorSheafification.tensorPresheaf` versus
`⊗`, `((whiskerRestriction O hO H).obj M).val` versus
`(whiskerPresheafRestriction O H).obj M.val`, and `TensorSheafification.toSheafify` versus
`TensorLocalProperties.sheafificationUnit`.

One spelling gap cannot be closed that way, because it is in a *type* the step lemma does not get
to choose: `whiskerTensorator` lands in the tensor product sheaf written
`Tensor.sheafTensor`, while the factor that follows it reads the same object as `⊗` for
`Strict.monoidalCategory`. The two agree by `Strict.tensorObj_eq`, which is `rfl` only once
`CategoryTheory.Monoidal.induced` has been unfolded. Deciding that against a *given* object is
affordable — the statements of the chases do it — but deciding it while `chase_step`'s `k`, `r`
and `T` are still metavariables is not, and exceeds the heartbeat budget on its own. Those steps
therefore pass `Y`, the common codomain of `f` and `v`, explicitly, at the spelling the goal uses.
Nothing else about the chases depends on those arguments; dropping a `(Y := …)` makes the
declaration time out at `isDefEq`.

The presheaf-level associativity is Mathlib's `Functor.OplaxMonoidal.associativity` for
`whiskerPresheafRestriction`, which is already the inverted convention the transport needs; no
objectwise computation on local pure tensors is involved, unlike the three coherences of
`WhiskerTensorCoherence`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.TensorLocalProperties

universe v u v' u' w

namespace Stacks.SheafOfModules

/-! ### Combinators for a term-mode chase -/

/-- **One step of a chase.** The head `u` of a composite is moved across the next factor `f` by
the step equation `h`, and the rest `k` of the composite is carried along by `hr`. Stated in an
abstract category: the chases below run in categories of presheaves of modules whose index
presheaf of rings is spelled in two definitionally equal ways, where `rewrite` is refused. -/
public theorem chase_step {D : Type*} [Category D] {W X Y Z T : D} {u : W ⟶ X} {f : X ⟶ Y}
    {g : W ⟶ Z} {v : Z ⟶ Y} (h : u ≫ f = g ≫ v) {k : Y ⟶ T} {r : Z ⟶ T} (hr : v ≫ k = r) :
    u ≫ f ≫ k = g ≫ r := by
  rw [← Category.assoc, h, Category.assoc, hr]

/-- An equality of three-fold composites with a common tail. -/
public theorem comp₃_tail {D : Type*} [Category D] {W X Y Z X' Y' T : D} {a₁ : W ⟶ X}
    {a₂ : X ⟶ Y} {a₃ : Y ⟶ Z} {b₁ : W ⟶ X'} {b₂ : X' ⟶ Y'} {b₃ : Y' ⟶ Z}
    (h : a₁ ≫ a₂ ≫ a₃ = b₁ ≫ b₂ ≫ b₃) (k : Z ⟶ T) :
    a₁ ≫ a₂ ≫ a₃ ≫ k = b₁ ≫ b₂ ≫ b₃ ≫ k := by
  have h₁ : a₁ ≫ a₂ ≫ a₃ ≫ k = (a₁ ≫ a₂ ≫ a₃) ≫ k := by simp
  have h₂ : b₁ ≫ b₂ ≫ b₃ ≫ k = (b₁ ≫ b₂ ≫ b₃) ≫ k := by simp
  rw [h₁, h₂, h]

/-- An equality of composites of morphisms of sheaves of modules, read on the underlying
morphisms of presheaves of modules. -/
public theorem comp_val_congr {C₀ : Type*} [Category C₀] {J₀ : GrothendieckTopology C₀}
    {Rs : Sheaf J₀ RingCat.{w}} {A B A' Z : _root_.SheafOfModules.{w} Rs}
    {f : A ⟶ B} {g : B ⟶ Z} {f' : A ⟶ A'} {g' : A' ⟶ Z} (h : f ≫ g = f' ≫ g') :
    f.val ≫ g.val = f'.val ≫ g'.val :=
  (_root_.SheafOfModules.comp_val f g).symm.trans
    ((congrArg (fun z : A ⟶ Z => z.val) h).trans (_root_.SheafOfModules.comp_val f' g'))

/-- A four-fold composite of morphisms of sheaves of modules, read on the underlying morphisms of
presheaves of modules. -/
public theorem comp_val₄ {C₀ : Type*} [Category C₀] {J₀ : GrothendieckTopology C₀}
    {Rs : Sheaf J₀ RingCat.{w}} {A B C D E : _root_.SheafOfModules.{w} Rs}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) :
    (a ≫ b ≫ c ≫ d).val = a.val ≫ b.val ≫ c.val ≫ d.val := by
  rw [_root_.SheafOfModules.comp_val, _root_.SheafOfModules.comp_val,
    _root_.SheafOfModules.comp_val]

/-! ### The associativity constraint read through the sheafification units -/

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory
  Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Naturality of the sheafification unit**, with the sheafification functor written at the
`Stacks.SheafOfModules.TensorSheafification.sheafify` spelling the tensor product development
uses. -/
public theorem sheafificationUnit_naturality_sheafify
    {P Q : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj} (g : P ⟶ Q) :
    sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map g).val =
      g ≫ sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) Q :=
  Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality_structureSheaf O hO g

/-- **The associativity constraint of the tensor product sheaf, precomposed with
`tensorSheafAssocLeft`.** Stated this way the inverted comparison inside
`Stacks.SheafOfModules.tensorSheafAssociator` has been cancelled, which is what makes the
constraint accessible to the transport calculus of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/WhiskerTensorCoherence.lean`. -/
public theorem tensorSheafAssocLeft_hom_comp_associator
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssocLeft O hO M N P).hom ≫ (α_ M N P).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (α_ M.val N.val P.val).hom ≫
        (tensorSheafAssocRight O hO M N P).hom := by
  rw [associator_eq_tensorSheafAssociator]
  exact Iso.hom_inv_id_assoc (tensorSheafAssocLeft O hO M N P)
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (α_ M.val N.val P.val).hom ≫
      (tensorSheafAssocRight O hO M N P).hom)

/-- Left whiskering by a sheaf of modules, read on the sheafification unit of the objectwise
tensor product. -/
public theorem sheafificationUnit_comp_whiskerLeft_val
    (X : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {Y Z : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f : Y ⟶ Z) :
    sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
          (X.val ⊗ Y.val) ≫ (X ◁ f).val =
      (X.val ◁ f.val) ≫ sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) (X.val ⊗ Z.val) :=
  (congrArg (fun z : X ⊗ Y ⟶ X ⊗ Z => sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
        (X.val ⊗ Y.val) ≫ z.val)
      (whiskerLeft_eq_sheafify_map O hO X f)).trans
    (sheafificationUnit_naturality_sheafify O hO (X.val ◁ f.val))

/-- Right whiskering by a sheaf of modules, read on the sheafification unit of the objectwise
tensor product. -/
public theorem sheafificationUnit_comp_whiskerRight_val
    {X Y : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f : X ⟶ Y)
    (Z : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
          (X.val ⊗ Z.val) ≫ (f ▷ Z).val =
      (f.val ▷ Z.val) ≫ sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) (Y.val ⊗ Z.val) :=
  (congrArg (fun z : X ⊗ Z ⟶ Y ⊗ Z => sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
        (X.val ⊗ Z.val) ≫ z.val)
      (whiskerRight_eq_sheafify_map O hO f Z)).trans
    (sheafificationUnit_naturality_sheafify O hO (f.val ▷ Z.val))

set_option maxHeartbeats 1000000 in
-- the term proof unifies long composites of sheafification units of tensor products
/-- **The associativity constraint of the tensor product sheaf, read through the sheafification
units of the objectwise tensor products.**

The left-hand side is the composite that the extra comparison layer produces: the sheafification
unit of `(M.val ⊗ N.val) ⊗ P.val` factors through `tensorSheafAssocLeft`, and what is left of the
associativity constraint once that factor is cancelled is the sheafified presheaf associator
followed by `tensorSheafAssocRight`. Both comparisons are naturality of the sheafification unit,
so the constraint becomes the presheaf associator followed by two units. -/
public theorem sheafificationUnit_whiskerRight_comp_associator
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
          (M.val ⊗ N.val) ▷ P.val) ≫
        sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
            ((M ⊗ N).val ⊗ P.val) ≫
          (α_ M N P).hom.val =
      (α_ M.val N.val P.val).hom ≫
        (M.val ◁ sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
            (N.val ⊗ P.val)) ≫
          sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
            (M.val ⊗ (N ⊗ P).val) :=
  (chase_step
      (sheafificationUnit_naturality_sheafify O hO
          (sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
            (M.val ⊗ N.val) ▷ P.val)).symm
      (comp_val_congr (tensorSheafAssocLeft_hom_comp_associator O hO M N P))).trans
    (chase_step (sheafificationUnit_naturality_sheafify O hO (α_ M.val N.val P.val).hom)
      (sheafificationUnit_naturality_sheafify O hO
        (M.val ◁ sheafificationUnit
          (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
          (N.val ⊗ P.val))))

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory
  Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

section Whisker

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (H : C' ⥤ C) [H.IsContinuous J' J] [H.IsCocontinuous J' J]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}]

/-! ### The presheaf-level tensorator at arbitrary presheaves -/

/-- **The tensorator of the restriction of presheaves of modules**, at arbitrary presheaves of
modules. `Stacks.SheafOfModules.TensorPower.whiskerPresheafTensorIso` is its value on the
underlying presheaves of a pair of sheaves; the transport of the associativity constraint needs it
at a tensor product presheaf in one slot, which is not of that form. -/
public def whiskerPresheafDelta
    (P Q : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :
    (whiskerPresheafRestriction O H).obj (P ⊗ Q) ⟶
      (whiskerPresheafRestriction O H).obj P ⊗ (whiskerPresheafRestriction O H).obj Q :=
  Functor.OplaxMonoidal.δ (whiskerPresheafRestriction O H) P Q

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Naturality of the presheaf-level tensorator in its first slot. -/
public theorem whiskerPresheafDelta_naturality_left
    {P Q : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj} (g : P ⟶ Q)
    (T : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :
    (whiskerPresheafRestriction O H).map (g ▷ T) ≫ whiskerPresheafDelta O hO H Q T =
      whiskerPresheafDelta O hO H P T ≫
        ((whiskerPresheafRestriction O H).map g ▷ (whiskerPresheafRestriction O H).obj T) :=
  (Functor.OplaxMonoidal.δ_natural_left (whiskerPresheafRestriction O H) g T).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Naturality of the presheaf-level tensorator in its second slot. -/
public theorem whiskerPresheafDelta_naturality_right
    (T : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
    {P Q : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj} (g : P ⟶ Q) :
    (whiskerPresheafRestriction O H).map (T ◁ g) ≫ whiskerPresheafDelta O hO H T Q =
      whiskerPresheafDelta O hO H T P ≫
        ((whiskerPresheafRestriction O H).obj T ◁ (whiskerPresheafRestriction O H).map g) :=
  (Functor.OplaxMonoidal.δ_natural_right (whiskerPresheafRestriction O H) T g).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The restriction tensorator is compatible with the associativity constraint at the level of
presheaves.** This is Mathlib's `Functor.OplaxMonoidal.associativity` for
`whiskerPresheafRestriction`, stated at the underlying presheaves of a triple of sheaves of
modules, which is where the transport delivers it. -/
public theorem whiskerPresheafDelta_associativity
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerPresheafDelta O hO H (M.val ⊗ N.val) P.val ≫
        (whiskerPresheafDelta O hO H M.val N.val ▷
          (whiskerPresheafRestriction O H).obj P.val) ≫
        (α_ ((whiskerPresheafRestriction O H).obj M.val)
          ((whiskerPresheafRestriction O H).obj N.val)
          ((whiskerPresheafRestriction O H).obj P.val)).hom =
      (whiskerPresheafRestriction O H).map (α_ M.val N.val P.val).hom ≫
        whiskerPresheafDelta O hO H M.val (N.val ⊗ P.val) ≫
          ((whiskerPresheafRestriction O H).obj M.val ◁
            whiskerPresheafDelta O hO H N.val P.val) :=
  Functor.OplaxMonoidal.associativity (whiskerPresheafRestriction O H) M.val N.val P.val

/-- `Stacks.SheafOfModules.chase_step` in a category of presheaves of modules. -/
private theorem chase_step_presheafOfModules {C₁ : Type*} [Category C₁] {R : C₁ᵒᵖ ⥤ RingCat.{w}}
    {W X Y Z T : PresheafOfModules.{w} R} {u : W ⟶ X} {f : X ⟶ Y} {g : W ⟶ Z} {v : Z ⟶ Y}
    (h : u ≫ f = g ≫ v) {k : Y ⟶ T} {r : Z ⟶ T} (hr : v ≫ k = r) : u ≫ f ≫ k = g ≫ r :=
  Stacks.SheafOfModules.chase_step h hr

/-! ### The transport steps, each at the spelling the next consumes -/

omit [J'.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J' AddCommGrpCat.{w}] in
/-- Two morphisms out of the restriction of a sheafification agreeing on the restricted
sheafification unit are equal. This is
`Stacks.SheafOfModules.TensorPower.whiskerTensorUnit_hom_ext` one layer below: at an arbitrary
presheaf of modules rather than at a tensor product presheaf. -/
public theorem whiskerSheafifyUnit_hom_ext
    (Q : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
    {X : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
        (whiskerStructureIsSheaf (J' := J') O hO H))}
    {a b : (whiskerRestriction (J' := J') O hO H).obj
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj Q) ⟶ X}
    (h : whiskerSheafifyUnit (J' := J') O hO H Q ≫ a.val =
      whiskerSheafifyUnit (J' := J') O hO H Q ≫ b.val) : a = b :=
  @hom_ext_of_locallyBijective _ _ J' _ _ _ _ _
    (isLocallyInjective_whiskerSheafifyUnit (J' := J') O hO H Q)
    (isLocallySurjective_whiskerSheafifyUnit (J' := J') O hO H Q) _ _ h

/-- **The characterizing equation of the restriction tensorator**, with the presheaf-level
tensorator written at `whiskerPresheafDelta` and the small site's sheafification unit written at
the objectwise tensor product of the underlying presheaves of the two restricted sheaves. That
last spelling is the one the whiskering steps below produce, and choosing it here is what keeps
the two chases free of comparisons between the two descriptions of a restricted presheaf. -/
public theorem whiskerSheafifyUnit_comp_whiskerTensorator
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ N.val) ≫
        (whiskerTensorator (J' := J') O hO H M N).hom.val =
      whiskerPresheafDelta O hO H M.val N.val ≫
        sheafificationUnit
          (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
            (whiskerStructureIsSheaf (J' := J') O hO H))
          (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
            ((whiskerRestriction (J' := J') O hO H).obj N).val) :=
  whiskerTensorSheafIso_hom (J' := J') O hO H M N

/-- Left whiskering distributes over the composite of the restricted sheafification unit and the
restriction tensorator. A separate declaration so that the one definitional check it carries is
not repeated inside a longer chain. -/
public theorem whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_head
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          whiskerSheafifyUnit (J' := J') O hO H (N.val ⊗ P.val) ≫
        ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          (whiskerTensorator (J' := J') O hO H N P).hom.val =
      ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
        (whiskerSheafifyUnit (J' := J') O hO H (N.val ⊗ P.val) ≫
          (whiskerTensorator (J' := J') O hO H N P).hom.val) :=
  (MonoidalCategory.whiskerLeft_comp
      (((whiskerRestriction (J' := J') O hO H).obj M).val)
      (whiskerSheafifyUnit (J' := J') O hO H (N.val ⊗ P.val))
      ((whiskerTensorator (J' := J') O hO H N P).hom.val)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    [H.IsCocontinuous J' J] in
/-- Left whiskering distributes over the composite of the presheaf-level tensorator and the
sheafification unit formed on the smaller site, the target shape of
`whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_head`. -/
public theorem whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_tail
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
        (whiskerPresheafDelta O hO H N.val P.val ≫
          sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj P).val)) =
      ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          whiskerPresheafDelta O hO H N.val P.val ≫
        ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj P).val) :=
  MonoidalCategory.whiskerLeft_comp
    (((whiskerRestriction (J' := J') O hO H).obj M).val)
    (whiskerPresheafDelta O hO H N.val P.val)
    (sheafificationUnit
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
        (whiskerStructureIsSheaf (J' := J') O hO H))
      (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
        ((whiskerRestriction (J' := J') O hO H).obj P).val))

/-- The characterizing equation of the restriction tensorator, whiskered on the left and read as
a single factor. Split off from `whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator` so that
the congruence and the two distributions of the whiskering over a composite are elaborated in
separate heartbeat budgets. -/
public theorem whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_congr
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
        (whiskerSheafifyUnit (J' := J') O hO H (N.val ⊗ P.val) ≫
          (whiskerTensorator (J' := J') O hO H N P).hom.val) =
      ((whiskerRestriction (J' := J') O hO H).obj M).val ◁
        (whiskerPresheafDelta O hO H N.val P.val ≫
          sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj P).val)) :=
  congrArg (fun z => ((whiskerRestriction (J' := J') O hO H).obj M).val ◁ z)
    (whiskerSheafifyUnit_comp_whiskerTensorator O hO H N P)

/-- The characterizing equation of the restriction tensorator, whiskered on the left by the
underlying presheaf of a restricted sheaf of modules. -/
public theorem whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          whiskerSheafifyUnit (J' := J') O hO H (N.val ⊗ P.val)) ≫
        (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          (whiskerTensorator (J' := J') O hO H N P).hom.val) =
      (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          whiskerPresheafDelta O hO H N.val P.val) ≫
        (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
          sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj P).val)) :=
  by
  rw [whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_head O hO H M N P,
    whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_congr O hO H M N P,
    whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_tail O hO H M N P]

/-- Right whiskering distributes over the composite of the restricted sheafification unit and the
restriction tensorator, the mirror of
`whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_head`. -/
public theorem whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator_head
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ N.val) ≫
          (whiskerTensorator (J' := J') O hO H M N).hom.val) ▷
        ((whiskerRestriction (J' := J') O hO H).obj P).val =
      whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ N.val) ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val ≫
        (whiskerTensorator (J' := J') O hO H M N).hom.val ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val :=
  MonoidalCategory.comp_whiskerRight
    (whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ N.val))
    ((whiskerTensorator (J' := J') O hO H M N).hom.val)
    (((whiskerRestriction (J' := J') O hO H).obj P).val)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    [H.IsCocontinuous J' J] in
/-- Right whiskering distributes over the composite of the presheaf-level tensorator and the
sheafification unit formed on the smaller site, the mirror of
`whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_tail`. -/
public theorem whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator_tail
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerPresheafDelta O hO H M.val N.val ≫
          sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj N).val)) ▷
        ((whiskerRestriction (J' := J') O hO H).obj P).val =
      whiskerPresheafDelta O hO H M.val N.val ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val ≫
        sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj N).val) ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val :=
  MonoidalCategory.comp_whiskerRight
    (whiskerPresheafDelta O hO H M.val N.val)
    (sheafificationUnit
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
        (whiskerStructureIsSheaf (J' := J') O hO H))
      (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
        ((whiskerRestriction (J' := J') O hO H).obj N).val))
    (((whiskerRestriction (J' := J') O hO H).obj P).val)

/-- The characterizing equation of the restriction tensorator, whiskered on the right and read as
a single factor, the mirror of
`whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator_congr`. -/
public theorem whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator_congr
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ N.val) ≫
          (whiskerTensorator (J' := J') O hO H M N).hom.val) ▷
        ((whiskerRestriction (J' := J') O hO H).obj P).val =
      (whiskerPresheafDelta O hO H M.val N.val ≫
          sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj N).val)) ▷
        ((whiskerRestriction (J' := J') O hO H).obj P).val :=
  congrArg (fun z => z ▷ ((whiskerRestriction (J' := J') O hO H).obj P).val)
    (whiskerSheafifyUnit_comp_whiskerTensorator O hO H M N)

/-- The characterizing equation of the restriction tensorator, whiskered on the right by the
underlying presheaf of a restricted sheaf of modules. -/
public theorem whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ N.val) ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
        ((whiskerTensorator (J' := J') O hO H M N).hom.val ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val) =
      (whiskerPresheafDelta O hO H M.val N.val ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
        (sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H))
            (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
              ((whiskerRestriction (J' := J') O hO H).obj N).val) ▷
          ((whiskerRestriction (J' := J') O hO H).obj P).val) :=
  by
  rw [← whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator_head O hO H M N P,
    whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator_congr O hO H M N P,
    whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator_tail O hO H M N P]

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J' AddCommGrpCat.{w}] in
/-- The restricted sheafification unit of the triple objectwise tensor product, pushed through the
restriction of `tensorSheafAssocLeft`. -/
public theorem whiskerSheafifyUnit_comp_assocLeft
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerSheafifyUnit (J' := J') O hO H ((M.val ⊗ N.val) ⊗ P.val) ≫
        ((whiskerRestriction (J' := J') O hO H).map
          (Stacks.SheafOfModules.tensorSheafAssocLeft O hO M N P).hom).val =
      (whiskerPresheafRestriction O H).map
          (sheafificationUnit
              (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
              (M.val ⊗ N.val) ▷ P.val) ≫
        whiskerSheafifyUnit (J' := J') O hO H ((M ⊗ N).val ⊗ P.val) :=
  whiskerSheafifyUnit_naturality (J' := J') O hO H
    (sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
      (M.val ⊗ N.val) ▷ P.val)

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J' AddCommGrpCat.{w}] in
/-- The restricted sheafification unit of `M.val ⊗ N.val ⊗ P.val`, pushed through the restriction
of `tensorSheafAssocRight`. -/
public theorem whiskerSheafifyUnit_comp_assocRight
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ N.val ⊗ P.val) ≫
        ((whiskerRestriction (J' := J') O hO H).map
          (Stacks.SheafOfModules.tensorSheafAssocRight O hO M N P).hom).val =
      (whiskerPresheafRestriction O H).map
          (M.val ◁ sheafificationUnit
            (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
            (N.val ⊗ P.val)) ≫
        whiskerSheafifyUnit (J' := J') O hO H (M.val ⊗ (N ⊗ P).val) :=
  whiskerSheafifyUnit_naturality (J' := J') O hO H
    (M.val ◁ sheafificationUnit
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) (N.val ⊗ P.val))

/-! ### The two sides of the normalisation -/

/-- **The left-hand side of the associativity normalisation, read on the restricted sheafification
unit of the triple objectwise tensor product**, after the inverted comparison has been cancelled:
the associativity constraint has become the sheafified presheaf associator followed by
`tensorSheafAssocRight`. -/
public theorem whiskerSheafifyUnit_comp_associative_left
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerSheafifyUnit (J' := J') O hO H ((M.val ⊗ N.val) ⊗ P.val) ≫
        ((whiskerRestriction (J' := J') O hO H).map
            ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
              (α_ M.val N.val P.val).hom)).val ≫
          ((whiskerRestriction (J' := J') O hO H).map
              (Stacks.SheafOfModules.tensorSheafAssocRight O hO M N P).hom).val ≫
            (whiskerTensorator (J' := J') O hO H M (N ⊗ P)).hom.val ≫
              ((whiskerRestriction (J' := J') O hO H).obj M ◁
                (whiskerTensorator (J' := J') O hO H N P).hom).val =
      (whiskerPresheafRestriction O H).map (α_ M.val N.val P.val).hom ≫
        whiskerPresheafDelta O hO H M.val (N.val ⊗ P.val) ≫
          (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
            whiskerPresheafDelta O hO H N.val P.val) ≫
            (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
              sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj P).val)) ≫
              sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj N ⊗
                    (whiskerRestriction (J' := J') O hO H).obj P).val) :=
  by
  refine Eq.trans ?_ (congrArg
    (fun z => (whiskerPresheafRestriction O H).map (α_ M.val N.val P.val).hom ≫ z)
    (chase_step_presheafOfModules
      (whiskerPresheafDelta_naturality_right O hO H M.val
        (sheafificationUnit
          (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
          (N.val ⊗ P.val)))
      (chase_step_presheafOfModules
        (Y := ((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
          ((whiskerRestriction (J' := J') O hO H).obj N ⊗
            (whiskerRestriction (J' := J') O hO H).obj P).val)
        (whiskerLeft_whiskerSheafifyUnit_comp_whiskerTensorator O hO H M N P) rfl)))
  refine chase_step_presheafOfModules
    (whiskerSheafifyUnit_naturality (J' := J') O hO H (α_ M.val N.val P.val).hom) ?_
  refine chase_step_presheafOfModules
    (whiskerSheafifyUnit_comp_assocRight O hO H M N P) ?_
  refine chase_step_presheafOfModules
    (Y := ((whiskerRestriction (J' := J') O hO H).obj M ⊗
      (whiskerRestriction (J' := J') O hO H).obj (N ⊗ P)).val)
    (whiskerSheafifyUnit_comp_whiskerTensorator O hO H M (N ⊗ P)) ?_
  exact Stacks.SheafOfModules.sheafificationUnit_comp_whiskerLeft_val (H.op ⋙ O)
    (whiskerStructureIsSheaf (J' := J') O hO H)
    ((whiskerRestriction (J' := J') O hO H).obj M)
    (whiskerTensorator (J' := J') O hO H N P).hom

/-- **The straight part of the right-hand chase**: the restricted sheafification unit of the
triple objectwise tensor product is pushed rightwards across the restriction of
`tensorSheafAssocLeft`, the tensorator at `(M ⊗ N, P)`, and the whiskering by the restriction of
`P`, leaving the associativity constraint at the end.

Split off from `whiskerSheafifyUnit_comp_associative_right` so that neither half has to elaborate
both the chase and the transformation of its result: a single declaration doing both exceeds the
default heartbeat budget, the associativity constraint of a triple of *restricted* sheaves being
the expensive subterm. -/
public theorem whiskerSheafifyUnit_comp_associative_right_chase
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerSheafifyUnit (J' := J') O hO H ((M.val ⊗ N.val) ⊗ P.val) ≫
        ((whiskerRestriction (J' := J') O hO H).map
            (Stacks.SheafOfModules.tensorSheafAssocLeft O hO M N P).hom).val ≫
          (whiskerTensorator (J' := J') O hO H (M ⊗ N) P).hom.val ≫
            ((whiskerTensorator (J' := J') O hO H M N).hom ▷
                (whiskerRestriction (J' := J') O hO H).obj P).val ≫
              (α_ ((whiskerRestriction (J' := J') O hO H).obj M)
                ((whiskerRestriction (J' := J') O hO H).obj N)
                ((whiskerRestriction (J' := J') O hO H).obj P)).hom.val =
      (whiskerPresheafRestriction O H).map
          (sheafificationUnit
              (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
              (M.val ⊗ N.val) ▷ P.val) ≫
        whiskerPresheafDelta O hO H (M ⊗ N).val P.val ≫
          ((whiskerTensorator (J' := J') O hO H M N).hom.val ▷
              ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
            sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj M ⊗
                    (whiskerRestriction (J' := J') O hO H).obj N).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
              (α_ ((whiskerRestriction (J' := J') O hO H).obj M)
                ((whiskerRestriction (J' := J') O hO H).obj N)
                ((whiskerRestriction (J' := J') O hO H).obj P)).hom.val :=
  by
  refine chase_step_presheafOfModules
    (whiskerSheafifyUnit_comp_assocLeft O hO H M N P) ?_
  refine chase_step_presheafOfModules
    (Y := ((whiskerRestriction (J' := J') O hO H).obj (M ⊗ N) ⊗
      (whiskerRestriction (J' := J') O hO H).obj P).val)
    (whiskerSheafifyUnit_comp_whiskerTensorator O hO H (M ⊗ N) P) ?_
  refine chase_step_presheafOfModules
    (Stacks.SheafOfModules.sheafificationUnit_comp_whiskerRight_val (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerTensorator (J' := J') O hO H M N).hom
      ((whiskerRestriction (J' := J') O hO H).obj P)) ?_
  rfl

/-- **The transformation of the right-hand chase's result.** The restricted sheafification units
are traded for the presheaf-level tensorator by its naturality in the first slot and by the
characterizing equation, and the final two factors are the one-site associativity statement
`Stacks.SheafOfModules.sheafificationUnit_whiskerRight_comp_associator` on the smaller site, which
is what brings this side to the same tail as the left-hand one. -/
public theorem whiskerSheafifyUnit_comp_associative_right_transfer
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerPresheafRestriction O H).map
          (sheafificationUnit
              (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
              (M.val ⊗ N.val) ▷ P.val) ≫
        whiskerPresheafDelta O hO H (M ⊗ N).val P.val ≫
          ((whiskerTensorator (J' := J') O hO H M N).hom.val ▷
              ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
            sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj M ⊗
                    (whiskerRestriction (J' := J') O hO H).obj N).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
              (α_ ((whiskerRestriction (J' := J') O hO H).obj M)
                ((whiskerRestriction (J' := J') O hO H).obj N)
                ((whiskerRestriction (J' := J') O hO H).obj P)).hom.val =
      whiskerPresheafDelta O hO H (M.val ⊗ N.val) P.val ≫
        (whiskerPresheafDelta O hO H M.val N.val ▷
            ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
          (α_ ((whiskerRestriction (J' := J') O hO H).obj M).val
              ((whiskerRestriction (J' := J') O hO H).obj N).val
              ((whiskerRestriction (J' := J') O hO H).obj P).val).hom ≫
            (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
              sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj P).val)) ≫
              sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj N ⊗
                    (whiskerRestriction (J' := J') O hO H).obj P).val) :=
  by
  refine chase_step_presheafOfModules
    (whiskerPresheafDelta_naturality_left O hO H
      (sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
        (M.val ⊗ N.val)) P.val) ?_
  refine chase_step_presheafOfModules
    (Y := ((whiskerRestriction (J' := J') O hO H).obj M ⊗
        (whiskerRestriction (J' := J') O hO H).obj N).val ⊗
      ((whiskerRestriction (J' := J') O hO H).obj P).val)
    (whiskerRight_whiskerSheafifyUnit_comp_whiskerTensorator O hO H M N P) ?_
  exact Stacks.SheafOfModules.sheafificationUnit_whiskerRight_comp_associator (H.op ⋙ O)
    (whiskerStructureIsSheaf (J' := J') O hO H)
    ((whiskerRestriction (J' := J') O hO H).obj M)
    ((whiskerRestriction (J' := J') O hO H).obj N)
    ((whiskerRestriction (J' := J') O hO H).obj P)

/-- **The right-hand side of the associativity normalisation, read on the restricted
sheafification unit of the triple objectwise tensor product**: the chase followed by the
transformation of its result. -/
public theorem whiskerSheafifyUnit_comp_associative_right
    (M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerSheafifyUnit (J' := J') O hO H ((M.val ⊗ N.val) ⊗ P.val) ≫
        ((whiskerRestriction (J' := J') O hO H).map
            (Stacks.SheafOfModules.tensorSheafAssocLeft O hO M N P).hom).val ≫
          (whiskerTensorator (J' := J') O hO H (M ⊗ N) P).hom.val ≫
            ((whiskerTensorator (J' := J') O hO H M N).hom ▷
                (whiskerRestriction (J' := J') O hO H).obj P).val ≫
              (α_ ((whiskerRestriction (J' := J') O hO H).obj M)
                ((whiskerRestriction (J' := J') O hO H).obj N)
                ((whiskerRestriction (J' := J') O hO H).obj P)).hom.val =
      whiskerPresheafDelta O hO H (M.val ⊗ N.val) P.val ≫
        (whiskerPresheafDelta O hO H M.val N.val ▷
            ((whiskerRestriction (J' := J') O hO H).obj P).val) ≫
          (α_ ((whiskerRestriction (J' := J') O hO H).obj M).val
              ((whiskerRestriction (J' := J') O hO H).obj N).val
              ((whiskerRestriction (J' := J') O hO H).obj P).val).hom ≫
            (((whiskerRestriction (J' := J') O hO H).obj M).val ◁
              sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj N).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj P).val)) ≫
              sheafificationUnit
                (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
                  (whiskerStructureIsSheaf (J' := J') O hO H))
                (((whiskerRestriction (J' := J') O hO H).obj M).val ⊗
                  ((whiskerRestriction (J' := J') O hO H).obj N ⊗
                    (whiskerRestriction (J' := J') O hO H).obj P).val) :=
  (whiskerSheafifyUnit_comp_associative_right_chase O hO H M N P).trans
    (whiskerSheafifyUnit_comp_associative_right_transfer O hO H M N P)

/-! ### The fourth normalisation -/

/-- **The restriction tensorator is compatible with the associativity constraint of Tag 01CA**:
the fourth and last of the normalisations of `map_coherentMulIso_tensorPowerComparison` that were
missing for restriction along a continuous and cocontinuous functor of sites.

The identity is precomposed with the restriction of `tensorSheafAssocLeft`, which is invertible,
and then tested on the restricted sheafification unit of the triple objectwise tensor product. -/
public theorem isAssociative_whiskerTensorator :
    IsAssociative (K := J') O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerRestriction O hO H) (whiskerTensorator (J' := J') O hO H) := by
  intro M N P
  refine (cancel_epi (((whiskerRestriction (J' := J') O hO H).mapIso
    (Stacks.SheafOfModules.tensorSheafAssocLeft O hO M N P)).hom)).mp ?_
  have hmerge : ((whiskerRestriction (J' := J') O hO H).mapIso
          (Stacks.SheafOfModules.tensorSheafAssocLeft O hO M N P)).hom ≫
        ((whiskerRestriction (J' := J') O hO H).map (α_ M N P).hom ≫
          (whiskerTensorator (J' := J') O hO H M (N ⊗ P)).hom ≫
            ((whiskerRestriction (J' := J') O hO H).obj M ◁
              (whiskerTensorator (J' := J') O hO H N P).hom)) =
      (whiskerRestriction (J' := J') O hO H).map
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
            (α_ M.val N.val P.val).hom) ≫
        ((whiskerRestriction (J' := J') O hO H).map
            (Stacks.SheafOfModules.tensorSheafAssocRight O hO M N P).hom ≫
          (whiskerTensorator (J' := J') O hO H M (N ⊗ P)).hom ≫
            ((whiskerRestriction (J' := J') O hO H).obj M ◁
              (whiskerTensorator (J' := J') O hO H N P).hom)) :=
    Stacks.SheafOfModules.chase_step
      (((whiskerRestriction (J' := J') O hO H).map_comp
            (Stacks.SheafOfModules.tensorSheafAssocLeft O hO M N P).hom
            (α_ M N P).hom).symm.trans
        ((congrArg (whiskerRestriction (J' := J') O hO H).map
            (Stacks.SheafOfModules.tensorSheafAssocLeft_hom_comp_associator O hO M N P)).trans
          ((whiskerRestriction (J' := J') O hO H).map_comp
            ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
              (α_ M.val N.val P.val).hom)
            (Stacks.SheafOfModules.tensorSheafAssocRight O hO M N P).hom)))
      rfl
  refine whiskerSheafifyUnit_hom_ext O hO H ((M.val ⊗ N.val) ⊗ P.val) ?_
  refine ((congrArg (fun z => whiskerSheafifyUnit (J' := J') O hO H ((M.val ⊗ N.val) ⊗ P.val) ≫
          _root_.SheafOfModules.Hom.val z) hmerge).trans
      ((congrArg (fun z => whiskerSheafifyUnit (J' := J') O hO H ((M.val ⊗ N.val) ⊗ P.val) ≫ z)
          (Stacks.SheafOfModules.comp_val₄ _ _ _ _)).trans
        (whiskerSheafifyUnit_comp_associative_left O hO H M N P))).trans ?_
  refine Eq.trans ?_ (((congrArg
      (fun z => whiskerSheafifyUnit (J' := J') O hO H ((M.val ⊗ N.val) ⊗ P.val) ≫ z)
      (Stacks.SheafOfModules.comp_val₄ _ _ _ _)).trans
    (whiskerSheafifyUnit_comp_associative_right O hO H M N P)).symm)
  exact Stacks.SheafOfModules.comp₃_tail
    (whiskerPresheafDelta_associativity O hO H M N P).symm _
/-! ### The payoff: multiplicativity of the comparison of tensor powers -/

/-- **The comparison `R(L^{⊗ n}) ≅ (R L)^{⊗ n}` of tensor powers along a restriction of sites is
multiplicative**: it carries the coherent multiplication of Tag 01CU for `L` to the one for the
restriction of `L`, in every pair of integer degrees.

All six normalisations of `map_coherentMulIso_tensorPowerComparison` are now available for
`whiskerTensorator`, and by `tensorPowerComparison_whiskerTensorator` the comparison they are
about is `whiskerTensorPowerIso`. In the slice case this is multiplicativity of
`Stacks.SheafOfModules.TensorPower.overTensorPowerIso`. -/
public theorem map_coherentMulIso_whiskerTensorPowerIso
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]
    [IsInvertible (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      ((whiskerRestriction O hO H).obj L)] (n m : ℤ) :
    (whiskerRestriction (J' := J') O hO H).map (coherentMulIso O hO L n m).hom ≫
        (whiskerTensorPowerIso (J' := J') O hO H L (n + m)).hom =
      (whiskerTensorator (J' := J') O hO H (tensorPower O hO L n)
            (tensorPower O hO L m)).hom ≫
        (tensorSheafMapIso (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
            (whiskerTensorPowerIso (J' := J') O hO H L n)
            (whiskerTensorPowerIso (J' := J') O hO H L m)).hom ≫
          (coherentMulIso (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
            ((whiskerRestriction O hO H).obj L) n m).hom := by
  rw [← tensorPowerComparison_whiskerTensorator (J' := J') O hO H L (n + m),
    ← tensorPowerComparison_whiskerTensorator (J' := J') O hO H L n,
    ← tensorPowerComparison_whiskerTensorator (J' := J') O hO H L m]
  exact map_coherentMulIso_tensorPowerComparison O hO (H.op ⋙ O)
    (whiskerStructureIsSheaf (J' := J') O hO H) (whiskerRestriction O hO H) L
    (whiskerTensorator (J' := J') O hO H) (whiskerUnitIso (J' := J') O hO H)
    (isLeftUnital_whiskerTensorator (J' := J') O hO H)
    (isRightUnital_whiskerTensorator (J' := J') O hO H)
    (isNaturalLeft_whiskerTensorator (J' := J') O hO H)
    (isNaturalRight_whiskerTensorator (J' := J') O hO H)
    (isAssociative_whiskerTensorator (J' := J') O hO H)
    (isSymmetric_whiskerTensorator (J' := J') O hO H) n m

end Whisker

/-! ### The slice case -/

section Slice

variable (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- **The comparison `(L^{⊗ n})|_U ≅ (L|_U)^{⊗ n}` for restriction to a slice is multiplicative**:
it carries the coherent multiplication of Tag 01CU for `L` to the one for `L|_U`, in every pair of
integer degrees.

`Stacks.SheafOfModules.TensorPower.overTensorPowerIso` is `whiskerTensorPowerIso` along
`CategoryTheory.Over.forget U`, and `sliceStructureIsSheaf` is `whiskerStructureIsSheaf` along the
same functor, so this is `map_coherentMulIso_whiskerTensorPowerIso` read at that functor.

This is the first of the three factors of
`Stacks.SheafOfModules.TensorPower.overTensorPowerUnitIso`, whose multiplicativity is what
`Stacks.AlgebraicGeometry.GradedAlgebraTwist.twistPieceSectionsEquiv` needs in order to assemble
into an isomorphism of graded section rings. The other two, `tensorPowerCongr` along a
trivialization and `unitTensorPowerIso`, are still not known to be multiplicative. -/
public theorem map_coherentMulIso_overTensorPowerIso
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]
    [IsInvertible ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
      ((whiskerRestriction O hO (Over.forget U)).obj L)] (n m : ℤ) :
    (whiskerRestriction O hO (Over.forget U)).map (coherentMulIso O hO L n m).hom ≫
        (overTensorPowerIso O hO U L (n + m)).hom =
      (whiskerTensorator O hO (Over.forget U) (tensorPower O hO L n)
            (tensorPower O hO L m)).hom ≫
        (tensorSheafMapIso ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
            (overTensorPowerIso O hO U L n) (overTensorPowerIso O hO U L m)).hom ≫
          (coherentMulIso ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
            ((whiskerRestriction O hO (Over.forget U)).obj L) n m).hom :=
  map_coherentMulIso_whiskerTensorPowerIso O hO (Over.forget U) L n m

end Slice

end Stacks.SheafOfModules.TensorPower

end
