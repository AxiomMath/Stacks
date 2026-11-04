module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceOverAlgebraicSpaceRepresentability
public import StacksFrontier.CategoryTheory.Monoidal.GroupObjectFromHoms

/-!
# The relative isomorphisms of two algebraic-space-valued points, as a group and a pseudo-torsor

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `Z` be an algebraic space
over `S` and let `x₁, x₂ : Z ⟶ 𝒳` be two algebraic-space-valued points of `𝒳`. The isomorphism
sheaves attached to these data satisfy:

1. the relative automorphism sheaf `Isom_{𝒳/𝒴}(x₂, x₂)` is a group algebraic space over `Z`;
2. the sequence `0 ⟶ Isom_{𝒳/𝒴}(x₂, x₂) ⟶ Isom_𝒳(x₂, x₂) ⟶ Isom_𝒴(f x₂, f x₂)` of groups
   over `Z` is exact;
3. there is a map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(f x₁, f x₂)` of algebraic spaces over `Z` making,
   for every 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f`, the square cutting out
   `Isom^α_{𝒳/𝒴}(x₁, x₂)` cartesian;
4. for every such `α` the algebraic space `Isom^α_{𝒳/𝒴}(x₁, x₂)` is a pseudo-torsor under
   `Isom_{𝒳/𝒴}(x₂, x₂)` over `Z`.

The map and the cartesian square of (3) are `AlgebraicGeometry.Stack.isomSpaceOverSpaceMap` and
`AlgebraicGeometry.Stack.isPullback_relativeIsomSpaceOverSpace`.

## Main definitions

* `AlgebraicGeometry.Stack.isomSpaceSlice` and
  `AlgebraicGeometry.Stack.relativeIsomSpaceSlice`: the sheaves `Isom_𝒳(x₁, x₂)` and
  `Isom^α_{𝒳/𝒴}(x₁, x₂)` as objects of `Over Z`.
* `AlgebraicGeometry.Stack.relativeAutSpaceSlice`: the relative automorphism sheaf
  `Isom_{𝒳/𝒴}(x, x)`, i.e. the case of the identity 2-morphism.
* `AlgebraicGeometry.Stack.isomSpaceSlicePoint` and
  `AlgebraicGeometry.Stack.relativeIsomSpaceSlicePoint`: the isomorphism a point of one of those
  objects names, read over the point of `Z` the test object prescribes.
* `AlgebraicGeometry.Stack.isomSpaceSliceGrpObj` and
  `AlgebraicGeometry.Stack.relativeAutSpaceSliceGrpObj`: the group structures over `Z`.
* `AlgebraicGeometry.Stack.relativeIsomSpaceSliceModObj`: the action of
  `Isom_{𝒳/𝒴}(x₂, x₂)` on `Isom^α_{𝒳/𝒴}(x₁, x₂)` by composition.

## Main results

* `AlgebraicGeometry.Stack.relativeAutGroupAlgebraicSpace`: `Isom_{𝒳/𝒴}(x, x)` is a group
  algebraic space over `Z`.
* `AlgebraicGeometry.Stack.isMonHom_relativeAutSpaceSliceι`,
  `AlgebraicGeometry.Stack.isMonHom_isomSpaceSliceMap`,
  `AlgebraicGeometry.Stack.relativeAutSpaceSliceι_injective` and
  `AlgebraicGeometry.Stack.relativeAutSpaceSlice_exact`: the sequence
  `0 ⟶ Isom_{𝒳/𝒴}(x, x) ⟶ Isom_𝒳(x, x) ⟶ Isom_𝒴(f x, f x)` of groups over `Z` is exact.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_isPullback_relativeIsomSpaceOverSpace`: the square
  cutting out `Isom^α_{𝒳/𝒴}(x₁, x₂)` is a cartesian square of algebraic spaces over `Z`.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_isPseudoTorsor_relativeIsomSpaceSlice`:
  `Isom^α_{𝒳/𝒴}(x₁, x₂)` is an algebraic space and a pseudo-torsor under `Isom_{𝒳/𝒴}(x₂, x₂)`
  over `Z`.
* `AlgebraicGeometry.Stack.relativeIsomSpaceSlice_properties`: the four assertions together.

## Implementation notes

Every sheaf is read as an object of the slice `Over Z`, which is cartesian monoidal
(`AlgebraicGeometry.Space.overCartesianMonoidalCategory`), so that "group over `Z`" and
"pseudo-torsor over `Z`" are `CategoryTheory.GrpObj` and `AlgebraicGeometry.IsPseudoTorsor`
there. The structure is built from the operations on points, the morphisms of the slice out of a
test object, through `CategoryTheory.grpObjOfHoms` and `CategoryTheory.modObjOfHoms`; the
isomorphism a point names is read over the point of `Z` the test object prescribes, through
`AlgebraicGeometry.Stack.pointHomCongr`.

## References

* [Stacks Project, Tag 0CPK](https://stacks.math.columbia.edu/tag/0CPK)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 0CPJ](https://stacks.math.columbia.edu/tag/0CPJ)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj ModObj

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-! ### The isomorphism sheaves as objects over `Z` -/

/-- `Isom_𝒳(x₁, x₂)` as an object over `Z`, through its structure morphism
`AlgebraicGeometry.Stack.isomSpaceOverSpaceProj`. -/
noncomputable def isomSpaceSlice (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    Over Z :=
  Over.mk (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂)

/-- `Isom^α_{𝒳/𝒴}(x₁, x₂)` as an object over `Z`. -/
noncomputable def relativeIsomSpaceSlice (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) : Over Z :=
  Over.mk (relativeIsomSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α)

/-- The relative automorphism sheaf `Isom_{𝒳/𝒴}(x, x)` as an object over `Z`: the automorphisms
of `x` whose image under `f` is the identity, that is,
`AlgebraicGeometry.Stack.relativeIsomSpaceSlice` at the identity 2-morphism of `x ≫ f`. -/
noncomputable abbrev relativeAutSpaceSlice (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) : Over Z :=
  relativeIsomSpaceSlice B S hS Z hZ f x x (𝟙 (x ≫ f))

/-- A morphism of test objects over `Z` commutes with the structure maps on points. -/
private lemma over_hom_app_comp {R Q : Over Z} (r : R ⟶ Q) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : R.left.obj W) : Q.hom.app W (r.left.app W t) = R.hom.app W t :=
  congrArg (fun (k : R.left ⟶ Z) => k.app W t) (Over.w r)

/-- A point of `Isom_𝒳(x₁, x₂)` over a test object of `Over Z` lies over the point of `Z` the
test object prescribes. -/
lemma isomSpaceSlice_hom_fst (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) {Q : Over Z}
    (q : Q ⟶ isomSpaceSlice B S hS Z hZ x₁ x₂) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) : (q.left.app W t).1 = Q.hom.app W t :=
  over_hom_app_comp B S hS Z q W t

/-- The same for `Isom^α_{𝒳/𝒴}(x₁, x₂)`. -/
lemma relativeIsomSpaceSlice_hom_fst (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) {Q : Over Z}
    (q : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) : (q.left.app W t).1 = Q.hom.app W t :=
  over_hom_app_comp B S hS Z q W t

/-- The isomorphism a point of `Isom_𝒳(x₁, x₂)` names, read over the point of `Z` the test object
prescribes. -/
noncomputable def isomSpaceSlicePoint (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {Q : Over Z} (q : Q ⟶ isomSpaceSlice B S hS Z hZ x₁ x₂) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    pointFiber B S hS Z hZ x₁ W.unop (Q.hom.app W t) ⟶
      pointFiber B S hS Z hZ x₂ W.unop (Q.hom.app W t) :=
  pointHomCongr B S hS Z hZ x₁ x₂ (isomSpaceSlice_hom_fst B S hS Z hZ x₁ x₂ q W t)
    (q.left.app W t).2.1

/-- The isomorphism a point of `Isom^α_{𝒳/𝒴}(x₁, x₂)` names, read over the point of `Z` the test
object prescribes. -/
noncomputable def relativeIsomSpaceSlicePoint (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) {Q : Over Z}
    (q : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    pointFiber B S hS Z hZ x₁ W.unop (Q.hom.app W t) ⟶
      pointFiber B S hS Z hZ x₂ W.unop (Q.hom.app W t) :=
  pointHomCongr B S hS Z hZ x₁ x₂
    (relativeIsomSpaceSlice_hom_fst B S hS Z hZ f x₁ x₂ α q W t) (q.left.app W t).2.1

/-- A point of `Isom_𝒳(x₁, x₂)` is an isomorphism of the fibre. -/
instance isIso_isomSpaceSlicePoint (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {Q : Over Z} (q : Q ⟶ isomSpaceSlice B S hS Z hZ x₁ x₂) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) : IsIso (isomSpaceSlicePoint B S hS Z hZ x₁ x₂ q W t) :=
  isIso_fiberHom B S hS 𝒳 _

/-- A point of `Isom^α_{𝒳/𝒴}(x₁, x₂)` is an isomorphism of the fibre. -/
instance isIso_relativeIsomSpaceSlicePoint (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) {Q : Over Z}
    (q : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    IsIso (relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W t) :=
  isIso_fiberHom B S hS 𝒳 _

/-- A point of `Isom^α_{𝒳/𝒴}(x₁, x₂)` lifts `α`: its image under `f` is the component of `α` at
the point of `Z` the test object prescribes. -/
theorem pointFiberMap_relativeIsomSpaceSlicePoint (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) {Q : Over Z}
    (q : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    pointFiberMap B S hS Z hZ f x₁ x₂ W.unop (Q.hom.app W t)
        (relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W t) =
      twistedComponent B S hS Z hZ f x₁ x₂ α W.unop (Q.hom.app W t) := by
  rw [relativeIsomSpaceSlicePoint, pointFiberMap_pointHomCongr, (q.left.app W t).2.2.2,
    pointHomCongr_twistedComponent]

/-- Restriction carries the isomorphism a point of `Isom_𝒳(x₁, x₂)` names at one object of the
site to the one it names at another. -/
lemma pointRestrict_isomSpaceSlicePoint (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {Q : Over Z} (q : Q ⟶ isomSpaceSlice B S hS Z hZ x₁ x₂)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (t : Q.left.obj W₁)
    (hz : Q.hom.app W₂ (Q.left.map g t) = Z.map g (Q.hom.app W₁ t)) :
    pointRestrict B S hS Z hZ x₁ x₂ g (Q.hom.app W₁ t) (Q.hom.app W₂ (Q.left.map g t)) hz
        (isomSpaceSlicePoint B S hS Z hZ x₁ x₂ q W₁ t) =
      isomSpaceSlicePoint B S hS Z hZ x₁ x₂ q W₂ (Q.left.map g t) :=
  pointRestrict_pointHomCongr_section B S hS Z hZ x₁ x₂ g (q.left.app W₁ t)
    (q.left.app W₂ (Q.left.map g t)) (NatTrans.naturality_apply q.left g t) _ _ _ _ hz

/-- The same for `Isom^α_{𝒳/𝒴}(x₁, x₂)`. -/
lemma pointRestrict_relativeIsomSpaceSlicePoint (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) {Q : Over Z}
    (q : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (t : Q.left.obj W₁)
    (hz : Q.hom.app W₂ (Q.left.map g t) = Z.map g (Q.hom.app W₁ t)) :
    pointRestrict B S hS Z hZ x₁ x₂ g (Q.hom.app W₁ t) (Q.hom.app W₂ (Q.left.map g t)) hz
        (relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W₁ t) =
      relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W₂ (Q.left.map g t) :=
  pointRestrict_pointHomCongr_relativeIsomSection B S hS Z hZ f x₁ x₂ α g (q.left.app W₁ t)
    (q.left.app W₂ (Q.left.map g t)) (NatTrans.naturality_apply q.left g t) _ _ _ _ hz

/-- A point of `Isom_𝒳(x₁, x₂)` is determined by the isomorphisms it names. -/
lemma isomSpaceSliceHom_ext (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) {Q : Over Z}
    (q q' : Q ⟶ isomSpaceSlice B S hS Z hZ x₁ x₂)
    (h : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      isomSpaceSlicePoint B S hS Z hZ x₁ x₂ q W t =
        isomSpaceSlicePoint B S hS Z hZ x₁ x₂ q' W t) : q = q' := by
  apply Over.OverMorphism.ext
  refine Functor.presheafHom_ext fun W t => ?_
  exact isomSection_eq_of_pointHomCongr B S hS Z hZ x₁ x₂ _ _ (Q.hom.app W t)
    (isomSpaceSlice_hom_fst B S hS Z hZ x₁ x₂ q W t)
    (isomSpaceSlice_hom_fst B S hS Z hZ x₁ x₂ q' W t) (h W t)

/-- A point of `Isom^α_{𝒳/𝒴}(x₁, x₂)` is determined by the isomorphisms it names. -/
lemma relativeIsomSpaceSliceHom_ext (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) {Q : Over Z}
    (q q' : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α)
    (h : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W t =
        relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q' W t) : q = q' := by
  apply Over.OverMorphism.ext
  refine Functor.presheafHom_ext fun W t => ?_
  exact relativeIsomSection_eq_of_pointHomCongr B S hS Z hZ f x₁ x₂ α _ _ (Q.hom.app W t)
    (relativeIsomSpaceSlice_hom_fst B S hS Z hZ f x₁ x₂ α q W t)
    (relativeIsomSpaceSlice_hom_fst B S hS Z hZ f x₁ x₂ α q' W t) (h W t)

/-! ### Building a point out of a family of isomorphisms -/

/-- The point of `Isom_𝒳(x₁, x₂)` given by a family of isomorphisms of the fibres, one over each
point of `Z` the test object prescribes, compatible with restriction. -/
noncomputable def isomSpaceSliceHomMk (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (Q : Over Z)
    (φ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      pointFiber B S hS Z hZ x₁ W.unop (Q.hom.app W t) ⟶
        pointFiber B S hS Z hZ x₂ W.unop (Q.hom.app W t))
    (hφ : ∀ {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (t : Q.left.obj W₁)
      (hz : Q.hom.app W₂ (Q.left.map g t) = Z.map g (Q.hom.app W₁ t)),
      pointRestrict B S hS Z hZ x₁ x₂ g (Q.hom.app W₁ t) (Q.hom.app W₂ (Q.left.map g t)) hz
          (φ W₁ t) =
        φ W₂ (Q.left.map g t)) :
    Q ⟶ isomSpaceSlice B S hS Z hZ x₁ x₂ :=
  Over.homMk
    { app := fun W => ↾fun t => ⟨Q.hom.app W t, ⟨φ W t, isIso_fiberHom B S hS 𝒳 _⟩⟩
      naturality := fun {W₁ W₂} g => by
        refine ConcreteCategory.hom_ext _ _ fun t => ?_
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        refine ((isomSectionRestrict_self B S hS Z hZ x₁ x₂ g
          ⟨Q.hom.app W₁ t, ⟨φ W₁ t, isIso_fiberHom B S hS 𝒳 _⟩⟩
          (Q.hom.app W₂ (Q.left.map g t))
          (NatTrans.naturality_apply Q.hom g t)).symm.trans ?_).symm
        exact (isomSection_mk_eq_iff B S hS Z hZ x₁ x₂ _ _ _).2
          (hφ g t (NatTrans.naturality_apply Q.hom g t)) }
    (Functor.presheafHom_ext fun _ _ => rfl)

/-- The point of `Isom_𝒳(x₁, x₂)` built from a family of isomorphisms of the fibres names those
isomorphisms. -/
@[simp] lemma isomSpaceSlicePoint_homMk (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (Q : Over Z)
    (φ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      pointFiber B S hS Z hZ x₁ W.unop (Q.hom.app W t) ⟶
        pointFiber B S hS Z hZ x₂ W.unop (Q.hom.app W t))
    (hφ : ∀ {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (t : Q.left.obj W₁)
      (hz : Q.hom.app W₂ (Q.left.map g t) = Z.map g (Q.hom.app W₁ t)),
      pointRestrict B S hS Z hZ x₁ x₂ g (Q.hom.app W₁ t) (Q.hom.app W₂ (Q.left.map g t)) hz
          (φ W₁ t) =
        φ W₂ (Q.left.map g t))
    (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W) :
    isomSpaceSlicePoint B S hS Z hZ x₁ x₂
      (isomSpaceSliceHomMk B S hS Z hZ x₁ x₂ Q φ hφ) W t = φ W t :=
  pointHomCongr_eq B S hS Z hZ x₁ x₂ _ _

/-- The point of `Isom^α_{𝒳/𝒴}(x₁, x₂)` given by a family of isomorphisms of the fibres lifting
the components of `α`, compatible with restriction. -/
noncomputable def relativeIsomSpaceSliceHomMk (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) (Q : Over Z)
    (φ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      pointFiber B S hS Z hZ x₁ W.unop (Q.hom.app W t) ⟶
        pointFiber B S hS Z hZ x₂ W.unop (Q.hom.app W t))
    (hspec : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      pointFiberMap B S hS Z hZ f x₁ x₂ W.unop (Q.hom.app W t) (φ W t) =
        twistedComponent B S hS Z hZ f x₁ x₂ α W.unop (Q.hom.app W t))
    (hφ : ∀ {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (t : Q.left.obj W₁)
      (hz : Q.hom.app W₂ (Q.left.map g t) = Z.map g (Q.hom.app W₁ t)),
      pointRestrict B S hS Z hZ x₁ x₂ g (Q.hom.app W₁ t) (Q.hom.app W₂ (Q.left.map g t)) hz
          (φ W₁ t) =
        φ W₂ (Q.left.map g t)) :
    Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α :=
  Over.homMk
    { app := fun W => ↾fun t =>
        ⟨Q.hom.app W t, ⟨φ W t, isIso_fiberHom B S hS 𝒳 _, hspec W t⟩⟩
      naturality := fun {W₁ W₂} g => by
        refine ConcreteCategory.hom_ext _ _ fun t => ?_
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        refine ((relativeIsomSectionRestrict_self B S hS Z hZ f x₁ x₂ α g
          ⟨Q.hom.app W₁ t, ⟨φ W₁ t, isIso_fiberHom B S hS 𝒳 _, hspec W₁ t⟩⟩
          (Q.hom.app W₂ (Q.left.map g t))
          (NatTrans.naturality_apply Q.hom g t)).symm.trans ?_).symm
        exact (relativeIsomSection_mk_eq_iff B S hS Z hZ f x₁ x₂ α _ _ _).2
          (hφ g t (NatTrans.naturality_apply Q.hom g t)) }
    (Functor.presheafHom_ext fun _ _ => rfl)

/-- The point of `Isom^α_{𝒳/𝒴}(x₁, x₂)` built from a family of isomorphisms of the fibres names
those isomorphisms. -/
@[simp] lemma relativeIsomSpaceSlicePoint_homMk (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) (Q : Over Z)
    (φ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      pointFiber B S hS Z hZ x₁ W.unop (Q.hom.app W t) ⟶
        pointFiber B S hS Z hZ x₂ W.unop (Q.hom.app W t))
    (hspec : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
      pointFiberMap B S hS Z hZ f x₁ x₂ W.unop (Q.hom.app W t) (φ W t) =
        twistedComponent B S hS Z hZ f x₁ x₂ α W.unop (Q.hom.app W t))
    (hφ : ∀ {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (t : Q.left.obj W₁)
      (hz : Q.hom.app W₂ (Q.left.map g t) = Z.map g (Q.hom.app W₁ t)),
      pointRestrict B S hS Z hZ x₁ x₂ g (Q.hom.app W₁ t) (Q.hom.app W₂ (Q.left.map g t)) hz
          (φ W₁ t) =
        φ W₂ (Q.left.map g t))
    (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W) :
    relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α
      (relativeIsomSpaceSliceHomMk B S hS Z hZ f x₁ x₂ α Q φ hspec hφ) W t = φ W t :=
  pointHomCongr_eq B S hS Z hZ x₁ x₂ _ _

/-- Precomposing a point of `Isom_𝒳(x₁, x₂)` with a morphism of test objects reads the same
isomorphisms, over the points the new test object prescribes. -/
lemma isomSpaceSlicePoint_comp (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {R Q : Over Z} (r : R ⟶ Q) (q : Q ⟶ isomSpaceSlice B S hS Z hZ x₁ x₂)
    (W : (BigFppfOver B S hS)ᵒᵖ) (t : R.left.obj W)
    (hr : Q.hom.app W (r.left.app W t) = R.hom.app W t) :
    isomSpaceSlicePoint B S hS Z hZ x₁ x₂ (r ≫ q) W t =
      pointHomCongr B S hS Z hZ x₁ x₂ hr
        (isomSpaceSlicePoint B S hS Z hZ x₁ x₂ q W (r.left.app W t)) := by
  unfold isomSpaceSlicePoint
  rw [pointHomCongr_trans]
  exact pointHomCongr_congr B S hS Z hZ x₁ x₂ _ _ _

/-- The same for `Isom^α_{𝒳/𝒴}(x₁, x₂)`. -/
lemma relativeIsomSpaceSlicePoint_comp (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    {R Q : Over Z} (r : R ⟶ Q) (q : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α)
    (W : (BigFppfOver B S hS)ᵒᵖ) (t : R.left.obj W)
    (hr : Q.hom.app W (r.left.app W t) = R.hom.app W t) :
    relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α (r ≫ q) W t =
      pointHomCongr B S hS Z hZ x₁ x₂ hr
        (relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W (r.left.app W t)) := by
  unfold relativeIsomSpaceSlicePoint
  rw [pointHomCongr_trans]
  exact pointHomCongr_congr B S hS Z hZ x₁ x₂ _ _ _

/-! ### The group structure on the relative automorphism sheaf -/

section Group

variable (f : 𝒳 ⟶ 𝒴) (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)

/-- The neutral point of `Isom_{𝒳/𝒴}(x, x)` over a test object: the identity automorphism over
every point of `Z`. -/
noncomputable def relativeAutOne (Q : Over Z) : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x :=
  relativeIsomSpaceSliceHomMk B S hS Z hZ f x x (𝟙 (x ≫ f)) Q (fun _ _ => 𝟙 _)
    (fun W t => by rw [pointFiberMap_id_hom, twistedComponent_id])
    (fun g t hz => pointRestrict_id_hom B S hS Z hZ x g _ _ hz)

/-- The neutral point of `Isom_{𝒳/𝒴}(x, x)` names the identity automorphism. -/
@[simp] lemma relativeAutOne_point (Q : Over Z) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f))
      (relativeAutOne B S hS Z hZ f x Q) W t = 𝟙 _ :=
  pointHomCongr_eq B S hS Z hZ x x _ _

/-- The product of two points of `Isom_{𝒳/𝒴}(x, x)`: composition of automorphisms, in the order
of `AlgebraicGeometry.Stack.isomSpaceComp`. -/
noncomputable def relativeAutMul (Q : Over Z)
    (g h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x :=
  relativeIsomSpaceSliceHomMk B S hS Z hZ f x x (𝟙 (x ≫ f)) Q
    (fun W t => relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) h W t ≫
      relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) g W t)
    (fun W t => by
      rw [pointFiberMap_comp_hom, pointFiberMap_relativeIsomSpaceSlicePoint,
        pointFiberMap_relativeIsomSpaceSlicePoint, twistedComponent_id, Category.comp_id])
    (fun gm t hz => by
      rw [pointRestrict_comp_hom, pointRestrict_relativeIsomSpaceSlicePoint,
        pointRestrict_relativeIsomSpaceSlicePoint])

/-- The product `g * h` of points of `Isom_{𝒳/𝒴}(x, x)` names the composite of the automorphism
`h` names with the one `g` names. -/
@[simp] lemma relativeAutMul_point (Q : Over Z)
    (g h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f))
        (relativeAutMul B S hS Z hZ f x Q g h) W t =
      relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) h W t ≫
        relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) g W t :=
  pointHomCongr_eq B S hS Z hZ x x _ _

/-- The inverse of a point of `Isom_{𝒳/𝒴}(x, x)`: the inverse automorphism over every point of
`Z`, which again has identity image under `f`. -/
noncomputable def relativeAutInv (Q : Over Z)
    (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x :=
  relativeIsomSpaceSliceHomMk B S hS Z hZ f x x (𝟙 (x ≫ f)) Q
    (fun W t => CategoryTheory.inv
      (relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) g W t))
    (fun W t => by
      rw [twistedComponent_id]
      have h : pointFiberMap B S hS Z hZ f x x W.unop (Q.hom.app W t)
            (relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) g W t) ≫
          pointFiberMap B S hS Z hZ f x x W.unop (Q.hom.app W t)
            (CategoryTheory.inv
              (relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) g W t)) = 𝟙 _ := by
        rw [← pointFiberMap_comp_hom, IsIso.hom_inv_id, pointFiberMap_id_hom]
      rw [pointFiberMap_relativeIsomSpaceSlicePoint, twistedComponent_id,
        Category.id_comp] at h
      exact h)
    (fun gm t hz => by
      refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
      rw [← pointRestrict_relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) g gm t hz,
        ← pointRestrict_comp_hom, IsIso.hom_inv_id, pointRestrict_id_hom])

/-- The inverse of a point of `Isom_{𝒳/𝒴}(x, x)` names the inverse automorphism. -/
@[simp] lemma relativeAutInv_point (Q : Over Z)
    (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f))
        (relativeAutInv B S hS Z hZ f x Q g) W t =
      CategoryTheory.inv
        (relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) g W t) :=
  pointHomCongr_eq B S hS Z hZ x x _ _

/-- The neutral point of `Isom_{𝒳/𝒴}(x, x)` is stable under precomposition by a morphism of test
objects. -/
lemma relativeAutOne_comp {R Q : Over Z} (r : R ⟶ Q) :
    r ≫ relativeAutOne B S hS Z hZ f x Q = relativeAutOne B S hS Z hZ f x R := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  have hr := over_hom_app_comp B S hS Z r W t
  rw [relativeIsomSpaceSlicePoint_comp B S hS Z hZ f x x (𝟙 (x ≫ f)) r
      (relativeAutOne B S hS Z hZ f x Q) W t hr,
    relativeAutOne_point, relativeAutOne_point, pointHomCongr_id]

/-- The product of points of `Isom_{𝒳/𝒴}(x, x)` commutes with precomposition by a morphism of
test objects. -/
lemma relativeAutMul_comp {R Q : Over Z} (r : R ⟶ Q)
    (g h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    r ≫ relativeAutMul B S hS Z hZ f x Q g h =
      relativeAutMul B S hS Z hZ f x R (r ≫ g) (r ≫ h) := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  have hr := over_hom_app_comp B S hS Z r W t
  rw [relativeIsomSpaceSlicePoint_comp B S hS Z hZ f x x (𝟙 (x ≫ f)) r
      (relativeAutMul B S hS Z hZ f x Q g h) W t hr,
    relativeAutMul_point, pointHomCongr_comp, relativeAutMul_point,
    relativeIsomSpaceSlicePoint_comp B S hS Z hZ f x x (𝟙 (x ≫ f)) r g W t hr,
    relativeIsomSpaceSlicePoint_comp B S hS Z hZ f x x (𝟙 (x ≫ f)) r h W t hr]

/-- The neutral point of `Isom_{𝒳/𝒴}(x, x)` is a left unit for the product. -/
lemma relativeAut_one_mul (Q : Over Z) (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    relativeAutMul B S hS Z hZ f x Q (relativeAutOne B S hS Z hZ f x Q) g = g := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  rw [relativeAutMul_point, relativeAutOne_point, Category.comp_id]

/-- The neutral point of `Isom_{𝒳/𝒴}(x, x)` is a right unit for the product. -/
lemma relativeAut_mul_one (Q : Over Z) (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    relativeAutMul B S hS Z hZ f x Q g (relativeAutOne B S hS Z hZ f x Q) = g := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  rw [relativeAutMul_point, relativeAutOne_point, Category.id_comp]

/-- The product of points of `Isom_{𝒳/𝒴}(x, x)` is associative. -/
lemma relativeAut_mul_assoc (Q : Over Z)
    (g h k : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    relativeAutMul B S hS Z hZ f x Q (relativeAutMul B S hS Z hZ f x Q g h) k =
      relativeAutMul B S hS Z hZ f x Q g (relativeAutMul B S hS Z hZ f x Q h k) := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  rw [relativeAutMul_point, relativeAutMul_point, relativeAutMul_point, relativeAutMul_point,
    Category.assoc]

/-- The inverse of a point of `Isom_{𝒳/𝒴}(x, x)` times the point is the neutral point. -/
lemma relativeAut_inv_mul (Q : Over Z) (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    relativeAutMul B S hS Z hZ f x Q (relativeAutInv B S hS Z hZ f x Q g) g =
      relativeAutOne B S hS Z hZ f x Q := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  rw [relativeAutMul_point, relativeAutInv_point, relativeAutOne_point, IsIso.hom_inv_id]

/-- A point of `Isom_{𝒳/𝒴}(x, x)` times its inverse is the neutral point. -/
lemma relativeAut_mul_inv (Q : Over Z) (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    relativeAutMul B S hS Z hZ f x Q g (relativeAutInv B S hS Z hZ f x Q g) =
      relativeAutOne B S hS Z hZ f x Q := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  rw [relativeAutMul_point, relativeAutInv_point, relativeAutOne_point, IsIso.inv_hom_id]

/-- The group structure over `Z` on the sheaf `Isom_{𝒳/𝒴}(x, x)` of automorphisms of an
algebraic-space-valued point `x` of `𝒳` whose image under `f` is the identity: the law is
composition of automorphisms, the unit is the identity and the inverse is the inverse
automorphism. -/
@[stacks 0CPK "part (1): the relative automorphism sheaf is a group over Z", instance_reducible]
noncomputable def relativeAutSpaceSliceGrpObj :
    GrpObj (relativeAutSpaceSlice B S hS Z hZ f x) :=
  grpObjOfHoms (relativeAutSpaceSlice B S hS Z hZ f x) (relativeAutOne B S hS Z hZ f x)
    (relativeAutMul B S hS Z hZ f x) (relativeAutInv B S hS Z hZ f x)
    (fun r => relativeAutOne_comp B S hS Z hZ f x r)
    (fun r g h => relativeAutMul_comp B S hS Z hZ f x r g h)
    (relativeAut_one_mul B S hS Z hZ f x) (relativeAut_mul_one B S hS Z hZ f x)
    (relativeAut_mul_assoc B S hS Z hZ f x) (relativeAut_inv_mul B S hS Z hZ f x)
    (relativeAut_mul_inv B S hS Z hZ f x)

/-- The unit of `AlgebraicGeometry.Stack.relativeAutSpaceSliceGrpObj` on points. -/
lemma relativeAutSpaceSliceGrpObj_hom_one (Q : Over Z) :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x
    (1 : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) = relativeAutOne B S hS Z hZ f x Q :=
  grpObjOfHoms_hom_one _ _ _ _ _ _ _ _ _ _ _ Q

/-- The law of `AlgebraicGeometry.Stack.relativeAutSpaceSliceGrpObj` on points. -/
lemma relativeAutSpaceSliceGrpObj_hom_mul (Q : Over Z)
    (g h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x
    (g * h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) =
      relativeAutMul B S hS Z hZ f x Q g h :=
  grpObjOfHoms_hom_mul _ _ _ _ _ _ _ _ _ _ _ Q g h

/-- The relative automorphism sheaf `Isom_{𝒳/𝒴}(x, x)` as a group algebraic space over `Z`, with
the group structure `AlgebraicGeometry.Stack.relativeAutSpaceSliceGrpObj`. -/
@[stacks 0CPK "part (1): the relative automorphisms are a group algebraic space over Z"]
noncomputable def relativeAutGroupAlgebraicSpace :
    Space.GroupAlgebraicSpace B S hS Z hZ := by
  letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x) :=
    relativeAutSpaceSliceGrpObj B S hS Z hZ f x
  exact ⟨Grp.mk (relativeAutSpaceSlice B S hS Z hZ f x),
    isAlgebraicSpace_relativeIsomSpaceOverSpace B S hS Z hZ f x x (𝟙 (x ≫ f))⟩

/-- The object over `Z` underlying `AlgebraicGeometry.Stack.relativeAutGroupAlgebraicSpace` is
`Isom_{𝒳/𝒴}(x, x)`, on the nose. -/
@[simp] lemma relativeAutGroupAlgebraicSpace_obj_X :
    (relativeAutGroupAlgebraicSpace B S hS Z hZ f x).obj.X =
      relativeAutSpaceSlice B S hS Z hZ f x :=
  rfl

end Group

/-! ### The relative isomorphisms as a pseudo-torsor -/

section PseudoTorsor

variable (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
  (α : x₁ ≫ f ⟶ x₂ ≫ f)

/-- The action of `Isom_{𝒳/𝒴}(x₂, x₂)` on `Isom^α_{𝒳/𝒴}(x₁, x₂)` on points: a relative
automorphism of `x₂` acts on an isomorphism `x₁ ⟶ x₂` lifting `α` by postcomposition. -/
noncomputable def relativeIsomSmul (Q : Over Z)
    (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂)
    (p : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :
    Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α :=
  relativeIsomSpaceSliceHomMk B S hS Z hZ f x₁ x₂ α Q
    (fun W t => relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α p W t ≫
      relativeIsomSpaceSlicePoint B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f)) g W t)
    (fun W t => by
      rw [pointFiberMap_comp_hom, pointFiberMap_relativeIsomSpaceSlicePoint,
        pointFiberMap_relativeIsomSpaceSlicePoint, twistedComponent_id, Category.comp_id])
    (fun gm t hz => by
      rw [pointRestrict_comp_hom, pointRestrict_relativeIsomSpaceSlicePoint,
        pointRestrict_relativeIsomSpaceSlicePoint])

/-- A relative automorphism `g` of `x₂` acting on a point `p` of `Isom^α_{𝒳/𝒴}(x₁, x₂)` names the
composite of the isomorphism `p` names with the automorphism `g` names. -/
@[simp] lemma relativeIsomSmul_point (Q : Over Z)
    (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂)
    (p : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α
        (relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q g p) W t =
      relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α p W t ≫
        relativeIsomSpaceSlicePoint B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f)) g W t :=
  pointHomCongr_eq B S hS Z hZ x₁ x₂ _ _

/-- The action of `Isom_{𝒳/𝒴}(x₂, x₂)` on `Isom^α_{𝒳/𝒴}(x₁, x₂)` commutes with precomposition
by a morphism of test objects. -/
lemma relativeIsomSmul_comp {R Q : Over Z} (r : R ⟶ Q)
    (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂)
    (p : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :
    r ≫ relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q g p =
      relativeIsomSmul B S hS Z hZ f x₁ x₂ α R (r ≫ g) (r ≫ p) := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x₁ x₂ α _ _ fun W t => ?_
  have hr := over_hom_app_comp B S hS Z r W t
  rw [relativeIsomSpaceSlicePoint_comp B S hS Z hZ f x₁ x₂ α r
      (relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q g p) W t hr,
    relativeIsomSmul_point, pointHomCongr_comp, relativeIsomSmul_point,
    relativeIsomSpaceSlicePoint_comp B S hS Z hZ f x₁ x₂ α r p W t hr,
    relativeIsomSpaceSlicePoint_comp B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f)) r g W t hr]

/-- The neutral point of `Isom_{𝒳/𝒴}(x₂, x₂)` acts trivially on `Isom^α_{𝒳/𝒴}(x₁, x₂)`. -/
lemma relativeIsomSmul_one (Q : Over Z)
    (p : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :
    relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q (relativeAutOne B S hS Z hZ f x₂ Q) p = p := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x₁ x₂ α _ _ fun W t => ?_
  rw [relativeIsomSmul_point, relativeAutOne_point, Category.comp_id]

/-- Acting by a product of relative automorphisms is acting by each in turn. -/
lemma relativeIsomSmul_mul (Q : Over Z)
    (g h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂)
    (p : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :
    relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q (relativeAutMul B S hS Z hZ f x₂ Q g h) p =
      relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q g
        (relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q h p) := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x₁ x₂ α _ _ fun W t => ?_
  rw [relativeIsomSmul_point, relativeIsomSmul_point, relativeIsomSmul_point,
    relativeAutMul_point, Category.assoc]

/-- The action of `Isom_{𝒳/𝒴}(x₂, x₂)` on `Isom^α_{𝒳/𝒴}(x₁, x₂)` over `Z`, by
postcomposition. -/
@[stacks 0CPK "part (4): the action by postcomposition", instance_reducible]
noncomputable def relativeIsomSpaceSliceModObj :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
    ModObj (relativeAutSpaceSlice B S hS Z hZ f x₂)
      (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) := by
  letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
    relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
  exact modObjOfHoms _ (relativeIsomSmul B S hS Z hZ f x₁ x₂ α)
    (fun r g p => relativeIsomSmul_comp B S hS Z hZ f x₁ x₂ α r g p)
    (fun Q p => (congrArg (fun k => relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q k p)
      (relativeAutSpaceSliceGrpObj_hom_one B S hS Z hZ f x₂ Q)).trans
      (relativeIsomSmul_one B S hS Z hZ f x₁ x₂ α Q p))
    (fun Q g h p => (congrArg (fun k => relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q k p)
      (relativeAutSpaceSliceGrpObj_hom_mul B S hS Z hZ f x₂ Q g h)).trans
      (relativeIsomSmul_mul B S hS Z hZ f x₁ x₂ α Q g h p))

/-- The action of `AlgebraicGeometry.Stack.relativeIsomSpaceSliceModObj` on points is
`AlgebraicGeometry.Stack.relativeIsomSmul`, i.e. postcomposition. -/
lemma relativeIsomSpaceSliceModObj_smul (Q : Over Z)
    (g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂)
    (p : Q ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
    letI : ModObj (relativeAutSpaceSlice B S hS Z hZ f x₂)
        (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :=
      relativeIsomSpaceSliceModObj B S hS Z hZ f x₁ x₂ α
    g • p = relativeIsomSmul B S hS Z hZ f x₁ x₂ α Q g p := by
  let : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
    relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
  exact modObjOfHoms_hom_smul _ _ _ _ _ Q g p

/-- The relative automorphism of `x₂` carrying one isomorphism lifting `α` to another: the
composite of the inverse of the first with the second. -/
noncomputable def relativeIsomShear (T : Over Z)
    (p q : T ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :
    T ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂ :=
  relativeIsomSpaceSliceHomMk B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f)) T
    (fun W t => CategoryTheory.inv
        (relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α p W t) ≫
      relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W t)
    (fun W t => by
      rw [twistedComponent_id, pointFiberMap_comp_hom]
      have hinv : pointFiberMap B S hS Z hZ f x₂ x₁ W.unop (T.hom.app W t)
            (CategoryTheory.inv
              (relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α p W t)) ≫
          twistedComponent B S hS Z hZ f x₁ x₂ α W.unop (T.hom.app W t) = 𝟙 _ := by
        rw [← pointFiberMap_relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α p W t,
          ← pointFiberMap_comp_hom, IsIso.inv_hom_id, pointFiberMap_id_hom]
      rw [pointFiberMap_relativeIsomSpaceSlicePoint]
      exact hinv)
    (fun gm t hz => by
      rw [pointRestrict_comp_hom, IsIso.eq_inv_comp,
        ← pointRestrict_relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α p gm t hz,
        ← pointRestrict_relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q gm t hz,
        ← Category.assoc, ← pointRestrict_comp_hom, IsIso.hom_inv_id, pointRestrict_id_hom,
        Category.id_comp])

/-- The relative automorphism `AlgebraicGeometry.Stack.relativeIsomShear` of `p` and `q` names
the composite of the inverse of the isomorphism `p` names with the one `q` names. -/
@[simp] lemma relativeIsomShear_point (T : Over Z)
    (p q : T ⟶ relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : T.left.obj W) :
    relativeIsomSpaceSlicePoint B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f))
        (relativeIsomShear B S hS Z hZ f x₁ x₂ α T p q) W t =
      CategoryTheory.inv (relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α p W t) ≫
        relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α q W t :=
  pointHomCongr_eq B S hS Z hZ x₂ x₂ _ _

/-- The isomorphisms lifting `α` are a pseudo-torsor under the relative automorphisms of the
target point, over `Z`: `Isom^α_{𝒳/𝒴}(x₁, x₂)` is a pseudo-torsor under `Isom_{𝒳/𝒴}(x₂, x₂)`. -/
@[stacks 0CPK "part (4): the relative isomorphisms are a pseudo-torsor"]
theorem isPseudoTorsor_relativeIsomSpaceSlice :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
    letI : ModObj (relativeAutSpaceSlice B S hS Z hZ f x₂)
        (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :=
      relativeIsomSpaceSliceModObj B S hS Z hZ f x₁ x₂ α
    IsPseudoTorsor (relativeAutSpaceSlice B S hS Z hZ f x₂)
      (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) := by
  let : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
    relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
  let : ModObj (relativeAutSpaceSlice B S hS Z hZ f x₂)
      (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :=
    relativeIsomSpaceSliceModObj B S hS Z hZ f x₁ x₂ α
  refine (isPseudoTorsor_iff_forall_existsUnique_smul _ _).mpr fun T p q => ?_
  refine ⟨relativeIsomShear B S hS Z hZ f x₁ x₂ α T p q, ?_, fun g hg => ?_⟩
  · refine ((relativeIsomSpaceSliceModObj_smul B S hS Z hZ f x₁ x₂ α T _ p).trans ?_)
    refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x₁ x₂ α _ _ fun W t => ?_
    rw [relativeIsomSmul_point, relativeIsomShear_point, IsIso.hom_inv_id_assoc]
  · refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f)) _ _ fun W t => ?_
    rw [relativeIsomShear_point, IsIso.eq_inv_comp]
    simpa only [relativeIsomSmul_point] using congrArg
      (fun k => relativeIsomSpaceSlicePoint B S hS Z hZ f x₁ x₂ α k W t)
      ((relativeIsomSpaceSliceModObj_smul B S hS Z hZ f x₁ x₂ α T g p).symm.trans hg)

/-- For every 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f` the sheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` and the relative
automorphism sheaf `Isom_{𝒳/𝒴}(x₂, x₂)` are algebraic spaces over `Z`, and the first is a
pseudo-torsor under the second over `Z`. -/
@[stacks 0CPK "part (4): the relative isomorphisms are an algebraic space and a pseudo-torsor"]
theorem isAlgebraicSpace_isPseudoTorsor_relativeIsomSpaceSlice :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
    letI : ModObj (relativeAutSpaceSlice B S hS Z hZ f x₂)
        (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :=
      relativeIsomSpaceSliceModObj B S hS Z hZ f x₁ x₂ α
    IsAlgebraicSpace B S hS (relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α) ∧
      IsAlgebraicSpace B S hS (relativeIsomSpaceOverSpace B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f))) ∧
      IsPseudoTorsor (relativeAutSpaceSlice B S hS Z hZ f x₂)
        (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :=
  ⟨isAlgebraicSpace_relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α,
    isAlgebraicSpace_relativeIsomSpaceOverSpace B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f)),
    isPseudoTorsor_relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α⟩

/-- The sheaves `Isom_𝒳(x₁, x₂)`, `Isom_𝒴(f x₁, f x₂)` and `Isom^α_{𝒳/𝒴}(x₁, x₂)` are algebraic
spaces over `Z`, and the square cutting out `Isom^α_{𝒳/𝒴}(x₁, x₂)` along
`AlgebraicGeometry.Stack.isomSpaceOverSpaceMap` is cartesian. -/
@[stacks 0CPK "part (3): the cartesian square of algebraic spaces over Z"]
theorem isAlgebraicSpace_isPullback_relativeIsomSpaceOverSpace :
    IsAlgebraicSpace B S hS (isomSpaceOverSpace B S hS Z hZ x₁ x₂) ∧
      IsAlgebraicSpace B S hS (isomSpaceOverSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f)) ∧
      IsAlgebraicSpace B S hS (relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α) ∧
      IsPullback (relativeIsomSpaceOverSpaceι B S hS Z hZ f x₁ x₂ α)
        (relativeIsomSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α)
        (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)
        (twistedSection B S hS Z hZ f x₁ x₂ α) :=
  ⟨isAlgebraicSpace_isomSpaceOverSpace B S hS Z hZ x₁ x₂,
    isAlgebraicSpace_isomSpaceOverSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f),
    isAlgebraicSpace_relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α,
    isPullback_relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α⟩

end PseudoTorsor

/-! ### The group structure on the automorphism sheaf, and the exact sequence -/

section ExactSequence

variable (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)

/-- The neutral point of `Isom_𝒳(x, x)` over a test object. -/
noncomputable def isomAutOne (Q : Over Z) : Q ⟶ isomSpaceSlice B S hS Z hZ x x :=
  isomSpaceSliceHomMk B S hS Z hZ x x Q (fun _ _ => 𝟙 _)
    (fun g _ hz => pointRestrict_id_hom B S hS Z hZ x g _ _ hz)

/-- The neutral point of `Isom_𝒳(x, x)` names the identity automorphism. -/
@[simp] lemma isomAutOne_point (Q : Over Z) (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W) :
    isomSpaceSlicePoint B S hS Z hZ x x (isomAutOne B S hS Z hZ x Q) W t = 𝟙 _ :=
  pointHomCongr_eq B S hS Z hZ x x _ _

/-- The product of two points of `Isom_𝒳(x, x)`: composition of automorphisms. -/
noncomputable def isomAutMul (Q : Over Z) (g h : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    Q ⟶ isomSpaceSlice B S hS Z hZ x x :=
  isomSpaceSliceHomMk B S hS Z hZ x x Q
    (fun W t => isomSpaceSlicePoint B S hS Z hZ x x h W t ≫
      isomSpaceSlicePoint B S hS Z hZ x x g W t)
    (fun gm t hz => by
      rw [pointRestrict_comp_hom, pointRestrict_isomSpaceSlicePoint,
        pointRestrict_isomSpaceSlicePoint])

/-- The product `g * h` of points of `Isom_𝒳(x, x)` names the composite of the automorphism `h`
names with the one `g` names. -/
@[simp] lemma isomAutMul_point (Q : Over Z) (g h : Q ⟶ isomSpaceSlice B S hS Z hZ x x)
    (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W) :
    isomSpaceSlicePoint B S hS Z hZ x x (isomAutMul B S hS Z hZ x Q g h) W t =
      isomSpaceSlicePoint B S hS Z hZ x x h W t ≫ isomSpaceSlicePoint B S hS Z hZ x x g W t :=
  pointHomCongr_eq B S hS Z hZ x x _ _

/-- The inverse of a point of `Isom_𝒳(x, x)`. -/
noncomputable def isomAutInv (Q : Over Z) (g : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    Q ⟶ isomSpaceSlice B S hS Z hZ x x :=
  isomSpaceSliceHomMk B S hS Z hZ x x Q
    (fun W t => CategoryTheory.inv (isomSpaceSlicePoint B S hS Z hZ x x g W t))
    (fun gm t hz => by
      refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
      rw [← pointRestrict_isomSpaceSlicePoint B S hS Z hZ x x g gm t hz,
        ← pointRestrict_comp_hom, IsIso.hom_inv_id, pointRestrict_id_hom])

/-- The inverse of a point of `Isom_𝒳(x, x)` names the inverse automorphism. -/
@[simp] lemma isomAutInv_point (Q : Over Z) (g : Q ⟶ isomSpaceSlice B S hS Z hZ x x)
    (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W) :
    isomSpaceSlicePoint B S hS Z hZ x x (isomAutInv B S hS Z hZ x Q g) W t =
      CategoryTheory.inv (isomSpaceSlicePoint B S hS Z hZ x x g W t) :=
  pointHomCongr_eq B S hS Z hZ x x _ _

/-- The neutral point of `Isom_𝒳(x, x)` is stable under precomposition by a morphism of test
objects. -/
lemma isomAutOne_comp {R Q : Over Z} (r : R ⟶ Q) :
    r ≫ isomAutOne B S hS Z hZ x Q = isomAutOne B S hS Z hZ x R := by
  refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
  have hr := over_hom_app_comp B S hS Z r W t
  rw [isomSpaceSlicePoint_comp B S hS Z hZ x x r (isomAutOne B S hS Z hZ x Q) W t hr,
    isomAutOne_point, isomAutOne_point, pointHomCongr_id]

/-- The product of points of `Isom_𝒳(x, x)` commutes with precomposition by a morphism of test
objects. -/
lemma isomAutMul_comp {R Q : Over Z} (r : R ⟶ Q)
    (g h : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    r ≫ isomAutMul B S hS Z hZ x Q g h = isomAutMul B S hS Z hZ x R (r ≫ g) (r ≫ h) := by
  refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
  have hr := over_hom_app_comp B S hS Z r W t
  rw [isomSpaceSlicePoint_comp B S hS Z hZ x x r (isomAutMul B S hS Z hZ x Q g h) W t hr,
    isomAutMul_point, pointHomCongr_comp, isomAutMul_point,
    isomSpaceSlicePoint_comp B S hS Z hZ x x r g W t hr,
    isomSpaceSlicePoint_comp B S hS Z hZ x x r h W t hr]

/-- The neutral point of `Isom_𝒳(x, x)` is a left unit for the product. -/
lemma isomAut_one_mul (Q : Over Z) (g : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    isomAutMul B S hS Z hZ x Q (isomAutOne B S hS Z hZ x Q) g = g := by
  refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
  rw [isomAutMul_point, isomAutOne_point, Category.comp_id]

/-- The neutral point of `Isom_𝒳(x, x)` is a right unit for the product. -/
lemma isomAut_mul_one (Q : Over Z) (g : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    isomAutMul B S hS Z hZ x Q g (isomAutOne B S hS Z hZ x Q) = g := by
  refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
  rw [isomAutMul_point, isomAutOne_point, Category.id_comp]

/-- The product of points of `Isom_𝒳(x, x)` is associative. -/
lemma isomAut_mul_assoc (Q : Over Z) (g h k : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    isomAutMul B S hS Z hZ x Q (isomAutMul B S hS Z hZ x Q g h) k =
      isomAutMul B S hS Z hZ x Q g (isomAutMul B S hS Z hZ x Q h k) := by
  refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
  rw [isomAutMul_point, isomAutMul_point, isomAutMul_point, isomAutMul_point, Category.assoc]

/-- The inverse of a point of `Isom_𝒳(x, x)` times the point is the neutral point. -/
lemma isomAut_inv_mul (Q : Over Z) (g : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    isomAutMul B S hS Z hZ x Q (isomAutInv B S hS Z hZ x Q g) g =
      isomAutOne B S hS Z hZ x Q := by
  refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
  rw [isomAutMul_point, isomAutInv_point, isomAutOne_point, IsIso.hom_inv_id]

/-- A point of `Isom_𝒳(x, x)` times its inverse is the neutral point. -/
lemma isomAut_mul_inv (Q : Over Z) (g : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    isomAutMul B S hS Z hZ x Q g (isomAutInv B S hS Z hZ x Q g) =
      isomAutOne B S hS Z hZ x Q := by
  refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
  rw [isomAutMul_point, isomAutInv_point, isomAutOne_point, IsIso.inv_hom_id]

/-- The group structure on `Isom_𝒳(x, x)` over `Z`, for an algebraic-space-valued point `x`:
composition of automorphisms over every point of `Z`. -/
@[instance_reducible]
noncomputable def isomSpaceSliceGrpObj : GrpObj (isomSpaceSlice B S hS Z hZ x x) :=
  grpObjOfHoms (isomSpaceSlice B S hS Z hZ x x) (isomAutOne B S hS Z hZ x)
    (isomAutMul B S hS Z hZ x) (isomAutInv B S hS Z hZ x)
    (fun r => isomAutOne_comp B S hS Z hZ x r) (fun r g h => isomAutMul_comp B S hS Z hZ x r g h)
    (isomAut_one_mul B S hS Z hZ x) (isomAut_mul_one B S hS Z hZ x)
    (isomAut_mul_assoc B S hS Z hZ x) (isomAut_inv_mul B S hS Z hZ x)
    (isomAut_mul_inv B S hS Z hZ x)

/-- The unit of `AlgebraicGeometry.Stack.isomSpaceSliceGrpObj` on points. -/
lemma isomSpaceSliceGrpObj_hom_one (Q : Over Z) :
    letI : GrpObj (isomSpaceSlice B S hS Z hZ x x) := isomSpaceSliceGrpObj B S hS Z hZ x
    (1 : Q ⟶ isomSpaceSlice B S hS Z hZ x x) = isomAutOne B S hS Z hZ x Q :=
  grpObjOfHoms_hom_one _ _ _ _ _ _ _ _ _ _ _ Q

/-- The law of `AlgebraicGeometry.Stack.isomSpaceSliceGrpObj` on points. -/
lemma isomSpaceSliceGrpObj_hom_mul (Q : Over Z)
    (g h : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    letI : GrpObj (isomSpaceSlice B S hS Z hZ x x) := isomSpaceSliceGrpObj B S hS Z hZ x
    (g * h : Q ⟶ isomSpaceSlice B S hS Z hZ x x) = isomAutMul B S hS Z hZ x Q g h :=
  grpObjOfHoms_hom_mul _ _ _ _ _ _ _ _ _ _ _ Q g h

variable (f : 𝒳 ⟶ 𝒴)

/-- The inclusion of the relative automorphisms of `x` into its automorphisms, as a morphism over
`Z`. -/
noncomputable def relativeAutSpaceSliceι :
    relativeAutSpaceSlice B S hS Z hZ f x ⟶ isomSpaceSlice B S hS Z hZ x x :=
  Over.homMk (relativeIsomSpaceOverSpaceι B S hS Z hZ f x x (𝟙 (x ≫ f)))
    (Functor.presheafHom_ext fun _ _ => rfl)

/-- The automorphism named by the image of a point of `Isom_{𝒳/𝒴}(x, x)` in `Isom_𝒳(x, x)` is the
one the point names. -/
@[simp] lemma isomSpaceSlicePoint_comp_ι {Q : Over Z}
    (q : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    isomSpaceSlicePoint B S hS Z hZ x x (q ≫ relativeAutSpaceSliceι B S hS Z hZ x f) W t =
      relativeIsomSpaceSlicePoint B S hS Z hZ f x x (𝟙 (x ≫ f)) q W t :=
  pointHomCongr_congr B S hS Z hZ x x _ _ _

/-- The map on automorphism sheaves induced by `f`, as a morphism over `Z`: the map
`AlgebraicGeometry.Stack.isomSpaceOverSpaceMap` at `x₁ = x₂ = x`. -/
noncomputable def isomSpaceSliceMap :
    isomSpaceSlice B S hS Z hZ x x ⟶ isomSpaceSlice B S hS Z hZ (x ≫ f) (x ≫ f) :=
  Over.homMk (isomSpaceOverSpaceMap B S hS Z hZ f x x)
    (isomSpaceOverSpaceMap_comp_proj B S hS Z hZ f x x)

/-- The automorphism of `x ≫ f` named by the image of a point of `Isom_𝒳(x, x)` under
`AlgebraicGeometry.Stack.isomSpaceSliceMap` is the image under `f` of the automorphism the point
names. -/
@[simp] lemma isomSpaceSlicePoint_comp_map {Q : Over Z}
    (q : Q ⟶ isomSpaceSlice B S hS Z hZ x x) (W : (BigFppfOver B S hS)ᵒᵖ)
    (t : Q.left.obj W) :
    isomSpaceSlicePoint B S hS Z hZ (x ≫ f) (x ≫ f)
        (q ≫ isomSpaceSliceMap B S hS Z hZ x f) W t =
      pointFiberMap B S hS Z hZ f x x W.unop (Q.hom.app W t)
        (isomSpaceSlicePoint B S hS Z hZ x x q W t) := by
  rw [isomSpaceSlicePoint, isomSpaceSlicePoint, pointFiberMap_pointHomCongr]
  exact pointHomCongr_congr B S hS Z hZ (x ≫ f) (x ≫ f) _ _ _

/-- The inclusion `Isom_{𝒳/𝒴}(x, x) ⟶ Isom_𝒳(x, x)` is a homomorphism of groups over `Z`. -/
@[stacks 0CPK "part (2): the first map is a homomorphism of groups over Z"]
theorem isMonHom_relativeAutSpaceSliceι :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x
    letI : GrpObj (isomSpaceSlice B S hS Z hZ x x) := isomSpaceSliceGrpObj B S hS Z hZ x
    IsMonHom (relativeAutSpaceSliceι B S hS Z hZ x f) := by
  let : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x) :=
    relativeAutSpaceSliceGrpObj B S hS Z hZ f x
  let : GrpObj (isomSpaceSlice B S hS Z hZ x x) := isomSpaceSliceGrpObj B S hS Z hZ x
  refine isMonHom_of_homs (relativeAutOne B S hS Z hZ f x) (relativeAutMul B S hS Z hZ f x)
    (fun r => relativeAutOne_comp B S hS Z hZ f x r)
    (fun r g h => relativeAutMul_comp B S hS Z hZ f x r g h)
    (relativeAut_one_mul B S hS Z hZ f x) (relativeAut_mul_one B S hS Z hZ f x)
    (relativeAut_mul_assoc B S hS Z hZ f x) (isomAutOne B S hS Z hZ x)
    (isomAutMul B S hS Z hZ x) (fun r => isomAutOne_comp B S hS Z hZ x r)
    (fun r g h => isomAutMul_comp B S hS Z hZ x r g h) (isomAut_one_mul B S hS Z hZ x)
    (isomAut_mul_one B S hS Z hZ x) (isomAut_mul_assoc B S hS Z hZ x)
    (relativeAutSpaceSliceι B S hS Z hZ x f) (fun Q => ?_) (fun Q g h => ?_)
  · refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
    rw [isomSpaceSlicePoint_comp_ι, relativeAutOne_point, isomAutOne_point]
  · refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
    rw [isomSpaceSlicePoint_comp_ι, relativeAutMul_point, isomAutMul_point,
      isomSpaceSlicePoint_comp_ι, isomSpaceSlicePoint_comp_ι]

/-- The map `Isom_𝒳(x, x) ⟶ Isom_𝒴(f x, f x)` induced by `f` is a homomorphism of groups over
`Z`. -/
@[stacks 0CPK "part (2): the second map is a homomorphism of groups over Z"]
theorem isMonHom_isomSpaceSliceMap :
    letI : GrpObj (isomSpaceSlice B S hS Z hZ x x) := isomSpaceSliceGrpObj B S hS Z hZ x
    letI : GrpObj (isomSpaceSlice B S hS Z hZ (x ≫ f) (x ≫ f)) :=
      isomSpaceSliceGrpObj B S hS Z hZ (x ≫ f)
    IsMonHom (isomSpaceSliceMap B S hS Z hZ x f) := by
  let : GrpObj (isomSpaceSlice B S hS Z hZ x x) := isomSpaceSliceGrpObj B S hS Z hZ x
  let : GrpObj (isomSpaceSlice B S hS Z hZ (x ≫ f) (x ≫ f)) :=
    isomSpaceSliceGrpObj B S hS Z hZ (x ≫ f)
  refine isMonHom_of_homs (isomAutOne B S hS Z hZ x) (isomAutMul B S hS Z hZ x)
    (fun r => isomAutOne_comp B S hS Z hZ x r)
    (fun r g h => isomAutMul_comp B S hS Z hZ x r g h) (isomAut_one_mul B S hS Z hZ x)
    (isomAut_mul_one B S hS Z hZ x) (isomAut_mul_assoc B S hS Z hZ x)
    (isomAutOne B S hS Z hZ (x ≫ f)) (isomAutMul B S hS Z hZ (x ≫ f))
    (fun r => isomAutOne_comp B S hS Z hZ (x ≫ f) r)
    (fun r g h => isomAutMul_comp B S hS Z hZ (x ≫ f) r g h)
    (isomAut_one_mul B S hS Z hZ (x ≫ f)) (isomAut_mul_one B S hS Z hZ (x ≫ f))
    (isomAut_mul_assoc B S hS Z hZ (x ≫ f)) (isomSpaceSliceMap B S hS Z hZ x f)
    (fun Q => ?_) (fun Q g h => ?_)
  · refine isomSpaceSliceHom_ext B S hS Z hZ (x ≫ f) (x ≫ f) _ _ fun W t => ?_
    rw [isomSpaceSlicePoint_comp_map, isomAutOne_point, isomAutOne_point, pointFiberMap_id_hom]
  · refine isomSpaceSliceHom_ext B S hS Z hZ (x ≫ f) (x ≫ f) _ _ fun W t => ?_
    rw [isomSpaceSlicePoint_comp_map, isomAutMul_point, isomAutMul_point,
      pointFiberMap_comp_hom, isomSpaceSlicePoint_comp_map, isomSpaceSlicePoint_comp_map]

/-- The inclusion `Isom_{𝒳/𝒴}(x, x) ⟶ Isom_𝒳(x, x)` is a monomorphism. -/
@[stacks 0CPK "part (2): injectivity of the first map"]
theorem relativeAutSpaceSliceι_injective (Q : Over Z)
    (g h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x)
    (hgh : g ≫ relativeAutSpaceSliceι B S hS Z hZ x f =
      h ≫ relativeAutSpaceSliceι B S hS Z hZ x f) : g = h := by
  refine relativeIsomSpaceSliceHom_ext B S hS Z hZ f x x (𝟙 (x ≫ f)) _ _ fun W t => ?_
  rw [← isomSpaceSlicePoint_comp_ι B S hS Z hZ x f g W t,
    ← isomSpaceSlicePoint_comp_ι B S hS Z hZ x f h W t, hgh]

/-- The sequence `0 ⟶ Isom_{𝒳/𝒴}(x, x) ⟶ Isom_𝒳(x, x) ⟶ Isom_𝒴(f x, f x)` of groups over `Z` is
exact at the middle term: a point of `Isom_𝒳(x, x)` is killed by the second map exactly when it
comes from a relative automorphism. -/
@[stacks 0CPK "part (2): exactness at Isom_𝒳(x, x)"]
theorem relativeAutSpaceSlice_exact (Q : Over Z) (p : Q ⟶ isomSpaceSlice B S hS Z hZ x x) :
    letI : GrpObj (isomSpaceSlice B S hS Z hZ (x ≫ f) (x ≫ f)) :=
      isomSpaceSliceGrpObj B S hS Z hZ (x ≫ f)
    p ≫ isomSpaceSliceMap B S hS Z hZ x f = 1 ↔
      ∃ g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x,
        g ≫ relativeAutSpaceSliceι B S hS Z hZ x f = p := by
  let : GrpObj (isomSpaceSlice B S hS Z hZ (x ≫ f) (x ≫ f)) :=
    isomSpaceSliceGrpObj B S hS Z hZ (x ≫ f)
  rw [isomSpaceSliceGrpObj_hom_one B S hS Z hZ (x ≫ f) Q]
  constructor
  · intro hp
    have hpt : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (t : Q.left.obj W),
        pointFiberMap B S hS Z hZ f x x W.unop (Q.hom.app W t)
            (isomSpaceSlicePoint B S hS Z hZ x x p W t) =
          twistedComponent B S hS Z hZ f x x (𝟙 (x ≫ f)) W.unop (Q.hom.app W t) := by
      intro W t
      rw [twistedComponent_id, ← isomSpaceSlicePoint_comp_map B S hS Z hZ x f p W t, hp,
        isomAutOne_point]
    refine ⟨relativeIsomSpaceSliceHomMk B S hS Z hZ f x x (𝟙 (x ≫ f)) Q
      (fun W t => isomSpaceSlicePoint B S hS Z hZ x x p W t) hpt
      (fun gm t hz => pointRestrict_isomSpaceSlicePoint B S hS Z hZ x x p gm t hz), ?_⟩
    refine isomSpaceSliceHom_ext B S hS Z hZ x x _ _ fun W t => ?_
    rw [isomSpaceSlicePoint_comp_ι, relativeIsomSpaceSlicePoint_homMk]
  · rintro ⟨g, rfl⟩
    refine isomSpaceSliceHom_ext B S hS Z hZ (x ≫ f) (x ≫ f) _ _ fun W t => ?_
    rw [isomSpaceSlicePoint_comp_map, isomSpaceSlicePoint_comp_ι, isomAutOne_point,
      pointFiberMap_relativeIsomSpaceSlicePoint, twistedComponent_id]

end ExactSequence

/-! ### The four assertions together -/

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, an algebraic space `Z` and two points
`x₁, x₂ : Z ⟶ 𝒳`, the isomorphism sheaves attached to these data, read in the slice over `Z`,
satisfy:

* the relative automorphism sheaf `Isom_{𝒳/𝒴}(x₂, x₂)` is an algebraic space over `Z` and
  carries a group structure over `Z`, i.e. is a group algebraic space over `Z`;
* the sequence `0 ⟶ Isom_{𝒳/𝒴}(x₂, x₂) ⟶ Isom_𝒳(x₂, x₂) ⟶ Isom_𝒴(f x₂, f x₂)` is a sequence of
  homomorphisms of groups over `Z`, injective at the first map and exact at the middle term;
* the two isomorphism sheaves are algebraic spaces over `Z` and there is a map
  `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(f x₁, f x₂)` for which the square cutting out
  `Isom^α_{𝒳/𝒴}(x₁, x₂)` is cartesian for every 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f`;
* that sheaf is an algebraic space over `Z` and a pseudo-torsor under `Isom_{𝒳/𝒴}(x₂, x₂)` over
  `Z` for every such `α`. -/
@[stacks 0CPK "the whole statement: parts (1), (2), (3) and (4)"]
theorem relativeIsomSpaceSlice_properties (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    letI : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
      relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
    letI : GrpObj (isomSpaceSlice B S hS Z hZ x₂ x₂) := isomSpaceSliceGrpObj B S hS Z hZ x₂
    letI : GrpObj (isomSpaceSlice B S hS Z hZ (x₂ ≫ f) (x₂ ≫ f)) :=
      isomSpaceSliceGrpObj B S hS Z hZ (x₂ ≫ f)
    IsAlgebraicSpace B S hS (relativeIsomSpaceOverSpace B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f))) ∧
      Nonempty (GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂)) ∧
      IsMonHom (relativeAutSpaceSliceι B S hS Z hZ x₂ f) ∧
      IsMonHom (isomSpaceSliceMap B S hS Z hZ x₂ f) ∧
      (∀ (Q : Over Z) (g h : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂),
        g ≫ relativeAutSpaceSliceι B S hS Z hZ x₂ f =
          h ≫ relativeAutSpaceSliceι B S hS Z hZ x₂ f → g = h) ∧
      (∀ (Q : Over Z) (p : Q ⟶ isomSpaceSlice B S hS Z hZ x₂ x₂),
        p ≫ isomSpaceSliceMap B S hS Z hZ x₂ f = 1 ↔
          ∃ g : Q ⟶ relativeAutSpaceSlice B S hS Z hZ f x₂,
            g ≫ relativeAutSpaceSliceι B S hS Z hZ x₂ f = p) ∧
      IsAlgebraicSpace B S hS (isomSpaceOverSpace B S hS Z hZ x₁ x₂) ∧
      IsAlgebraicSpace B S hS (isomSpaceOverSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f)) ∧
      (∀ α : x₁ ≫ f ⟶ x₂ ≫ f,
        IsPullback (relativeIsomSpaceOverSpaceι B S hS Z hZ f x₁ x₂ α)
          (relativeIsomSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α)
          (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)
          (twistedSection B S hS Z hZ f x₁ x₂ α)) ∧
      (∀ α : x₁ ≫ f ⟶ x₂ ≫ f,
        IsAlgebraicSpace B S hS (relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α)) ∧
      (∀ α : x₁ ≫ f ⟶ x₂ ≫ f,
        letI : ModObj (relativeAutSpaceSlice B S hS Z hZ f x₂)
            (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α) :=
          relativeIsomSpaceSliceModObj B S hS Z hZ f x₁ x₂ α
        IsPseudoTorsor (relativeAutSpaceSlice B S hS Z hZ f x₂)
          (relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α)) := by
  let : GrpObj (relativeAutSpaceSlice B S hS Z hZ f x₂) :=
    relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂
  let : GrpObj (isomSpaceSlice B S hS Z hZ x₂ x₂) := isomSpaceSliceGrpObj B S hS Z hZ x₂
  let : GrpObj (isomSpaceSlice B S hS Z hZ (x₂ ≫ f) (x₂ ≫ f)) :=
    isomSpaceSliceGrpObj B S hS Z hZ (x₂ ≫ f)
  exact ⟨isAlgebraicSpace_relativeIsomSpaceOverSpace B S hS Z hZ f x₂ x₂ (𝟙 (x₂ ≫ f)),
    ⟨relativeAutSpaceSliceGrpObj B S hS Z hZ f x₂⟩,
    isMonHom_relativeAutSpaceSliceι B S hS Z hZ x₂ f,
    isMonHom_isomSpaceSliceMap B S hS Z hZ x₂ f,
    fun Q g h hgh => relativeAutSpaceSliceι_injective B S hS Z hZ x₂ f Q g h hgh,
    fun Q p => relativeAutSpaceSlice_exact B S hS Z hZ x₂ f Q p,
    isAlgebraicSpace_isomSpaceOverSpace B S hS Z hZ x₁ x₂,
    isAlgebraicSpace_isomSpaceOverSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f),
    fun α => isPullback_relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α,
    fun α => isAlgebraicSpace_relativeIsomSpaceOverSpace B S hS Z hZ f x₁ x₂ α,
    fun α => isPseudoTorsor_relativeIsomSpaceSlice B S hS Z hZ f x₁ x₂ α⟩

end AlgebraicGeometry.Stack

end
