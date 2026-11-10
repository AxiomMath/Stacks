module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# The 2-categorical correspondence of Stacks 04X5

Let `g : S ⟶ S'` be a morphism of a big fppf site. Stacks 04X5 asserts that Constructions A and
B of Stacks, Section 04WT restrict to a *canonical correspondence* between

* the 2-category of algebraic stacks over `S` (Stacks 03YP), and
* the 2-category of pairs `(𝒳', a)` consisting of an algebraic stack `𝒳'` over `S'` and a
  1-morphism `a : 𝒳' ⟶ S/S'` to the stack represented by `S` over `S'`,

bijectively on objects, on 1-morphisms and on 2-morphisms, compatibly with identities,
composition and whiskering.

`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff` (Stacks 04X5, the algebraicity
criterion) is what makes the object map well defined in both directions; everything else here is
the transport of the 04WV correspondence across the iterated-slice identification of the big fppf
site of `S` with the localization of the big fppf site of `S'` at the object `S/S'`. Both
directions of that transport are *strict*: `CategoryTheory.Over.iteratedSliceBackward_forget` is
an equality of functors on the nose, and
`CategoryTheory.Over.iteratedSliceForward_comp_iteratedSliceBackward` below upgrades
`CategoryTheory.Over.iteratedSliceEquiv` to an isomorphism of categories. That is the only new
ingredient; the two round-trip identities, the two bijections and all seven compatibilities are
then `rfl`.

## Main definitions

* `CategoryTheory.Over.iteratedSliceForward_comp_iteratedSliceBackward`: the iterated-slice
  equivalence is an isomorphism of categories, not merely an equivalence.
* `AlgebraicGeometry.Stack.AlgebraicStackPair`, `...PairHom`, `...PairHom₂`, `...PairHom.id` and
  `...PairHom.comp`: the right-hand 2-category of the correspondence, read strictly.
* `AlgebraicGeometry.Stack.changeBaseStructureHom`: the 1-morphism to the stack represented by
  `S` that Construction A equips its output with.
* `AlgebraicGeometry.Stack.algebraicStackConstructionA` and `...ConstructionB`: the two
  constructions on objects of the two 2-categories.
* `AlgebraicGeometry.Stack.AlgebraicStackCorrespondence` and
  `...categoryOfAlgebraicStacksOverSmallerBaseScheme`: the whole correspondence bundled as a
  single object, with one field for each component below.

## Main results

* `AlgebraicGeometry.Stack.algebraicStackConstructionObjEquiv`: the two constructions are
  mutually inverse on objects, with `...ConstructionA_val_val` and
  `changeBaseStructureHom_toFunctor` pinning the object map and its structure 1-morphism and
  `...ConstructionB_p` pinning the inverse;
* `AlgebraicGeometry.Stack.algebraicStackConstructionHomEquiv`, with `..._id`, `..._comp` and
  `..._val_hom_toFunctor`: the bijection on 1-morphisms;
* `AlgebraicGeometry.Stack.algebraicStackConstructionHom₂Equiv`, with `..._id`, `..._comp`,
  `..._whiskerLeft`, `..._whiskerRight` and `..._hom_toNatTrans`: the bijection on 2-morphisms.

Together with `AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory`, which is the
assertion that the base `S/S'` is itself an algebraic stack over `S'` and is proved for an
arbitrary scheme over the base in `StacksFrontier/AlgebraicGeometry/Stacks/SchemeStack.lean`, those
declarations are the covering set of the part key
`04X5 "canonical 2-categorical correspondence"`: there is exactly one of them for each component
of the correspondence Stacks 04X5 asserts, plus
`AlgebraicGeometry.Stack.algebraicStackConstructionB_p`, which pins the inverse object map as
well.

`AlgebraicGeometry.Stack.categoryOfAlgebraicStacksOverSmallerBaseScheme` collects those same
components into a single `AlgebraicGeometry.Stack.AlgebraicStackCorrespondence`, and that is how
the source states the result: Stacks 04X5 asserts *one* thing, that constructions A and B give
isomorphisms of the two 2-categories. So the bundle, rather than any one component, is the
declaration that states the content of the part key
`04X5 "canonical 2-categorical correspondence"`, and it carries that key. The fourteen components
listed above carry it too, which leaves the key's covering set over-determined by design: each of
them states one clause of the single assertion.

## Implementation notes

The 1-morphisms of the right-hand 2-category are read *strictly*, as in
`StacksFrontier/CategoryTheory/Sites/Localization/StacksAndLocalization.lean`: a 1-morphism of pairs
is a 1-morphism of algebraic stacks over `S'` commuting with the two structure 1-morphisms on the
nose, and no condition at all is imposed on a 2-morphism of pairs
(`CategoryTheory.Over.map_app_eq_eqToHom` is why none is needed). This is what the source's
parenthetical "(!)" in "mutually inverse (!)" asks for: with commutation only up to
2-isomorphism the two 2-categories would be equivalent but not isomorphic.

Construction B needs the structure functor of the pair's first component to be substituted before
anything reduces, so the two properties it has to verify are proved by separate `_aux` lemmas
whose statements spell the pair's data out; the same device makes the second round-trip identity
`rfl` after the underlying 1-morphism `A` is replaced by `A ⋙ j_! ⋙ j^!`, which is legitimate
precisely because the iterated-slice equivalence is strict.

The universes are those of Stacks 03YP and of the criterion: `AlgebraicStacks.{u, w}` over a big
fppf site of `Scheme.{u}`, with `w` the descent universe of the stack clause.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04WV](https://stacks.math.columbia.edu/tag/04WV)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Over

universe v₂ u₂ v₁ u₁

variable {T : Type u₁} [Category.{v₁} T] {X : T}

/-- **The iterated-slice equivalence is an isomorphism of categories.** Composing
`CategoryTheory.Over.iteratedSliceForward` with `CategoryTheory.Over.iteratedSliceBackward` gives
the identity functor of `T/f` on the nose, as the other composite does by
`CategoryTheory.Over.iteratedSliceBackward_forget`.

This strengthens both `CategoryTheory.Over.iteratedSliceEquiv`, whose unit is only an isomorphism,
and `CategoryTheory.Over.iteratedSliceForward_comp_map` (Stacks 03EH), which is the consequence of
this equality obtained by composing with `CategoryTheory.Over.forget f`. It is a general statement
about slices and a candidate for Mathlib.

Both halves are proved by presenting an object of `T/f` as a morphism `u` to `f` whose source has
its structure morphism given as a separate variable `y`, and substituting the factorization
`u ≫ f.hom = y`: the round trip recovers that structure morphism as `u ≫ f.hom`, which is the
given one only through `CategoryTheory.Over.w`, and after the substitution the two sides are
literally the same. -/
theorem iteratedSliceForward_comp_iteratedSliceBackward (f : Over X) :
    Over.iteratedSliceForward f ⋙ Over.iteratedSliceBackward f = 𝟭 (Over f) := by
  have hobj : ∀ {Z : T} (u : Z ⟶ f.left) (y : Z ⟶ X) (hu : u ≫ f.hom = y),
      (Over.iteratedSliceForward f ⋙ Over.iteratedSliceBackward f).obj
          (Over.mk (Over.homMk u hu : Over.mk y ⟶ f)) =
        Over.mk (Over.homMk u hu : Over.mk y ⟶ f) := by
    intro Z u y hu
    subst hu
    rfl
  have hmap : ∀ {Z W : T} (u : Z ⟶ f.left) (y : Z ⟶ X) (hu : u ≫ f.hom = y)
      (u' : W ⟶ f.left) (y' : W ⟶ X) (hu' : u' ≫ f.hom = y')
      (φ : (Over.mk (Over.homMk u hu : Over.mk y ⟶ f)) ⟶
        (Over.mk (Over.homMk u' hu' : Over.mk y' ⟶ f))),
      HEq ((Over.iteratedSliceForward f ⋙ Over.iteratedSliceBackward f).map φ) φ := by
    intro Z W u y hu u' y' hu' φ
    subst hu
    subst hu'
    rfl
  exact CategoryTheory.Functor.hext (fun a ↦ hobj a.hom.left a.left.hom (Over.w a.hom))
    fun a b φ ↦ hmap a.hom.left a.left.hom (Over.w a.hom) b.hom.left b.left.hom (Over.w b.hom) φ

/-- `CategoryTheory.Over.iteratedSliceForward_comp_iteratedSliceBackward` for a functor into
`T/f`, in the shape in which it is used: a functor to `T/f` is unchanged by the round trip
through `T/f.left`. -/
theorem comp_iteratedSliceForward_comp_iteratedSliceBackward {Y : Type u₂} [Category.{v₂} Y]
    (f : Over X) (A : Y ⥤ Over f) :
    (A ⋙ Over.iteratedSliceForward f) ⋙ Over.iteratedSliceBackward f = A := by
  rw [Functor.assoc, iteratedSliceForward_comp_iteratedSliceBackward, Functor.comp_id]

/-- `CategoryTheory.Over.iteratedSliceForward_comp_map` (Stacks 03EH) for a functor into
`T/(V/W)`, with the morphism `h : V ⟶ W` named rather than read off the object: the structure
functor of a category over the localization of `T/W` at `V/W` is its 1-morphism followed by the
relocalization functor of `h`. -/
theorem comp_iteratedSliceForward_comp_map {Y : Type u₂} [Category.{v₂} Y] {V W : T} (h : V ⟶ W)
    (A : Y ⥤ Over (Over.mk h)) :
    (A ⋙ Over.iteratedSliceForward (Over.mk h)) ⋙ Over.map h =
      A ⋙ Over.forget (Over.mk h) :=
  congrArg (fun F ↦ A ⋙ F) (Over.iteratedSliceForward_comp_map (Over.mk h))

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-! ### The right-hand 2-category -/

/-- An object of the right-hand 2-category of Stacks 04X5: an algebraic stack `𝒳'` over `S'`
together with a 1-morphism from `𝒳'` to the category fibred in groupoids over the big fppf site
of `S'` represented by `S/S'`. -/
abbrev AlgebraicStackPair :=
  Σ 𝒳' : AlgebraicStacks.{u, w} B S' hS', 𝒳'.val ⟶ schemeFibredCategory B S' hS' (Over.mk g)

/-- A 1-morphism of the right-hand 2-category of Stacks 04X5: a 1-morphism of algebraic stacks
over `S'` commuting strictly with the two 1-morphisms to the stack represented by `S/S'`. -/
abbrev AlgebraicStackPairHom (X Y : AlgebraicStackPair.{u, w} B S S' hS hS' g) :=
  { f : X.1.val ⟶ Y.1.val // f ≫ Y.2 = X.2 }

/-- A 2-morphism of the right-hand 2-category of Stacks 04X5. No compatibility with the
1-morphisms to `S/S'` is imposed: `CategoryTheory.Over.map_app_eq_eqToHom` shows that the triangle
condition the strict slice would ask for holds automatically. -/
abbrev AlgebraicStackPairHom₂ {X Y : AlgebraicStackPair.{u, w} B S S' hS hS' g}
    (f k : AlgebraicStackPairHom B S S' hS hS' g X Y) := f.val ⟶ k.val

/-- The identity 1-morphism of the right-hand 2-category of Stacks 04X5. -/
def AlgebraicStackPairHom.id (X : AlgebraicStackPair.{u, w} B S S' hS hS' g) :
    AlgebraicStackPairHom B S S' hS hS' g X X :=
  ⟨𝟙 X.1.val, Category.id_comp _⟩

/-- Composition of 1-morphisms in the right-hand 2-category of Stacks 04X5. -/
def AlgebraicStackPairHom.comp {X Y Z : AlgebraicStackPair.{u, w} B S S' hS hS' g}
    (f : AlgebraicStackPairHom B S S' hS hS' g X Y)
    (k : AlgebraicStackPairHom B S S' hS hS' g Y Z) :
    AlgebraicStackPairHom B S S' hS hS' g X Z :=
  ⟨f.val ≫ k.val, by rw [Category.assoc, k.2, f.2]⟩

/-! ### Constructions A and B on objects -/

/-- The 1-morphism to the stack represented by `S/S'` that Construction A equips its output with:
the original structure functor, read through the iterated-slice identification of the big fppf
site of `S` with the localization of the big fppf site of `S'` at `S/S'`. The commutation with the
two structure functors is `AlgebraicGeometry.Stack.changeBase_p_eq_comp_forget_iteratedSlice`,
which holds on the nose. -/
def changeBaseStructureHom (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (changeBaseAlgebraicStack B S S' hS hS' g 𝒳).val ⟶
      schemeFibredCategory B S' hS' (Over.mk g) :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := 𝒳.val.val.p ⋙ Over.iteratedSliceBackward (Over.mk g)
      w := rfl }

/-- The underlying functor of `AlgebraicGeometry.Stack.changeBaseStructureHom` is the structure
functor of `𝒳`, read through the inverse of the iterated-slice equivalence. This is the
`object_structure` clause of the correspondence of Stacks 04X5. -/
@[simp, stacks 04X5 "Construction A on 1-morphisms, as a functor"]
lemma changeBaseStructureHom_toFunctor (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (changeBaseStructureHom B S S' hS hS' g 𝒳).hom.toFunctor =
      𝒳.val.val.p ⋙ (Over.iteratedSliceEquiv (Over.mk g)).inverse :=
  rfl

/-- **Construction A of Stacks, Section 04WT on objects of the 2-category of algebraic stacks.**
An algebraic stack over `S` is sent to Construction A of it, which is algebraic over `S'` by
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff`, together with its original structure
functor as a 1-morphism to the stack represented by `S/S'`. -/
def algebraicStackConstructionA (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStackPair.{u, w} B S S' hS hS' g :=
  ⟨changeBaseAlgebraicStack B S S' hS hS' g 𝒳, changeBaseStructureHom B S S' hS hS' g 𝒳⟩

/-- The algebraic stack over `S'` underlying Construction A is Construction A of the underlying
category over the big fppf site of `S`. This is the `object_underlying` clause of the
correspondence of Stacks 04X5. -/
@[simp, stacks 04X5 "Construction A on objects, on the underlying fibred category"]
lemma algebraicStackConstructionA_val_val (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (algebraicStackConstructionA B S S' hS hS' g 𝒳).1.val.val =
      changeBase B S S' hS hS' g 𝒳.val.val :=
  rfl

/-- Construction B produces a category fibred in groupoids, with the data of the pair spelled out
so that the commutation `A ⋙ j = q` can be substituted: the composite of the pair's 1-morphism
with the iterated-slice equivalence is fibred in groupoids over the big fppf site of `S` by
Constructions A and B for categories fibred in groupoids. -/
lemma isFiberedInGroupoids_of_pair_aux {X₀ : Type (u + 1)} [Category.{u} X₀]
    (A : X₀ ⥤ Over (Over.mk g)) (q : X₀ ⥤ BigFppfOver B S' hS')
    (hw : A ⋙ Over.forget (Over.mk g) = q) (hq : q.IsFiberedInGroupoids) :
    (A ⋙ Over.iteratedSliceForward (Over.mk g)).IsFiberedInGroupoids := by
  subst hw
  have h : ((A ⋙ Over.iteratedSliceForward (Over.mk g)) ⋙ Over.map g).IsFiberedInGroupoids := by
    rw [Over.comp_iteratedSliceForward_comp_map]
    exact hq
  exact (Functor.isFiberedInGroupoids_comp_overMap_iff g
    (A ⋙ Over.iteratedSliceForward (Over.mk g))).1 h

/-- Construction B produces an algebraic stack, with the data of the pair spelled out so that the
commutation `A ⋙ j = q` can be substituted: Construction A of the output is then the pair's first
component, so the algebraicity criterion
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff` applies. This is where the criterion
makes the inverse object map well defined. -/
lemma isAlgebraicStack_of_pair_aux {X₀ : Type (u + 1)}
    [instX : Category.{u} X₀] (A : X₀ ⥤ Over (Over.mk g))
    (q : X₀ ⥤ BigFppfOver B S' hS') (hw : A ⋙ Over.forget (Over.mk g) = q)
    (hq : IsAlgebraicStack.{u, w} B S' hS' ⟨X₀, instX, q⟩) :
    IsAlgebraicStack.{u, w} B S hS
      ⟨X₀, instX, A ⋙ Over.iteratedSliceForward (Over.mk g)⟩ := by
  subst hw
  refine (isAlgebraicStack_changeBase_iff.{u, w} B S S' hS hS' g
    ⟨X₀, instX, A ⋙ Over.iteratedSliceForward (Over.mk g)⟩).1 ?_
  change IsAlgebraicStack.{u, w} B S' hS'
    ⟨X₀, instX, (A ⋙ Over.iteratedSliceForward (Over.mk g)) ⋙ Over.map g⟩
  rw [Over.comp_iteratedSliceForward_comp_map]
  exact hq

/-- **Construction B of Stacks, Section 04WT on objects of the 2-category of algebraic stacks.**
A pair `(𝒳', a)` is sent to the category of `𝒳'` over the big fppf site of `S` with structure
functor `a`, read through the iterated-slice equivalence. The pair carries no information beyond
`a`, because "`a` is a 1-morphism over `S'`" says exactly that the structure functor of `𝒳'` is
`a` followed by the localization functor of `S/S'`. -/
def algebraicStackConstructionB (X : AlgebraicStackPair.{u, w} B S S' hS hS' g) :
    AlgebraicStacks.{u, w} B S hS :=
  ⟨⟨⟨X.1.val.val.obj, X.1.val.val.category,
      X.2.hom.toFunctor ⋙ Over.iteratedSliceForward (Over.mk g)⟩,
    isFiberedInGroupoids_of_pair_aux B S S' hS hS' g X.2.hom.toFunctor
      X.1.val.val.p X.2.hom.w X.1.val.2⟩,
    isAlgebraicStack_of_pair_aux.{u, w} B S S' hS hS' g X.2.hom.toFunctor
      X.1.val.val.p X.2.hom.w X.1.2⟩

/-- The structure functor produced by Construction B is the pair's 1-morphism to the stack
represented by `S/S'`, read through the iterated-slice equivalence. -/
@[simp, stacks 04X5 "Construction B on objects, on the projection"]
lemma algebraicStackConstructionB_p (X : AlgebraicStackPair.{u, w} B S S' hS hS' g) :
    (algebraicStackConstructionB B S S' hS hS' g X).val.val.p =
      X.2.hom.toFunctor ⋙ (Over.iteratedSliceEquiv (Over.mk g)).functor :=
  rfl

/-- The round trip `A ∘ B` on objects, with the pair's data spelled out so that the commutation
`A ⋙ j = q` can be substituted and the underlying 1-morphism `A` replaced by
`(A ⋙ j_!) ⋙ j^!`. After those two steps the two pairs are literally the same, the second
replacement being available exactly because
`CategoryTheory.Over.iteratedSliceForward_comp_iteratedSliceBackward` makes the iterated-slice
equivalence strict. -/
lemma algebraicStackConstructionA_algebraicStackConstructionB_aux {X₀ : Type (u + 1)}
    [instX : Category.{u} X₀] (A : X₀ ⥤ Over (Over.mk g))
    (q : X₀ ⥤ BigFppfOver B S' hS') (hw : A ⋙ Over.forget (Over.mk g) = q)
    (hfib : q.IsFiberedInGroupoids) (halg : IsAlgebraicStack.{u, w} B S' hS' ⟨X₀, instX, q⟩) :
    algebraicStackConstructionA B S S' hS hS' g (algebraicStackConstructionB B S S' hS hS' g
        ⟨⟨⟨⟨X₀, instX, q⟩, hfib⟩, halg⟩, Bicategory.InducedBicategory.mkHom ⟨A, hw⟩⟩) =
      ⟨⟨⟨⟨X₀, instX, q⟩, hfib⟩, halg⟩, Bicategory.InducedBicategory.mkHom ⟨A, hw⟩⟩ := by
  subst hw
  obtain ⟨P, rfl⟩ : ∃ P : X₀ ⥤ BigFppfOver B S hS,
      P ⋙ Over.iteratedSliceBackward (Over.mk g) = A :=
    ⟨_, Over.comp_iteratedSliceForward_comp_iteratedSliceBackward (Over.mk g) A⟩
  rfl

/-- **Constructions A and B of Stacks 04X5 are mutually inverse on objects.** An algebraic stack
over `S` is the same thing as an algebraic stack over `S'` together with a 1-morphism to the stack
represented by `S/S'`.

Both round trips are strict. In one direction nothing has to be done: the pair carries no
information beyond its 1-morphism, and the iterated-slice equivalence composed the other way is
the identity on the nose. In the other the structure functor of the pair's first component has to
be recognized as the 1-morphism followed by the localization functor of `S/S'`, which is what
being a 1-morphism over `S'` says. The two algebraicity conditions agree by
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff`. -/
@[stacks 04X5 "the bijection on objects"]
def algebraicStackConstructionObjEquiv :
    AlgebraicStacks.{u, w} B S hS ≃ AlgebraicStackPair.{u, w} B S S' hS hS' g where
  toFun := algebraicStackConstructionA B S S' hS hS' g
  invFun := algebraicStackConstructionB B S S' hS hS' g
  left_inv _ := rfl
  right_inv X :=
    algebraicStackConstructionA_algebraicStackConstructionB_aux.{u, w} B S S' hS hS' g
      X.2.hom.toFunctor X.1.val.val.p X.2.hom.w X.1.val.2 X.1.2

/-! ### Constructions A and B on 1-morphisms and 2-morphisms -/

/-- **Constructions A and B of Stacks 04X5 are bijective on 1-morphisms**, and both are the
identity on the underlying functor. In one direction the commutation with the structure functors
is composed with the relocalization functor and with the inverse iterated-slice equivalence; in
the other it is recovered by composing the pair condition with the iterated-slice equivalence,
which cancels on the nose. -/
@[stacks 04X5 "the bijection on 1-morphisms"]
def algebraicStackConstructionHomEquiv (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) :
    (𝒳 ⟶ 𝒴) ≃ AlgebraicStackPairHom B S S' hS hS' g
      (algebraicStackConstructionA B S S' hS hS' g 𝒳)
      (algebraicStackConstructionA B S S' hS hS' g 𝒴) where
  toFun φ :=
    ⟨Bicategory.InducedBicategory.mkHom
        { toFunctor := φ.hom.hom.toFunctor
          w := congrArg (fun F ↦ F ⋙ Over.map g) φ.hom.hom.w },
      Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext'
        (congrArg (fun F ↦ F ⋙ Over.iteratedSliceBackward (Over.mk g)) φ.hom.hom.w))⟩
  invFun f :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := f.val.hom.toFunctor
        w := congrArg (fun F ↦ F ⋙ Over.iteratedSliceForward (Over.mk g))
          (congrArg (fun h ↦ h.hom.toFunctor) f.2) })
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection on 1-morphisms is the identity on the underlying functor. This is the
`hom_underlying` clause of the correspondence of Stacks 04X5; no heterogeneous equality is needed,
the two functors having the same type. -/
@[simp, stacks 04X5 "that bijection, on the underlying functor"]
lemma algebraicStackConstructionHomEquiv_val_hom_toFunctor
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (φ : 𝒳 ⟶ 𝒴) :
    (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 φ).val.hom.toFunctor =
      φ.hom.hom.toFunctor :=
  rfl

/-- Construction A preserves the identity 1-morphism. -/
@[simp, stacks 04X5 "that bijection carries the identity to the identity"]
lemma algebraicStackConstructionHomEquiv_id (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒳 (𝟙 𝒳) =
      AlgebraicStackPairHom.id B S S' hS hS' g
        (algebraicStackConstructionA B S S' hS hS' g 𝒳) :=
  rfl

/-- Construction A preserves composition of 1-morphisms. -/
@[simp, stacks 04X5 "that bijection is compatible with composition"]
lemma algebraicStackConstructionHomEquiv_comp {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (φ : 𝒳 ⟶ 𝒴) (ψ : 𝒴 ⟶ 𝒵) :
    algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒵 (φ ≫ ψ) =
      AlgebraicStackPairHom.comp B S S' hS hS' g
        (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 φ)
        (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒴 𝒵 ψ) :=
  rfl

/-- **Constructions A and B of Stacks 04X5 are bijective on 2-morphisms**, and both are the
identity on the underlying morphism of functors. The only thing to transfer is the condition that
a component lie over an identity, and that is unchanged by the relocalization functor by
`CategoryTheory.Functor.isHomLift_overMap_iff`. -/
@[stacks 04X5 "the bijection on 2-morphisms"]
def algebraicStackConstructionHom₂Equiv {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (φ ψ : 𝒳 ⟶ 𝒴) :
    (φ ⟶ ψ) ≃ AlgebraicStackPairHom₂ B S S' hS hS' g
      (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 φ)
      (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 ψ) where
  toFun η :=
    ⟨{ toNatTrans := η.hom.hom.toNatTrans
       isHomLift' := fun x ↦
        (Functor.isHomLift_overMap_iff 𝒴.val.val.p g (𝟙 (𝒳.val.val.p.obj x))
          (η.hom.hom.toNatTrans.app x) (BasedFunctor.w_obj φ.hom.hom x)
          (BasedFunctor.w_obj ψ.hom.hom x)).2 (η.hom.hom.isHomLift' x) }⟩
  invFun η :=
    ⟨⟨{ toNatTrans := η.hom.toNatTrans
        isHomLift' := fun x ↦
          (Functor.isHomLift_overMap_iff 𝒴.val.val.p g (𝟙 (𝒳.val.val.p.obj x))
            (η.hom.toNatTrans.app x) (BasedFunctor.w_obj φ.hom.hom x)
            (BasedFunctor.w_obj ψ.hom.hom x)).1 (η.hom.isHomLift' x) }⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection on 2-morphisms is the identity on the underlying morphism of functors. This is
the `twoHom_underlying` clause of the correspondence of Stacks 04X5. -/
@[simp, stacks 04X5 "the 2-morphism bijection, on the underlying natural transformation"]
lemma algebraicStackConstructionHom₂Equiv_hom_toNatTrans
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {φ ψ : 𝒳 ⟶ 𝒴} (η : φ ⟶ ψ) :
    (algebraicStackConstructionHom₂Equiv B S S' hS hS' g φ ψ η).hom.toNatTrans =
      η.hom.hom.toNatTrans :=
  rfl

/-- Construction A preserves identity 2-morphisms. -/
@[simp, stacks 04X5 "the 2-morphism bijection carries the identity to the identity"]
lemma algebraicStackConstructionHom₂Equiv_id {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (φ : 𝒳 ⟶ 𝒴) :
    algebraicStackConstructionHom₂Equiv B S S' hS hS' g φ φ (𝟙 φ) = 𝟙 _ :=
  rfl

/-- Construction A preserves vertical composition of 2-morphisms. -/
@[simp, stacks 04X5 "the 2-morphism bijection is compatible with vertical composition"]
lemma algebraicStackConstructionHom₂Equiv_comp {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {φ ψ χ : 𝒳 ⟶ 𝒴} (η : φ ⟶ ψ) (θ : ψ ⟶ χ) :
    algebraicStackConstructionHom₂Equiv B S S' hS hS' g φ χ (η ≫ θ) =
      algebraicStackConstructionHom₂Equiv B S S' hS hS' g φ ψ η ≫
        algebraicStackConstructionHom₂Equiv B S S' hS hS' g ψ χ θ :=
  rfl

/-- Construction A preserves left whiskering. -/
@[simp, stacks 04X5 "the 2-morphism bijection is compatible with left whiskering"]
lemma algebraicStackConstructionHom₂Equiv_whiskerLeft
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (a : 𝒳 ⟶ 𝒴) {φ ψ : 𝒴 ⟶ 𝒵} (η : φ ⟶ ψ) :
    algebraicStackConstructionHom₂Equiv B S S' hS hS' g (a ≫ φ) (a ≫ ψ)
        (Bicategory.whiskerLeft a η) =
      Bicategory.whiskerLeft (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 a).val
        (algebraicStackConstructionHom₂Equiv B S S' hS hS' g φ ψ η) :=
  rfl

/-- Construction A preserves right whiskering. -/
@[simp, stacks 04X5 "the 2-morphism bijection is compatible with right whiskering"]
lemma algebraicStackConstructionHom₂Equiv_whiskerRight
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {φ ψ : 𝒳 ⟶ 𝒴} (η : φ ⟶ ψ) (a : 𝒴 ⟶ 𝒵) :
    algebraicStackConstructionHom₂Equiv B S S' hS hS' g (φ ≫ a) (ψ ≫ a)
        (Bicategory.whiskerRight η a) =
      Bicategory.whiskerRight (algebraicStackConstructionHom₂Equiv B S S' hS hS' g φ ψ η)
        (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒴 𝒵 a).val :=
  rfl

/-! ### The correspondence as a single object -/

/-- **The canonical correspondence between the 2-category of algebraic stacks over `S` and the
2-category of algebraic stacks over `S'` mapping to the stack represented by `S`.**

The first field records that the right-hand 2-category is non-degenerate, in that the base
`S/S'` it is sliced over is itself an algebraic stack over `S'`. The remaining fields are the
three bijections — on objects, on 1-morphisms and on 2-morphisms — together with the
identifications pinning what each of them does to the underlying data, and the compatibility of
the bijections with identities, composition and the two whiskerings. Both the hom and the
2-hom bijection are the identity on the underlying functor and natural transformation
respectively, which is what makes the two 2-categories isomorphic rather than merely
equivalent. -/
structure AlgebraicStackCorrespondence
    (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') where
  /-- the base of the right-hand 2-category is an algebraic stack over `S'` -/
  representedBaseIsAlgebraic :
    IsAlgebraicStack.{u, w} B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val
  /-- Constructions A and B are mutually inverse on objects -/
  objectEquiv : AlgebraicStacks.{u, w} B S hS ≃ AlgebraicStackPair.{u, w} B S S' hS hS' g
  /-- the object bijection is Construction A on the underlying category -/
  object_underlying (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (objectEquiv 𝒳).1.val.val = changeBase B S S' hS hS' g 𝒳.val.val
  /-- the 1-morphism to the represented base is the structure functor read through the
  iterated-slice identification -/
  object_structure (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (objectEquiv 𝒳).2.hom.toFunctor =
      (object_underlying 𝒳).symm ▸
        (𝒳.val.val.p ⋙ (Over.iteratedSliceEquiv (Over.mk g)).inverse)
  /-- Constructions A and B are mutually inverse on 1-morphisms -/
  homEquiv (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) :
    (𝒳 ⟶ 𝒴) ≃ AlgebraicStackPairHom B S S' hS hS' g (objectEquiv 𝒳) (objectEquiv 𝒴)
  /-- the 1-morphism bijection is the identity on the underlying functor -/
  hom_underlying (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) (φ : 𝒳 ⟶ 𝒴) :
    HEq ((homEquiv 𝒳 𝒴 φ).val.hom.toFunctor) φ.hom.hom.toFunctor
  /-- the 1-morphism bijection preserves identities -/
  hom_id (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    homEquiv 𝒳 𝒳 (𝟙 𝒳) = AlgebraicStackPairHom.id B S S' hS hS' g (objectEquiv 𝒳)
  /-- the 1-morphism bijection preserves composition -/
  hom_comp {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (φ : 𝒳 ⟶ 𝒴) (ψ : 𝒴 ⟶ 𝒵) :
    homEquiv 𝒳 𝒵 (φ ≫ ψ) =
      AlgebraicStackPairHom.comp B S S' hS hS' g (homEquiv 𝒳 𝒴 φ) (homEquiv 𝒴 𝒵 ψ)
  /-- Constructions A and B are mutually inverse on 2-morphisms -/
  twoHomEquiv {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (φ ψ : 𝒳 ⟶ 𝒴) :
    (φ ⟶ ψ) ≃ AlgebraicStackPairHom₂ B S S' hS hS' g (homEquiv 𝒳 𝒴 φ) (homEquiv 𝒳 𝒴 ψ)
  /-- the 2-morphism bijection is the identity on the underlying natural transformation -/
  twoHom_underlying {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {φ ψ : 𝒳 ⟶ 𝒴} (η : φ ⟶ ψ) :
    HEq (twoHomEquiv φ ψ η).hom.toNatTrans η.hom.hom.toNatTrans
  /-- the 2-morphism bijection preserves identities -/
  twoHom_id {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (φ : 𝒳 ⟶ 𝒴) :
    twoHomEquiv φ φ (𝟙 φ) = 𝟙 _
  /-- the 2-morphism bijection preserves vertical composition -/
  twoHom_comp {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {φ ψ χ : 𝒳 ⟶ 𝒴} (η : φ ⟶ ψ) (θ : ψ ⟶ χ) :
    twoHomEquiv φ χ (η ≫ θ) = twoHomEquiv φ ψ η ≫ twoHomEquiv ψ χ θ
  /-- the 2-morphism bijection preserves left whiskering -/
  twoHom_whiskerLeft {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (a : 𝒳 ⟶ 𝒴) {φ ψ : 𝒴 ⟶ 𝒵}
      (η : φ ⟶ ψ) :
    HEq (twoHomEquiv (a ≫ φ) (a ≫ ψ) (Bicategory.whiskerLeft a η))
      (Bicategory.whiskerLeft (homEquiv 𝒳 𝒴 a).val (twoHomEquiv φ ψ η))
  /-- the 2-morphism bijection preserves right whiskering -/
  twoHom_whiskerRight {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {φ ψ : 𝒳 ⟶ 𝒴} (η : φ ⟶ ψ)
      (a : 𝒴 ⟶ 𝒵) :
    HEq (twoHomEquiv (φ ≫ a) (ψ ≫ a) (Bicategory.whiskerRight η a))
      (Bicategory.whiskerRight (twoHomEquiv φ ψ η) (homEquiv 𝒴 𝒵 a).val)

/-- **Constructions A and B restrict to mutually inverse isomorphisms on objects, 1-morphisms and
2-morphisms of algebraic stacks.** This is the whole of the correspondence of Stacks 04X5 as a
single object, assembled from the components proved above; the algebraicity criterion
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff` is what makes its object map well
defined in both directions. -/
@[stacks 04X5 "the resulting equivalence of 2-categories"]
noncomputable def categoryOfAlgebraicStacksOverSmallerBaseScheme :
    AlgebraicStackCorrespondence.{u, w} B S S' hS hS' g where
  representedBaseIsAlgebraic :=
    isAlgebraicStack_schemeFibredCategory.{u, w} B S' hS' (Over.mk g)
  objectEquiv := algebraicStackConstructionObjEquiv.{u, w} B S S' hS hS' g
  object_underlying 𝒳 := algebraicStackConstructionA_val_val B S S' hS hS' g 𝒳
  object_structure 𝒳 := changeBaseStructureHom_toFunctor B S S' hS hS' g 𝒳
  homEquiv 𝒳 𝒴 := algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴
  hom_underlying _ _ φ :=
    heq_of_eq (algebraicStackConstructionHomEquiv_val_hom_toFunctor B S S' hS hS' g φ)
  hom_id 𝒳 := algebraicStackConstructionHomEquiv_id B S S' hS hS' g 𝒳
  hom_comp φ ψ := algebraicStackConstructionHomEquiv_comp B S S' hS hS' g φ ψ
  twoHomEquiv φ ψ := algebraicStackConstructionHom₂Equiv B S S' hS hS' g φ ψ
  twoHom_underlying η :=
    heq_of_eq (algebraicStackConstructionHom₂Equiv_hom_toNatTrans B S S' hS hS' g η)
  twoHom_id φ := algebraicStackConstructionHom₂Equiv_id B S S' hS hS' g φ
  twoHom_comp η θ := algebraicStackConstructionHom₂Equiv_comp B S S' hS hS' g η θ
  twoHom_whiskerLeft := fun {_ _ _} a {_ _} η ↦
    heq_of_eq (algebraicStackConstructionHom₂Equiv_whiskerLeft B S S' hS hS' g a η)
  twoHom_whiskerRight η a :=
    heq_of_eq (algebraicStackConstructionHom₂Equiv_whiskerRight B S S' hS hS' g η a)

end AlgebraicGeometry.Stack

end
