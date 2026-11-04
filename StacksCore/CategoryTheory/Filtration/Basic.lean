module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksCore.CategoryTheory.Limits.Shapes.Images
public import StacksCore.CategoryTheory.Subobject.Limits
import StacksCore.Tactic.StacksAttribute

/-! # Filtered objects

Stacks 0121 defines, for an abelian category `𝒜`, a decreasing filtration on an object `A` as
a family `(F^nA)_{n ∈ ℤ}` of subobjects with `F^{n+1}A ⊆ F^nA`, the category `Fil(𝒜)` of
filtered objects, and the induced, quotient, finite, separated and exhaustive filtrations.

Mathlib's `CategoryTheory.Filtration X I` is a filtration on `X` indexed by an arbitrary
category `I`: a functor `I ⥤ MonoOver X`, so that the steps and their inclusions into `X` are
bundled together and functorial in the index. `CategoryTheory.FilteredObject C I` is the
category of filtered objects of an arbitrary category `C`, with `FilteredObject.Hom` the
morphisms `φ : A ⟶ B` together with the induced maps `F^iA ⟶ F^iB`. Stacks' decreasing
`ℤ`-filtrations are the case `I := ℤᵒᵖ`: for `h : n ≤ m` the arrow `opHomOfLE h : op m ⟶ op n`
is sent to the inclusion `F^mA ⟶ F^nA`. (The index category `ℤᵒᵈ` would serve equally well;
`FilteredObject.opEquivOd` passes between the two conventions.)

This file adds the Stacks-facing vocabulary on top of the Mathlib definitions.

* `Filtration.subobject F i : Subobject X` is the `i`-th step as a subobject, and
  `Filtration.antitone` is the decreasing condition of 0121(1). Conversely
  `Filtration.ofAntitone` turns an antitone family `ℤ → Subobject X` into a filtration.
* `FilteredObject.factors` and `FilteredObject.homMk'` are the two directions of 0121(3): a
  morphism `φ : A ⟶ B` of `C` is a morphism of filtered objects if and only if
  `φ(F^iA) ⊆ F^iB` for all `i`; `FilteredObject.exists_subobject_le` is the first direction in
  the language of the image functor `Subobject.exists`.
* `Filtration.pullback` and `Filtration.pushforward` are the induced filtration
  `F^nX = X ∩ F^nA` of 0121(5) and the quotient filtration `F^nY = π(F^nA)` of 0121(6),
  defined along an arbitrary morphism rather than only a monomorphism or an epimorphism.
* `Filtration.HasInter`, `Filtration.HasUnion`, `Filtration.IsSeparated` and
  `Filtration.IsExhaustive` are 0121(8)-(9), phrased in the lattice `Subobject X`; finiteness,
  0121(7), lives in `StacksCore.CategoryTheory.Filtration.Finite`.
* `Filtration.step` is the inclusion `F^iX ⟶ F^jX` along an index arrow `i ⟶ j`;
  `FilteredObject.eval i` is the functor `A ↦ F^iA`; `FilteredObject.pullbackObj`/`pullbackHom`
  and `pushforwardObj`/`pushforwardHom` package the induced and quotient filtrations of 0121(5),(6)
  as filtered objects with their canonical morphisms.
* `Filtration.reindex` and `FilteredObject.reindex` reindex along a functor of index
  categories; `FilteredObject.reindexEquivalence` does so along an equivalence.
* `FilteredObject.forgetAdjOfTop` and `ofBotAdjForget` are the adjunctions `ofBot ⊣ forget ⊣ ofTop`
  with the trivially filtered objects `ofTop W` (steps `W`) and `ofBot W` (steps `⊥`, when `C` has
  an initial object with mono initial morphisms); hence the forgetful functor preserves all
  colimits and, under that hypothesis, all limits, in particular epimorphisms and monomorphisms,
  and being faithful it reflects both. This is the remark after 0121: a morphism of filtered
  objects is a monomorphism (epimorphism) if and only if its underlying morphism is
  (`forget.mono_map_iff_mono`, `forget.epi_map_iff_epi`); `mono_of_mono_hom` and `epi_of_epi_hom`
  are the reflection direction spelled on `f.hom`.
* `FilteredObject.isIso_iff` and `isIso_iff_isStrictHom`: a morphism of filtered objects is an
  isomorphism if and only if its underlying morphism and all its level maps `F^iA ⟶ F^iB` are,
  equivalently if and only if its underlying morphism is an isomorphism and it is cartesian
  (`IsStrictHom`); in particular isomorphisms are cartesian (`isStrictHom_of_isIso`). Cartesian
  morphisms are stable under base change once the fibre product is computed both on the
  underlying objects and on every step (`isStrictHom_of_isPullback`, by pasting).
* Functoriality of the induced and quotient filtrations in a commutative square over a morphism
  `u : A' ⟶ A` of filtered objects: `FilteredObject.pullbackMap : pullbackObj A' m' ⟶ pullbackObj
  A m` (cartesian when `u` is, `isStrictHom_pullbackMap`; an isomorphism over isomorphisms,
  `pullbackMapIso`) and `FilteredObject.pushforwardMap : pushforwardObj A' e' ⟶ pushforwardObj A
  e`, and the inclusion
  `pullbackObjHom : pullbackObj A (k ≫ n) ⟶ pullbackObj A n` of `X ⊆ Y ⊆ A` with their induced
  filtrations, which is cartesian (`isStrictHom_pullbackObjHom`), as is `pullbackHom A m`
  (`isStrictHom_pullbackHom`). Cartesian morphisms cancel on the right (`isStrictHom_of_comp`).
  This is the vocabulary of Stacks 0129 (`StacksCore.CategoryTheory.Filtration.Subquotient`).
-/

@[expose] public section

add_to_stacks 0121 "(1) for an arbitrary index category `I`; the tag is `I := ℤᵒᵖ`"
  CategoryTheory.Filtration
add_to_stacks 0121 "(2) filtered objects of an arbitrary category" CategoryTheory.FilteredObject
add_to_stacks 0121 "(3) morphisms of filtered objects, as `φ` together with the maps `F^iA ⟶ F^iB`"
  CategoryTheory.FilteredObject.Hom
add_to_stacks 0121 "(4) the category `Fil(𝒜)`" CategoryTheory.FilteredObject.instCategory
add_to_stacks 0121 "the forgetful functor `Fil(𝒜) ⥤ 𝒜`" CategoryTheory.FilteredObject.forget

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {I : Type*} [Category* I] {J : Type*} [Category* J]

namespace Filtration

variable {X : C}

/-- The `i`-th step of a filtration, as a subobject of `X`. -/
noncomputable abbrev subobject (F : Filtration X I) (i : I) : Subobject X :=
  Subobject.mk (F.ι.app i)

/-- The transition map `F^iX ⟶ F^jX` followed by the inclusion `F^jX ⟶ X` is the inclusion
`F^iX ⟶ X`. -/
@[reassoc]
lemma diagram_map_comp_ι_app (F : Filtration X I) {i j : I} (f : i ⟶ j) :
    F.diagram.map f ≫ F.ι.app j = F.ι.app i := by
  simpa using F.ι.naturality f

/-- The transition maps of a filtration are monomorphisms. -/
instance (F : Filtration X I) {i j : I} (f : i ⟶ j) : Mono (F.diagram.map f) :=
  mono_of_mono_fac (F.diagram_map_comp_ι_app f)

/-- The step morphism `F^iX ⟶ F^jX` of a filtration along an index arrow `f : i ⟶ j`. This is
`F.diagram.map f`, wrapped in a definition so that `simp` does not unfold it through
`Functor.comp_map`; conversely `simp` folds `F.diagram.map f` back into `F.step f` through
`toMonoOver_map_hom_left`. -/
def step (F : Filtration X I) {i j : I} (f : i ⟶ j) : F.obj i ⟶ F.obj j :=
  F.diagram.map f

/-- The step `F^iX ⟶ F^jX` followed by the inclusion `F^jX ⟶ X` is the inclusion `F^iX ⟶ X`. -/
@[reassoc (attr := simp)]
lemma step_comp_ι_app (F : Filtration X I) {i j : I} (f : i ⟶ j) :
    F.step f ≫ F.ι.app j = F.ι.app i :=
  F.diagram_map_comp_ι_app f

/-- The steps of a filtration are monomorphisms. -/
instance (F : Filtration X I) {i j : I} (f : i ⟶ j) : Mono (F.step f) :=
  inferInstanceAs (Mono (F.diagram.map f))

/-- The step along an identity arrow is the identity. -/
@[simp] lemma step_id (F : Filtration X I) (i : I) : F.step (𝟙 i) = 𝟙 _ :=
  F.diagram.map_id i

/-- The steps of a filtration compose as the index arrows. -/
@[reassoc (attr := simp)]
lemma step_comp (F : Filtration X I) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    F.step f ≫ F.step g = F.step (f ≫ g) :=
  (F.diagram.map_comp f g).symm

/-- The step in the form `simp` produces after unfolding `diagram` (through `Functor.comp_map` and
`Over.forget_map`); folding it back lets the `step` lemmas fire. -/
@[simp] lemma toMonoOver_map_hom_left (F : Filtration X I) {i j : I} (f : i ⟶ j) :
    (F.toMonoOver.map f).hom.left = F.step f := rfl

/-- The steps of a filtration are ordered as the index category. -/
lemma subobject_le_of_hom (F : Filtration X I) {i j : I} (f : i ⟶ j) :
    F.subobject i ≤ F.subobject j :=
  Subobject.mk_le_mk_of_comm (F.diagram.map f) (F.diagram_map_comp_ι_app f)

/-- Stacks 0121(1): a filtration indexed by `ℤᵒᵖ` is decreasing, `F^mA ⊆ F^nA` for `n ≤ m`. -/
@[stacks 0121 "(1) the decreasing condition, for `I := ℤᵒᵖ`"]
lemma antitone (F : Filtration X ℤᵒᵖ) : Antitone fun n : ℤ => F.subobject (op n) :=
  fun _ _ h => F.subobject_le_of_hom (opHomOfLE h)

/-- Stacks 0121(1), conversely: a decreasing family `F : ℤ → Subobject X` of subobjects is a
filtration indexed by `ℤᵒᵖ`, whose `n`-th step is (the underlying object of) `F n`. -/
@[implicit_reducible,
  stacks 0121 "(1) a decreasing family of subobjects, as a filtration indexed by `ℤᵒᵖ`"]
noncomputable def ofAntitone (F : ℤ → Subobject X) (hF : Antitone F) : Filtration X ℤᵒᵖ where
  toMonoOver :=
    { obj n := ⟨Over.mk (F n.unop).arrow, inferInstanceAs (Mono (F n.unop).arrow)⟩
      map f := MonoOver.homMk (Subobject.ofLE _ _ (hF (leOfHom f.unop))) (Subobject.ofLE_arrow _)
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }

/-- The `n`-th step of `ofAntitone F hF` is the underlying object of `F n`. -/
lemma ofAntitone_obj (F : ℤ → Subobject X) (hF : Antitone F) (n : ℤ) :
    (ofAntitone F hF).obj (op n) = (F n : C) := rfl

/-- The inclusion of the `n`-th step of `ofAntitone F hF` is the arrow of `F n`. -/
@[simp]
lemma ofAntitone_ι_app (F : ℤ → Subobject X) (hF : Antitone F) (n : ℤ) :
    (ofAntitone F hF).ι.app (op n) = (F n).arrow := rfl

/-- The `n`-th step of `ofAntitone F hF`, as a subobject, is `F n`. -/
@[simp]
lemma subobject_ofAntitone (F : ℤ → Subobject X) (hF : Antitone F) (n : ℤ) :
    (ofAntitone F hF).subobject (op n) = F n :=
  Subobject.mk_arrow _

/-- Reindex a filtration along a functor `e : J ⥤ I` of index categories. -/
@[implicit_reducible]
def reindex (e : J ⥤ I) (F : Filtration X I) : Filtration X J :=
  ⟨e ⋙ F.toMonoOver⟩

/-- The `j`-th step of `F.reindex e` is the `e j`-th step of `F`. -/
lemma reindex_obj (e : J ⥤ I) (F : Filtration X I) (j : J) :
    (F.reindex e).obj j = F.obj (e.obj j) := rfl

/-- The inclusion of the `j`-th step of `F.reindex e` is that of the `e j`-th step of `F`. -/
@[simp]
lemma reindex_ι_app (e : J ⥤ I) (F : Filtration X I) (j : J) :
    (F.reindex e).ι.app j = F.ι.app (e.obj j) := rfl

section Pullback

variable [HasPullbacks C]

/-- The pullback filtration `f⁻¹F` along `f : Y ⟶ X`, with steps `Y ×_X F^iX`. For a
monomorphism `f` this is the induced filtration `F^iY = Y ∩ F^iX` of Stacks 0121(5). -/
@[implicit_reducible,
  stacks 0121 "(5) the induced filtration, along any morphism `f`; the tag is `f` a monomorphism"]
noncomputable def pullback (F : Filtration X I) {Y : C} (f : Y ⟶ X) : Filtration Y I where
  toMonoOver :=
    { obj i := ⟨Over.mk (pullback.snd (F.ι.app i) f), inferInstanceAs (Mono (pullback.snd _ _))⟩
      map g := MonoOver.homMk
        (pullback.lift (pullback.fst _ _ ≫ F.step g) (pullback.snd _ _)
          (by rw [Category.assoc, step_comp_ι_app, pullback.condition]))
        (pullback.lift_snd _ _ _)
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }

/-- The `i`-th step of `F.pullback f` is the fibre product `F^iX ×_X Y`. -/
lemma pullback_obj (F : Filtration X I) {Y : C} (f : Y ⟶ X) (i : I) :
    (F.pullback f).obj i = Limits.pullback (F.ι.app i) f := rfl

/-- The inclusion of the `i`-th step of `F.pullback f` is the second projection of
`F^iX ×_X Y`. -/
@[simp]
lemma pullback_ι_app (F : Filtration X I) {Y : C} (f : Y ⟶ X) (i : I) :
    (F.pullback f).ι.app i = pullback.snd (F.ι.app i) f := rfl

/-- The steps of the pullback filtration, in the form `simp` produces after unfolding
`diagram`; this lets `simp` close goals about `(F.pullback f).ι.app i`. -/
@[simp]
lemma pullback_toMonoOver_obj_obj_left (F : Filtration X I) {Y : C} (f : Y ⟶ X) (i : I) :
    ((F.pullback f).toMonoOver.obj i).obj.left = Limits.pullback (F.ι.app i) f := rfl

/-- The steps of the pullback filtration are the preimages `f⁻¹(F^iX)`. -/
lemma subobject_pullback (F : Filtration X I) {Y : C} (f : Y ⟶ X) (i : I) :
    (F.pullback f).subobject i = (Subobject.pullback f).obj (F.subobject i) :=
  (Subobject.pullback_obj_mk (IsPullback.of_hasPullback (F.ι.app i) f)).symm

end Pullback

section Pushforward

variable [HasImages C]

/-- The image filtration `π(F)` along `π : X ⟶ Y`, with steps the images of `F^iX ⟶ X ⟶ Y`.
For an epimorphism `π` this is the quotient filtration `F^iY = π(F^iX)` of Stacks 0121(6). -/
@[implicit_reducible,
  stacks 0121 "(6) the quotient filtration, along any morphism `π`; the tag is `π` an epimorphism"]
noncomputable def pushforward (F : Filtration X I) {Y : C} (g : X ⟶ Y) : Filtration Y I where
  toMonoOver :=
    { obj i := ⟨Over.mk (image.ι (F.ι.app i ≫ g)), inferInstanceAs (Mono (image.ι _))⟩
      map {i j} k := MonoOver.homMk
        (image.lift
          { I := image (F.ι.app j ≫ g)
            m := image.ι _
            e := F.step k ≫ factorThruImage _
            fac := by rw [Category.assoc, image.fac, step_comp_ι_app_assoc] })
        (image.lift_fac _)
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }

/-- The `i`-th step of `F.pushforward g` is the image of `F^iX ⟶ X ⟶ Y`. -/
lemma pushforward_obj (F : Filtration X I) {Y : C} (g : X ⟶ Y) (i : I) :
    (F.pushforward g).obj i = image (F.ι.app i ≫ g) := rfl

/-- The inclusion of the `i`-th step of `F.pushforward g` is the image inclusion of
`F^iX ⟶ X ⟶ Y`. -/
@[simp]
lemma pushforward_ι_app (F : Filtration X I) {Y : C} (g : X ⟶ Y) (i : I) :
    (F.pushforward g).ι.app i = image.ι (F.ι.app i ≫ g) := rfl

/-- The steps of the image filtration, in the form `simp` produces after unfolding `diagram`;
this lets `simp` close goals about `(F.pushforward g).ι.app i`. -/
@[simp]
lemma pushforward_toMonoOver_obj_obj_left (F : Filtration X I) {Y : C} (g : X ⟶ Y) (i : I) :
    ((F.pushforward g).toMonoOver.obj i).obj.left = image (F.ι.app i ≫ g) := rfl

/-- The steps of the image filtration are the images `g(F^iX)`. -/
lemma subobject_pushforward (F : Filtration X I) {Y : C} (g : X ⟶ Y) (i : I) :
    (F.pushforward g).subobject i = (Subobject.exists g).obj (F.subobject i) :=
  (Subobject.exists_mk_eq_imageSubobject (F.ι.app i) g).symm

end Pushforward

/-- Stacks 0121(8): `⋂ F^iA` exists, i.e. the steps have a greatest lower bound in
`Subobject X`. -/
@[stacks 0121 "(8) existence of `⋂ F^iA`, as a greatest lower bound in `Subobject A`"]
def HasInter (F : Filtration X I) : Prop := ∃ S, IsGLB (Set.range F.subobject) S

/-- Stacks 0121(8): `⋃ F^iA` exists, i.e. the steps have a least upper bound in `Subobject X`. -/
@[stacks 0121 "(8) existence of `⋃ F^iA`, as a least upper bound in `Subobject A`"]
def HasUnion (F : Filtration X I) : Prop := ∃ S, IsLUB (Set.range F.subobject) S

/-- Stacks 0121(9): a filtration is separated if `⋂ F^iA = 0`. -/
@[stacks 0121 "(9) separated"]
def IsSeparated [HasInitial C] [InitialMonoClass C] (F : Filtration X I) : Prop :=
  IsGLB (Set.range F.subobject) ⊥

/-- Stacks 0121(9): a filtration is exhaustive if `⋃ F^iA = A`. -/
@[stacks 0121 "(9) exhaustive"]
def IsExhaustive (F : Filtration X I) : Prop := IsLUB (Set.range F.subobject) ⊤

/-- The trivial filtration `F^iX = X`. -/
@[implicit_reducible]
def top (X : C) : Filtration X I :=
  ⟨(Functor.const I).obj ⟨Over.mk (𝟙 X), inferInstanceAs (Mono (𝟙 X))⟩⟩

/-- The inclusions of the steps of the trivial filtration `F^iX = X` are identities. -/
@[simp] lemma top_ι_app (X : C) (i : I) : (top (I := I) X).ι.app i = 𝟙 X := rfl

/-- The steps of the trivial filtration `F^iX = X`, in the form `simp` produces after unfolding
`diagram`; this lets `simp` close goals about `(top X).ι.app i`. -/
@[simp] lemma top_toMonoOver_obj_obj_left (X : C) (i : I) :
    ((top (I := I) X).toMonoOver.obj i).obj.left = X := rfl

section Bot

variable [HasInitial C] [InitialMonoClass C]

/-- The trivial filtration `F^iX = ⊥`. -/
@[implicit_reducible]
noncomputable def bot (X : C) : Filtration X I :=
  ⟨(Functor.const I).obj ⟨Over.mk (initial.to X), inferInstanceAs (Mono (initial.to X))⟩⟩

/-- The inclusions of the steps of the trivial filtration `F^iX = ⊥` are the morphisms out of
the initial object. -/
@[simp] lemma bot_ι_app (X : C) (i : I) : (bot (I := I) X).ι.app i = initial.to X := rfl

/-- The steps of the trivial filtration `F^iX = ⊥`, in the form `simp` produces after unfolding
`diagram`; this lets `simp` close goals about `(bot X).ι.app i`. -/
@[simp] lemma bot_toMonoOver_obj_obj_left (X : C) (i : I) :
    ((bot (I := I) X).toMonoOver.obj i).obj.left = ⊥_ C := rfl

end Bot

end Filtration

namespace FilteredObject

variable {A B : FilteredObject C I}

/-- `F^iA` as a subobject of `A.X`. -/
noncomputable abbrev subobject (A : FilteredObject C I) (i : I) : Subobject A.X :=
  A.filtration.subobject i

/-- The level maps of a morphism of filtered objects commute with the steps. -/
@[reassoc (attr := simp)]
lemma step_natTrans_app (φ : A ⟶ B) {i j : I} (f : i ⟶ j) :
    A.filtration.step f ≫ φ.natTrans.app j = φ.natTrans.app i ≫ B.filtration.step f :=
  φ.natTrans.naturality f

/-- Evaluation at a step: the functor `A ↦ F^iA`, `φ ↦ φ|_{F^iA}`. -/
@[implicit_reducible, simps]
def eval (i : I) : FilteredObject C I ⥤ C where
  obj A := A.filtration.obj i
  map φ := φ.natTrans.app i

/-- Level maps of a morphism whose underlying morphism is a monomorphism are monomorphisms. -/
lemma mono_natTrans_app_of_mono_hom (f : A ⟶ B) [Mono f.hom] (i : I) :
    Mono (f.natTrans.app i) :=
  have : Mono (A.filtration.ι.app i ≫ f.hom) := mono_comp _ _
  mono_of_mono_fac (f.comm i)

section PullbackObj

variable [HasPullbacks C]

/-- `Y` with the filtration pulled back from `A` along `m : Y ⟶ A.X`; for a monomorphism `m` this
is `Y ⊆ A` with the induced filtration `F^iY = Y ∩ F^iA` of Stacks 0121 (5). -/
noncomputable abbrev pullbackObj (A : FilteredObject C I) {Y : C} (m : Y ⟶ A.X) :
    FilteredObject C I :=
  ⟨Y, A.filtration.pullback m⟩

/-- `m` as a morphism of filtered objects out of `pullbackObj A m`. -/
noncomputable abbrev pullbackHom (A : FilteredObject C I) {Y : C} (m : Y ⟶ A.X) :
    pullbackObj A m ⟶ A :=
  homMk m (fun _ => pullback.fst _ _) (fun _ => pullback.condition)

/-- The underlying morphism of `pullbackHom A m` is `m`. -/
@[simp] lemma pullbackHom_hom (A : FilteredObject C I) {Y : C} (m : Y ⟶ A.X) :
    (pullbackHom A m).hom = m := rfl

/-- The level maps of `pullbackHom A m` are the first projections of the fibre products. -/
@[simp] lemma pullbackHom_natTrans_app (A : FilteredObject C I) {Y : C} (m : Y ⟶ A.X) (i : I) :
    (pullbackHom A m).natTrans.app i = pullback.fst (A.filtration.ι.app i) m := rfl

/-- The induced filtration is cartesian over `A`. For `X ⊆ Y ⊆ A` and `m = k ≫ n` this makes
`X → A` strict (Stacks 0129), through `IsStrictHom.isStrict`; no hypothesis on `k`, `n`. -/
@[stacks 0129 "`X → A` is strict, for any `k`, `n`"]
instance isStrictHom_pullbackHom (A : FilteredObject C I) {Y : C} (m : Y ⟶ A.X) :
    IsStrictHom (pullbackHom A m) where
  isPullback i := IsPullback.of_hasPullback (A.filtration.ι.app i) m

/-- The steps of the induced filtration are the preimages `m⁻¹(F^iA)`. -/
lemma pullbackObj_subobject (A : FilteredObject C I) {Y : C} (m : Y ⟶ A.X) (i : I) :
    (pullbackObj A m).subobject i = (Subobject.pullback m).obj (A.subobject i) :=
  Filtration.subobject_pullback _ _ _

end PullbackObj

section IsStrictHomPullback

variable {P M D A : FilteredObject C I}

/-- Cartesian morphisms are stable under base change, diagrammatically: if `m : M ⟶ A` is
cartesian and the square `fst, snd, m, g` is a fibre product both on the underlying objects and
on every step, then `snd : P ⟶ D` is cartesian. Indeed the rectangle
`F^iP ⟶ F^iM ⟶ M, F^iD ⟶ F^iA ⟶ A` is a pullback (pasting), and it is also the rectangle
`F^iP ⟶ P ⟶ M, F^iD ⟶ D ⟶ A` whose right square is the underlying fibre product; cancel it.
No hypothesis on `𝒜` or `I`. -/
theorem isStrictHom_of_isPullback {fst : P ⟶ M} {snd : P ⟶ D} {m : M ⟶ A} {g : D ⟶ A}
    [IsStrictHom m] (hX : IsPullback fst.hom snd.hom m.hom g.hom)
    (h : ∀ i, IsPullback (fst.natTrans.app i) (snd.natTrans.app i) (m.natTrans.app i)
      (g.natTrans.app i)) :
    IsStrictHom snd where
  isPullback i := by
    have big : IsPullback (P.filtration.ι.app i ≫ fst.hom) (snd.natTrans.app i) m.hom
        (D.filtration.ι.app i ≫ g.hom) := by
      have := (h i).paste_horiz (IsStrictHom.isPullback m i).flip
      rwa [fst.comm i, g.comm i] at this
    exact (big.of_right (snd.comm i).symm hX).flip

end IsStrictHomPullback

section PushforwardObj

variable [HasImages C]

/-- `Z` with the image filtration from `A` along `e : A.X ⟶ Z`; for an epimorphism `e` this is
the quotient with the quotient filtration `F^iZ = e(F^iA)` of Stacks 0121 (6). -/
noncomputable abbrev pushforwardObj (A : FilteredObject C I) {Z : C} (e : A.X ⟶ Z) :
    FilteredObject C I :=
  ⟨Z, A.filtration.pushforward e⟩

/-- `e` as a morphism of filtered objects into `pushforwardObj A e`. -/
noncomputable abbrev pushforwardHom (A : FilteredObject C I) {Z : C} (e : A.X ⟶ Z) :
    A ⟶ pushforwardObj A e :=
  homMk e (fun i => factorThruImage (A.filtration.ι.app i ≫ e)) (fun _ => image.fac _)

/-- The underlying morphism of `pushforwardHom A e` is `e`. -/
@[simp] lemma pushforwardHom_hom (A : FilteredObject C I) {Z : C} (e : A.X ⟶ Z) :
    (pushforwardHom A e).hom = e := rfl

/-- The level maps of `pushforwardHom A e` are the factorisations through the images. -/
@[simp] lemma pushforwardHom_natTrans_app (A : FilteredObject C I) {Z : C} (e : A.X ⟶ Z)
    (i : I) :
    (pushforwardHom A e).natTrans.app i = factorThruImage (A.filtration.ι.app i ≫ e) := rfl

/-- The steps of the image filtration are the images `e(F^iA)`. -/
lemma pushforwardObj_subobject (A : FilteredObject C I) {Z : C} (e : A.X ⟶ Z) (i : I) :
    (pushforwardObj A e).subobject i = (Subobject.exists e).obj (A.subobject i) :=
  Filtration.subobject_pushforward _ _ _

end PushforwardObj

/-- Stacks 0121(3), one direction: a morphism of filtered objects satisfies `φ(F^iA) ⊆ F^iB`. -/
@[stacks 0121 "(3) a morphism of filtered objects satisfies `φ(F^iA) ⊆ F^iB`"]
lemma factors (f : A ⟶ B) (i : I) :
    (B.subobject i).Factors (A.filtration.ι.app i ≫ f.hom) :=
  (Subobject.mk_factors_iff _ _).2 ⟨f.natTrans.app i, f.comm i⟩

/-- Stacks 0121(3), the other direction: a morphism `φ : A ⟶ B` with `φ(F^iA) ⊆ F^iB` for all
`i` is a morphism of filtered objects. -/
@[stacks 0121 "(3) `φ` with `φ(F^iA) ⊆ F^iB` for all `i` is a morphism of filtered objects"]
noncomputable def homMk' (φ : A.X ⟶ B.X)
    (h : ∀ i, (B.subobject i).Factors (A.filtration.ι.app i ≫ φ)) : A ⟶ B :=
  homMk φ (fun i => ((Subobject.mk_factors_iff _ _).1 (h i)).choose)
    (fun i => ((Subobject.mk_factors_iff _ _).1 (h i)).choose_spec)

/-- The underlying morphism of `homMk' φ h` is `φ`. -/
@[simp]
lemma homMk'_hom (φ : A.X ⟶ B.X) (h : ∀ i, (B.subobject i).Factors (A.filtration.ι.app i ≫ φ)) :
    (homMk' φ h).hom = φ := rfl

/-- A morphism of filtered objects maps each step into the corresponding step: `f(F^iA) ⊆ F^iB`.
This is the first direction of Stacks 0121 (3) (`factors`) in the language of the image functor
`Subobject.exists`. -/
lemma exists_subobject_le [HasImages C] (f : A ⟶ B) (i : I) :
    (Subobject.exists f.hom).obj (A.subobject i) ≤ B.subobject i :=
  (Subobject.exists_mk_eq_imageSubobject (A.filtration.ι.app i) f.hom).trans_le
    (imageSubobject_le_mk _ _ (f.natTrans.app i) (f.comm i))

/-- Morphisms of filtered objects are determined by their underlying morphisms. -/
instance : (forget (C := C) (I := I)).Faithful where
  map_injective h := hom_ext h

/-- A morphism of filtered objects whose underlying morphism is a monomorphism is a
monomorphism: the forgetful functor is faithful, so it reflects monomorphisms. The converse is
`forget.map_mono`, once `C` has an initial object with mono initial morphisms (the forgetful
functor is then a right adjoint, `ofBotAdjForget`).

Not an instance, following `Over.mono_of_mono_left`. -/
theorem mono_of_mono_hom (f : A ⟶ B) [h : Mono f.hom] : Mono f :=
  (forget (C := C) (I := I)).mono_of_mono_map h

/-- A morphism of filtered objects whose underlying morphism is an epimorphism is an
epimorphism: the forgetful functor is faithful, so it reflects epimorphisms. The converse is
`forget.map_epi` (the forgetful functor is a left adjoint, `forgetAdjOfTop`).

Not an instance, following `Over.epi_of_epi_left`. -/
theorem epi_of_epi_hom (f : A ⟶ B) [h : Epi f.hom] : Epi f :=
  (forget (C := C) (I := I)).epi_of_epi_map h

/-- `W` with the trivial filtration `F^iW = W`. -/
abbrev ofTop (W : C) : FilteredObject C I := ⟨W, Filtration.top W⟩

/-- The trivial filtration `F^iW = W`, as a functor `C ⥤ FilteredObject C I`; it is right adjoint
to the forgetful functor (`forgetAdjOfTop`). -/
@[implicit_reducible, simps! obj map_hom map_natTrans_app]
def ofTopFunctor : C ⥤ FilteredObject C I where
  obj W := ofTop W
  map g := homMk g (fun _ => g) (fun _ => (Category.comp_id g).trans (Category.id_comp g).symm)

/-- `forget ⊣ ofTopFunctor`: a morphism `A ⟶ ofTop W` of filtered objects is just a morphism
`A.X ⟶ W`. Hence the forgetful functor is a left adjoint and preserves epimorphisms and all
colimits; being faithful it also reflects epimorphisms. This is the remark after Stacks 0121: a
morphism of filtered objects is an epimorphism if and only if its underlying morphism is, for
filtered objects of any category. -/
def forgetAdjOfTop : (forget (C := C) (I := I)) ⊣ ofTopFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv A _ :=
        { toFun g := homMk g (fun i => A.filtration.ι.app i ≫ g) (fun _ => Category.comp_id _)
          invFun φ := φ.hom
          left_inv _ := rfl
          right_inv _ := hom_ext rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := hom_ext rfl }

/-- The unit of `forgetAdjOfTop` at `A` has identity underlying morphism. -/
@[simp] lemma forgetAdjOfTop_unit_app_hom (A : FilteredObject C I) :
    ((forgetAdjOfTop (C := C) (I := I)).unit.app A).hom = 𝟙 A.X := rfl

/-- The counit of `forgetAdjOfTop` at `W` is the identity. -/
@[simp] lemma forgetAdjOfTop_counit_app (W : C) :
    (forgetAdjOfTop (C := C) (I := I)).counit.app W = 𝟙 W := rfl

/-- The forgetful functor from filtered objects is a left adjoint. -/
instance : (forget (C := C) (I := I)).IsLeftAdjoint := forgetAdjOfTop.isLeftAdjoint

section Bot

variable [HasInitial C] [InitialMonoClass C]

/-- `W` with the trivial filtration `F^iW = ⊥`. -/
noncomputable abbrev ofBot (W : C) : FilteredObject C I := ⟨W, Filtration.bot W⟩

/-- The trivial filtration `F^iW = ⊥`, as a functor `C ⥤ FilteredObject C I`; it is left adjoint
to the forgetful functor (`ofBotAdjForget`). -/
@[implicit_reducible, simps! obj map_hom map_natTrans_app]
noncomputable def ofBotFunctor : C ⥤ FilteredObject C I where
  obj W := ofBot W
  map g := homMk g (fun _ => 𝟙 _) (fun _ => initial.hom_ext _ _)

/-- `ofBotFunctor ⊣ forget`: a morphism `ofBot W ⟶ A` of filtered objects is just a morphism
`W ⟶ A.X`. Hence the forgetful functor is a right adjoint and preserves monomorphisms and all
limits; being faithful it also reflects monomorphisms. This is the remark after Stacks 0121: a
morphism of filtered objects is a monomorphism if and only if its underlying morphism is. Only an
initial object with mono initial morphisms is needed (for instance a zero object). -/
noncomputable def ofBotAdjForget : ofBotFunctor ⊣ (forget (C := C) (I := I)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun φ := φ.hom
          invFun g := homMk g (fun _ => initial.to _) (fun _ => initial.hom_ext _ _)
          left_inv _ := hom_ext rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := hom_ext rfl
      homEquiv_naturality_right _ _ := rfl }

/-- The unit of `ofBotAdjForget` at `W` is the identity. -/
@[simp] lemma ofBotAdjForget_unit_app (W : C) :
    (ofBotAdjForget (C := C) (I := I)).unit.app W = 𝟙 W := rfl

/-- The counit of `ofBotAdjForget` at `A` has identity underlying morphism. -/
@[simp] lemma ofBotAdjForget_counit_app_hom (A : FilteredObject C I) :
    ((ofBotAdjForget (C := C) (I := I)).counit.app A).hom = 𝟙 A.X := rfl

/-- The forgetful functor from filtered objects is a right adjoint. -/
instance : (forget (C := C) (I := I)).IsRightAdjoint := ofBotAdjForget.isRightAdjoint

end Bot

/-- The forgetful functor preserves isomorphisms: `IsIso f → IsIso f.hom`. This is Mathlib's
`forget.map_isIso` spelled on `f.hom`; not an instance, so that `f.hom`-level facts are derived
from `forget` explicitly. -/
theorem isIso_hom_of_isIso (f : A ⟶ B) [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((forget (C := C) (I := I)).map f))

/-- A morphism of filtered objects is an isomorphism if and only if its underlying morphism and
all of its level maps `F^iA ⟶ F^iB` are isomorphisms. -/
lemma isIso_iff (f : A ⟶ B) : IsIso f ↔ IsIso f.hom ∧ ∀ i, IsIso (f.natTrans.app i) := by
  refine ⟨fun _ => ⟨isIso_hom_of_isIso f, fun i => ⟨(inv f).natTrans.app i, ?_, ?_⟩⟩,
    fun ⟨_, _⟩ => ?_⟩
  · rw [← NatTrans.comp_app, ← comp_natTrans, IsIso.hom_inv_id, id_natTrans, NatTrans.id_app]
  · rw [← NatTrans.comp_app, ← comp_natTrans, IsIso.inv_hom_id, id_natTrans, NatTrans.id_app]
  · have e : f = (isoMk (asIso f.hom) (fun i => asIso (f.natTrans.app i))
        (fun i => by rw [asIso_hom, asIso_hom]; exact f.comm i)).hom :=
      hom_ext rfl
    rw [e]; infer_instance

/-- A morphism of filtered objects is an isomorphism if and only if its underlying morphism is
an isomorphism and it is strict in Mathlib's cartesian sense, `F^iA = f⁻¹(F^iB)` for all `i`. -/
lemma isIso_iff_isStrictHom (f : A ⟶ B) : IsIso f ↔ IsIso f.hom ∧ IsStrictHom f := by
  rw [isIso_iff]
  refine and_congr_right fun _ => ⟨fun _ => ⟨fun i => IsPullback.of_horiz_isIso ⟨f.comm i⟩⟩,
    fun h i => (h.isPullback i).isIso_fst_of_isIso⟩

/-- Isomorphisms of filtered objects are cartesian. -/
instance isStrictHom_of_isIso (f : A ⟶ B) [IsIso f] : IsStrictHom f :=
  ((isIso_iff_isStrictHom f).1 ‹_›).2

/-- Cartesian morphisms cancel on the right: if `f ≫ g` and `g` are cartesian then so is `f`
(`IsPullback.of_right`), the converse of Mathlib's instance for `f ≫ g`. Not an instance, since
`IsStrictHom (f ≫ g)` cannot be found from `f` alone. -/
theorem isStrictHom_of_comp {D : FilteredObject C I} (f : A ⟶ B) (g : B ⟶ D)
    [IsStrictHom (f ≫ g)] [IsStrictHom g] : IsStrictHom f where
  isPullback i :=
    (IsStrictHom.isPullback (f ≫ g) i).of_right (f.comm i) (IsStrictHom.isPullback g i)

section PullbackMap

variable [HasPullbacks C] {A' A : FilteredObject C I} (u : A' ⟶ A) {Y' Y : C} (m' : Y' ⟶ A'.X)
  (m : Y ⟶ A.X) (ψ : Y' ⟶ Y) (h : ψ ≫ m = m' ≫ u.hom)

/-- Functoriality of the induced filtration: a commutative square `ψ ≫ m = m' ≫ u.hom` with
`u : A' ⟶ A` a morphism of filtered objects induces `pullbackObj A' m' ⟶ pullbackObj A m` with
underlying morphism `ψ`, the level maps being the induced maps `pullback.map` on fibre
products. -/
@[implicit_reducible]
noncomputable def pullbackMap : pullbackObj A' m' ⟶ pullbackObj A m :=
  homMk ψ
    (fun i => pullback.map (A'.filtration.ι.app i) m' (A.filtration.ι.app i) m (u.natTrans.app i)
      ψ u.hom (u.comm i).symm h.symm)
    (fun _ => pullback.lift_snd _ _ _)

/-- The underlying morphism of `pullbackMap` is `ψ`. -/
@[simp] lemma pullbackMap_hom : (pullbackMap u m' m ψ h).hom = ψ := rfl

/-- The level maps of `pullbackMap` are the induced maps `pullback.map` on the fibre products;
`simp` unfolds them through this lemma and finishes with `pullback.lift_fst`/
`pullback.lift_snd`. -/
@[simp] lemma pullbackMap_natTrans_app (i : I) :
    (pullbackMap u m' m ψ h).natTrans.app i =
      pullback.map (A'.filtration.ι.app i) m' (A.filtration.ι.app i) m (u.natTrans.app i) ψ u.hom
        (u.comm i).symm h.symm := rfl

/-- The level maps of `pullbackMap` over the projections to the steps of `A'`, `A` (a `rw` lemma:
the left-hand side is not in simp normal form, see `pullbackMap_natTrans_app`). -/
lemma pullbackMap_natTrans_app_fst (i : I) :
    (pullbackMap u m' m ψ h).natTrans.app i ≫ pullback.fst (A.filtration.ι.app i) m =
      pullback.fst (A'.filtration.ι.app i) m' ≫ u.natTrans.app i :=
  pullback.lift_fst _ _ _

/-- The level maps of `pullbackMap` over the projections to `Y'`, `Y` (a `rw` lemma). -/
lemma pullbackMap_natTrans_app_snd (i : I) :
    (pullbackMap u m' m ψ h).natTrans.app i ≫ pullback.snd (A.filtration.ι.app i) m =
      pullback.snd (A'.filtration.ι.app i) m' ≫ ψ :=
  pullback.lift_snd _ _ _

/-- `pullbackMap` lies over `u`: the square `pullbackObj A' m' ⟶ pullbackObj A m ⟶ A` equals
`pullbackObj A' m' ⟶ A' ⟶ A`. -/
@[reassoc (attr := simp)]
lemma pullbackMap_comp_pullbackHom :
    pullbackMap u m' m ψ h ≫ pullbackHom A m = pullbackHom A' m' ≫ u :=
  hom_ext h

/-- The induced filtration is functorial in cartesian morphisms: if `u` is cartesian then so is
`pullbackMap u`, as `pullbackMap u ≫ pullbackHom A m = pullbackHom A' m' ≫ u` is cartesian and
`pullbackHom A m` is. -/
instance isStrictHom_pullbackMap [IsStrictHom u] : IsStrictHom (pullbackMap u m' m ψ h) :=
  have : IsStrictHom (pullbackMap u m' m ψ h ≫ pullbackHom A m) := by
    rw [pullbackMap_comp_pullbackHom]; infer_instance
  isStrictHom_of_comp _ (pullbackHom A m)

/-- `pullbackMap` over isomorphisms `u`, `ψ` is an isomorphism: it is cartesian and its
underlying morphism `ψ` is an isomorphism. -/
instance isIso_pullbackMap [IsIso u] [IsIso ψ] : IsIso (pullbackMap u m' m ψ h) :=
  (isIso_iff_isStrictHom _).2 ⟨inferInstanceAs (IsIso ψ), inferInstance⟩

end PullbackMap

section PullbackMapIso

variable [HasPullbacks C] {A' A : FilteredObject C I} (e : A' ≅ A) {Y' Y : C} (m' : Y' ⟶ A'.X)
  (m : Y ⟶ A.X) (ψ : Y' ≅ Y) (h : ψ.hom ≫ m = m' ≫ e.hom.hom)

/-- Transport of the induced filtration along isomorphisms: a commutative square
`ψ.hom ≫ m = m' ≫ e.hom.hom` with `e : A' ≅ A`, `ψ : Y' ≅ Y` induces
`pullbackObj A' m' ≅ pullbackObj A m`, with underlying isomorphism `ψ`. -/
noncomputable def pullbackMapIso : pullbackObj A' m' ≅ pullbackObj A m :=
  asIso (pullbackMap e.hom m' m ψ.hom h)

/-- The forward morphism of `pullbackMapIso` is `pullbackMap`. -/
@[simp] lemma pullbackMapIso_hom :
    (pullbackMapIso e m' m ψ h).hom = pullbackMap e.hom m' m ψ.hom h := rfl

end PullbackMapIso

section PullbackObjHom

variable [HasPullbacks C] (A : FilteredObject C I) {X Y : C} (k : X ⟶ Y) (n : Y ⟶ A.X)

/-- Inducing along `n : Y ⟶ A` and then along `k : X ⟶ Y` is inducing along `k ≫ n : X ⟶ A`:
the canonical morphism `pullbackObj A (k ≫ n) ⟶ pullbackObj A n` with underlying morphism `k`,
the level maps `X ∩ F^iA ⟶ Y ∩ F^iA` being induced on the fibre products. For monomorphisms
`k`, `n` this is the inclusion `X ⊆ Y` of subobjects `X ⊆ Y ⊆ A` with their induced
filtrations. (It is `pullbackMap (𝟙 A) (k ≫ n) n k _` up to `(𝟙 A).natTrans.app i = 𝟙 _`; the
direct construction gives the cleaner level maps.) -/
noncomputable def pullbackObjHom : pullbackObj A (k ≫ n) ⟶ pullbackObj A n :=
  homMk k
    (fun i => pullback.lift (pullback.fst (A.filtration.ι.app i) (k ≫ n))
      (pullback.snd (A.filtration.ι.app i) (k ≫ n) ≫ k)
      (pullback.condition.trans (Category.assoc _ _ _).symm))
    (fun _ => pullback.lift_snd _ _ _)

/-- The underlying morphism of `pullbackObjHom A k n` is `k`. -/
@[simp] lemma pullbackObjHom_hom : (pullbackObjHom A k n).hom = k := rfl

/-- The level maps of `pullbackObjHom` are the induced maps on the fibre products; `simp` unfolds
them through this lemma and finishes with `pullback.lift_fst`/`pullback.lift_snd`. -/
@[simp] lemma pullbackObjHom_natTrans_app (i : I) :
    (pullbackObjHom A k n).natTrans.app i =
      pullback.lift (pullback.fst (A.filtration.ι.app i) (k ≫ n))
        (pullback.snd (A.filtration.ι.app i) (k ≫ n) ≫ k)
        (pullback.condition.trans (Category.assoc _ _ _).symm) := rfl

/-- The level maps of `pullbackObjHom` over the projections to the steps of `A` (a `rw` lemma:
the left-hand side is not in simp normal form, see `pullbackObjHom_natTrans_app`). -/
lemma pullbackObjHom_natTrans_app_fst (i : I) :
    (pullbackObjHom A k n).natTrans.app i ≫ pullback.fst (A.filtration.ι.app i) n =
      pullback.fst (A.filtration.ι.app i) (k ≫ n) :=
  pullback.lift_fst _ _ _

/-- The level maps of `pullbackObjHom` over the projections to `X`, `Y` (a `rw` lemma). -/
lemma pullbackObjHom_natTrans_app_snd (i : I) :
    (pullbackObjHom A k n).natTrans.app i ≫ pullback.snd (A.filtration.ι.app i) n =
      pullback.snd (A.filtration.ι.app i) (k ≫ n) ≫ k :=
  pullback.lift_snd _ _ _

/-- `X → Y → A` is `X → A`, for the induced filtrations. -/
@[reassoc (attr := simp)]
lemma pullbackObjHom_comp_pullbackHom :
    pullbackObjHom A k n ≫ pullbackHom A n = pullbackHom A (k ≫ n) :=
  hom_ext rfl

/-- The filtration induced along `k ≫ n` is induced along `k` from the one induced along `n`,
`X ∩ F^iA = X ∩ (Y ∩ F^iA)`: `pullbackObjHom A k n` is cartesian, as its composite with the
cartesian `pullbackHom A n` is the cartesian `pullbackHom A (k ≫ n)`. No hypothesis on `k`, `n`.
Hence `X → Y` is strict (Stacks 0129), through `IsStrictHom.isStrict`.
(An instance: `pullbackObjHom` is a `def`, so type class search cannot derive this.) -/
@[stacks 0129 "`X → Y` is strict"]
instance isStrictHom_pullbackObjHom : IsStrictHom (pullbackObjHom A k n) :=
  have : IsStrictHom (pullbackObjHom A k n ≫ pullbackHom A n) := by
    rw [pullbackObjHom_comp_pullbackHom]; infer_instance
  isStrictHom_of_comp _ (pullbackHom A n)

end PullbackObjHom

section PushforwardMap

variable [HasImages C] [HasImageMaps C] {A' A : FilteredObject C I} (u : A' ⟶ A) {Z' Z : C}
  (e' : A'.X ⟶ Z') (e : A.X ⟶ Z) (φ : Z' ⟶ Z) (h : e' ≫ φ = u.hom ≫ e)

/-- Functoriality of the image filtration: a commutative square `e' ≫ φ = u.hom ≫ e` with
`u : A' ⟶ A` a morphism of filtered objects induces `pushforwardObj A' e' ⟶ pushforwardObj A e`
with underlying morphism `φ`, the level maps being the induced maps on images (`image.map`).
This needs image maps in `C`, for instance strong epi images as in any abelian category. -/
@[implicit_reducible]
noncomputable def pushforwardMap : pushforwardObj A' e' ⟶ pushforwardObj A e :=
  homMk φ
    (fun i => image.map (Arrow.homMk' (f := A'.filtration.ι.app i ≫ e')
      (g := A.filtration.ι.app i ≫ e) (u.natTrans.app i) φ
      (by rw [Category.assoc, h, ← Hom.comm_assoc])))
    (fun _ => image.map_ι _)

/-- The underlying morphism of `pushforwardMap` is `φ`. -/
@[simp] lemma pushforwardMap_hom : (pushforwardMap u e' e φ h).hom = φ := rfl

/-- The level maps of `pushforwardMap` are the maps `image.map` induced on the images; `simp`
unfolds them through this lemma and finishes with `image.map_ι` or
`factorThruImage_comp_image_map_homMk'`. -/
@[simp] lemma pushforwardMap_natTrans_app (i : I) :
    (pushforwardMap u e' e φ h).natTrans.app i =
      image.map (Arrow.homMk' (f := A'.filtration.ι.app i ≫ e')
        (g := A.filtration.ι.app i ≫ e) (u.natTrans.app i) φ
        (by rw [Category.assoc, h, ← Hom.comm_assoc])) := rfl

/-- The level maps of `pushforwardMap` are compatible with the `factorThruImage`s; together with
`Hom.comm` (compatibility with the `image.ι`s, which are monomorphisms) this determines them. A
`rw` lemma: the left-hand side is not in simp normal form, see `pushforwardMap_natTrans_app`. -/
lemma factorThruImage_comp_pushforwardMap_natTrans_app (i : I) :
    factorThruImage (A'.filtration.ι.app i ≫ e') ≫ (pushforwardMap u e' e φ h).natTrans.app i =
      u.natTrans.app i ≫ factorThruImage (A.filtration.ι.app i ≫ e) := by
  rw [pushforwardMap_natTrans_app]; exact image.factor_map (Arrow.homMk' _ _ _)

/-- `pushforwardMap` lies under `u`: the square `A' ⟶ pushforwardObj A' e' ⟶ pushforwardObj A e`
equals `A' ⟶ A ⟶ pushforwardObj A e`. -/
@[reassoc (attr := simp)]
lemma pushforwardHom_comp_pushforwardMap :
    pushforwardHom A' e' ≫ pushforwardMap u e' e φ h = u ≫ pushforwardHom A e :=
  hom_ext h

end PushforwardMap

variable (C) in
/-- Reindexing filtered objects along a functor `e : J ⥤ I` of index categories. -/
@[implicit_reducible, simps]
def reindex (e : J ⥤ I) : FilteredObject C I ⥤ FilteredObject C J where
  obj A := ⟨A.X, A.filtration.reindex e⟩
  map f := homMk f.hom (fun j => f.natTrans.app (e.obj j)) (fun j => f.comm (e.obj j))

variable (C) in
/-- Reindexing along an equivalence of index categories is an equivalence. -/
noncomputable def reindexEquivalence (e : J ≌ I) : FilteredObject C I ≌ FilteredObject C J :=
  Equivalence.mk (reindex C e.functor) (reindex C e.inverse)
    (NatIso.ofComponents (fun A =>
      isoMk (Iso.refl _) (fun i => A.filtration.diagram.mapIso (e.counitIso.symm.app i))
        (fun i => A.filtration.ι.naturality (e.counitIso.symm.app i).hom))
      (fun {A B} f => hom_ext (by simp)))
    (NatIso.ofComponents (fun A =>
      isoMk (Iso.refl _) (fun j => A.filtration.diagram.mapIso (e.unitIso.symm.app j))
        (fun j => A.filtration.ι.naturality (e.unitIso.symm.app j).hom))
      (fun {A B} f => hom_ext (by simp)))

variable (C) in
/-- The two conventions for decreasing `ℤ`-filtrations, `I := ℤᵒᵖ` and `I := ℤᵒᵈ`, give
equivalent categories of filtered objects. -/
noncomputable def opEquivOd : FilteredObject C ℤᵒᵖ ≌ FilteredObject C ℤᵒᵈ :=
  reindexEquivalence C (orderDualEquivalence ℤ)

/-- Reindexing preserves Mathlib's strict (cartesian) morphisms. -/
instance (e : J ⥤ I) (f : A ⟶ B) [IsStrictHom f] : IsStrictHom ((reindex C e).map f) where
  isPullback j := IsStrictHom.isPullback f (e.obj j)

end FilteredObject

end CategoryTheory
