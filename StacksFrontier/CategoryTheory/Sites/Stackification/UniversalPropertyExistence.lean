module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EssentiallySurjective
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-! # Extending a 1-morphism along a stackification

Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` be a fibred category, let `G : 𝒮 ⥤ 𝒮'` exhibit `𝒮'` as the
stackification of `𝒮` in the sense of Stacks 02ZN, and let `F : 𝒮 ⥤ 𝒳` be a 1-morphism of fibred
categories over `𝒞` into a stack. Stacks 0435 asserts that `F` extends along `G`, i.e. that there
are a 1-morphism `H : 𝒮' ⥤ 𝒳` over `𝒞` and a 2-isomorphism `G ⋙ H ≅ F`.

This file builds the ingredients of that extension. Its centrepiece is the *transfer* of a
morphism of a fibre along `G`: for `a`, `b` in the fibre of `𝒮` over `U`, every morphism
`G a ⟶ G b` of the fibre of `𝒮'` comes from a unique morphism `F a ⟶ F b` of the fibre of `𝒳`,
because the map `Mor(a, b) ⟶ Mor(G a, G b)` of presheaves on `𝒞/U` is locally bijective and
`Mor(F a, F b)` is a sheaf. The transfer is the action that any extension `H` must have on
morphisms between objects in the image of `G`, and the local presentations of an object of `𝒮'`
supplied by clause (2) of Stacks 02ZN are glued by it into a descent datum for `𝒳`.

Nothing here carries the tag 0435: the 1-morphism `H` and the 2-isomorphism are not constructed.

## Main definitions

* `CategoryTheory.Functor.morOfSection`, the inverse of `CategoryTheory.Functor.morSection`;
* `CategoryTheory.Functor.IsFibredOneMorphism.morMapAt`, the map `Mor(a, b) ⟶ Mor(K a, K b)` of
  Stacks 042V evaluated at an object of `𝒞/U`, and
  `CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberCompIso`, the comparison through
  which it interacts with the contraction of an iterated chosen pullback;
* `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMapULift`, the map of morphism presheaves
  of Stacks 042V for total categories whose hom universes are independent, both presheaves having
  been raised to their common upper bound;
* `CategoryTheory.Functor.Stackification.morMapULift`, the factorisation of the map induced by `F`
  through the map induced by `G`, and `CategoryTheory.Functor.Stackification.morMapSection`, its
  action on sections;
* `CategoryTheory.Functor.Stackification.transfer`, the transfer of a morphism of a fibre along a
  stackification, and `CategoryTheory.Functor.Stackification.transferIso`, its isomorphism form;
* `CategoryTheory.Functor.Stackification.localIso`, the comparison of two local presentations of an
  object of `𝒮'`, and `CategoryTheory.Functor.Stackification.descentDatum`, the descent datum
  for `𝒳` built from the local presentations by transferring those comparisons.

## Main results

* `CategoryTheory.Functor.morRestrict_morSection`, that restricting a morphism of a fibre, read as
  a section of `Mor(x, y)` over the terminal object of `𝒞/U`, along an arrow `f` of `𝒞/U` is base
  change along `f`. This is the bridge between the presheaf `Mor(x, y)` and the fibres;
* `CategoryTheory.Functor.IsFibredOneMorphism.morMapAt_pullbackFiberCompIso`, the bookkeeping
  identity that transports a statement about morphisms of the fibre over `U` to the fibre over the
  source of `f`;
* `CategoryTheory.Functor.Stackification.morMapAt_transfer`, the local characterization of the
  transfer, from which all of its properties are read off;
* `CategoryTheory.Functor.Stackification.transfer_id`,
  `CategoryTheory.Functor.Stackification.transfer_comp` and
  `CategoryTheory.Functor.Stackification.transfer_map`, functoriality of the transfer and its
  compatibility with `G`;
* `CategoryTheory.Functor.Stackification.transfer_pullbackFiberHom`, its compatibility with base
  change;
* `CategoryTheory.Functor.Stackification.exists_descends` and
  `CategoryTheory.Functor.Stackification.exists_descends_of_isStack`, that the descent datum of the
  local presentations of an object of `𝒮'` is effective. Its value is the value on objects of the
  extension asserted by Stacks 0435;
* `CategoryTheory.Functor.Stackification.descentDatum_descends_map` and
  `CategoryTheory.Functor.Stackification.nonempty_iso_map_of_descends`, that at an object `G a`
  globally in the image of `G` that value is `F a`. This is the 2-isomorphism of Stacks 0435 on
  objects.

## Implementation notes

*Universes.* Four independent object universes, one for each of `𝒞`, `𝒮`, `𝒮'` and `𝒳`; the hom
universe of `𝒞`; the hom universe shared by `𝒮` and `𝒮'`; and the hom universe of `𝒳`,
independent of all of them. `𝒮` and `𝒮'` do share one, because
`IsFibredOneMorphism.morPresheafMap` — the map of Stacks 042V in which clause (1) of Stacks 02ZN
is stated — has for source the presheaf `Mor(·, ·)` of `𝒮`, valued in the hom universe of `𝒮`,
and for target that of `𝒮'`. `𝒳` does not: the map `Mor(G a, G b) ⟶ Mor(F a, F b)` the transfer
is read off is built between presheaves raised to the common upper bound of the two universes by
`CategoryTheory.uliftFunctor`, which preserves each of the three hypotheses the factorisation
consumes. That independence is what lets the extension be built into a stack whose morphisms live
in a universe unrelated to those of the stackification — for instance the quotient stack of a
groupoid in algebraic spaces, whose morphisms were raised one universe by
`CategoryTheory.ULiftHom`.

No `UnivLE` hypothesis occurs: the factorisation through a locally bijective map used here,
`CategoryTheory.Presheaf.existsUnique_hom_of_isLocallyBijective`, is proved from the sheaf
condition rather than through a sheafification functor.

## References

* [Stacks 0435](https://stacks.math.columbia.edu/tag/0435);
* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN), whose two clauses are the hypotheses.
-/

@[expose] public section

universe vb

namespace CategoryTheory

open Opposite

namespace Functor

/-- A functor carries the two composites of an isomorphism to identities, in the spelling in which
the two directions are separate images rather than the two directions of one image. -/
@[reassoc]
lemma map_inv_comp_map_hom {A B : Type*} [Category A] [Category B] (T : A ⥤ B) {X Y : A}
    (e : X ≅ Y) : T.map e.inv ≫ T.map e.hom = 𝟙 _ := by
  rw [← T.map_comp, e.inv_hom_id, T.map_id]

/-- A functor carries the composite `e.hom ≫ e.inv` of an isomorphism `e`, taken image by image,
to the identity. -/
@[reassoc]
lemma map_hom_comp_map_inv {A B : Type*} [Category A] [Category B] (T : A ⥤ B) {X Y : A}
    (e : X ≅ Y) : T.map e.hom ≫ T.map e.inv = 𝟙 _ := by
  rw [← T.map_comp, e.hom_inv_id, T.map_id]

/-! ### A morphism of a fibre and the sections of `Mor(x, y)`

`CategoryTheory.Functor.morSection` reads a morphism of the fibre over `U` as a section of
`Mor(x, y)` over the terminal object `𝟙 U` of `𝒞/U`. It is a bijection, and under it the
restriction maps of `Mor(x, y)` are base change of morphisms of fibres. -/

section MorSection

universe w v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

/-- The restriction maps of the presheaf `Mor(x, y)` of Stacks 02ZB with its values raised to a
larger universe are the restriction maps of `Mor(x, y)` itself. Raising the values is how a map
from `Mor(x, y)` to the morphism presheaf of a total category with a different hom universe is
stated. -/
@[simp]
lemma uliftMorPresheaf_map (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf p x y ⋙ uliftFunctor.{w}).obj (op g₂)) :
    (morPresheaf p x y ⋙ uliftFunctor.{w}).map h.op m =
      ULift.up (morRestrict p x y h m.down) := rfl

/-- A section of `Mor(x, y)` over the terminal object `𝟙 U` of `𝒮/U`, read as a morphism of the
fibre over `U`. This inverts `CategoryTheory.Functor.morSection`. -/
noncomputable def morOfSection (x y : p.Fiber U)
    (s : pullbackFiber p x (𝟙 U) ⟶ pullbackFiber p y (𝟙 U)) : x ⟶ y :=
  (pullbackFiberIdIso x).inv ≫ s ≫ (pullbackFiberIdIso y).hom

/-- Reading a morphism of the fibre as a section of `Mor(x, y)` and back returns the morphism. -/
@[simp]
lemma morOfSection_morSection (x y : p.Fiber U) (m : x ⟶ y) :
    morOfSection p x y (morSection p x y m) = m := by
  unfold morOfSection morSection
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- Reading a section of `Mor(x, y)` over `𝟙 U` as a morphism of the fibre and back returns the
section. -/
@[simp]
lemma morSection_morOfSection (x y : p.Fiber U)
    (s : pullbackFiber p x (𝟙 U) ⟶ pullbackFiber p y (𝟙 U)) :
    morSection p x y (morOfSection p x y s) = s := by
  unfold morOfSection morSection
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Base changing the forward direction of `CategoryTheory.Functor.pullbackFiberIdIso` along `b`
contracts the chosen pullback along the identity. This is the companion of
`CategoryTheory.Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq`. -/
lemma pullbackFiberHom_pullbackFiberIdIso_hom_eq {T Z : 𝒮} (y : p.Fiber T) (b : Z ⟶ T) :
    pullbackFiberHom (pullbackFiberIdIso y).hom b =
      (pullbackFiberCompIso' y (𝟙 T) b b (Category.comp_id b)).hom := by
  have h1 : pullbackFiberHom (pullbackFiberIdIso y).inv b =
      (pullbackFiberCompIso' y (𝟙 T) b b (Category.comp_id b)).inv :=
    pullbackFiberHom_pullbackFiberIdIso_inv_eq y b
  have h2 := (pullbackFiberIso (pullbackFiberIdIso y) b).hom_inv_id
  rw [pullbackFiberIso_hom, pullbackFiberIso_inv, h1] at h2
  rw [← Category.comp_id (pullbackFiberHom (pullbackFiberIdIso y).hom b),
    ← Iso.inv_hom_id (pullbackFiberCompIso' y (𝟙 T) b b (Category.comp_id b)), ← Category.assoc,
    h2, Category.id_comp]

-- `pullbackFiberHom_hom_inv_id` and `pullbackFiberHom_inv_hom_id` were declared here too; they now
-- live once in `Sites/Descent/IsStack/PullbackFiberHom.lean`. See the note in
-- `Sites/Stackification/StageThreeEffectiveDescent.lean`.

/-- A morphism `f : V ⟶ U` read as an arrow of `𝒮/U` from `Over.mk f` to the terminal object
`Over.mk (𝟙 U)`. Every arrow of `𝒮/U` into the terminal object is of this form. -/
def overArrow {V : 𝒮} (f : V ⟶ U) : (Over.mk f : Over U) ⟶ Over.mk (𝟙 U) :=
  Over.homMk f (by simp)

/-- The underlying morphism of `overArrow f` is `f`. -/
@[simp]
lemma overArrow_left {V : 𝒮} (f : V ⟶ U) : (overArrow (U := U) f).left = f := rfl

/-- The arrows of `𝒮/U` into the terminal object that a sieve on the terminal object contains are,
up to the identification of an arrow into `Over.mk (𝟙 U)` with its underlying morphism, the members
of the corresponding sieve on `U`. This is the direction of the identification
`CategoryTheory.Sieve.overEquiv` that a local surjectivity hypothesis is read through, dual to
`CategoryTheory.Functor.mem_of_overEquiv_symm`. -/
lemma mem_of_overEquiv {S : Sieve (Over.mk (𝟙 U) : Over U)} {V : 𝒮} {f : V ⟶ U}
    (hf : (Sieve.overEquiv (Over.mk (𝟙 U) : Over U) S).arrows f) :
    S.arrows (overArrow (U := U) f) := by
  rw [Sieve.overEquiv_iff] at hf
  have h := S.downward_closed hf
    (Over.homMk (𝟙 V) (by simp) : (Over.mk f : Over U) ⟶ Over.mk (f ≫ (Over.mk (𝟙 U)).hom))
  refine (?_ : _ = overArrow (U := U) f) ▸ h
  ext
  simp [overArrow]

/-- The restriction map of `Mor(x, y)` along an arrow of `𝒮/U`, applied to a section. -/
@[simp]
lemma morPresheaf_map_op_apply (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf p x y).obj (op g₂)) :
    (morPresheaf p x y).map h.op m = morRestrict p x y h m := rfl

/-- **The bridge between `Mor(x, y)` and the fibres.** Restricting a morphism `m : x ⟶ y` of the
fibre over `U`, read as a section of `Mor(x, y)` over the terminal object of `𝒮/U`, along the
arrow of `𝒮/U` given by `f : V ⟶ U` is the base change of `m` along `f`.

Both restriction operations are conjugates of base change along `f` by the canonical contractions
of the iterated chosen pullbacks, and the two conjugations cancel. -/
lemma morRestrict_morSection (x y : p.Fiber U) (m : x ⟶ y) {V : 𝒮} (f : V ⟶ U) :
    morRestrict p x y (overArrow (U := U) f) (morSection p x y m) = pullbackFiberHom m f := by
  rw [morRestrict_eq_pullbackFiberHom, morSection, pullbackFiberHom_comp, pullbackFiberHom_comp,
    pullbackFiberHom_pullbackFiberIdIso_hom_eq, pullbackFiberHom_pullbackFiberIdIso_inv_eq]
  simp [overArrow_left, Over.mk_hom, Over.mk_left, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end MorSection

/-! ### The comparisons along a 1-morphism of fibred categories

Everything below is about a single 1-morphism `K : 𝒮 ⥤ 𝒴` of fibred categories over `𝒞`, and is
used twice over: once for the stackification `G` and once for the 1-morphism `F` that is being
extended along it. The content is the interaction of the comparison
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` between `f^* (K a)` and
`K (f^* a)` with the two other canonical comparisons of chosen pullbacks: base change of a
morphism of a fibre, and the contraction of an iterated chosen pullback. -/

section Comparison

universe v v' u₁ u₂ u₃

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒴 : Type u₃}
  [Category.{v'} 𝒴] {p : 𝒮 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} {K : 𝒮 ⥤ 𝒴} [p.IsFibered] [r.IsFibered]

/-! #### The `K`-images of the factorizations that define the comparisons in `𝒮` -/

/-- The image under `K` of the factorization `CategoryTheory.Functor.pullbackFiberHom_fac`: the
base change of `m` along `f`, followed by the chosen pullback map of `b`, equals the chosen
pullback map of `a` followed by `m`, after applying `K`. -/
@[reassoc (attr := simp)]
lemma map_pullbackFiberHom_fac (K : 𝒮 ⥤ 𝒴) {U : 𝒞} {a b : p.Fiber U} (m : a ⟶ b) {V : 𝒞}
    (f : V ⟶ U) :
    K.map (Fiber.fiberInclusion.map (pullbackFiberHom m f)) ≫
        K.map (IsPreFibered.pullbackMap b.2 f) =
      K.map (IsPreFibered.pullbackMap a.2 f) ≫ K.map (Fiber.fiberInclusion.map m) := by
  simp only [← K.map_comp]
  exact congrArg K.map (pullbackFiberHom_fac m f)

/-- The image under `K` of `CategoryTheory.Functor.pullbackFiberCompIso_hom_fac`: the comparison
`γ^* f^* a ≅ (γ ≫ f)^* a`, followed by the chosen pullback map along `γ ≫ f`, equals the
composite of the chosen pullback maps along `γ` and `f`, after applying `K`. -/
@[reassoc (attr := simp)]
lemma map_pullbackFiberCompIso_hom_fac (K : 𝒮 ⥤ 𝒴) {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    K.map (Fiber.fiberInclusion.map (pullbackFiberCompIso a f γ).hom) ≫
        K.map (IsPreFibered.pullbackMap a.2 (γ ≫ f)) =
      K.map (IsPreFibered.pullbackMap (pullbackFiber p a f).2 γ) ≫
        K.map (IsPreFibered.pullbackMap a.2 f) := by
  simp only [← K.map_comp]
  exact congrArg K.map (pullbackFiberCompIso_hom_fac a f γ)

/-- The image under `K` of `CategoryTheory.Functor.pullbackFiberCompIso_inv_fac`: the inverse
comparison, followed by the chosen pullback maps along `γ` and `f`, equals the chosen pullback
map along `γ ≫ f`, after applying `K`. -/
@[reassoc (attr := simp)]
lemma map_pullbackFiberCompIso_inv_fac (K : 𝒮 ⥤ 𝒴) {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    K.map (Fiber.fiberInclusion.map (pullbackFiberCompIso a f γ).inv) ≫
        K.map (IsPreFibered.pullbackMap (pullbackFiber p a f).2 γ) ≫
        K.map (IsPreFibered.pullbackMap a.2 f) =
      K.map (IsPreFibered.pullbackMap a.2 (γ ≫ f)) := by
  simp only [← K.map_comp]
  exact congrArg K.map (pullbackFiberCompIso_inv_fac a f γ)

/-- The image under `K` of `CategoryTheory.Functor.pullbackFiberComparison_hom_fac`: the
comparison `ε^* f^* y ≅ ε'^* g^* y`, followed by the chosen pullback maps along `ε'` and `g`,
equals the chosen pullback maps along `ε` and `f`, after applying `K`. -/
@[reassoc (attr := simp)]
lemma map_pullbackFiberComparison_hom_fac (K : 𝒮 ⥤ 𝒴) {T : 𝒞} (y : p.Fiber T) {V W Z : 𝒞}
    {f : V ⟶ T} {g : W ⟶ T} (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    K.map (Fiber.fiberInclusion.map (pullbackFiberComparison y ε ε' heq).hom) ≫
        K.map (IsPreFibered.pullbackMap (pullbackFiber p y g).2 ε') ≫
        K.map (IsPreFibered.pullbackMap y.2 g) =
      K.map (IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε) ≫
        K.map (IsPreFibered.pullbackMap y.2 f) := by
  simp only [← K.map_comp]
  exact congrArg K.map (pullbackFiberComparison_hom_fac y ε ε' heq)

namespace IsFibredOneMorphism

variable (hK : IsFibredOneMorphism p r K)

/-! #### The induced map on morphism presheaves, section by section -/

/-- The map `Mor(a, b) ⟶ Mor(K a, K b)` of Stacks 042V evaluated at the object `Over.mk f` of
`𝒞/U`: it conjugates the image under `K` of a morphism of the fibre by the comparisons
`IsFibredOneMorphism.mapPullbackFiberIso`. Every statement below about the induced map is a
statement about this, rather than about the presheaf map, so that the sections of the presheaves
`Mor` never have to be unfolded into morphisms of fibres. -/
noncomputable def morMapAt {U : 𝒞} (a b : p.Fiber U) {V : 𝒞} (f : V ⟶ U)
    (u : pullbackFiber p a f ⟶ pullbackFiber p b f) :
    pullbackFiber r ((fiberFunctorOfCompEq hK.comp_eq U).obj a) f ⟶
      pullbackFiber r ((fiberFunctorOfCompEq hK.comp_eq U).obj b) f :=
  (hK.mapPullbackFiberIso a f).hom ≫ (fiberFunctorOfCompEq hK.comp_eq V).map u ≫
    (hK.mapPullbackFiberIso b f).inv

/-- `IsFibredOneMorphism.morMapAt` is the image of `u` under the fibre functor of `K`, conjugated
by the comparisons `IsFibredOneMorphism.mapPullbackFiberIso`. -/
lemma morMapAt_def {U : 𝒞} (a b : p.Fiber U) {V : 𝒞} (f : V ⟶ U)
    (u : pullbackFiber p a f ⟶ pullbackFiber p b f) :
    hK.morMapAt a b f u = (hK.mapPullbackFiberIso a f).hom ≫
      (fiberFunctorOfCompEq hK.comp_eq V).map u ≫ (hK.mapPullbackFiberIso b f).inv := rfl

section SharedHomUniverse

-- The map of morphism presheaves of Stacks 042V exists only when the two total categories have
-- one hom universe: its source and target are the presheaves `Mor(·, ·)` of `𝒮` and of `𝒴`, and
-- those are valued in the hom universe of `𝒮` and of `𝒴` respectively.
variable {𝒴₀ : Type u₃} [Category.{v} 𝒴₀] {r₀ : 𝒴₀ ⥤ 𝒞} {K₀ : 𝒮 ⥤ 𝒴₀} [r₀.IsFibered]

/-- `IsFibredOneMorphism.morMapAt` is the map of morphism presheaves of Stacks 042V evaluated at
`Over.mk f`. -/
lemma morPresheafMap_app_eq (hK₀ : IsFibredOneMorphism p r₀ K₀) {U : 𝒞} (a b : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) (u : pullbackFiber p a f ⟶ pullbackFiber p b f) :
    (hK₀.morPresheafMap a b).app (op (Over.mk f)) u = hK₀.morMapAt a b f u := rfl

end SharedHomUniverse

/-- The equation that determines `IsFibredOneMorphism.morMapAt`: composed with the comparison at
the target it is the comparison at the source followed by the image of the section. -/
@[reassoc]
lemma morMapAt_comp_mapPullbackFiberIso_hom {U : 𝒞} (a b : p.Fiber U) {V : 𝒞} (f : V ⟶ U)
    (u : pullbackFiber p a f ⟶ pullbackFiber p b f) :
    hK.morMapAt a b f u ≫ (hK.mapPullbackFiberIso b f).hom =
      (hK.mapPullbackFiberIso a f).hom ≫ (fiberFunctorOfCompEq hK.comp_eq V).map u := by
  simp [morMapAt_def, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `IsFibredOneMorphism.morMapAt`, composed with the chosen cartesian lift of `f` at `K b`. This
is the factorization every identity below is proved by. -/
@[reassoc (attr := simp)]
lemma morMapAt_fac {U : 𝒞} (a b : p.Fiber U) {V : 𝒞} (f : V ⟶ U)
    (u : pullbackFiber p a f ⟶ pullbackFiber p b f) :
    Fiber.fiberInclusion.map (hK.morMapAt a b f u) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj b).2 f =
      Fiber.fiberInclusion.map (hK.mapPullbackFiberIso a f).hom ≫
        K.map (Fiber.fiberInclusion.map u) ≫ K.map (IsPreFibered.pullbackMap b.2 f) := by
  rw [morMapAt_def]
  simp [Functor.map_comp, Category.assoc, mapPullbackFiberIso_inv_fac,
    fiberInclusion_map_fiberFunctorOfCompEq_map]

/-- `IsFibredOneMorphism.morMapAt` carries the identity to the identity. -/
@[simp]
lemma morMapAt_id {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    hK.morMapAt a a f (𝟙 (pullbackFiber p a f)) = 𝟙 _ := by
  rw [morMapAt_def, Functor.map_id, Category.id_comp, Iso.hom_inv_id]

/-- `IsFibredOneMorphism.morMapAt` carries a composite to the composite of the images. -/
lemma morMapAt_comp {U : 𝒞} {a b c : p.Fiber U} {V : 𝒞} (f : V ⟶ U)
    (u : pullbackFiber p a f ⟶ pullbackFiber p b f)
    (u' : pullbackFiber p b f ⟶ pullbackFiber p c f) :
    hK.morMapAt a c f (u ≫ u') = hK.morMapAt a b f u ≫ hK.morMapAt b c f u' := by
  rw [morMapAt_def, morMapAt_def, morMapAt_def, Functor.map_comp]
  simp [Category.assoc, Iso.inv_hom_id_assoc]

/-- **`IsFibredOneMorphism.morMapAt` commutes with restriction.** Restricting the image of a
section of `Mor(a, b)` along an arrow of `𝒞/U` is the image of its restriction. This is the
naturality of the map of morphism presheaves of Stacks 042V, written on sections so that it does
not need the two total categories to share a hom universe. -/
lemma morRestrict_morMapAt {U : 𝒞} (a b : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (u : pullbackFiber p a g₂.hom ⟶ pullbackFiber p b g₂.hom) :
    morRestrict r ((fiberFunctorOfCompEq hK.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hK.comp_eq U).obj b) h (hK.morMapAt a b g₂.hom u) =
      hK.morMapAt a b g₁.hom (morRestrict p a b h u) := by
  rw [morMapAt_def, morMapAt_def]
  exact (hK.morRestrict_mapPullbackFiberIso_conj a b h u).symm

/-- **The map of morphism presheaves of Stacks 042V for total categories whose hom universes are
independent.** The presheaf `Mor(a, b)` of `𝒮` is valued in the hom universe of `𝒮` and the
presheaf `Mor(K a, K b)` of `𝒴` in that of `𝒴`, so there is no map between them unless the two
universes agree; raising each to their common upper bound by `CategoryTheory.uliftFunctor` removes
that restriction, and this is the resulting map. Its sections are
`IsFibredOneMorphism.morMapAt`, so it carries exactly the same information as
`IsFibredOneMorphism.morPresheafMap`, which it specialises to when the two universes do agree. -/
noncomputable def morPresheafMapULift {U : 𝒞} (a b : p.Fiber U) :
    morPresheaf p a b ⋙ uliftFunctor.{v'} ⟶
      morPresheaf r ((fiberFunctorOfCompEq hK.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hK.comp_eq U).obj b) ⋙ uliftFunctor.{v} where
  app g := ↾fun m ↦ ULift.up (hK.morMapAt a b g.unop.hom m.down)
  naturality := by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    exact congrArg ULift.up (hK.morRestrict_morMapAt a b h m.down).symm

/-- The sections of `IsFibredOneMorphism.morPresheafMapULift` are
`IsFibredOneMorphism.morMapAt`. -/
@[simp]
lemma morPresheafMapULift_app_up {U : 𝒞} (a b : p.Fiber U) {V : 𝒞} (f : V ⟶ U)
    (u : pullbackFiber p a f ⟶ pullbackFiber p b f) :
    (hK.morPresheafMapULift a b).app (op (Over.mk f)) (ULift.up u) =
      ULift.up (hK.morMapAt a b f u) := rfl

/-- The base change of a morphism of a fibre is carried by `IsFibredOneMorphism.morMapAt` to the
base change of its image, so that `IsFibredOneMorphism.mapPullbackFiberIso` is natural in the
morphism of the fibre. -/
lemma morMapAt_pullbackFiberHom {U : 𝒞} {a b : p.Fiber U} (m : a ⟶ b) {V : 𝒞} (f : V ⟶ U) :
    hK.morMapAt a b f (pullbackFiberHom m f) =
      pullbackFiberHom ((fiberFunctorOfCompEq hK.comp_eq U).map m) f := by
  refine fiber_hom_ext_of_cartesian f
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj b).2 f)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  rw [morMapAt_fac, map_pullbackFiberHom_fac, mapPullbackFiberIso_hom_fac_assoc,
    pullbackFiberHom_fac, fiberInclusion_map_fiberFunctorOfCompEq_map]

/-! #### The contraction of an iterated chosen pullback along `K` -/

/-- The chosen cartesian lift of `γ` at `K (f^* a)`, followed by the image under `K` of the chosen
cartesian lift of `f` at `a`, is strongly cartesian over `γ ≫ f`. -/
lemma isStronglyCartesian_pullbackMap_comp_map_pullbackMap {U : 𝒞} (a : p.Fiber U) {V W : 𝒞}
    (f : V ⟶ U) (γ : W ⟶ V) :
    r.IsStronglyCartesian (γ ≫ f)
      (IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hK.comp_eq V).obj (pullbackFiber p a f)).2 γ ≫
        K.map (IsPreFibered.pullbackMap a.2 f)) := by
  have h2 : r.IsStronglyCartesian f (K.map (IsPreFibered.pullbackMap a.2 f)) :=
    hK.map_isStronglyCartesian f _ inferInstance
  infer_instance

/-- The comparison, in the fibre of `𝒴` over `W`, between the chosen pullback along `γ` of
`K (f^* a)` and the chosen pullback of `K a` along `γ ≫ f`: both carry a cartesian morphism to
`K a` over `γ ≫ f`. It is the comparison through which
`IsFibredOneMorphism.mapPullbackFiberIso` and `CategoryTheory.Functor.pullbackFiberCompIso` are
related. -/
noncomputable def mapPullbackFiberCompIso {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    pullbackFiber r ((fiberFunctorOfCompEq hK.comp_eq V).obj (pullbackFiber p a f)) γ ≅
      pullbackFiber r ((fiberFunctorOfCompEq hK.comp_eq U).obj a) (γ ≫ f) :=
  have := hK.isStronglyCartesian_pullbackMap_comp_map_pullbackMap a f γ
  fiberIsoOfCartesian (γ ≫ f)
    (IsPreFibered.pullbackMap
        ((fiberFunctorOfCompEq hK.comp_eq V).obj (pullbackFiber p a f)).2 γ ≫
      K.map (IsPreFibered.pullbackMap a.2 f))
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj a).2 (γ ≫ f))
    inferInstance (IsPreFibered.pullbackMap.IsCartesian _ _)

/-- `IsFibredOneMorphism.mapPullbackFiberCompIso`, followed by the chosen pullback map of `K a`
along `γ ≫ f`, is the chosen pullback map of `K (f^* a)` along `γ` followed by the image under
`K` of the chosen pullback map of `a` along `f`. -/
@[reassoc (attr := simp)]
lemma mapPullbackFiberCompIso_hom_fac {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U) (γ : W ⟶ V) :
    Fiber.fiberInclusion.map (hK.mapPullbackFiberCompIso a f γ).hom ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj a).2 (γ ≫ f) =
      IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hK.comp_eq V).obj (pullbackFiber p a f)).2 γ ≫
        K.map (IsPreFibered.pullbackMap a.2 f) :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- **The two comparisons are compatible.** Contracting an iterated chosen pullback in `𝒮` and
comparing with `K` afterwards is comparing with `K` first and then contracting through
`IsFibredOneMorphism.mapPullbackFiberCompIso`. Both composites carry the image under `K` of the
chosen cartesian lift of `γ ≫ f` at `a` to the composite of the two chosen lifts. -/
lemma mapPullbackFiberCompIso_hom_comp {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    (hK.mapPullbackFiberCompIso a f γ).hom ≫ (hK.mapPullbackFiberIso a (γ ≫ f)).hom =
      (hK.mapPullbackFiberIso (pullbackFiber p a f) γ).hom ≫
        (fiberFunctorOfCompEq hK.comp_eq W).map (pullbackFiberCompIso a f γ).hom := by
  refine fiber_hom_ext_of_cartesian (γ ≫ f) (K.map (IsPreFibered.pullbackMap a.2 (γ ≫ f)))
    (hK.isCartesian_map_pullbackMap a (γ ≫ f)) _ _ ?_
  rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
    Category.assoc, mapPullbackFiberIso_hom_fac, mapPullbackFiberCompIso_hom_fac,
    fiberInclusion_map_fiberFunctorOfCompEq_map, map_pullbackFiberCompIso_hom_fac,
    mapPullbackFiberIso_hom_fac_assoc]

-- The chosen pullbacks, the fibre inclusion and the induced functor on fibres are semireducible,
-- so the endpoints of the composites below agree only once they unfold.
/-- **The induced map on morphism presheaves against base change.** Suppose a section `u` of
`Mor(a, b)` over `γ ≫ f` has image under `K` the base change of a morphism `σ : K a ⟶ K b` of the
fibre. Then the corresponding section of `Mor(f^* a, f^* b)` over `γ` — the contraction of `u`
through the iterated chosen pullbacks — has image under `K` the base change along `γ` of the
morphism `K (f^* a) ⟶ K (f^* b)` that `σ` induces.

This is the identity that transports every statement about the transfer of a morphism of a fibre
from the fibre over `U` to the fibre over the source of `f`, and the reason
`IsFibredOneMorphism.mapPullbackFiberCompIso` is introduced. -/
lemma morMapAt_pullbackFiberCompIso {U : 𝒞} {a b : p.Fiber U} {V W : 𝒞} (f : V ⟶ U) (γ : W ⟶ V)
    (u : pullbackFiber p a (γ ≫ f) ⟶ pullbackFiber p b (γ ≫ f))
    (σ : (fiberFunctorOfCompEq hK.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hK.comp_eq U).obj b)
    (hu : hK.morMapAt a b (γ ≫ f) u = pullbackFiberHom σ (γ ≫ f)) :
    hK.morMapAt (pullbackFiber p a f) (pullbackFiber p b f) γ
        ((pullbackFiberCompIso a f γ).hom ≫ u ≫ (pullbackFiberCompIso b f γ).inv) =
      pullbackFiberHom ((hK.mapPullbackFiberIso a f).inv ≫ pullbackFiberHom σ f ≫
        (hK.mapPullbackFiberIso b f).hom) γ := by
  -- The hypothesis, composed with the chosen cartesian lift of `γ ≫ f` at `K b`.
  have hu' : Fiber.fiberInclusion.map (hK.mapPullbackFiberIso a (γ ≫ f)).hom ≫
      K.map (Fiber.fiberInclusion.map u) ≫ K.map (IsPreFibered.pullbackMap b.2 (γ ≫ f)) =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj a).2 (γ ≫ f) ≫
        Fiber.fiberInclusion.map σ := by
    rw [← morMapAt_fac, hu, pullbackFiberHom_fac]
  -- The compatibility of the two comparisons, seen in `𝒴`.
  have key : Fiber.fiberInclusion.map (hK.mapPullbackFiberIso (pullbackFiber p a f) γ).hom ≫
      K.map (Fiber.fiberInclusion.map (pullbackFiberCompIso a f γ).hom) =
      Fiber.fiberInclusion.map (hK.mapPullbackFiberCompIso a f γ).hom ≫
        Fiber.fiberInclusion.map (hK.mapPullbackFiberIso a (γ ≫ f)).hom := by
    have h := congrArg Fiber.fiberInclusion.map (hK.mapPullbackFiberCompIso_hom_comp a f γ)
    simpa only [Fiber.fiberInclusion.map_comp, fiberInclusion_map_fiberFunctorOfCompEq_map]
      using h.symm
  -- Both sides are pinned down by their composite with the cartesian morphism to `K b` over
  -- `γ ≫ f` out of the chosen pullback of `K (f^* b)` along `γ`.
  have hcart := hK.isStronglyCartesian_pullbackMap_comp_map_pullbackMap b f γ
  refine fiber_hom_ext_of_cartesian (γ ≫ f)
    (IsPreFibered.pullbackMap
        ((fiberFunctorOfCompEq hK.comp_eq V).obj (pullbackFiber p b f)).2 γ ≫
      K.map (IsPreFibered.pullbackMap b.2 f)) inferInstance _ _ ?_
  simp only [morMapAt_fac_assoc, Fiber.fiberInclusion.map_comp, Functor.map_comp, Category.assoc,
    map_pullbackFiberCompIso_inv_fac, pullbackFiberHom_fac_assoc,
    mapPullbackFiberIso_hom_fac, mapPullbackFiberIso_inv_fac_assoc, pullbackFiberHom_fac]
  rw [← Category.assoc, key, Category.assoc, hu']
  simp [mapPullbackFiberCompIso_hom_fac_assoc]

/-- The inverse form of the factorization defining
`IsFibredOneMorphism.mapPullbackFiberCompIso`. -/
@[reassoc (attr := simp)]
lemma mapPullbackFiberCompIso_inv_fac {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U) (γ : W ⟶ V) :
    Fiber.fiberInclusion.map (hK.mapPullbackFiberCompIso a f γ).inv ≫
        IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hK.comp_eq V).obj (pullbackFiber p a f)).2 γ ≫
        K.map (IsPreFibered.pullbackMap a.2 f) =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj a).2 (γ ≫ f) :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- `IsFibredOneMorphism.mapPullbackFiberCompIso` in terms of the contraction of the iterated
chosen pullback of `K a` and the base change of the comparison at `f`. -/
@[reassoc]
lemma mapPullbackFiberCompIso_hom_eq {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U) (γ : W ⟶ V) :
    (hK.mapPullbackFiberCompIso a f γ).hom =
      pullbackFiberHom (hK.mapPullbackFiberIso a f).inv γ ≫
        (pullbackFiberCompIso ((fiberFunctorOfCompEq hK.comp_eq U).obj a) f γ).hom := by
  refine fiber_hom_ext_of_cartesian (γ ≫ f)
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj a).2 (γ ≫ f))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp [Fiber.fiberInclusion.map_comp, Category.assoc, mapPullbackFiberCompIso_hom_fac,
    pullbackFiberCompIso_hom_fac, pullbackFiberHom_fac_assoc, mapPullbackFiberIso_inv_fac]

/-- The inverse form of `IsFibredOneMorphism.mapPullbackFiberCompIso_hom_eq`. -/
@[reassoc]
lemma mapPullbackFiberCompIso_inv_eq {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U) (γ : W ⟶ V) :
    (hK.mapPullbackFiberCompIso a f γ).inv =
      (pullbackFiberCompIso ((fiberFunctorOfCompEq hK.comp_eq U).obj a) f γ).inv ≫
        pullbackFiberHom (hK.mapPullbackFiberIso a f).hom γ := by
  rw [← cancel_epi (hK.mapPullbackFiberCompIso a f γ).hom, Iso.hom_inv_id,
    mapPullbackFiberCompIso_hom_eq]
  simp

/-- The base change of the inverse comparison at `f`, in terms of
`IsFibredOneMorphism.mapPullbackFiberCompIso`. -/
@[reassoc]
lemma pullbackFiberHom_mapPullbackFiberIso_inv {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    pullbackFiberHom (hK.mapPullbackFiberIso a f).inv γ =
      (hK.mapPullbackFiberCompIso a f γ).hom ≫
        (pullbackFiberCompIso ((fiberFunctorOfCompEq hK.comp_eq U).obj a) f γ).inv := by
  rw [mapPullbackFiberCompIso_hom_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The base change of the comparison at `f`, in terms of
`IsFibredOneMorphism.mapPullbackFiberCompIso`. -/
@[reassoc]
lemma pullbackFiberHom_mapPullbackFiberIso_hom {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    pullbackFiberHom (hK.mapPullbackFiberIso a f).hom γ =
      (pullbackFiberCompIso ((fiberFunctorOfCompEq hK.comp_eq U).obj a) f γ).hom ≫
        (hK.mapPullbackFiberCompIso a f γ).inv := by
  rw [mapPullbackFiberCompIso_inv_eq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The composite of the inverse of `IsFibredOneMorphism.mapPullbackFiberCompIso` with the
comparison at `γ`, solved for the comparison at `γ ≫ f`. This is the form in which the
compatibility of the two comparisons is applied to the gluing isomorphisms of a descent datum. -/
@[reassoc]
lemma mapPullbackFiberCompIso_inv_comp {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    (hK.mapPullbackFiberCompIso a f γ).inv ≫
        (hK.mapPullbackFiberIso (pullbackFiber p a f) γ).hom =
      (hK.mapPullbackFiberIso a (γ ≫ f)).hom ≫
        (fiberFunctorOfCompEq hK.comp_eq W).map (pullbackFiberCompIso a f γ).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, hK.mapPullbackFiberCompIso_hom_comp]
  simp

/-- The composite of the comparison at `γ` with
`IsFibredOneMorphism.mapPullbackFiberCompIso`, solved for the comparison at `γ ≫ f`. -/
@[reassoc]
lemma mapPullbackFiberCompIso_comp_hom {U : 𝒞} (a : p.Fiber U) {V W : 𝒞} (f : V ⟶ U)
    (γ : W ⟶ V) :
    (hK.mapPullbackFiberIso (pullbackFiber p a f) γ).inv ≫
        (hK.mapPullbackFiberCompIso a f γ).hom =
      (fiberFunctorOfCompEq hK.comp_eq W).map (pullbackFiberCompIso a f γ).hom ≫
        (hK.mapPullbackFiberIso a (γ ≫ f)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hK.mapPullbackFiberCompIso_hom_comp]
  simp

end IsFibredOneMorphism

end Comparison

/-! ### The transfer of a morphism of a fibre along a stackification

Let `G : 𝒮 ⥤ 𝒮'` exhibit `𝒮'` as the stackification of `𝒮` and let `F : 𝒮 ⥤ 𝒳` be a 1-morphism
into a stack. For `a`, `b` in the fibre of `𝒮` over `U` the map `Mor(a, b) ⟶ Mor(G a, G b)` of
presheaves on `𝒞/U` is locally bijective and `Mor(F a, F b)` is a sheaf, so the map induced by `F`
factors uniquely through the one induced by `G`
(`CategoryTheory.Presheaf.existsUnique_hom_of_isLocallyBijective`, applied after raising the
values of both presheaves to the common upper bound of the hom universes of `𝒮'` and `𝒳`).
Evaluating the factorisation at the terminal object of `𝒞/U` transfers a morphism `G a ⟶ G b` of
the fibre of `𝒮'` to a morphism `F a ⟶ F b` of the fibre of `𝒳`.

Everything about the transfer is read off from one local characterization,
`CategoryTheory.Functor.Stackification.morMapAt_transfer`: wherever a morphism `G a ⟶ G b` is the
image of a section `u` of `Mor(a, b)`, its transfer is the image of `u` under `F`. Since a morphism
`G a ⟶ G b` is locally such an image and the target is a sheaf, that determines it. -/

section Transfer

universe v v₄ u₁ u₂ u₃ u₄

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v₄} 𝒳] {J : GrothendieckTopology 𝒞}
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {F : 𝒮 ⥤ 𝒳}
  [p.IsFibered] [p'.IsFibered] [q.IsFibered]

namespace Stackification

variable (hG : p.IsFibredOneMorphism p' G) (hF : p.IsFibredOneMorphism q F)
  (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
  (hqmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)

include hmor in
/-- **Clause (1) of Stacks 02ZN in the base site.** A morphism `G a ⟶ G b` of the fibre of `𝒮'`
over `U` is, along the members of a covering sieve of `U`, the image under `G` of a morphism of the
fibres of `𝒮`. This is local surjectivity of the map `Mor(a, b) ⟶ Mor(G a, G b)` of presheaves on
`𝒞/U`, read through the identification of sieves on the terminal object of `𝒞/U` with sieves
on `U`. -/
lemma exists_covering_lift {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f →
      ∃ u : pullbackFiber p a f ⟶ pullbackFiber p b f,
        hG.morMapAt a b f u = pullbackFiberHom θ f := by
  have hsurj := (hmor U a b).2
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 U) : Over U)
      (Presheaf.imageSieve (hG.morPresheafMap a b) (morSection p' _ _ θ)),
    Presheaf.imageSieve_mem (J.over U) (hG.morPresheafMap a b)
      (U := op (Over.mk (𝟙 U) : Over U)) _, ?_⟩
  intro V f hf
  obtain ⟨u, hu⟩ := mem_of_overEquiv hf
  exact ⟨u, by
    rw [← hG.morPresheafMap_app_eq, hu, morPresheaf_map_op_apply, morRestrict_morSection]⟩

/-- The map of presheaves `Mor(G a, G b) ⟶ Mor(F a, F b)` on `𝒞/U` through which the map induced
by `F` factors, the unique one provided by
`CategoryTheory.Presheaf.existsUnique_hom_of_isLocallyBijective`.

Both presheaves are raised to the common upper bound of the hom universes of `𝒮'` and `𝒳` by
`CategoryTheory.uliftFunctor`, so that no relation between those two universes is needed: the
three presheaves the factorisation relates are `Mor(a, b)`, `Mor(G a, G b)` — both valued in the
hom universe of `𝒮` and of `𝒮'`, which clause (1) of Stacks 02ZN ties together — and
`Mor(F a, F b)`, valued in the hom universe of `𝒳`. Raising preserves local injectivity, local
surjectivity and the sheaf condition
(`CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_typeUliftFunctor` and its
companions). -/
noncomputable def morMapULift {U : 𝒞} (a b : p.Fiber U) :
    morPresheaf p' ((fiberFunctorOfCompEq hG.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hG.comp_eq U).obj b) ⋙ uliftFunctor.{v₄} ⟶
      morPresheaf q ((fiberFunctorOfCompEq hF.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hF.comp_eq U).obj b) ⋙ uliftFunctor.{v} :=
  haveI := (hmor U a b).1
  haveI := (hmor U a b).2
  (Presheaf.existsUnique_hom_of_isLocallyBijective (J.over U)
    (Functor.whiskerRight (hG.morPresheafMap a b) uliftFunctor.{v₄})
    (hF.morPresheafMapULift a b)
    (Presheaf.isSheaf_whiskerRight_typeUliftFunctor (J.over U) (hqmor U _ _))).choose

/-- The defining property of `CategoryTheory.Functor.Stackification.morMapULift`. -/
lemma morPresheafMap_comp_morMapULift {U : 𝒞} (a b : p.Fiber U) :
    Functor.whiskerRight (hG.morPresheafMap a b) uliftFunctor.{v₄} ≫
        morMapULift hG hF hmor hqmor a b = hF.morPresheafMapULift a b :=
  have := (hmor U a b).1
  have := (hmor U a b).2
  (Presheaf.existsUnique_hom_of_isLocallyBijective (J.over U)
    (Functor.whiskerRight (hG.morPresheafMap a b) uliftFunctor.{v₄})
    (hF.morPresheafMapULift a b)
    (Presheaf.isSheaf_whiskerRight_typeUliftFunctor (J.over U) (hqmor U _ _))).choose_spec.1

/-- `CategoryTheory.Functor.Stackification.morMapULift` read on sections: it takes a section of
`Mor(G a, G b)` over an object of `𝒞/U` to a section of `Mor(F a, F b)` over that object. -/
noncomputable def morMapSection {U : 𝒞} (a b : p.Fiber U) {g : Over U}
    (s : pullbackFiber p' ((fiberFunctorOfCompEq hG.comp_eq U).obj a) g.hom ⟶
      pullbackFiber p' ((fiberFunctorOfCompEq hG.comp_eq U).obj b) g.hom) :
    pullbackFiber q ((fiberFunctorOfCompEq hF.comp_eq U).obj a) g.hom ⟶
      pullbackFiber q ((fiberFunctorOfCompEq hF.comp_eq U).obj b) g.hom :=
  ((morMapULift hG hF hmor hqmor a b).app (op g) (ULift.up s)).down

/-- **`morMapSection` undoes the image under `G`.** The section of `Mor(F a, F b)` attached to the
image under `G` of a section `u` of `Mor(a, b)` is the image of `u` under `F`. This is the
factorisation of `CategoryTheory.Functor.Stackification.morMapULift` read on sections. -/
@[simp]
lemma morMapSection_morMapAt {U : 𝒞} (a b : p.Fiber U) {V : 𝒞} (f : V ⟶ U)
    (u : pullbackFiber p a f ⟶ pullbackFiber p b f) :
    morMapSection hG hF hmor hqmor a b (g := Over.mk f) (hG.morMapAt a b f u) =
      hF.morMapAt a b f u := by
  have key : ULift.down ((morMapULift hG hF hmor hqmor a b).app (op (Over.mk f))
      ((Functor.whiskerRight (hG.morPresheafMap a b) uliftFunctor.{v₄}).app (op (Over.mk f))
        (ULift.up u))) =
      ULift.down ((hF.morPresheafMapULift a b).app (op (Over.mk f)) (ULift.up u)) := by
    rw [← morPresheafMap_comp_morMapULift hG hF hmor hqmor a b]
    rfl
  exact key

/-- **`morMapSection` commutes with restriction**, being the action on sections of a map of
presheaves. -/
lemma morRestrict_morMapSection {U : 𝒞} (a b : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (s : pullbackFiber p' ((fiberFunctorOfCompEq hG.comp_eq U).obj a) g₂.hom ⟶
      pullbackFiber p' ((fiberFunctorOfCompEq hG.comp_eq U).obj b) g₂.hom) :
    morRestrict q _ _ h (morMapSection hG hF hmor hqmor a b (g := g₂) s) =
      morMapSection hG hF hmor hqmor a b (g := g₁) (morRestrict p' _ _ h s) := by
  have hnat : (morPresheaf q ((fiberFunctorOfCompEq hF.comp_eq U).obj a)
          ((fiberFunctorOfCompEq hF.comp_eq U).obj b) ⋙ uliftFunctor.{v}).map h.op
        ((morMapULift hG hF hmor hqmor a b).app (op g₂) (ULift.up s)) =
      (morMapULift hG hF hmor hqmor a b).app (op g₁)
        ((morPresheaf p' ((fiberFunctorOfCompEq hG.comp_eq U).obj a)
          ((fiberFunctorOfCompEq hG.comp_eq U).obj b) ⋙ uliftFunctor.{v₄}).map h.op
          (ULift.up s)) :=
    (NatTrans.naturality_apply _ _ _).symm
  simp only [uliftMorPresheaf_map] at hnat
  exact ULift.up.inj hnat

/-- **The transfer of a morphism of a fibre along the stackification.** A morphism
`G a ⟶ G b` of the fibre of `𝒮'` over `U` determines a morphism `F a ⟶ F b` of the fibre of `𝒳`
over `U`: read it as a section of `Mor(G a, G b)` over the terminal object of `𝒞/U`, push it
through `CategoryTheory.Functor.Stackification.morMapULift`, and read the result back as a
morphism of the fibre. -/
noncomputable def transfer {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b) :
    (fiberFunctorOfCompEq hF.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hF.comp_eq U).obj b :=
  morOfSection q _ _
    (morMapSection hG hF hmor hqmor a b (g := Over.mk (𝟙 U)) (morSection p' _ _ θ))

/-- **The local characterization of the transfer.** Wherever a morphism `θ : G a ⟶ G b` of the
fibre is the image under `G` of a section `u` of `Mor(a, b)`, the base change of its transfer is
the image of `u` under `F`.

Since a morphism `G a ⟶ G b` is locally such an image and the presheaves `Mor` of `𝒳` are sheaves,
this determines the transfer, and every property of it below is proved from it. -/
lemma morMapAt_transfer {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b)
    {V : 𝒞} (f : V ⟶ U) (u : pullbackFiber p a f ⟶ pullbackFiber p b f)
    (hu : hG.morMapAt a b f u = pullbackFiberHom θ f) :
    pullbackFiberHom (transfer hG hF hmor hqmor θ) f = hF.morMapAt a b f u := by
  rw [← morRestrict_morSection q _ _ (transfer hG hF hmor hqmor θ) f, transfer,
    morSection_morOfSection, morRestrict_morMapSection, morRestrict_morSection, ← hu,
    morMapSection_morMapAt]

/-- **The transfer is the unique morphism with its local characterization.** A morphism
`ψ : F a ⟶ F b` of the fibre whose base changes along the members of a covering sieve are the
images under `F` of lifts of `θ` is the transfer of `θ`. This is the uniqueness that makes the
transfer usable: any construction with the local property of
`CategoryTheory.Functor.Stackification.morMapAt_transfer` agrees with it. -/
lemma eq_transfer_of_locally {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b)
    (ψ : (fiberFunctorOfCompEq hF.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hF.comp_eq U).obj b)
    {R : Sieve U} (hR : R ∈ J U)
    (h : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → ∃ u : pullbackFiber p a f ⟶ pullbackFiber p b f,
      hG.morMapAt a b f u = pullbackFiberHom θ f ∧ pullbackFiberHom ψ f = hF.morMapAt a b f u) :
    ψ = transfer hG hF hmor hqmor θ := by
  refine eq_of_pullbackFiberHom_locally_eq q (hqmor U _ _) hR ?_
  intro V f hf
  obtain ⟨u, hu, hψ⟩ := h f hf
  rw [hψ, morMapAt_transfer hG hF hmor hqmor θ f u hu]

/-- The transfer of the identity of `G a` is the identity of `F a`. -/
@[simp]
lemma transfer_id {U : 𝒞} (a : p.Fiber U) :
    transfer hG hF hmor hqmor (𝟙 ((fiberFunctorOfCompEq hG.comp_eq U).obj a)) = 𝟙 _ := by
  refine eq_of_pullbackFiberHom_locally_eq q (hqmor U _ _) (J.top_mem U) ?_
  intro V f _
  rw [morMapAt_transfer hG hF hmor hqmor _ f (𝟙 (pullbackFiber p a f))
      (by rw [hG.morMapAt_id, pullbackFiberHom_id]), hF.morMapAt_id, pullbackFiberHom_id]

/-- The transfer is functorial: it respects composition of morphisms of the fibre. Both sides have
the same base change along the members of a covering sieve on which both factors are images
under `G`, and the presheaves `Mor` of `𝒳` are sheaves. -/
lemma transfer_comp {U : 𝒞} {a b c : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b)
    (θ' : (fiberFunctorOfCompEq hG.comp_eq U).obj b ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj c) :
    transfer hG hF hmor hqmor (θ ≫ θ') =
      transfer hG hF hmor hqmor θ ≫ transfer hG hF hmor hqmor θ' := by
  obtain ⟨R, hR, hlift⟩ := exists_covering_lift hG hmor θ
  obtain ⟨R', hR', hlift'⟩ := exists_covering_lift hG hmor θ'
  refine eq_of_pullbackFiberHom_locally_eq q (hqmor U _ _) (J.intersection_covering hR hR') ?_
  rintro V f ⟨hf, hf'⟩
  obtain ⟨u, hu⟩ := hlift f hf
  obtain ⟨u', hu'⟩ := hlift' f hf'
  rw [morMapAt_transfer hG hF hmor hqmor _ f (u ≫ u')
      (by rw [hG.morMapAt_comp, hu, hu', pullbackFiberHom_comp]),
    hF.morMapAt_comp, pullbackFiberHom_comp, morMapAt_transfer hG hF hmor hqmor _ f u hu,
    morMapAt_transfer hG hF hmor hqmor _ f u' hu']

/-- The transfer of the image under `G` of a morphism of the fibre of `𝒮` is its image under `F`.
This is the 2-commutativity of the triangle of Stacks 0435 on fibres. -/
lemma transfer_map {U : 𝒞} {a b : p.Fiber U} (m : a ⟶ b) :
    transfer hG hF hmor hqmor ((fiberFunctorOfCompEq hG.comp_eq U).map m) =
      (fiberFunctorOfCompEq hF.comp_eq U).map m := by
  refine eq_of_pullbackFiberHom_locally_eq q (hqmor U _ _) (J.top_mem U) ?_
  intro V f _
  rw [morMapAt_transfer hG hF hmor hqmor _ f (pullbackFiberHom m f)
      (hG.morMapAt_pullbackFiberHom m f), hF.morMapAt_pullbackFiberHom m f]

/-- The transfer of an isomorphism of fibres. -/
@[simps]
noncomputable def transferIso {U : 𝒞} {a b : p.Fiber U}
    (e : (fiberFunctorOfCompEq hG.comp_eq U).obj a ≅ (fiberFunctorOfCompEq hG.comp_eq U).obj b) :
    (fiberFunctorOfCompEq hF.comp_eq U).obj a ≅ (fiberFunctorOfCompEq hF.comp_eq U).obj b where
  hom := transfer hG hF hmor hqmor e.hom
  inv := transfer hG hF hmor hqmor e.inv
  hom_inv_id := by
    rw [← transfer_comp, e.hom_inv_id, transfer_id]
  inv_hom_id := by
    rw [← transfer_comp, e.inv_hom_id, transfer_id]

/-- **The transfer commutes with base change.** The transfer of the morphism of the fibre over `V`
that `θ` induces between the chosen pullbacks is the morphism induced by the transfer of `θ`.

Over the members of a covering sieve of `V` pulled back from one on which `θ` is an image under
`G`, both sides are the image under `F` of one and the same section, by
`CategoryTheory.Functor.IsFibredOneMorphism.morMapAt_pullbackFiberCompIso` applied to `G` and
to `F`. -/
lemma transfer_pullbackFiberHom {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b)
    {V : 𝒞} (f : V ⟶ U) :
    transfer hG hF hmor hqmor ((hG.mapPullbackFiberIso a f).inv ≫ pullbackFiberHom θ f ≫
        (hG.mapPullbackFiberIso b f).hom) =
      (hF.mapPullbackFiberIso a f).inv ≫ pullbackFiberHom (transfer hG hF hmor hqmor θ) f ≫
        (hF.mapPullbackFiberIso b f).hom := by
  obtain ⟨R, hR, hlift⟩ := exists_covering_lift hG hmor θ
  refine eq_of_pullbackFiberHom_locally_eq q (hqmor V _ _) (J.pullback_stable f hR) ?_
  intro W γ hγ
  obtain ⟨u, hu⟩ := hlift (γ ≫ f) hγ
  rw [morMapAt_transfer hG hF hmor hqmor _ γ
    ((pullbackFiberCompIso a f γ).hom ≫ u ≫ (pullbackFiberCompIso b f γ).inv)
    (hG.morMapAt_pullbackFiberCompIso f γ u θ hu)]
  exact hF.morMapAt_pullbackFiberCompIso f γ u (transfer hG hF hmor hqmor θ)
    (morMapAt_transfer hG hF hmor hqmor θ (γ ≫ f) u hu).symm

/-- `CategoryTheory.Functor.Stackification.transfer_pullbackFiberHom` solved for the base change of
a transfer, which is how it is applied. -/
lemma pullbackFiberHom_transfer {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b)
    {V : 𝒞} (f : V ⟶ U) :
    pullbackFiberHom (transfer hG hF hmor hqmor θ) f =
      (hF.mapPullbackFiberIso a f).hom ≫
        transfer hG hF hmor hqmor ((hG.mapPullbackFiberIso a f).inv ≫ pullbackFiberHom θ f ≫
          (hG.mapPullbackFiberIso b f).hom) ≫ (hF.mapPullbackFiberIso b f).inv := by
  rw [transfer_pullbackFiberHom]
  simp

/-! ### The descent datum of the local presentations of an object of `𝒮'`

Clause (2) of Stacks 02ZN presents an object `x'` of the fibre of `𝒮'` over `U`, along the members
`f` of a covering sieve `R`, as the image under `G` of an object `s f` of the fibre of `𝒮`. The
images `F (s f)` then carry gluing isomorphisms — the transfers of the comparisons of the local
presentations — and form a descent datum for `𝒳` relative to `R`, whose effectiveness is the value
on `x'` of the extension of `F` along `G`. -/

section LocalPresentation

variable {U : 𝒞} {x' : p'.Fiber U} {R : Sieve U}
  (s : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V)
  (φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
    (fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf) ≅ pullbackFiber p' x' f)

/-- The comparison, in the fibre of `𝒮'` over `Z`, of the chosen pullbacks along `ε` and `ε'` of
the two local presentations of `x'` at a pair of members of the sieve: both present the chosen
pullback of `x'` along the common composite. -/
noncomputable def localIsoCore ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullbackFiber p' ((fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf)) ε ≅
      pullbackFiber p' ((fiberFunctorOfCompEq hG.comp_eq W).obj (s g hg)) ε' :=
  pullbackFiberIso (φ f hf) ε ≪≫ pullbackFiberComparison x' ε ε' heq ≪≫
    (pullbackFiberIso (φ g hg) ε').symm

omit [p.IsFibered] in
/-- The forward morphism of `localIsoCore` is the base change of `(φ f hf).hom` along `ε`,
followed by the comparison `CategoryTheory.Functor.pullbackFiberComparison` and the base change
of `(φ g hg).inv` along `ε'`. -/
@[simp]
lemma localIsoCore_hom ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (localIsoCore hG s φ hf hg ε ε' heq).hom =
      pullbackFiberHom (φ f hf).hom ε ≫ (pullbackFiberComparison x' ε ε' heq).hom ≫
        pullbackFiberHom (φ g hg).inv ε' := by
  simp [localIsoCore]

omit [p.IsFibered] in
/-- The comparison of the local presentations is compatible with base change: over `Z'` it is the
base change of the one over `Z`, after the iterated chosen pullbacks are contracted. This is the
compatibility of `CategoryTheory.Functor.pullbackFiberComparison` with base change, conjugated by
the local presentations. -/
lemma localIsoCore_pullback ⦃V W Z Z' : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z) :
    (pullbackFiberCompIso ((fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf)) ε γ).inv ≫
        pullbackFiberHom (localIsoCore hG s φ hf hg ε ε' heq).hom γ ≫
        (pullbackFiberCompIso ((fiberFunctorOfCompEq hG.comp_eq W).obj (s g hg)) ε' γ).hom =
      (localIsoCore hG s φ hf hg (γ ≫ ε) (γ ≫ ε')
        (by rw [Category.assoc, Category.assoc, heq])).hom := by
  rw [localIsoCore_hom, localIsoCore_hom, pullbackFiberHom_comp, pullbackFiberHom_comp,
    pullbackFiberHom_comp_base (φ f hf).hom ε γ, pullbackFiberHom_comp_base (φ g hg).inv ε' γ,
    ← pullbackFiberComparison_pullback x' ε ε' heq γ, pullbackFiberIso_hom]
  simp [Category.assoc, Iso.hom_inv_id_assoc]

/-- The comparison of the local presentations, read as an isomorphism between the images under `G`
of the chosen pullbacks of the two local objects. This is the morphism of `𝒮'` whose transfer is
the gluing isomorphism of the descent datum for `𝒳`. -/
noncomputable def localIso ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (fiberFunctorOfCompEq hG.comp_eq Z).obj (pullbackFiber p (s f hf) ε) ≅
      (fiberFunctorOfCompEq hG.comp_eq Z).obj (pullbackFiber p (s g hg) ε') :=
  (hG.mapPullbackFiberIso (s f hf) ε).symm ≪≫ localIsoCore hG s φ hf hg ε ε' heq ≪≫
    hG.mapPullbackFiberIso (s g hg) ε'

/-- The forward morphism of `localIso` is the forward morphism of `localIsoCore`, conjugated by
the comparisons `IsFibredOneMorphism.mapPullbackFiberIso` of `G`. -/
@[simp]
lemma localIso_hom ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (localIso hG s φ hf hg ε ε' heq).hom =
      (hG.mapPullbackFiberIso (s f hf) ε).inv ≫ (localIsoCore hG s φ hf hg ε ε' heq).hom ≫
        (hG.mapPullbackFiberIso (s g hg) ε').hom := by
  simp [localIso]

/-- The comparisons of the local presentations compose: this is the cocycle condition, and it comes
from the corresponding identity for `CategoryTheory.Functor.pullbackFiberComparison`. -/
lemma localIso_comp ⦃V W X' Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U} (hg : R.arrows g)
    {h : X' ⟶ U} (hh : R.arrows h) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X')
    (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    (localIso hG s φ hf hg ε₁ ε₂ h₁₂).hom ≫ (localIso hG s φ hg hh ε₂ ε₃ h₂₃).hom =
      (localIso hG s φ hf hh ε₁ ε₃ h₁₃).hom := by
  simp only [localIso_hom, localIsoCore_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullbackFiberHom_inv_hom_id_assoc]
  rw [← Category.assoc (pullbackFiberComparison x' ε₁ ε₂ h₁₂).hom,
    pullbackFiberComparison_comp x' ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]

/-- **The comparison of the local presentations against base change.** Contracting the iterated
chosen pullbacks of the two local objects turns the base change along `γ` of the comparison at
`(ε, ε')` into the comparison at `(γ ≫ ε, γ ≫ ε')`.

This is `CategoryTheory.Functor.Stackification.localIsoCore_pullback`, conjugated by the
compatibility of the two comparisons of `G`,
`IsFibredOneMorphism.mapPullbackFiberCompIso_hom_comp`. -/
lemma localIso_pullback ⦃V W Z Z' : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z) :
    (fiberFunctorOfCompEq hG.comp_eq Z').map (pullbackFiberCompIso (s f hf) ε γ).inv ≫
        (hG.mapPullbackFiberIso (pullbackFiber p (s f hf) ε) γ).inv ≫
        pullbackFiberHom (localIso hG s φ hf hg ε ε' heq).hom γ ≫
        (hG.mapPullbackFiberIso (pullbackFiber p (s g hg) ε') γ).hom ≫
        (fiberFunctorOfCompEq hG.comp_eq Z').map (pullbackFiberCompIso (s g hg) ε' γ).hom =
      (localIso hG s φ hf hg (γ ≫ ε) (γ ≫ ε')
        (by rw [Category.assoc, Category.assoc, heq])).hom := by
  rw [localIso_hom, localIso_hom, pullbackFiberHom_comp, pullbackFiberHom_comp,
    hG.pullbackFiberHom_mapPullbackFiberIso_inv (s f hf) ε γ,
    hG.pullbackFiberHom_mapPullbackFiberIso_hom (s g hg) ε' γ]
  simp only [Category.assoc]
  rw [← Category.assoc (hG.mapPullbackFiberIso (pullbackFiber p (s f hf) ε) γ).inv,
    hG.mapPullbackFiberCompIso_comp_hom]
  simp only [Category.assoc]
  rw [map_inv_comp_map_hom_assoc, ← Category.assoc
      (hG.mapPullbackFiberCompIso (s g hg) ε' γ).inv, hG.mapPullbackFiberCompIso_inv_comp]
  simp only [Category.assoc]
  rw [map_inv_comp_map_hom, Category.comp_id,
    reassoc_of% localIsoCore_pullback hG s φ hf hg ε ε' heq γ]

/-- **The descent datum for `𝒳` of the local presentations of `x'`.** Its object at a member `f` of
the sieve is the image under `F` of the local object `s f`, and its gluing isomorphisms are the
transfers of the comparisons `CategoryTheory.Functor.Stackification.localIso`, conjugated by the
comparison `IsFibredOneMorphism.mapPullbackFiberIso` of `F`.

The cocycle condition is functoriality of the transfer together with
`CategoryTheory.Functor.Stackification.localIso_comp`, and the compatibility with base change is
the compatibility of the transfer with base change together with
`CategoryTheory.Functor.Stackification.localIsoCore_pullback`. -/
@[implicit_reducible]
noncomputable def descentDatum : SieveDescentDatum q R where
  obj := fun {V} f hf => (fiberFunctorOfCompEq hF.comp_eq V).obj (s f hf)
  iso := fun {_V _W _Z} {_f} hf {_g} hg ε ε' heq =>
    hF.mapPullbackFiberIso (s _ hf) ε ≪≫
      transferIso hG hF hmor hqmor (localIso hG s φ hf hg ε ε' heq) ≪≫
      (hF.mapPullbackFiberIso (s _ hg) ε').symm
  cocycle := by
    intro V W X' Z f hf g hg h hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃
    simp only [Iso.trans_hom, Iso.symm_hom, transferIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Category.assoc (transfer hG hF hmor hqmor (localIso hG s φ hf hg ε₁ ε₂ h₁₂).hom),
      ← transfer_comp, localIso_comp]
  iso_pullback := by
    intro V W Z Z' f hf g hg ε ε' heq γ
    have hT : (fiberFunctorOfCompEq hF.comp_eq Z').map (pullbackFiberCompIso (s f hf) ε γ).inv ≫
        transfer hG hF hmor hqmor
            ((hG.mapPullbackFiberIso (pullbackFiber p (s f hf) ε) γ).inv ≫
              pullbackFiberHom (localIso hG s φ hf hg ε ε' heq).hom γ ≫
              (hG.mapPullbackFiberIso (pullbackFiber p (s g hg) ε') γ).hom) ≫
          (fiberFunctorOfCompEq hF.comp_eq Z').map (pullbackFiberCompIso (s g hg) ε' γ).hom =
        transfer hG hF hmor hqmor (localIso hG s φ hf hg (γ ≫ ε) (γ ≫ ε')
          (by rw [Category.assoc, Category.assoc, heq])).hom := by
      rw [← transfer_map hG hF hmor hqmor (pullbackFiberCompIso (s f hf) ε γ).inv,
        ← transfer_map hG hF hmor hqmor (pullbackFiberCompIso (s g hg) ε' γ).hom,
        ← transfer_comp, ← transfer_comp]
      simp only [Category.assoc]
      rw [localIso_pullback]
    simp only [Iso.trans_hom, Iso.symm_hom, transferIso_hom, pullbackFiberIso_hom,
      pullbackFiberHom_comp, Category.assoc]
    rw [← hF.mapPullbackFiberCompIso_inv_eq_assoc (s f hf) ε γ,
      ← hF.mapPullbackFiberCompIso_hom_eq (s g hg) ε' γ,
      pullbackFiberHom_transfer hG hF hmor hqmor _ γ]
    simp only [Category.assoc]
    rw [hF.mapPullbackFiberCompIso_inv_comp_assoc (s f hf) ε γ,
      hF.mapPullbackFiberCompIso_comp_hom (s g hg) ε' γ, reassoc_of% hT]

/-- The gluing isomorphisms of `CategoryTheory.Functor.Stackification.descentDatum`, unfolded: the
transfer of the comparison of the local presentations, conjugated by the comparisons of `F` with
the chosen pullbacks. -/
lemma descentDatum_iso_hom ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    ((descentDatum hG hF hmor hqmor s φ).iso hf hg ε ε' heq).hom =
      (hF.mapPullbackFiberIso (s f hf) ε).hom ≫
        transfer hG hF hmor hqmor (localIso hG s φ hf hg ε ε' heq).hom ≫
          (hF.mapPullbackFiberIso (s g hg) ε').inv :=
  rfl

/-- **The descent datum of the local presentations is effective.** The object of the fibre of `𝒳`
over `U` that it descends to is the value on `x'` of an extension of `F` along `G`, and the family
`ζ` of cartesian morphisms is the comparison of that value with the images under `F` of the local
objects.

This is step 3 of the proof of Stacks 0435: with the value on objects in hand, what remains is the
action of the extension on morphisms and the 2-isomorphism. -/
theorem exists_descends (hdesc : HasEffectiveDescent q J) (hR : R ∈ J U) :
    ∃ (y : q.Fiber U) (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
        ((descentDatum hG hF hmor hqmor s φ).obj f hf).1 ⟶ y.1),
      (descentDatum hG hF hmor hqmor s φ).Descends q y ζ :=
  hdesc R hR (descentDatum hG hF hmor hqmor s φ)

end LocalPresentation

/-- **The value on objects of an extension of `F` along `G`.** Let `x'` be an object of the fibre
of `𝒮'` over `U` which is, along the members of a covering sieve `R`, in the essential image of `G`
on fibres — clause (2) of Stacks 02ZN. Then there are local objects `s f` of `𝒮` presenting `x'`,
an object `y` of the fibre of `𝒳` over `U`, and a family of cartesian morphisms exhibiting `y` as
the object to which the images under `F` of the `s f` descend. -/
theorem exists_descends_of_locally_essImage (hdesc : HasEffectiveDescent q J) {U : 𝒞}
    (x' : p'.Fiber U) {R : Sieve U} (hR : R ∈ J U)
    (hess : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x' f)) :
    ∃ (y : q.Fiber U) (s : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V)
      (φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
        (fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf) ≅ pullbackFiber p' x' f)
      (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
        ((fiberFunctorOfCompEq hF.comp_eq V).obj (s f hf)).1 ⟶ y.1),
      (descentDatum hG hF hmor hqmor s φ).Descends q y ζ := by
  have hess' : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), ∃ z : p.Fiber V,
      Nonempty ((fiberFunctorOfCompEq hG.comp_eq V).obj z ≅ pullbackFiber p' x' f) :=
    fun {_V} f hf => hess hf
  obtain ⟨y, ζ, hζ⟩ := hdesc R hR (descentDatum hG hF hmor hqmor
    (fun {_V} f hf => (hess' f hf).choose) (fun {_V} f hf => (hess' f hf).choose_spec.some))
  exact ⟨y, _, _, ζ, hζ⟩

/-! ### The datum of an object globally in the image of `G`

When `x'` is the image `G a` of an object of `𝒮`, the chosen pullbacks of `a` present it along
every sieve, and the resulting descent datum for `𝒳` descends to `F a`. Together with
`CategoryTheory.Functor.SieveDescentDatum.nonempty_iso_of_descends` this identifies the value of
any extension of `F` along `G` at `G a` with `F a`, which is the 2-isomorphism of Stacks 0435 on
objects. -/

section GlobalPresentation

variable {U : 𝒞} (a : p.Fiber U) (R : Sieve U)

/-- The chosen pullbacks of an object `a` of the fibre of `𝒮` over `U`, as the local objects
presenting `G a` along any sieve on `U`. -/
@[implicit_reducible]
noncomputable def pullbackObjects : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V :=
  fun ⦃_V⦄ f _ => pullbackFiber p a f

/-- The comparison `IsFibredOneMorphism.mapPullbackFiberIso`, read as the local presentation of
`G a` by the chosen pullbacks of `a`. -/
@[implicit_reducible]
noncomputable def pullbackPresentation :
    ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      (fiberFunctorOfCompEq hG.comp_eq V).obj (pullbackObjects a R f hf) ≅
        pullbackFiber p' ((fiberFunctorOfCompEq hG.comp_eq U).obj a) f :=
  fun ⦃_V⦄ f _ => (hG.mapPullbackFiberIso a f).symm

/-- The comparison of the local presentations of `G a` by the chosen pullbacks of `a` is the image
under `G` of the canonical comparison of the chosen pullbacks of `a` itself. Both composites with
the cartesian morphism to `G a` over the common base morphism are the image under `G` of the
composite of the two chosen lifts. -/
lemma localIso_pullbackPresentation ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (localIso hG (pullbackObjects a R) (pullbackPresentation hG a R) hf hg ε ε' heq).hom =
      (fiberFunctorOfCompEq hG.comp_eq Z).map (pullbackFiberComparison a ε ε' heq).hom := by
  have hGc : p'.IsStronglyCartesian (ε' ≫ g)
      (G.map (IsPreFibered.pullbackMap (pullbackFiber p a g).2 ε' ≫
        IsPreFibered.pullbackMap a.2 g)) :=
    hG.map_isStronglyCartesian _ _ inferInstance
  have hGc' : p'.IsCartesian (ε ≫ f)
      (G.map (IsPreFibered.pullbackMap (pullbackFiber p a g).2 ε' ≫
        IsPreFibered.pullbackMap a.2 g)) := by
    rw [heq]; infer_instance
  refine fiber_hom_ext_of_cartesian (ε ≫ f)
    (G.map (IsPreFibered.pullbackMap (pullbackFiber p a g).2 ε' ≫
      IsPreFibered.pullbackMap a.2 g)) hGc' _ _ ?_
  rw [localIso_hom, localIsoCore_hom]
  simp only [pullbackPresentation, Fiber.fiberInclusion.map_comp, Functor.map_comp,
    Category.assoc, Iso.symm_hom, Iso.symm_inv, fiberInclusion_map_fiberFunctorOfCompEq_map,
    IsFibredOneMorphism.mapPullbackFiberIso_hom_fac_assoc,
    IsFibredOneMorphism.mapPullbackFiberIso_hom_fac, pullbackFiberHom_fac_assoc,
    pullbackFiberComparison_hom_fac, IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  exact (map_pullbackFiberComparison_hom_fac G a ε ε' heq).symm

/-- **The descent datum of a globally presented object descends to the image under `F`.** For the
presentation of `G a` by the chosen pullbacks of `a`, the descent datum for `𝒳` of
`CategoryTheory.Functor.Stackification.descentDatum` descends to `F a` along the images under `F`
of the chosen cartesian lifts. -/
theorem descentDatum_descends_map :
    (descentDatum hG hF hmor hqmor (pullbackObjects a R)
        (pullbackPresentation hG a R)).Descends q ((fiberFunctorOfCompEq hF.comp_eq U).obj a)
      (fun ⦃V⦄ (f : V ⟶ U) (_ : R.arrows f) => F.map (IsPreFibered.pullbackMap a.2 f)) := by
  refine ⟨fun {_V} f _ => hF.isCartesian_map_pullbackMap a f, ?_⟩
  intro V W Z f hf g hg ε ε' heq
  rw [descentDatum_iso_hom, localIso_pullbackPresentation hG a R hf hg ε ε' heq, transfer_map]
  simp [Fiber.fiberInclusion.map_comp, Category.assoc,
    fiberInclusion_map_fiberFunctorOfCompEq_map,
    IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc,
    map_pullbackFiberComparison_hom_fac,
    IsFibredOneMorphism.mapPullbackFiberIso_hom_fac_assoc]

/-- **The value of an extension of `F` along `G` at `G a` is `F a`.** Any object of the fibre of
`𝒳` over `U` to which the descent datum of the presentation of `G a` by the chosen pullbacks of `a`
descends is isomorphic to `F a`. This is the 2-isomorphism of Stacks 0435 on objects. -/
theorem nonempty_iso_map_of_descends {y : q.Fiber U} (hR : R ∈ J U)
    {ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      ((descentDatum hG hF hmor hqmor (pullbackObjects a R)
        (pullbackPresentation hG a R)).obj f hf).1 ⟶ y.1}
    (hζ : (descentDatum hG hF hmor hqmor (pullbackObjects a R)
      (pullbackPresentation hG a R)).Descends q y ζ) :
    Nonempty (y ≅ (fiberFunctorOfCompEq hF.comp_eq U).obj a) :=
  SieveDescentDatum.nonempty_iso_of_descends (hqmor U) hR hζ
    (descentDatum_descends_map hG hF hmor hqmor a R)

end GlobalPresentation

end Stackification

end Transfer

/-! ### The hypotheses of Stacks 0435 in the form Stacks 02ZN provides them -/

section IsStack

universe v v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v₄} 𝒳]

/-- **The object half of Stacks 0435.** Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` be a fibred
category, let `G : 𝒮 ⥤ 𝒮'` exhibit `𝒮'` as the stackification of `𝒮` — a 1-morphism onto a stack
satisfying the two clauses of Stacks 02ZN — and let `F : 𝒮 ⥤ 𝒳` be a 1-morphism of fibred
categories over `𝒞` into a stack. Then every object `x'` of a fibre of `𝒮'` is presented, along a
covering sieve, by objects of `𝒮` whose images under `F` descend to an object `y` of the fibre
of `𝒳`.

That object is the value on `x'` of the 1-morphism `H : 𝒮' ⥤ 𝒳` asserted by Stacks 0435. The
gluing isomorphisms of the descent datum are the transfers along `G` of the comparisons of the
local presentations, `CategoryTheory.Functor.Stackification.descentDatum`. -/
theorem Stackification.exists_descends_of_isStack {J : GrothendieckTopology 𝒞} {p : 𝒮 ⥤ 𝒞}
    {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {F : 𝒮 ⥤ 𝒳} [p.IsFibered] (hp' : p'.IsStack J)
    (hq : q.IsStack J) (hG : p.IsFibredOneMorphism p' G) (hF : p.IsFibredOneMorphism q F)
    (hmor : haveI : p'.IsFibered := hp'.isFibered
      ∀ (U : 𝒞) (x y : p.Fiber U),
        Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
          Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
    (hobj : haveI : p'.IsFibered := hp'.isFibered
      ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x' f))
    (U : 𝒞) (x' : p'.Fiber U) :
    haveI : p'.IsFibered := hp'.isFibered
    haveI : q.IsFibered := hq.isFibered
    ∃ (y : q.Fiber U) (R : Sieve U) (_ : R ∈ J U)
      (s : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V)
      (φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
        (fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf) ≅ pullbackFiber p' x' f)
      (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
        ((fiberFunctorOfCompEq hF.comp_eq V).obj (s f hf)).1 ⟶ y.1),
      (Stackification.descentDatum hG hF hmor (fun U x y => hq.isMorSheaf U x y) s φ).Descends
        q y ζ := by
  have : p'.IsFibered := hp'.isFibered
  have : q.IsFibered := hq.isFibered
  obtain ⟨R, hR, hess⟩ := hobj U x'
  obtain ⟨y, s, φ, ζ, hζ⟩ := Stackification.exists_descends_of_locally_essImage hG hF hmor
    (fun U x y => hq.isMorSheaf U x y) hq.hasEffectiveDescent x' hR hess
  exact ⟨y, R, hR, s, φ, ζ, hζ⟩

end IsStack

end Functor

end CategoryTheory
