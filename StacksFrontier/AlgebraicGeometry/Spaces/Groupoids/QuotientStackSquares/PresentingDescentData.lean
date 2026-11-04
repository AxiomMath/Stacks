module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FibreFullFaithfulness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyFunctor

/-!
# Objects of a quotient stack as descent data in the presenting groupoid

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `[U/R]` be its quotient stack and let
`π : 𝒮_U ⟶ [U/R]` be the canonical 1-morphism from the pointwise groupoid presentation. An
object `x` of the fibre `[U/R]_T` becomes, after an fppf covering `{T i ⟶ T}` of the test
object, isomorphic to `π (u i)` for points `u i` of the object space; the resulting transition
isomorphisms on the overlaps are the images under `π` of arrows `r i j` of the arrow space, the
system `(u i, r i j)` is a descent datum for the presentation, every such system arises this
way, and morphisms of `[U/R]` over `T` are exactly morphisms of these descent data,
compatibly with refinement of the covering.

This is **Stacks 044X**, parts (1)–(6). The descent data of the source are descent data for the
*pointwise groupoid fibration* `quotientPrestack G`, whose fibre over a test object `T` has
`U (T)` for objects and `R (T)` for arrows; so the category of systems `(u i, r i j)` of the
source is `CategoryTheory.Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰`, and `π` induces
a functor from it to the descent data of `[U/R]` relative to the same covering.

## Main definitions

* `AlgebraicGeometry.Stack.presentingDescentFunctor`: the functor on descent data relative to a
  fixed covering induced by the canonical 1-morphism from the pointwise groupoid presentation to
  the quotient stack.
* `AlgebraicGeometry.Stack.homEquiv_presentingDescentDatum`: the canonical bijection of part (5),
  bundled with the equation that characterises it.
* `AlgebraicGeometry.Stack.presentingDescentFunctor_refinementIso`: the compatibility of part (6)
  with refinement of the covering.

## Main results

* `AlgebraicGeometry.Stack.presentingDescentFunctor_obj`,
  `AlgebraicGeometry.Stack.presentingDescentFunctor_hom` and
  `AlgebraicGeometry.Stack.presentingDescentFunctor_map_hom`: the components of the induced
  functor, which are parts (2) and (5) read off the construction.
* `AlgebraicGeometry.Stack.exists_presentingDescentDatum`: parts (1)–(3) — every object of a
  fibre of the quotient stack is, after an fppf covering, the projection of a descent datum for
  the presentation.
* `AlgebraicGeometry.Stack.effective_presentingDescentDatum`: part (4) — every descent datum for
  the presentation arises in that way.
* `AlgebraicGeometry.Stack.fullyFaithful_presentingDescentFunctor` and
  `AlgebraicGeometry.Stack.homEquiv_presentingDescentDatum`: part (5).

## Implementation notes

The source's covering `{T i ⟶ T}` is a family, so the descent data used here are those relative
to a `CategoryTheory.PreZeroHypercover`, and the transition arrow on an overlap is given not for
a chosen fibre product `T i ×_T T j` but for every pair of maps `a : W ⟶ T i`, `c : W ⟶ T j`
agreeing over `T`; the cocycle condition is then the single equation `hom_comp` for a triple of
such maps. The index type of the covering produced in
`AlgebraicGeometry.Stack.exists_presentingDescentDatum` lies in the universe of the site, which
is what `CategoryTheory.Precoverage.ZeroHypercover.restrictIndexOfSmall` provides once
`AlgebraicGeometry.bigFppfPrecoverage_eq_comap` identifies the site's chosen covering
families with the fppf ones.

Several steps are pure fibred-category bookkeeping and are kept `private` and stated for an
arbitrary 1-morphism of fibred categories: the naturality of the comparison between the chosen
pullback of an image and the image of a chosen pullback, its compatibility with composition, and
the transport of a descent datum along isomorphisms of its local objects.

Part (2) on a single test object is
`AlgebraicGeometry.Stack.fullyFaithful_fiberFunctor_toQuotientStack`, in
`FibreFullFaithfulness.lean`; it is used here through
`AlgebraicGeometry.Stack.presentingDescentFunctor` and is stated there because it needs nothing
of the descent data of this file.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor.IsFibered

universe u w u₁ u₂ u₃ v₁ v₂

namespace AlgebraicGeometry.Stack

/- The pullback pseudofunctor of a fibred category is built from the fibres and the chosen
pullbacks, but none of the definitions involved is unfolded at `implicit` transparency, so the
identifications `(pullbackPseudofunctor p).obj ⟨op U⟩ = p.Fiber U` and
`((pullbackPseudofunctor p).map f.op.toLoc).obj a = p.pullbackFiber a f` -- which hold by `rfl`
-- are invisible to the ordinary tactics. Naming the definitions is what lets them see through
it, as in `IsomorphismSheafAlgebraic.lean`.

The last two entries are what mediate the two spellings of a *pulled-back* descent datum: the
object of `Functor.FamilyDescentDatum.pull q Φ D` over `i` is `q.pullbackFiber (D.obj (Φ.s₀ i))
(Φ.h₀ i)` by `rfl`, but only through `Pseudofunctor.DescentData.pullFunctorObj`. Without them
the goal of `presentingDescentFunctor_refinementIso` is not type-correct at `implicit`
transparency after `pull_hom_eq`, so neither `rw` nor `simp` can act on it. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.homMk CategoryTheory.Functor.pullbackFiberHom
  CategoryTheory.Functor.IsFibered.pullbackPseudofunctor
  CategoryTheory.Functor.IsFibered.pbObj CategoryTheory.Functor.IsFibered.pbMap
  CategoryTheory.Functor.IsFibered.fiberPullback
  CategoryTheory.Functor.IsFibered.fiberPullbackMap
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  CategoryTheory.Cat.str CategoryTheory.LocallyDiscrete.categoryStruct
  CategoryTheory.catToReflQuiver
  CategoryTheory.Functor.Fiber.fiberCategory Quiver.Hom.toLoc
  CategoryTheory.Pseudofunctor.DescentData.pullFunctorObj
  CategoryTheory.Functor.FamilyDescentDatum.pull

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### Naturality of the comparison with the chosen pullbacks -/

@[reassoc]
private lemma mapPullbackIso_naturality
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒮} {a b : q.Fiber U} (φ : a ⟶ b)
    {V : 𝒮} (f : V ⟶ U) :
    (Functor.fiberFunctorOfCompEq hF.comp_eq V).map (Functor.pullbackFiberHom φ f) ≫
        (hF.mapPullbackFiberIso b f).inv =
      (hF.mapPullbackFiberIso a f).inv ≫
        Functor.pullbackFiberHom ((Functor.fiberFunctorOfCompEq hF.comp_eq U).map φ) f := by
  refine Functor.fiber_hom_ext_of_cartesian f
    (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj b).2 f)
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    Functor.pullbackFiberHom_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, Functor.pullbackFiberHom_fac]

private lemma pullbackFiberHom_fiberFunctor_map
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒮} {a b : q.Fiber U} (φ : a ⟶ b)
    {V : 𝒮} (f : V ⟶ U) :
    Functor.pullbackFiberHom ((Functor.fiberFunctorOfCompEq hF.comp_eq U).map φ) f =
      (hF.mapPullbackFiberIso a f).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq V).map (Functor.pullbackFiberHom φ f) ≫
        (hF.mapPullbackFiberIso b f).inv := by
  rw [mapPullbackIso_naturality hF φ f]
  simp

/-- The descent-datum compatibility square of a morphism of descent data, read off the fibres.

Stated at an abstract fibred 1-morphism, where `hF` is a variable: at the call site `hF` is
let-bound and `FullyFaithful.map_preimage` reintroduces the unfolded spelling of `comp_eq`, so
the two sides of `pullbackFiberHom_fiberFunctor_map` are `rfl`-equal but not syntactically
equal and `rw`/`simp` cannot match them.  Here the match is syntactic and the only defeq the
call site needs is the one `exact` performs. -/
private lemma fiberFunctor_map_comm_of_image_comm
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {W U₁ U₂ : 𝒮}
    {d₁ e₁ : q.Fiber U₁} {d₂ e₂ : q.Fiber U₂}
    (ψ₁ : d₁ ⟶ e₁) (ψ₂ : d₂ ⟶ e₂) (a : W ⟶ U₁) (c : W ⟶ U₂)
    (dh : Functor.pullbackFiber q d₁ a ⟶ Functor.pullbackFiber q d₂ c)
    (eh : Functor.pullbackFiber q e₁ a ⟶ Functor.pullbackFiber q e₂ c)
    (h : Functor.pullbackFiberHom
          ((Functor.fiberFunctorOfCompEq hF.comp_eq U₁).map ψ₁) a ≫
            (hF.mapPullbackFiberIso e₁ a).hom ≫
            (Functor.fiberFunctorOfCompEq hF.comp_eq W).map eh ≫
            (hF.mapPullbackFiberIso e₂ c).inv =
        ((hF.mapPullbackFiberIso d₁ a).hom ≫
            (Functor.fiberFunctorOfCompEq hF.comp_eq W).map dh ≫
            (hF.mapPullbackFiberIso d₂ c).inv) ≫
          Functor.pullbackFiberHom
            ((Functor.fiberFunctorOfCompEq hF.comp_eq U₂).map ψ₂) c) :
    (Functor.fiberFunctorOfCompEq hF.comp_eq W).map
        (Functor.pullbackFiberHom ψ₁ a ≫ eh) =
      (Functor.fiberFunctorOfCompEq hF.comp_eq W).map
        (dh ≫ Functor.pullbackFiberHom ψ₂ c) := by
  rw [pullbackFiberHom_fiberFunctor_map hF ψ₁ a,
    pullbackFiberHom_fiberFunctor_map hF ψ₂ c] at h
  simpa only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right_assoc] using h

@[reassoc]
private lemma mapPullbackIso_compIso_hom
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒮} (a : q.Fiber U)
    {V Z : 𝒮} (f : V ⟶ U) (γ : Z ⟶ V) :
    (Functor.fiberFunctorOfCompEq hF.comp_eq Z).map
          (Functor.pullbackFiberCompIso a f γ).hom ≫
        (hF.mapPullbackFiberIso a (γ ≫ f)).inv =
      (hF.mapPullbackFiberIso (Functor.pullbackFiber q a f) γ).inv ≫
        Functor.pullbackFiberHom (hF.mapPullbackFiberIso a f).inv γ ≫
        (Functor.pullbackFiberCompIso
          ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f γ).hom := by
  refine Functor.fiber_hom_ext_of_cartesian (γ ≫ f)
    (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a).2 (γ ≫ f))
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    Functor.pullbackFiberCompIso_hom_fac, Functor.pullbackFiberHom_fac_assoc,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    Functor.pullbackFiberCompIso_hom_fac]

@[reassoc]
private lemma mapPullbackIso_compIso_inv
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒮} (a : q.Fiber U)
    {V Z : 𝒮} (f : V ⟶ U) (γ : Z ⟶ V) :
    (hF.mapPullbackFiberIso a (γ ≫ f)).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq Z).map
          (Functor.pullbackFiberCompIso a f γ).inv ≫
        (hF.mapPullbackFiberIso (Functor.pullbackFiber q a f) γ).inv =
      (Functor.pullbackFiberCompIso
          ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f γ).inv ≫
        Functor.pullbackFiberHom (hF.mapPullbackFiberIso a f).hom γ := by
  have hγ : r.IsCartesian γ (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj (Functor.pullbackFiber q a f)).2 γ) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian _ _
  have hf : r.IsCartesian f (F.map (Functor.IsPreFibered.pullbackMap a.2 f)) :=
    hF.isCartesian_map_pullbackMap a f
  refine Functor.fiber_hom_ext_of_cartesian (p := r) (γ ≫ f)
    (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj (Functor.pullbackFiber q a f)).2 γ ≫
      F.map (Functor.IsPreFibered.pullbackMap a.2 f)) inferInstance _ _ ?_
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac,
    Functor.pullbackFiberHom_fac_assoc, Functor.pullbackFiberCompIso_inv_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    Functor.pullbackFiberCompIso_inv_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac hF a (γ ≫ f)]

@[reassoc]
private lemma pullbackFiberHom_mapPullbackIso_hom
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒮} (a : q.Fiber U)
    {V Z : 𝒮} (f : V ⟶ U) (γ : Z ⟶ V) :
    Functor.pullbackFiberHom (hF.mapPullbackFiberIso a f).hom γ ≫
        (hF.mapPullbackFiberIso (Functor.pullbackFiber q a f) γ).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq Z).map
          (Functor.pullbackFiberCompIso a f γ).hom =
      (Functor.pullbackFiberCompIso
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f γ).hom ≫
        (hF.mapPullbackFiberIso a (γ ≫ f)).hom := by
  rw [← cancel_mono (hF.mapPullbackFiberIso a (γ ≫ f)).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    mapPullbackIso_compIso_hom, Iso.hom_inv_id_assoc]
  rw [← Functor.pullbackFiberHom_comp_assoc]
  simp

/-! ### The functor on descent data induced by the quotient projection -/

/- The cocycle condition is preserved by conjugating with a functor and comparison
isomorphisms. Stated separately because the two sides of the condition for the projected datum
live in a fibre of the pullback pseudofunctor, where the ordinary tactics do not see the
composition of arrows of a fibre; applied as a whole it needs no rewriting inside that fibre. -/
private lemma conjugate_comp {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ]
    (Φ : 𝒜 ⥤ ℬ) {p₁ p₂ p₃ : 𝒜} {x₁ x₂ x₃ : ℬ}
    (e₁ : x₁ ≅ Φ.obj p₁) (e₂ : x₂ ≅ Φ.obj p₂) (e₃ : x₃ ≅ Φ.obj p₃)
    (m₁ : p₁ ⟶ p₂) (m₂ : p₂ ⟶ p₃) (m₃ : p₁ ⟶ p₃) (hm : m₁ ≫ m₂ = m₃) :
    (e₁.hom ≫ Φ.map m₁ ≫ e₂.inv) ≫ e₂.hom ≫ Φ.map m₂ ≫ e₃.inv =
      e₁.hom ≫ Φ.map m₃ ≫ e₃.inv := by
  rw [← hm, Φ.map_comp]
  simp

/- Two conjugated composites agree as soon as the composites inside the functor agree. Used for
the naturality square of the projected morphism of descent data, for the same reason as
`conjugate_comp`. -/
private lemma conjugate_comp_eq {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ]
    (Φ : 𝒜 ⥤ ℬ) {p₁ p₂ p₃ p₄ : 𝒜} {x₁ x₂ x₃ x₄ : ℬ}
    (e₁ : x₁ ≅ Φ.obj p₁) (e₂ : x₂ ≅ Φ.obj p₂) (e₃ : x₃ ≅ Φ.obj p₃) (e₄ : x₄ ≅ Φ.obj p₄)
    (m₁ : p₁ ⟶ p₂) (m₂ : p₂ ⟶ p₄) (n₁ : p₁ ⟶ p₃) (n₂ : p₃ ⟶ p₄) (h : m₁ ≫ m₂ = n₁ ≫ n₂) :
    (e₁.hom ≫ Φ.map m₁ ≫ e₂.inv) ≫ e₂.hom ≫ Φ.map m₂ ≫ e₄.inv =
      (e₁.hom ≫ Φ.map n₁ ≫ e₃.inv) ≫ e₃.hom ≫ Φ.map n₂ ≫ e₄.inv := by
  rw [conjugate_comp Φ e₁ e₂ e₄ m₁ m₂ _ rfl, conjugate_comp Φ e₁ e₃ e₄ n₁ n₂ _ rfl, h]

/-- **Stacks 044X**, parts (2) and (3). The functor on descent data relative to a fixed covering
of a test object induced by the canonical 1-morphism `π : 𝒮_U ⟶ [U/R]`: a system `(u i, r i j)`
of points of the object space and arrows of the arrow space is carried to the descent datum of
`[U/R]` whose local objects are the `π (u i)` and whose transition isomorphisms are the images
`π (r i j)`, conjugated by the canonical comparison between the chosen pullback of an image and
the image of a chosen pullback. Part (3), that `(u i, r i j)` *is* a descent datum, is the
hypothesis on the source; the content here is that its image is one for the quotient. -/
@[stacks 044X "parts (2) and (3): projection of presenting data"]
noncomputable def presentingDescentFunctor
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T) :
    Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰 ⥤
      Functor.FamilyDescentDatum (quotientStack G).p 𝒰 := by
  let q := (quotientPrestack G).p
  let r := (quotientStack G).p
  let hF := isFibredOneMorphism_toQuotientStack G
  let mapCat : ∀ (V : BigFppfOver C S hS),
      (pullbackPseudofunctor q).obj ⟨Opposite.op V⟩ ⥤
        (pullbackPseudofunctor r).obj ⟨Opposite.op V⟩ := fun V =>
    Functor.fiberFunctorOfCompEq (p := q) (r := r)
      (F := toQuotientStack G) hF.comp_eq V
  have mapCat_map (V : BigFppfOver C S hS)
      {a b : q.Fiber V} (φ : a ⟶ b) :
      (mapCat V).map φ =
        (Functor.fiberFunctorOfCompEq hF.comp_eq V).map φ := rfl
  refine
    { obj := fun D =>
        { obj := fun i => (Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X i)).obj (D.obj i)
          hom := fun Y b i₁ i₂ f₁ f₂ hf₁ hf₂ =>
            show r.pullbackFiber
                  ((Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X i₁)).obj (D.obj i₁)) f₁ ⟶
                r.pullbackFiber
                  ((Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X i₂)).obj (D.obj i₂)) f₂ from
              (hF.mapPullbackFiberIso (D.obj i₁) f₁).hom ≫
                (Functor.fiberFunctorOfCompEq hF.comp_eq Y).map
                  (show q.pullbackFiber (D.obj i₁) f₁ ⟶ q.pullbackFiber (D.obj i₂) f₂ from
                    D.hom b f₁ f₂ hf₁ hf₂) ≫
                (hF.mapPullbackFiberIso (D.obj i₂) f₂).inv
          pullHom_hom := by
            intro Y' Y g b b' hb i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
            subst hb hgf₁ hgf₂
            rw [Functor.pullHom_eq r
              ((Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X i₁)).obj (D.obj i₁))
              ((Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X i₂)).obj (D.obj i₂))
              f₁ f₂ g
              ((hF.mapPullbackFiberIso (D.obj i₁) f₁).hom ≫
                (Functor.fiberFunctorOfCompEq hF.comp_eq Y).map
                  (show q.pullbackFiber (D.obj i₁) f₁ ⟶ q.pullbackFiber (D.obj i₂) f₂ from
                    D.hom b f₁ f₂ hf₁ hf₂) ≫
                (hF.mapPullbackFiberIso (D.obj i₂) f₂).inv)]
            simp only [Functor.pullbackFiberHom_comp, Category.assoc]
            rw [← D.pullHom_hom g b (g ≫ b) rfl f₁ f₂ hf₁ hf₂ (g ≫ f₁) (g ≫ f₂) rfl rfl,
              Functor.pullHom_eq q (D.obj i₁) (D.obj i₂) f₁ f₂ g (D.hom b f₁ f₂ hf₁ hf₂)]
            simp only [Functor.map_comp, Category.assoc,
              ← mapPullbackIso_compIso_inv_assoc hF (D.obj i₁) f₁ g]
            rw [← mapPullbackIso_naturality_assoc hF
              (a := q.pullbackFiber (D.obj i₁) f₁)
              (b := q.pullbackFiber (D.obj i₂) f₂)
              (D.hom b f₁ f₂ hf₁ hf₂) g,
              ← mapPullbackIso_compIso_hom hF (D.obj i₂) f₂ g]
          hom_self := by
            intro Y b i f hi
            rw [D.hom_self b f hi]
            change (hF.mapPullbackFiberIso (D.obj i) f).hom ≫
              (Functor.fiberFunctorOfCompEq hF.comp_eq Y).map (𝟙 _) ≫
              (hF.mapPullbackFiberIso (D.obj i) f).inv = 𝟙 _
            simp
          hom_comp := by
            intro Y b i₁ i₂ i₃ f₁ f₂ f₃ h₁ h₂ h₃
            exact conjugate_comp (Functor.fiberFunctorOfCompEq hF.comp_eq Y)
              (hF.mapPullbackFiberIso (D.obj i₁) f₁) (hF.mapPullbackFiberIso (D.obj i₂) f₂)
              (hF.mapPullbackFiberIso (D.obj i₃) f₃) _ _ _
              (D.hom_comp b f₁ f₂ f₃ h₁ h₂ h₃) }
      map := fun {D E} φ =>
        { hom := fun i => (mapCat (𝒰.X i)).map (φ.hom i)
          comm := by
            intro Y b i₁ i₂ f₁ f₂ hf₁ hf₂
            have hcomm := φ.comm b f₁ f₂ hf₁ hf₂
            rw [Functor.pullbackPseudofunctor_map_map,
              Functor.pullbackPseudofunctor_map_map] at hcomm
            rw [Functor.pullbackPseudofunctor_map_map, Functor.pullbackPseudofunctor_map_map,
              mapCat_map (V := 𝒰.X i₁) (φ.hom i₁), mapCat_map (V := 𝒰.X i₂) (φ.hom i₂),
              pullbackFiberHom_fiberFunctor_map hF (φ.hom i₁) f₁,
              pullbackFiberHom_fiberFunctor_map hF (φ.hom i₂) f₂]
            exact conjugate_comp_eq (Functor.fiberFunctorOfCompEq hF.comp_eq Y)
              (hF.mapPullbackFiberIso (D.obj i₁) f₁) (hF.mapPullbackFiberIso (E.obj i₁) f₁)
              (hF.mapPullbackFiberIso (D.obj i₂) f₂) (hF.mapPullbackFiberIso (E.obj i₂) f₂)
              _ _ _ _ hcomm }
      map_id := by
        intro D
        ext i
        exact (mapCat (𝒰.X i)).map_id (D.obj i)
      map_comp := by
        intro D E F φ ψ
        ext i
        exact (mapCat (𝒰.X i)).map_comp (φ.hom i) (ψ.hom i) }

/-! ### The components of the induced functor -/

/-- **Stacks 044X**, part (2). The local objects of the projected descent datum are the images
under `π` of the local points of the object space. -/
@[stacks 044X "part (2): local components"]
theorem presentingDescentFunctor_obj
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T)
    (D : Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰)
    (i : 𝒰.I₀) :
    ((presentingDescentFunctor G 𝒰).obj D).obj i =
      (Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_toQuotientStack G).comp_eq
        (𝒰.X i)).obj (D.obj i) := rfl

/-- **Stacks 044X**, part (2). The transition isomorphism of the projected descent datum on an
overlap is the image under `π` of the arrow of the arrow space, conjugated by the canonical
comparisons between the chosen pullbacks of the images and the images of the chosen
pullbacks. -/
@[stacks 044X "part (2): transition specification"]
theorem presentingDescentFunctor_hom
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T)
    (D : Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰)
    {W : BigFppfOver C S hS} (q : W ⟶ T)
    {i j : 𝒰.I₀} (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j)
    (ha : a ≫ 𝒰.f i = q) (hb : b ≫ 𝒰.f j = q) :
    HEq (((presentingDescentFunctor G 𝒰).obj D).hom q a b ha hb)
      (((isFibredOneMorphism_toQuotientStack G).mapPullbackFiberIso
        (D.obj i) a).hom ≫
      (Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_toQuotientStack G).comp_eq W).map
          (D.hom q a b ha hb) ≫
      ((isFibredOneMorphism_toQuotientStack G).mapPullbackFiberIso
        (D.obj j) b).inv) := by
  rfl

/-- **Stacks 044X**, part (5). On morphisms the projection applies `π` to each local arrow of
the arrow space. -/
@[stacks 044X "part (5): local arrows of the projected morphism"]
theorem presentingDescentFunctor_map_hom
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T)
    {D E : Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰}
    (f : D ⟶ E) (i : 𝒰.I₀) :
    HEq (((presentingDescentFunctor G 𝒰).map f).hom i)
      ((Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_toQuotientStack G).comp_eq
        (𝒰.X i)).map (f.hom i)) := by
  rfl

/-! ### Lifting a descent datum of the quotient to the presentation -/

private noncomputable def overlapHomEquiv
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F)
    (ff : ∀ V, (Functor.fiberFunctorOfCompEq hF.comp_eq V).FullyFaithful)
    {U V W : 𝒮} (a : q.Fiber U) (b : q.Fiber V) (f : W ⟶ U) (g : W ⟶ V) :
    (q.pullbackFiber a f ⟶ q.pullbackFiber b g) ≃
      (r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f ⟶
        r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj b) g) :=
  (ff W).homEquiv.trans
    (Iso.homCongr (hF.mapPullbackFiberIso a f).symm (hF.mapPullbackFiberIso b g).symm)

private lemma overlapHomEquiv_apply
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F)
    (ff : ∀ V, (Functor.fiberFunctorOfCompEq hF.comp_eq V).FullyFaithful)
    {U V W : 𝒮} (a : q.Fiber U) (b : q.Fiber V) (f : W ⟶ U) (g : W ⟶ V)
    (φ : q.pullbackFiber a f ⟶ q.pullbackFiber b g) :
    overlapHomEquiv hF ff a b f g φ =
      (hF.mapPullbackFiberIso a f).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq W).map φ ≫
        (hF.mapPullbackFiberIso b g).inv := rfl

private lemma overlapHomEquiv_comp
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F)
    (ff : ∀ V, (Functor.fiberFunctorOfCompEq hF.comp_eq V).FullyFaithful)
    {U V W Z : 𝒮} (a : q.Fiber U) (b : q.Fiber V) (c : q.Fiber W)
    (f : Z ⟶ U) (g : Z ⟶ V) (h : Z ⟶ W)
    (φ : q.pullbackFiber a f ⟶ q.pullbackFiber b g)
    (ψ : q.pullbackFiber b g ⟶ q.pullbackFiber c h) :
    overlapHomEquiv hF ff a c f h (φ ≫ ψ) =
      overlapHomEquiv hF ff a b f g φ ≫ overlapHomEquiv hF ff b c g h ψ := by
  simp only [overlapHomEquiv_apply, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]

private lemma overlapHomEquiv_pullHom
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F)
    (ff : ∀ V, (Functor.fiberFunctorOfCompEq hF.comp_eq V).FullyFaithful)
    {U V W Z : 𝒮} (a : q.Fiber U) (b : q.Fiber V) (f : W ⟶ U) (g : W ⟶ V)
    (φ : q.pullbackFiber a f ⟶ q.pullbackFiber b g) (γ : Z ⟶ W) :
    overlapHomEquiv hF ff a b (γ ≫ f) (γ ≫ g)
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor q) φ γ (γ ≫ f) (γ ≫ g) rfl rfl) =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := pullbackPseudofunctor r) (overlapHomEquiv hF ff a b f g φ)
        γ (γ ≫ f) (γ ≫ g) rfl rfl := by
  simp only [overlapHomEquiv_apply]
  rw [Functor.pullHom_eq q, Functor.pullHom_eq r]
  simp only [Functor.pullbackFiberHom_comp, Functor.map_comp, Category.assoc]
  rw [← mapPullbackIso_compIso_inv_assoc hF a f γ,
    ← mapPullbackIso_naturality_assoc hF
      (a := q.pullbackFiber a f) (b := q.pullbackFiber b g) φ γ,
    ← mapPullbackIso_compIso_hom hF b g γ]

private lemma overlapHomEquiv_id
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F)
    (ff : ∀ V, (Functor.fiberFunctorOfCompEq hF.comp_eq V).FullyFaithful)
    {U W : 𝒮} (a : q.Fiber U) (f : W ⟶ U) :
    overlapHomEquiv hF ff a a f f (𝟙 (q.pullbackFiber a f)) =
      𝟙 (r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f) := by
  rw [overlapHomEquiv_apply]
  simp

private lemma overlapHomEquiv_symm_pullHom
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F)
    (ff : ∀ V, (Functor.fiberFunctorOfCompEq hF.comp_eq V).FullyFaithful)
    {U V W Z : 𝒮} (a : q.Fiber U) (b : q.Fiber V) (f : W ⟶ U) (g : W ⟶ V)
    (ψ : r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f ⟶
      r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj b) g) (γ : Z ⟶ W) :
    (overlapHomEquiv hF ff a b (γ ≫ f) (γ ≫ g)).symm
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor r) ψ γ (γ ≫ f) (γ ≫ g) rfl rfl) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor q)
        ((overlapHomEquiv hF ff a b f g).symm ψ) γ (γ ≫ f) (γ ≫ g) rfl rfl := by
  apply (overlapHomEquiv hF ff a b (γ ≫ f) (γ ≫ g)).injective
  rw [Equiv.apply_symm_apply, overlapHomEquiv_pullHom, Equiv.apply_symm_apply]

private lemma overlapHomEquiv_symm_comp
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F)
    (ff : ∀ V, (Functor.fiberFunctorOfCompEq hF.comp_eq V).FullyFaithful)
    {U V W Z : 𝒮} (a : q.Fiber U) (b : q.Fiber V) (c : q.Fiber W)
    (f : Z ⟶ U) (g : Z ⟶ V) (h : Z ⟶ W)
    (φ : r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f ⟶
      r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj b) g)
    (ψ : r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj b) g ⟶
      r.pullbackFiber ((Functor.fiberFunctorOfCompEq hF.comp_eq W).obj c) h) :
    (overlapHomEquiv hF ff a b f g).symm φ ≫ (overlapHomEquiv hF ff b c g h).symm ψ =
      (overlapHomEquiv hF ff a c f h).symm (φ ≫ ψ) := by
  apply (overlapHomEquiv hF ff a c f h).injective
  rw [Equiv.apply_symm_apply, overlapHomEquiv_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- The comparison isomorphisms of a 1-morphism of fibred categories identify the two ways of
reading a transition arrow over a twofold chosen pullback: contracting the pullback first and
then comparing, or comparing first and then contracting. This is the equation that makes the
projection on descent data compatible with refinement of the covering. -/
private lemma mapPullbackIso_refinement
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₂} 𝒴]
    {q : 𝒳 ⥤ 𝒮} {r : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U V Z Z' W : 𝒮}
    (a : q.Fiber U) (b : q.Fiber V) (f : Z ⟶ U) (g : Z' ⟶ V)
    (γ : W ⟶ Z) (δ : W ⟶ Z')
    (ψ : q.pullbackFiber a (γ ≫ f) ⟶ q.pullbackFiber b (δ ≫ g)) :
    Functor.pullbackFiberHom (hF.mapPullbackFiberIso a f).hom γ ≫
        (hF.mapPullbackFiberIso (q.pullbackFiber a f) γ).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq W).map
          ((Functor.pullbackFiberCompIso a f γ).hom ≫ ψ ≫
            (Functor.pullbackFiberCompIso b g δ).inv) ≫
        (hF.mapPullbackFiberIso (q.pullbackFiber b g) δ).inv =
      ((Functor.pullbackFiberCompIso
            ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f γ).hom ≫
          ((hF.mapPullbackFiberIso a (γ ≫ f)).hom ≫
            (Functor.fiberFunctorOfCompEq hF.comp_eq W).map ψ ≫
            (hF.mapPullbackFiberIso b (δ ≫ g)).inv) ≫
          (Functor.pullbackFiberCompIso
            ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj b) g δ).inv) ≫
        Functor.pullbackFiberHom (hF.mapPullbackFiberIso b g).hom δ := by
  simp only [Functor.map_comp, Category.assoc]
  rw [pullbackFiberHom_mapPullbackIso_hom_assoc hF]
  rw [← mapPullbackIso_compIso_inv hF]
  simp only [Iso.inv_hom_id_assoc]

private noncomputable def replaceDescentObjects
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
    {T : 𝒮} {ι : Type w} {X : ι → 𝒮} {f : ∀ i, X i ⟶ T}
    (D : F.DescentData f) (M : ∀ i, F.obj ⟨Opposite.op (X i)⟩)
    (e : ∀ i, D.obj i ≅ M i) : F.DescentData f where
  obj := M
  hom W b i j a c ha hc :=
    (F.map a.op.toLoc).toFunctor.map (e i).inv ≫ D.hom b a c ha hc ≫
      (F.map c.op.toLoc).toFunctor.map (e j).hom
  pullHom_hom := by
    intro W' W g b b' hb i j a c ha hc ga gc hga hgc
    dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [← F.mapComp'_hom_naturality_assoc, F.mapComp'_inv_naturality]
    congr 1
    simpa only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Category.assoc] using
      congrArg (fun k => k ≫ (F.map gc.op.toLoc).toFunctor.map (e j).hom)
        (D.pullHom_hom g b b' hb a c ha hc ga gc hga hgc)
  hom_self := by
    intro W b i a ha
    rw [D.hom_self b a ha, Category.id_comp, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  hom_comp := by
    intro W b i j k a c d ha hc hd
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [D.hom_comp_assoc b a c d ha hc hd]

private noncomputable def replaceDescentObjectsIso
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
    {T : 𝒮} {ι : Type w} {X : ι → 𝒮} {f : ∀ i, X i ⟶ T}
    (D : F.DescentData f) (M : ∀ i, F.obj ⟨Opposite.op (X i)⟩)
    (e : ∀ i, D.obj i ≅ M i) : D ≅ replaceDescentObjects D M e :=
  Pseudofunctor.DescentData.isoMk e (by
    intro W b i j a c ha hc
    dsimp [replaceDescentObjects]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp])

private lemma exists_lift_descentDatum
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T)
    (D : Functor.FamilyDescentDatum (quotientStack G).p 𝒰)
    (a : ∀ i, (quotientPrestack G).p.Fiber (𝒰.X i))
    (e : ∀ i, D.obj i ≅ (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_toQuotientStack G).comp_eq
        (𝒰.X i)).obj (a i)) :
    ∃ E : Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰,
      Nonempty (D ≅ (presentingDescentFunctor G 𝒰).obj E) := by
  classical
  let q := (quotientPrestack G).p
  let r := (quotientStack G).p
  let hF := isFibredOneMorphism_toQuotientStack G
  let ff := fun V => (fullyFaithful_fiberFunctor_toQuotientStack G V).some
  let M := replaceDescentObjects D
    (fun i => (Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X i)).obj (a i)) e
  let E : Functor.FamilyDescentDatum q 𝒰 := {
    obj := a
    hom := fun W b i j f g hf hg =>
      (overlapHomEquiv hF ff (a i) (a j) f g).symm (M.hom b f g hf hg)
    pullHom_hom := by
      intro W' W γ b b' hb i j f g hf hg γf γg hγf hγg
      subst hb hγf hγg
      exact (overlapHomEquiv_symm_pullHom hF ff (a i) (a j) f g _ γ).symm.trans
        (congrArg (overlapHomEquiv hF ff (a i) (a j) (γ ≫ f) (γ ≫ g)).symm
          (M.pullHom_hom γ b (γ ≫ b) rfl f g hf hg (γ ≫ f) (γ ≫ g) rfl rfl))
    hom_self := by
      intro W b i f hf
      exact (congrArg (overlapHomEquiv hF ff (a i) (a i) f f).symm (M.hom_self b f hf)).trans
        ((Equiv.symm_apply_eq _).2 (overlapHomEquiv_id hF ff (a i) f).symm)
    hom_comp := by
      intro W b i j k f g h hf hg hh
      exact (overlapHomEquiv_symm_comp hF ff (a i) (a j) (a k) f g h _ _).trans
        (congrArg (overlapHomEquiv hF ff (a i) (a k) f h).symm (M.hom_comp b f g h hf hg hh)) }
  refine ⟨E, ⟨replaceDescentObjectsIso D _ e ≪≫ ?_⟩⟩
  refine Pseudofunctor.DescentData.isoMk (fun i => Iso.refl (M.obj i)) ?_
  intro W b i j f g hf hg
  rw [Functor.pullbackPseudofunctor_map_map, Functor.pullbackPseudofunctor_map_map]
  show Functor.pullbackFiberHom (𝟙 (M.obj i)) f ≫
      ((presentingDescentFunctor G 𝒰).obj E).hom b f g hf hg =
    M.hom b f g hf hg ≫ Functor.pullbackFiberHom (𝟙 (M.obj j)) g
  rw [Functor.pullbackFiberHom_id, Functor.pullbackFiberHom_id]
  exact (Category.id_comp _).trans
    ((Equiv.apply_symm_apply (overlapHomEquiv hF ff (a i) (a j) f g)
      (M.hom b f g hf hg)).trans (Category.comp_id _).symm)

/-! ### Local presentability, effectivity and the bijection on morphisms -/

private lemma exists_small_covering
    {T : BigFppfOver C S hS} (R : Sieve T)
    (hR : R ∈ BigFppfOver.topology C S hS T) :
    ∃ 𝒰 : PreZeroHypercover.{u} T,
      𝒰.sieve₀ ∈ BigFppfOver.topology C S hS T ∧
        ∀ i, R.arrows (𝒰.f i) := by
  classical
  have hsmall : Precoverage.Small.{u} C.precoverage := by
    rw [bigFppfPrecoverage_eq_comap C]
    show Precoverage.Small.{u}
      ((Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)).comap C.inclusion)
    infer_instance
  obtain ⟨E, hE, hER⟩ := BigFppfOver.exists_isCovering_of_mem_topology C S hS hR
  have hE₀ : (E.map (BigFppfOver.forget C S hS)).presieve₀ ∈ C.precoverage T.left :=
    ⟨E.map (BigFppfOver.forget C S hS), rfl, hE⟩
  let E₀ : C.precoverage.ZeroHypercover T.left :=
    ⟨E.map (BigFppfOver.forget C S hS), hE₀⟩
  let E' : C.precoverage.ZeroHypercover.{u} T.left := E₀.restrictIndexOfSmall
  let σ : E'.I₀ → E.I₀ := Precoverage.ZeroHypercover.Small.restrictFun E₀
  refine ⟨E.restrictIndex σ, ?_, fun i => hER (σ i)⟩
  refine (C.topology.mem_over_iff _).mpr ?_
  rw [Sieve.overEquiv_ofArrows]
  exact C.precoverage.generate_mem_toGrothendieck E'.mem₀

/-- **Stacks 044X**, parts (1)–(3). Every object `x` of a fibre of the quotient stack is, after
an fppf covering of the test object, the projection of a descent datum for the pointwise
groupoid presentation: there is a covering `𝒰` indexed in the universe of the site, a system
`(u i, r i j)` of points of the object space and arrows of the arrow space forming a descent
datum for the presentation relative to `𝒰`, and an isomorphism between the canonical descent
datum of `x` and the projection of that system. The local isomorphisms `f i ^* x ≅ π (u i)` and
their transition arrows are the components of that isomorphism. -/
@[stacks 044X "parts (1)–(3): local presenting descent datum"]
theorem exists_presentingDescentDatum
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x : (quotientStack G).p.Fiber T) :
    ∃ (𝒰 : PreZeroHypercover.{u} T)
      (_ : 𝒰.sieve₀ ∈ BigFppfOver.topology C S hS T)
      (D : Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰),
      Nonempty (((Functor.toFamilyDescentDatum
        (quotientStack G).p 𝒰).obj x) ≅
          (presentingDescentFunctor G 𝒰).obj D) := by
  classical
  obtain ⟨R, hR, hx⟩ := essImage_toQuotientStack G T x
  obtain ⟨𝒰, h𝒰, h𝒰R⟩ := exists_small_covering R hR
  choose a ea using fun i : 𝒰.I₀ => hx (h𝒰R i)
  obtain ⟨E, hE⟩ := exists_lift_descentDatum G 𝒰
    ((Functor.toFamilyDescentDatum (quotientStack G).p 𝒰).obj x)
    a (fun i => (ea i).some.symm)
  exact ⟨𝒰, h𝒰, E, hE⟩

/-- **Stacks 044X**, part (4). Every descent datum for the pointwise groupoid presentation
relative to an fppf covering arises as in parts (1)–(3): its projection is the canonical descent
datum of an object of the fibre of the quotient stack over the test object. This is the
effectivity of descent data in the stack `[U/R]`. -/
@[stacks 044X "part (4): effectivity"]
theorem effective_presentingDescentDatum
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T)
    (h𝒰 : 𝒰.sieve₀ ∈ BigFppfOver.topology C S hS T)
    (D : Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰) :
    ∃ x : (quotientStack G).p.Fiber T,
      Nonempty (((Functor.toFamilyDescentDatum
        (quotientStack G).p 𝒰).obj x) ≅
          (presentingDescentFunctor G 𝒰).obj D) := by
  have : (Functor.toFamilyDescentDatum (quotientStack G).p 𝒰).IsEquivalence :=
    Functor.isEquivalence_toDescentData_of_isStack _ (isStack_quotientStack G) 𝒰.f h𝒰
  exact ⟨_, ⟨(Functor.toFamilyDescentDatum (quotientStack G).p 𝒰).objObjPreimageIso
    ((presentingDescentFunctor G 𝒰).obj D)⟩⟩

/-- **Stacks 044X**, part (5). For a fixed covering the projection is fully faithful on descent
data for the presentation: a morphism of the projected data is the image of a unique compatible
family of arrows of the arrow space. -/
@[stacks 044X "part (5): morphisms of presenting data"]
theorem fullyFaithful_presentingDescentFunctor
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T) :
    Nonempty (presentingDescentFunctor G 𝒰).FullyFaithful := by
  classical
  let hF := isFibredOneMorphism_toQuotientStack G
  let ff := fun V => (fullyFaithful_fiberFunctor_toQuotientStack G V).some
  refine ⟨{
    preimage := fun {D E} φ =>
      { hom := fun i => (ff (𝒰.X i)).preimage (φ.hom i)
        comm := by
          intro W b i j a c ha hc
          rw [Functor.pullbackPseudofunctor_map_map,
            Functor.pullbackPseudofunctor_map_map]
          apply (ff W).map_injective
          have h := φ.comm b a c ha hc
          change Functor.pullbackFiberHom (φ.hom i) a ≫
              (hF.mapPullbackFiberIso (E.obj i) a).hom ≫
              (Functor.fiberFunctorOfCompEq hF.comp_eq W).map (E.hom b a c ha hc) ≫
              (hF.mapPullbackFiberIso (E.obj j) c).inv =
            ((hF.mapPullbackFiberIso (D.obj i) a).hom ≫
              (Functor.fiberFunctorOfCompEq hF.comp_eq W).map (D.hom b a c ha hc) ≫
              (hF.mapPullbackFiberIso (D.obj j) c).inv) ≫
              Functor.pullbackFiberHom (φ.hom j) c at h
          rw [← (ff (𝒰.X i)).map_preimage (φ.hom i),
            ← (ff (𝒰.X j)).map_preimage (φ.hom j)] at h
          exact fiberFunctor_map_comm_of_image_comm hF _ _ a c _ _ h }
    map_preimage := by
      intro D E φ
      ext i
      exact (ff (𝒰.X i)).map_preimage (φ.hom i)
    preimage_map := by
      intro D E φ
      ext i
      exact (ff (𝒰.X i)).preimage_map (φ.hom i) }⟩

/-- **Stacks 044X**, part (5). The canonical bijection between the morphisms `x ⟶ y` of a fibre
of the quotient stack and the morphisms of the descent data for the presentation that represent
`x` and `y`, together with the equation that characterises it: the projection of the morphism of
descent data is the canonical descent datum morphism of `f`, conjugated by the two
representing isomorphisms. -/
@[stacks 044X "part (5): canonical bijection"]
noncomputable def homEquiv_presentingDescentDatum
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS} (𝒰 : PreZeroHypercover.{w} T)
    (h𝒰 : 𝒰.sieve₀ ∈ BigFppfOver.topology C S hS T)
    (x y : (quotientStack G).p.Fiber T)
    (D E : Functor.FamilyDescentDatum (quotientPrestack G).p 𝒰)
    (δ : (Functor.toFamilyDescentDatum (quotientStack G).p 𝒰).obj x ≅
      (presentingDescentFunctor G 𝒰).obj D)
    (ε : (Functor.toFamilyDescentDatum (quotientStack G).p 𝒰).obj y ≅
      (presentingDescentFunctor G 𝒰).obj E) :
    {e : (x ⟶ y) ≃ (D ⟶ E) //
      ∀ f, (presentingDescentFunctor G 𝒰).map (e f) = δ.inv ≫
        (Functor.toFamilyDescentDatum (quotientStack G).p 𝒰).map f ≫ ε.hom} := by
  let L := Functor.toFamilyDescentDatum (quotientStack G).p 𝒰
  have : L.IsEquivalence := Functor.isEquivalence_toDescentData_of_isStack _
    (isStack_quotientStack G) 𝒰.f h𝒰
  let ff := (fullyFaithful_presentingDescentFunctor G 𝒰).some
  refine ⟨((Functor.FullyFaithful.ofFullyFaithful L).homEquiv.trans
    (Iso.homCongr δ ε)).trans ff.homEquiv.symm, fun _ => ff.map_preimage _⟩

/-! ### Compatibility with refinement of the covering -/

private lemma pull_hom_eq
    {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {T : 𝒮}
    {𝒰 𝒱 : PreZeroHypercover.{w} T} (Φ : 𝒱.HomOver 𝒰 (𝟙 T))
    (D : Functor.FamilyDescentDatum p 𝒰) {W : 𝒮} (b : W ⟶ T)
    {i j : 𝒱.I₀} (a : W ⟶ 𝒱.X i) (c : W ⟶ 𝒱.X j)
    (ha : a ≫ 𝒱.f i = b) (hc : c ≫ 𝒱.f j = b) :
    (Functor.FamilyDescentDatum.pull p Φ D).hom b a c ha hc =
      (Functor.pullbackFiberCompIso (D.obj (Φ.s₀ i)) (Φ.h₀ i) a).hom ≫
        D.hom (b ≫ 𝟙 T) (a ≫ Φ.h₀ i) (c ≫ Φ.h₀ j)
          (by rw [Category.assoc, Φ.w₀, reassoc_of% ha])
          (by rw [Category.assoc, Φ.w₀, reassoc_of% hc]) ≫
        (Functor.pullbackFiberCompIso (D.obj (Φ.s₀ j)) (Φ.h₀ j) c).inv := by
  rw [Functor.FamilyDescentDatum.pull_hom]
  have h₁ := Functor.pullbackPseudofunctor_mapComp'_inv_app p
    (Φ.h₀ i) a (a ≫ Φ.h₀ i) rfl (D.obj (Φ.s₀ i))
  have h₂ := Functor.pullbackPseudofunctor_mapComp'_hom_app p
    (Φ.h₀ j) c (c ≫ Φ.h₀ j) rfl (D.obj (Φ.s₀ j))
  simp only [op_comp, Quiver.Hom.comp_toLoc, Pseudofunctor.mapComp'_eq_mapComp] at h₁ h₂
  rw [h₁, h₂, Functor.pullbackFiberCompIso'_rfl, Functor.pullbackFiberCompIso'_rfl]
  rfl

/-- **Stacks 044X**, part (6). The correspondence of parts (1)–(5) is compatible with refinement
of the fppf covering: projecting a descent datum for the presentation and then pulling it back
along a refinement is naturally isomorphic to pulling it back first and then projecting, and the
isomorphism is natural in the descent datum, hence compatible with the bijection of part (5). -/
@[stacks 044X "part (6): refinement compatibility"]
noncomputable def presentingDescentFunctor_refinementIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : BigFppfOver C S hS}
    {𝒰 : PreZeroHypercover.{w} T} {𝒱 : PreZeroHypercover.{w} T}
    (Φ : 𝒱.HomOver 𝒰 (𝟙 T)) :
    presentingDescentFunctor G 𝒰 ⋙
        Functor.FamilyDescentDatum.pullFunctor (quotientStack G).p Φ ≅
      Functor.FamilyDescentDatum.pullFunctor (quotientPrestack G).p Φ ⋙
        presentingDescentFunctor G 𝒱 := by
  let q := (quotientPrestack G).p
  let r := (quotientStack G).p
  let hF := isFibredOneMorphism_toQuotientStack G
  exact NatIso.ofComponents (fun D => Pseudofunctor.DescentData.isoMk
    (fun i => hF.mapPullbackFiberIso (D.obj (Φ.s₀ i)) (Φ.h₀ i)) (by
    intro W b i j a c ha hc
    rw [Functor.pullbackPseudofunctor_map_map,
      Functor.pullbackPseudofunctor_map_map]
    change Functor.pullbackFiberHom
        (hF.mapPullbackFiberIso (D.obj (Φ.s₀ i)) (Φ.h₀ i)).hom a ≫
        (hF.mapPullbackFiberIso (q.pullbackFiber (D.obj (Φ.s₀ i)) (Φ.h₀ i)) a).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq W).map
          ((Functor.FamilyDescentDatum.pull q Φ D).hom b a c ha hc) ≫
        (hF.mapPullbackFiberIso (q.pullbackFiber (D.obj (Φ.s₀ j)) (Φ.h₀ j)) c).inv =
      ((Functor.FamilyDescentDatum.pull r Φ
        ((presentingDescentFunctor G 𝒰).obj D)).hom b a c ha hc) ≫
        Functor.pullbackFiberHom
          (hF.mapPullbackFiberIso (D.obj (Φ.s₀ j)) (Φ.h₀ j)).hom c
    rw [pull_hom_eq q, pull_hom_eq r]
    change _ = ((Functor.pullbackFiberCompIso
        ((Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X (Φ.s₀ i))).obj
          (D.obj (Φ.s₀ i))) (Φ.h₀ i) a).hom ≫
        ((hF.mapPullbackFiberIso (D.obj (Φ.s₀ i)) (a ≫ Φ.h₀ i)).hom ≫
          (Functor.fiberFunctorOfCompEq hF.comp_eq W).map
            (D.hom (b ≫ 𝟙 T) (a ≫ Φ.h₀ i) (c ≫ Φ.h₀ j) _ _) ≫
          (hF.mapPullbackFiberIso (D.obj (Φ.s₀ j)) (c ≫ Φ.h₀ j)).inv) ≫
        (Functor.pullbackFiberCompIso
          ((Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X (Φ.s₀ j))).obj
            (D.obj (Φ.s₀ j))) (Φ.h₀ j) c).inv) ≫ _
    simp only [Functor.map_comp, Category.assoc]
    rw [pullbackFiberHom_mapPullbackIso_hom_assoc hF, ← mapPullbackIso_compIso_inv hF]
    simp only [Iso.inv_hom_id_assoc]
    rfl)) (by
    intro D E φ
    ext i
    change Functor.pullbackFiberHom
        ((Functor.fiberFunctorOfCompEq hF.comp_eq (𝒰.X (Φ.s₀ i))).map (φ.hom (Φ.s₀ i)))
        (Φ.h₀ i) ≫ (hF.mapPullbackFiberIso (E.obj (Φ.s₀ i)) (Φ.h₀ i)).hom =
      (hF.mapPullbackFiberIso (D.obj (Φ.s₀ i)) (Φ.h₀ i)).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq (𝒱.X i)).map
          (Functor.pullbackFiberHom (φ.hom (Φ.s₀ i)) (Φ.h₀ i))
    rw [pullbackFiberHom_fiberFunctor_map hF]
    simp)

end AlgebraicGeometry.Stack

end
