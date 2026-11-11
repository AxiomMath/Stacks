module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Limits.FunctorCategory.Pointwise

/-!
# Fibre products and pushouts of (co)simplicial objects

Fibre products of simplicial objects, and the descriptions of morphisms into a fibre product and
out of a pushout of (co)simplicial objects.
-/

/-!
## Fibre products of simplicial objects

Let `C` be a category, let `U`, `V`, `W` be simplicial objects of `C`, let `a : V ⟶ U` and
`b : W ⟶ U` be morphisms, and assume the fibre product `V_n ×_{U_n} W_n` exists in `C` for every
`n`. The *fibre product of `V` and `W` over `U`* is the simplicial object `V ×_U W` with
`(V ×_U W)_n = V_n ×_{U_n} W_n`, a morphism `φ` of `Δ` acting by the morphism that `V φ`, `W φ`
and `U φ` induce on the pullbacks, so that `d^n_i = (d^n_i, d^n_i)` and `s^n_i = (s^n_i, s^n_i)`;
equivalently, it is the fibre product of the presheaves `V` and `W` over the presheaf `U` on `Δ`,
formed degreewise.

### Main definitions

* `CategoryTheory.SimplicialObject.fibreProduct`: the fibre product `V ×_U W` of simplicial
  objects of `C`, defined degreewise.

### Implementation notes

Nothing in the construction uses the index category `Δᵒᵖ`, so this is the case
`D = SimplexCategoryᵒᵖ` of `CategoryTheory.Limits.pointwisePullback`, the pointwise pullback of a
cospan of functors, and it is a reducible abbreviation of that functor. Its `@[simps]` lemmas
`Limits.pointwisePullback_obj` and `Limits.pointwisePullback_map` then apply verbatim and are the
three clauses above, the last two at `(SimplexCategory.δ i).op` and at `(SimplexCategory.σ i).op`,
so no user of the definition has to unfold it and it carries no API of its own.

What the abbreviation adds to that functor is the `SimplicialObject` API, dot notation resolving
on the ascribed head constant rather than through the abbreviation: `(fibreProduct a b).δ i`
elaborates, and equals `(fibreProduct a b).map (SimplexCategory.δ i).op` by `rfl`, whereas
`(Limits.pointwisePullback a b).δ i` does not elaborate at all, that term being ascribed the type
`SimplexCategoryᵒᵖ ⥤ C`.

The source defines `V ×_U W` degreewise rather than as a fibre product of `a` and `b` in the
category of simplicial objects of `C`, since the latter may exist without being described
degreewise. Under the hypothesis above the two agree, and it is the degreewise one that is defined
here; the comparison — with the limiting cone that the degreewise pullback cones combine into, and
with Mathlib's `Limits.pullback a b`, which when `C` has pullbacks agrees with the degreewise
object only up to `CategoryTheory.Limits.pullbackObjIso` — is in the implementation notes of
`Limits.pointwisePullback`.

### References

* [Stacks, Tag 016T](https://stacks.math.columbia.edu/tag/016T)
* [Stacks, Tag 0172](https://stacks.math.columbia.edu/tag/0172)
-/

section

@[expose] public section

namespace CategoryTheory.SimplicialObject

universe v u

variable {C : Type u} [Category.{v} C] {U V W : SimplicialObject C}

/-- **Stacks 016T.** The fibre product `V ×_U W` of two simplicial objects `V`, `W` of a category
`C` over a third one `U`, along morphisms `a : V ⟶ U` and `b : W ⟶ U`, when the fibre product
`V_n ×_{U_n} W_n` exists in `C` in every degree: the simplicial object with
`(V ×_U W)_n = V_n ×_{U_n} W_n` on which a morphism `φ : ⦋m⦌ ⟶ ⦋n⦌` of `Δ` acts by the morphism
that `V φ`, `W φ` and `U φ` induce on the pullbacks, so that `d^n_i = (d^n_i, d^n_i)` and
`s^n_i = (s^n_i, s^n_i)`. -/
@[stacks 016T "the case `D = SimplexCategoryᵒᵖ` of `CategoryTheory.Limits.pointwisePullback`, \
  Tag 0172, which is stated for an arbitrary index category `D`"]
noncomputable abbrev fibreProduct (a : V ⟶ U) (b : W ⟶ U)
    [∀ n, Limits.HasPullback (a.app n) (b.app n)] : SimplicialObject C :=
  Limits.pointwisePullback a b

end CategoryTheory.SimplicialObject

end

end

/-!
## Morphisms into a fibre product of simplicial objects

Let `C` be a category, let `U`, `V`, `W` be simplicial objects of `C` and let `a : V ⟶ U`,
`b : W ⟶ U` be morphisms whose fibre product `V ×_U W` exists, with structure projections `p`,
`q`. For every simplicial object `T` of `C`, composing with `p` and `q` identifies
`Mor(T, V ×_U W)` with the fibre product of sets
`Mor(T, V) ×_{Mor(T, U)} Mor(T, W) = {(f, g) | a ∘ f = b ∘ g}`, by `h ↦ (p ∘ h, q ∘ h)`. This is
the universal property of the fibre product and uses nothing simplicial, so it is stated for a
pullback cone in an arbitrary category and then specialized to `SimplicialObject C`; the
simplicial content of the source is that the degreewise fibre product of Tag 016T is such a
limit, which only needs the degreewise fibre products `V_n ×_{U_n} W_n` to exist.

### Main definitions

* `CategoryTheory.Limits.PullbackCone.canonicalMap`: for a pullback cone `c` of `a : V ⟶ U` and
  `b : W ⟶ U`, the map `h ↦ (h ≫ c.fst, h ≫ c.snd)` from `Mor(T, c.pt)` to the fibre product
  `Types.PullbackObj` of the sets `Mor(T, V)` and `Mor(T, W)` over `Mor(T, U)`.
* `CategoryTheory.Limits.PullbackCone.canonicalEquiv`: `canonicalMap` for a limit pullback cone,
  as an equivalence.

### Main results

* `CategoryTheory.Limits.PullbackCone.isBijective_canonicalMap`: for a limit pullback cone in an
  arbitrary category, `canonicalMap` is a bijection.
* `CategoryTheory.Limits.PullbackCone.canonicalEquiv_apply`: `canonicalEquiv` is given by
  `canonicalMap`.
* `CategoryTheory.SimplicialObject.isBijective_canonicalMap`: the same bijection for a limit
  pullback cone of simplicial objects of `C`.
* `CategoryTheory.SimplicialObject.fibreProduct.isLimit`: the degreewise fibre product
  `fibreProduct a b` of Tag 016T, with its degreewise projections `fibreProduct.fst` and
  `fibreProduct.snd`, is a fibre product in `SimplicialObject C`.
* `CategoryTheory.SimplicialObject.fibreProduct.isBijective_canonicalMap`: the source's
  statement, `Mor(T, V ×_U W) = Mor(T, V) ×_{Mor(T, U)} Mor(T, W)` for the degreewise fibre
  product.

### References

* [Stacks, Tag 016U](https://stacks.math.columbia.edu/tag/016U)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits.PullbackCone

variable {𝒜 : Type u} [Category.{v} 𝒜]

/-- For morphisms `a : V ⟶ U`, `b : W ⟶ U` of a category `𝒜` and a pullback cone `c` of `a` and
`b`, the map sending `h : T ⟶ c.pt` to the compatible pair `(h ≫ c.fst, h ≫ c.snd)` of the fibre
product of sets `Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`. -/
def canonicalMap {U V W T : 𝒜} (a : V ⟶ U) (b : W ⟶ U) (c : PullbackCone a b)
    (h : T ⟶ c.pt) :
    Types.PullbackObj (TypeCat.ofHom fun f : T ⟶ V => f ≫ a)
      (TypeCat.ofHom fun g : T ⟶ W => g ≫ b) :=
  ⟨(h ≫ c.fst, h ≫ c.snd), by simp [c.condition]⟩

/-- For objects `U V W T` of a category `𝒜`, morphisms `a : V ⟶ U`, `b : W ⟶ U` and a fibre
product `V ×_U W` of `a` and `b` witnessed by a limit pullback cone `c`, the map
`h ↦ (h ≫ c.fst, h ≫ c.snd)` is a bijection from `Mor(T, V ×_U W)` onto the fibre product of sets
`Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`. -/
theorem isBijective_canonicalMap {U V W T : 𝒜} (a : V ⟶ U) (b : W ⟶ U)
    (c : PullbackCone a b) (hc : IsLimit c) :
    Function.Bijective (canonicalMap a b c (T := T)) := by
  constructor
  · intro h₁ h₂ heq
    have e1 : h₁ ≫ c.fst = h₂ ≫ c.fst := congrArg (fun p => p.1.1) heq
    have e2 : h₁ ≫ c.snd = h₂ ≫ c.snd := congrArg (fun p => p.1.2) heq
    exact PullbackCone.IsLimit.hom_ext hc e1 e2
  · rintro ⟨⟨f, g⟩, hfg⟩
    obtain ⟨l, hl1, hl2⟩ := PullbackCone.IsLimit.lift' hc f g hfg
    exact ⟨l, Subtype.ext (by simp [canonicalMap, hl1, hl2])⟩

/-- The bijection between `Mor(T, V ×_U W)` and the fibre product of sets
`Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`, as an `Equiv`. -/
noncomputable def canonicalEquiv {U V W T : 𝒜} (a : V ⟶ U) (b : W ⟶ U)
    (c : PullbackCone a b) (hc : IsLimit c) :
    (T ⟶ c.pt) ≃ Types.PullbackObj (TypeCat.ofHom fun f : T ⟶ V => f ≫ a)
      (TypeCat.ofHom fun g : T ⟶ W => g ≫ b) :=
  Equiv.ofBijective _ (isBijective_canonicalMap a b c hc)

/-- The equivalence `canonicalEquiv` is given by the map `h ↦ (h ≫ c.fst, h ≫ c.snd)`. -/
theorem canonicalEquiv_apply {U V W T : 𝒜} (a : V ⟶ U) (b : W ⟶ U)
    (c : PullbackCone a b) (hc : IsLimit c) (h : T ⟶ c.pt) :
    canonicalEquiv a b c hc h = canonicalMap a b c h :=
  rfl

end CategoryTheory.Limits.PullbackCone

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Let `C` be a category, let `U V W` be simplicial objects of `C` and let `a : V ⟶ U`,
`b : W ⟶ U` be morphisms of simplicial objects, and let `c` be a limit pullback cone of `a` and
`b` in `SimplicialObject C`, with projections `p`, `q`. For every simplicial object `T` the map
`h ↦ (h ≫ p, h ≫ q)` is a bijection from `Mor(T, c.pt)` onto
`Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`. This is the universal property of an arbitrary categorical
fibre product; the source's statement, about the degreewise fibre product `fibreProduct a b`, is
`fibreProduct.isBijective_canonicalMap`. -/
theorem isBijective_canonicalMap
    {U V W T : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (c : PullbackCone a b) (hc : IsLimit c) :
    Function.Bijective (PullbackCone.canonicalMap a b c (T := T)) :=
  PullbackCone.isBijective_canonicalMap a b c hc

namespace fibreProduct

variable {U V W : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
  [∀ n, HasPullback (a.app n) (b.app n)]

/-- The first projection `V ×_U W ⟶ V` of the degreewise fibre product of simplicial objects,
given in degree `n` by `pullback.fst : V_n ×_{U_n} W_n ⟶ V_n`. -/
@[simps]
noncomputable def fst : fibreProduct a b ⟶ V where
  app n := pullback.fst (a.app n) (b.app n)
  naturality _ _ _ := by exact pullback.lift_fst _ _ _

/-- The second projection `V ×_U W ⟶ W` of the degreewise fibre product of simplicial objects,
given in degree `n` by `pullback.snd : V_n ×_{U_n} W_n ⟶ W_n`. -/
@[simps]
noncomputable def snd : fibreProduct a b ⟶ W where
  app n := pullback.snd (a.app n) (b.app n)
  naturality _ _ _ := by exact pullback.lift_snd _ _ _

lemma fst_comp_eq_snd_comp : fst a b ≫ a = snd a b ≫ b := by
  ext n
  exact pullback.condition

/-- The pullback cone of `a` and `b` with point the degreewise fibre product `fibreProduct a b`
and with the degreewise projections `fst a b`, `snd a b`. -/
noncomputable abbrev cone : PullbackCone a b :=
  PullbackCone.mk (fst a b) (snd a b) (fst_comp_eq_snd_comp a b)

variable {a b}

/-- `pullback.hom_ext` in degree `n` of `fibreProduct a b`, with the source and target of the
morphisms written through `fibreProduct a b` rather than through `pullback`. -/
private lemma app_hom_ext {n : SimplexCategoryᵒᵖ} {X : C} {k l : X ⟶ (fibreProduct a b).obj n}
    (h₁ : k ≫ (fst a b).app n = l ≫ (fst a b).app n)
    (h₂ : k ≫ (snd a b).app n = l ≫ (snd a b).app n) : k = l :=
  pullback.hom_ext h₁ h₂

/-- The morphism `X ⟶ V_n ×_{U_n} W_n` into degree `n` of `fibreProduct a b` induced by a pair
`f : X ⟶ V_n`, `g : X ⟶ W_n` with `f ≫ a_n = g ≫ b_n`; it is `pullback.lift f g w`, with its
target written through `fibreProduct a b`. -/
noncomputable def appLift {n : SimplexCategoryᵒᵖ} {X : C} (f : X ⟶ V.obj n) (g : X ⟶ W.obj n)
    (w : f ≫ a.app n = g ≫ b.app n) : X ⟶ (fibreProduct a b).obj n :=
  pullback.lift f g w

@[reassoc (attr := simp)]
lemma appLift_fst {n : SimplexCategoryᵒᵖ} {X : C} (f : X ⟶ V.obj n) (g : X ⟶ W.obj n)
    (w : f ≫ a.app n = g ≫ b.app n) : appLift f g w ≫ (fst a b).app n = f :=
  pullback.lift_fst f g w

@[reassoc (attr := simp)]
lemma appLift_snd {n : SimplexCategoryᵒᵖ} {X : C} (f : X ⟶ V.obj n) (g : X ⟶ W.obj n)
    (w : f ≫ a.app n = g ≫ b.app n) : appLift f g w ≫ (snd a b).app n = g :=
  pullback.lift_snd f g w

variable (a b)

/-- The degreewise fibre product `fibreProduct a b`, with its degreewise projections, is a fibre
product of `a` and `b` in the category of simplicial objects of `C`. -/
noncomputable def isLimit : IsLimit (cone a b) :=
  PullbackCone.IsLimit.mk (fst_comp_eq_snd_comp a b)
    (fun s =>
      { app := fun n => appLift (s.fst.app n) (s.snd.app n)
          (by simpa using congrArg (fun t => NatTrans.app t n) s.condition)
        naturality := fun _ _ φ => by
          apply app_hom_ext
          · rw [Category.assoc, Category.assoc, appLift_fst, (fst a b).naturality φ,
              ← Category.assoc, appLift_fst]
            exact s.fst.naturality φ
          · rw [Category.assoc, Category.assoc, appLift_snd, (snd a b).naturality φ,
              ← Category.assoc, appLift_snd]
            exact s.snd.naturality φ })
    (fun s => by ext n; exact appLift_fst _ _ _)
    (fun s => by ext n; exact appLift_snd _ _ _)
    (fun s m h₁ h₂ => by
      ext n
      exact app_hom_ext
        ((congrArg (fun t => NatTrans.app t n) h₁).trans (appLift_fst _ _ _).symm)
        ((congrArg (fun t => NatTrans.app t n) h₂).trans (appLift_snd _ _ _).symm))

/-- **Stacks 016U.** Let `C` be a category, let `U V W` be simplicial objects of `C` and let
`a : V ⟶ U`, `b : W ⟶ U` be morphisms such that the fibre products `V_n ×_{U_n} W_n` exist in `C`,
so that the degreewise fibre product `V ×_U W = fibreProduct a b` of Tag 016T exists. For every
simplicial object `T` of `C`, the map `h ↦ (h ≫ p, h ≫ q)`, with `p`, `q` the degreewise
projections, is a bijection
`Mor(T, V ×_U W) → Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`. -/
@[stacks 016U "the fibre product of sets is `Types.PullbackObj`, and the identification is the \
  map `h ↦ (h ≫ p, h ≫ q)` given by the degreewise projections `fibreProduct.fst`, \
  `fibreProduct.snd`; the limit structure itself is `fibreProduct.isLimit`"]
theorem isBijective_canonicalMap (T : SimplicialObject C) :
    Function.Bijective (PullbackCone.canonicalMap a b (cone a b) (T := T)) :=
  PullbackCone.isBijective_canonicalMap a b _ (isLimit a b)

end fibreProduct

end CategoryTheory.SimplicialObject

end

end

/-!
## Morphisms out of a pushout are pairs of morphisms agreeing on the source

Let `C` be a category and let

```
U --a--> V
|        |
b        f
v        v
W --g--> P
```

be a pushout square in `C`. For every object `T` of `C`, composition with `f` and with `g`
identifies `Mor(P, T)` with the fibre product of sets

`Mor(V, T) ×_{Mor(U, T)} Mor(W, T) = {(p, q) | a ≫ p = b ≫ q}`,

which is the universal property of the pushout in the shape in which [Stacks, Tag 016X] states
it: a compatible pair `(p, q)` extends to `P` in exactly one way. The source states this for
simplicial objects `U, V, W, T` of `C`, that is in the category `SimplicialObject C = Δᵒᵖ ⥤ C`,
and for the pushout `V ∐_U W` of [Stacks, Tag 016W], which is formed degreewise:
`(V ∐_U W)_n = V_n ∐_{U_n} W_n`. Nothing in the universal property uses the simplicial
structure, so it is stated here for a square in an arbitrary category.

### Main results

* `CategoryTheory.IsPushout.existsUnique_desc`: for a pushout square as above and a pair
  `p : V ⟶ T`, `q : W ⟶ T` with `a ≫ p = b ≫ q`, there is a unique `φ : P ⟶ T` with
  `f ≫ φ = p` and `g ≫ φ = q`; equivalently, `φ ↦ (f ≫ φ, g ≫ φ)` is a bijection
  `Mor(P, T) → Mor(V, T) ×_{Mor(U, T)} Mor(W, T)`.

### References

* [Stacks, Tag 016X](https://stacks.math.columbia.edu/tag/016X)
* [Stacks, Tag 016W](https://stacks.math.columbia.edu/tag/016W)
-/

section

universe v u

namespace CategoryTheory

/-- **Stacks 016X** (for a pushout square in an arbitrary category, elementwise).
For a pushout square

```
U --a--> V
|        |
b        f
v        v
W --g--> P
```

in a category `C` and an object `T` of `C`, composition with `f` and with `g` identifies
`Mor(P, T)` with the fibre product `Mor(V, T) ×_{Mor(U, T)} Mor(W, T)`: a pair `p : V ⟶ T`,
`q : W ⟶ T` with `a ≫ p = b ≫ q` extends to `P` in exactly one way. -/
@[stacks 016X "for a pushout square in an arbitrary category rather than for the pushout \
  `V ∐_U W` of simplicial objects, and elementwise: an element of the fibre product \
  `Mor(V, T) ×_{Mor(U, T)} Mor(W, T)` is a pair `(p, q)` with `a ≫ p = b ≫ q`, and \
  bijectivity of `φ ↦ (f ≫ φ, g ≫ φ)` is existence and uniqueness of `φ`"]
public theorem IsPushout.existsUnique_desc {C : Type u} [Category.{v} C] {U V W P : C}
    {a : U ⟶ V} {b : U ⟶ W} {f : V ⟶ P} {g : W ⟶ P} (h : IsPushout a b f g) {T : C}
    (p : V ⟶ T) (q : W ⟶ T) (w : a ≫ p = b ≫ q) :
    ∃! φ : P ⟶ T, f ≫ φ = p ∧ g ≫ φ = q := by
  refine ⟨h.desc p q w, ⟨h.inl_desc p q w, h.inr_desc p q w⟩, fun φ ⟨hφ₁, hφ₂⟩ => ?_⟩
  exact h.hom_ext (by rw [hφ₁, h.inl_desc]) (by rw [hφ₂, h.inr_desc])

end CategoryTheory

add_to_stacks 016X "the same identification of hom-sets, bundled and in both directions: a \
  square is a pushout square if and only if for every `T` the image of the opposite square \
  under `Mor(-, T)` is a pullback square of types, whose four maps are composition with `f`, \
  `g`, `a`, `b` by `rfl`, so at each `T` it is the source's \
  `Mor(P, T) = Mor(V, T) ×_{Mor(U, T)} Mor(W, T)`"
  CategoryTheory.Square.isPushout_iff_op_map_yoneda_isPullback
add_to_stacks 016X "with the source's hypothesis that `V ∐_U W` exists: the degreewise pushout \
  of Tag 016W, whose squares `V_n ∐_{U_n} W_n` are pushout squares, is a pushout in the \
  category `Δᵒᵖ ⥤ C` of simplicial objects, to which the statements above then apply"
  CategoryTheory.IsPushout.of_forall_isPushout_app

end

section

@[expose] public section

universe u v

/-!
# Fibre products of cosimplicial objects

Let `C` be a category and let `a : V ⟶ U` and `b : W ⟶ U` be morphisms of cosimplicial objects
of `C`. If `P` is a fibre product of `a` and `b` in the category of cosimplicial objects, then for
every cosimplicial object `T` the Hom-set `Mor(T, P)` is the fibre product of `Mor(T, V)` and
`Mor(T, W)` over `Mor(T, U)`. The case of the degreewise fibre product `V ×_U W` of
[Stacks, Tag 0172], which is the statement of [Stacks, Tag 0173], is
`CategoryTheory.CosimplicialObject.isBijective_canonicalMap_pointwisePullback`.

## Main results

* `CategoryTheory.CosimplicialObject.isBijective_canonicalMap`: for a pullback square `P` of `a`
  and `b` in the category of cosimplicial objects, with projections `p`, `q`, the comparison map
  `Mor(T, P) → Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`, `f ↦ (f ≫ p, f ≫ q)`, is a bijection; the
  comparison map is `CategoryTheory.Limits.PullbackCone.canonicalMap` and its target the fibre
  product of sets `Types.PullbackObj`.

## References

* [Stacks, Tag 0172](https://stacks.math.columbia.edu/tag/0172)
* [Stacks, Tag 0173](https://stacks.math.columbia.edu/tag/0173)
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CosimplicialObject

/-- Let `C` be a category, `U V W` cosimplicial objects of `C`, and `a : V ⟶ U`, `b : W ⟶ U`
morphisms of cosimplicial objects. If `P`, with projections `p` and `q`, is a fibre product of
`a` and `b` in the category of cosimplicial objects, then for every cosimplicial object `T` the
comparison map `Mor(T, P) → Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`, `f ↦ (f ≫ p, f ≫ q)`, is a
bijection. For the degreewise fibre product of [Stacks, Tag 0172] this is
`isBijective_canonicalMap_pointwisePullback`, the statement of [Stacks, Tag 0173]. -/
theorem isBijective_canonicalMap
    {C : Type u} [Category.{v} C] {U V W : CosimplicialObject C}
    {a : V ⟶ U} {b : W ⟶ U}
    {P : CosimplicialObject C} {p : P ⟶ V} {q : P ⟶ W}
    (hPB : IsPullback p q a b) (T : CosimplicialObject C) :
    Function.Bijective (PullbackCone.canonicalMap a b hPB.cone (T := T)) :=
  PullbackCone.isBijective_canonicalMap a b _ hPB.isLimit

end CategoryTheory.CosimplicialObject

end

end
