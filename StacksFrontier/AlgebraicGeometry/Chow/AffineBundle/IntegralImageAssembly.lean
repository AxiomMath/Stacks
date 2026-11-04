module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.QuasiCompactBundle
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.DeltaDimensionInduction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# The locally finite family of integral closed subschemes carrying the images of a cycle

The first step of the proof of Stacks 02TT writes a class on `X` as a locally finite combination
`∑ m_j [W_j]` of integral closed subschemes, passes to the closures `Z_j = closure(f(W_j))` of
their images, and reassembles a rational equivalence on `Y` out of rational equivalences on the
`Z_j`. The reassembly itself is Stacks 02RZ, already available in this repository as
`Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports`; what this file supplies is the
*index datum* that step needs, and the one property of it the source uses silently.

An integral closed subscheme of `X` is the reduced induced structure on the closure of its
generic point (`Stacks.Chow.integralComponentAt_genericPointOf`), so the family `{W_j}` is the
family `closure {σ j}` of the closures of a family of points of `X`, and the family `{Z_j}` is
the family `closure {f(σ j)}` — because the closure of the image of the closure of a point is
the closure of the image of the point. The `Z_j` are therefore `integralComponentAt (f(σ j))`:
integral closed subschemes of `Y`, on the nose, with no further argument.

## The finiteness of the delta-dimension

Beyond carrying the cycle, that family plays a second role in the proof of Stacks 02TT, which
the source does not spell out. The induction of the second step descends on `dim_δ(Y)`, and
`Stacks.Chow.schemeDeltaDimension_induction` can only start from a base of *finite*
delta-dimension — a scheme merely locally of finite type over `S` can have delta-dimension `⊤`,
its irreducible components having unbounded delta-dimension. Each `Z_j` is integral, hence
irreducible, hence has exactly one irreducible component, so its delta-dimension is the relative
dimension of its generic point: an integer. That is
`Stacks.Chow.exists_schemeDeltaDimension_eq_of_irreducibleSpace`, and it is what makes the
reduction to the `Z_j` a reduction to a situation the induction can run in.

## Main results

* `Stacks.Chow.exists_schemeDeltaDimension_eq_of_irreducibleSpace`,
  `Stacks.Chow.schemeDeltaDimension_lt_top_of_irreducibleSpace` — an irreducible scheme locally
  of finite type over the base has finite delta-dimension.
* `Stacks.Chow.exists_schemeDeltaDimension_eq_integralComponentAt` — the delta-dimension of the
  integral closed subscheme attached to a point is an integer.
* `Stacks.Chow.closure_image_closure_singleton` — the closure of the image of the closure of a
  point is the closure of the image of the point.
* `Stacks.Chow.coe_support_integralComponentAt_base` — hence `Z_j = closure(f(W_j))` is carried
  by `Stacks.Chow.integralComponentAt (f (σ j))`.
* `Stacks.Chow.locallyFinite_integralComponentAt_base_of_quasiCompact`,
  `Stacks.Chow.locallyFinite_integralComponentAt_base_of_isAffineSpaceBundle` — the family
  `{Z_j}` is locally finite.
* `Stacks.Chow.rationallyEquivalent_finsum_integralComponentAt_base_of_quasiCompact`,
  `Stacks.Chow.rationallyEquivalent_finsum_integralComponentAt_base_of_isAffineSpaceBundle` —
  Stacks 02RZ at that family: rational equivalences over the `Z_j` sum to a rational equivalence
  on `Y`.

## Implementation notes

No `@[stacks 02RZ]` attribute is placed here. The tag's statement is the summation of rational
equivalences over an arbitrary locally finite family of closed subschemes, which is
`Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports` in
`StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier`, where the attribute
already sits; the results below are that statement at one particular family together with
properties of the family, and each proves strictly less than the tag.

## References

* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### An irreducible scheme has finite delta-dimension -/

/-- **The delta-dimension of an irreducible scheme locally of finite type over the base is an
integer.** The delta-dimension is the supremum over the irreducible components of the relative
dimension of their generic points, and an irreducible space has a single irreducible component,
so the supremum is attained and is the relative dimension of the generic point.

This is what starts the delta-dimension induction of Stacks 02TT: a scheme merely locally of
finite type over `S` can have delta-dimension `⊤`, and `Stacks.Chow.schemeDeltaDimension_induction`
asks for finiteness. -/
theorem exists_schemeDeltaDimension_eq_of_irreducibleSpace (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IrreducibleSpace X] :
    ∃ n : ℤ, schemeDeltaDimension C p = (n : EInt) :=
  ⟨relativeDimension C.dimensionFunction p (genericPoint X),
    schemeDeltaDimension_eq_genericPoint C p⟩

/-- An irreducible scheme locally of finite type over the base has finite delta-dimension, in the
form `Stacks.Chow.schemeDeltaDimension_induction` takes. -/
theorem schemeDeltaDimension_lt_top_of_irreducibleSpace (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IrreducibleSpace X] :
    schemeDeltaDimension C p < ⊤ := by
  obtain ⟨n, hn⟩ := exists_schemeDeltaDimension_eq_of_irreducibleSpace C p
  rw [hn]
  exact lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top n)

/-- The delta-dimension of the integral closed subscheme attached to a point of a scheme locally
of finite type over the base is an integer: that subscheme is integral, hence irreducible. -/
theorem exists_schemeDeltaDimension_eq_integralComponentAt (C : ChowSituation.{u})
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (y : Y) :
    ∃ n : ℤ, schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ sY) = (n : EInt) :=
  let := isIntegral_integralComponentAt y
  exists_schemeDeltaDimension_eq_of_irreducibleSpace C _

/-- The delta-dimension of the integral closed subscheme attached to a point of a scheme locally
of finite type over the base is finite. -/
theorem schemeDeltaDimension_lt_top_integralComponentAt (C : ChowSituation.{u})
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (y : Y) :
    schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ sY) < ⊤ :=
  let := isIntegral_integralComponentAt y
  schemeDeltaDimension_lt_top_of_irreducibleSpace C _

/-! ### The closures of the images -/

/-- **The closure of the image of the closure of a point is the closure of the image of the
point.** This is `closure_image_closure` at a singleton. -/
theorem closure_image_closure_singleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (x : X) :
    closure (f '' closure ({x} : Set X)) = closure ({f x} : Set Y) := by
  rw [closure_image_closure hf, Set.image_singleton]

/-- **`Z_j = closure(f(W_j))` is the integral closed subscheme attached to `f` of the generic
point of `W_j`.** An integral closed subscheme `W_j` of `X` is the reduced induced structure on
the closure of its generic point `σ j` (`Stacks.Chow.integralComponentAt_genericPointOf`), and
the closure of the image of that closure is the closure of `f (σ j)`. -/
theorem coe_support_integralComponentAt_base {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ((integralComponentAt (f.base x)).support : Set Y) =
      closure (f.base '' closure ({x} : Set X)) := by
  rw [coe_support_integralComponentAt,
    closure_image_closure_singleton (Scheme.Hom.continuous f) x]

/-- **The family `{Z_j}` of Stacks 02TT step one is locally finite.** For a quasi-compact
morphism `f` and a locally finite family of integral closed subschemes `closure {σ j}` of the
source, the integral closed subschemes of the target attached to the images `f (σ j)` form a
locally finite family: their supports are the closures of the images of the supports, and
`Stacks.Chow.locallyFinite_closure_image_of_quasiCompact` applies. -/
theorem locallyFinite_integralComponentAt_base_of_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {J : Type*} (σ : J → X)
    (hσ : LocallyFinite fun j ↦ closure ({σ j} : Set X)) :
    LocallyFinite fun j ↦ ((integralComponentAt (f.base (σ j))).support : Set Y) := by
  have h := locallyFinite_closure_image_of_quasiCompact f hσ
  exact h.subset fun j ↦ (coe_support_integralComponentAt_base f (σ j)).subset

/-- **The family `{Z_j}` of Stacks 02TT step one is locally finite, for an affine-space bundle.**
An affine-space bundle is quasi-compact
(`Stacks.Chow.quasiCompact_of_isAffineSpaceBundle`). -/
theorem locallyFinite_integralComponentAt_base_of_isAffineSpaceBundle {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : ℕ) (h : IsAffineSpaceBundle f r) {J : Type*} (σ : J → X)
    (hσ : LocallyFinite fun j ↦ closure ({σ j} : Set X)) :
    LocallyFinite fun j ↦ ((integralComponentAt (f.base (σ j))).support : Set Y) :=
  let := quasiCompact_of_isAffineSpaceBundle f r h
  locallyFinite_integralComponentAt_base_of_quasiCompact f σ hσ

/-! ### Stacks 02RZ at that family -/

/-- **The assembly of the first step of Stacks 02TT.** Let `f : X ⟶ Y` be quasi-compact with `Y`
locally of finite type over the base, let `{closure {σ j}}` be a locally finite family of
integral closed subschemes of `X` — the components of a class on `X` — and let `Z_j` be the
integral closed subscheme of `Y` carried by `closure(f(closure {σ j}))`. If `k`-cycles `a j` and
`b j` on `Z_j` are rationally equivalent for every `j`, and the `k`-cycles `α`, `β` on `Y` are
coefficientwise the locally finite sums of their pushforwards, then `α` and `β` are rationally
equivalent on `Y`.

This is Stacks 02RZ (`Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports`) at the family
`{Z_j}`, whose local finiteness is
`Stacks.Chow.locallyFinite_integralComponentAt_base_of_quasiCompact`. Each `Z_j` is integral by
`Stacks.Chow.isIntegral_integralComponentAt` and has finite delta-dimension by
`Stacks.Chow.exists_schemeDeltaDimension_eq_integralComponentAt`, which is what lets the
delta-dimension induction of the second step run over it. -/
theorem rationallyEquivalent_finsum_integralComponentAt_base_of_quasiCompact
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [QuasiCompact f] (k : ℤ) {J : Type u} (σ : J → X)
    (hσ : LocallyFinite fun j ↦ closure ({σ j} : Set X))
    (a b : ∀ j, CycleGroup C ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) k)
    (hab : ∀ j, RationallyEquivalent C
      ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) k (a j) (b j))
    {α β : CycleGroup C sY k}
    (hα : ∀ y : Y, α.1 y = ∑ᶠ j : J, (properPushforward C
      ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) sY
      (integralComponentAt (f.base (σ j))).subschemeι rfl k (a j)).1 y)
    (hβ : ∀ y : Y, β.1 y = ∑ᶠ j : J, (properPushforward C
      ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) sY
      (integralComponentAt (f.base (σ j))).subschemeι rfl k (b j)).1 y) :
    RationallyEquivalent C sY k α β :=
  rationallyEquivalent_finsum_of_closedSupports C sY k
    (fun j ↦ integralComponentAt (f.base (σ j)))
    (locallyFinite_integralComponentAt_base_of_quasiCompact f σ hσ) a b hab hα hβ

/-- **The assembly of the first step of Stacks 02TT, for an affine-space bundle.** This is
`Stacks.Chow.rationallyEquivalent_finsum_integralComponentAt_base_of_quasiCompact` with
quasi-compactness supplied by `Stacks.Chow.quasiCompact_of_isAffineSpaceBundle`, which is the
form the proof of Stacks 02TT uses. -/
theorem rationallyEquivalent_finsum_integralComponentAt_base_of_isAffineSpaceBundle
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (r : ℕ) (hbundle : IsAffineSpaceBundle f r) (k : ℤ) {J : Type u} (σ : J → X)
    (hσ : LocallyFinite fun j ↦ closure ({σ j} : Set X))
    (a b : ∀ j, CycleGroup C ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) k)
    (hab : ∀ j, RationallyEquivalent C
      ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) k (a j) (b j))
    {α β : CycleGroup C sY k}
    (hα : ∀ y : Y, α.1 y = ∑ᶠ j : J, (properPushforward C
      ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) sY
      (integralComponentAt (f.base (σ j))).subschemeι rfl k (a j)).1 y)
    (hβ : ∀ y : Y, β.1 y = ∑ᶠ j : J, (properPushforward C
      ((integralComponentAt (f.base (σ j))).subschemeι ≫ sY) sY
      (integralComponentAt (f.base (σ j))).subschemeι rfl k (b j)).1 y) :
    RationallyEquivalent C sY k α β :=
  let := quasiCompact_of_isAffineSpaceBundle f r hbundle
  rationallyEquivalent_finsum_integralComponentAt_base_of_quasiCompact C sY f k σ hσ a b hab hα hβ

end Stacks.Chow

end
