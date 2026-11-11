module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose
public import StacksCore.Tactic.StacksAttribute

/-!
# Chow groups of Chow motives

A Chow motive over a base field is a triple `(X, p, m)` with `X` a smooth projective scheme,
`p ∈ Corr⁰(X, X)` a correspondence satisfying `p ∘ p = p`, and `m ∈ ℤ`. Its `i`-th Chow group is
the image of `p` acting on the rational Chow classes of `X` in codimension `i + m`:
`CH^i(M) = p(CH^{i+m}(X) ⊗ ℚ)`.

This file defines that image, as a `ℚ`-subspace of `CH^{i+m}(X) ⊗ ℚ`, relative to a
correspondence calculus carried as data (`Stacks.WeilCohomology.CorrespondenceCalculus`). It is
not the registration of Stacks 0FGL: the Chow groups of a Chow motive with the correspondence
calculus of Section 0FFZ actually constructed, for an arbitrary smooth projective scheme over a
field, are `Stacks.WeilCohomology.SmoothProjectiveScheme.ChowMotive.chowGroup` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroupsOfMotives`, which carries the
tag.

## Main definitions

* `Stacks.WeilCohomology.RationalChowGroup`: the rational Chow group `A_n(X) ⊗ ℚ`.
* `Stacks.WeilCohomology.RationalChowGroupCodim`: the same group indexed by codimension,
  `CH^j(X) ⊗ ℚ = A_{d-j}(X) ⊗ ℚ` for `X` of dimension `d`.
* `Stacks.WeilCohomology.CorrespondenceCalculus`: composition of degree-zero
  self-correspondences and their pushforward action on rational Chow groups, together with the
  compatibility of the two.
* `Stacks.WeilCohomology.ChowMotive`: a Chow motive `(X, p, m)` relative to such a calculus.
* `Stacks.WeilCohomology.ChowMotive.projectorAction`: the action `p_*` of the projector on
  `CH^{i+m}(X) ⊗ ℚ`.
* `Stacks.WeilCohomology.ChowMotive.chowGroup`: the Chow group `CH^i(M)`, the range of `p_*`,
  relative to the carried calculus.

## Main results

* `Stacks.WeilCohomology.ChowMotive.projectorAction_idempotent`: the action of the projector is
  an idempotent endomorphism of `CH^{i+m}(X) ⊗ ℚ`.
* `Stacks.WeilCohomology.ChowMotive.mem_chowGroup_iff`: `CH^i(M)` is the fixed subspace of
  `p_*`, so a class lies in it exactly when `p` acts on it as the identity.
* `Stacks.WeilCohomology.ChowMotive.chowGroup_eq_top_of_projectorAction_eq_id`: when `p` acts as
  the identity — the case `M = h(X)` of the unit projector — the Chow group of the motive is all
  of `CH^{i+m}(X) ⊗ ℚ`.

## Implementation notes

**Grading.** This repository grades Chow groups by dimension: `Stacks.Chow.chowGroup C sX n` is
`A_n(X)`. The source grades the Chow groups of a motive by codimension. For `X` of dimension `d`
the two are related by `CH^j(X) = A_{d-j}(X)`, and `RationalChowGroupCodim` performs that
translation, so that the index `i + m` of the source appears literally in the statement of
`ChowMotive.chowGroup`. The dimension `d` is carried as a field of `ChowMotive` rather than
derived from `X`, exactly as `Stacks.WeilCohomology.Correspondence` carries the dimension of its
target as a parameter: with the dimension supplied, the definitions make sense, and are the
intended ones, for any scheme locally of finite type over the base, and no equidimensionality
hypothesis is needed. Note `Correspondence C sX sX d 0` is `A_d(X ×_S X) ⊗ ℚ`, which for `X`
equidimensional of dimension `d` is the source's `Corr⁰(X, X) = CH^d(X × X) ⊗ ℚ`.

**The carried hypothesis.** The definition of `CH^i(M)` presupposes two things from the
correspondence calculus of Stacks 0FFZ: composition of correspondences, needed to say what it
means for `p` to be a projector, and the pushforward action `c ↦ c_*` of a correspondence on
rational Chow groups, which is what `p(-)` denotes. Both are built from the intersection product
on a smooth projective scheme together with flat pullback and proper pushforward. Here they are
carried as data, in `CorrespondenceCalculus`, alongside the one law relating them that this
definition uses, `(c' ∘ c)_* = c'_* ∘ c_*` — part (4) of Stacks 0FG0. Nothing else about the
calculus is assumed: in particular bilinearity and associativity of composition, the
identifications of `Corr^r(X, Spec k)` and `Corr^r(Spec k, X)` with rational Chow groups, and the
behaviour of the unit correspondence are not imposed, since `CH^i(M)` does not use them. This is
the same device by which `StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory` carries
the Chow cycle operations it needs as the fields of `Stacks.WeilCohomology.ChowCycleData`.

The correspondence calculus of Section 0FFZ is constructed, from the equidimensional pieces of a
smooth projective scheme over a field, in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroupsOfMotives`
(`SmoothProjectiveScheme.correspondenceComp` and
`SmoothProjectiveScheme.correspondencePushforward`), and the Chow groups defined there,
`SmoothProjectiveScheme.ChowMotive.chowGroup`, are the unconditional ones of Stacks 0FGL.

**Why a `Submodule`.** `CH^i(M)` is returned as a `Submodule ℚ (CH^{i+m}(X) ⊗ ℚ)` rather than as
a bare type. The source's own uses of it are all uses of the subspace: a morphism of motives
`c : M → N` induces `c_* : CH^i(M) → CH^i(N)` by *restricting* the ambient map
`CH^{i+m}(X) ⊗ ℚ → CH^{i+n}(Y) ⊗ ℚ` to the two subspaces, and the direct sum decompositions
coming from the Karoubian structure of the category of motives are decompositions of
`CH^*(X) ⊗ ℚ` into subspaces. Both need the embedding into the ambient group, which a quotient
or an opaque type would discard; and `Submodule ℚ` supplies the `ℚ`-vector space structure of
Stacks 0FGM on the coercion for free.

**Smoothness and projectivity.** Neither hypothesis enters the definition, and so, following
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose` and
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Graph`, neither is imposed: a
Chow motive in the sense of the source is a `ChowMotive` whose `X` is smooth and projective
over a base field.

## References

* [Stacks Project, Tag 0FGL](https://stacks.math.columbia.edu/tag/0FGL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### Rational Chow groups -/

/-- The rational Chow group `A_n(X) ⊗ ℚ` of a scheme locally of finite type over the base. It is
a `ℚ`-vector space through `TensorProduct.leftModule`, the rational factor being on the left. -/
abbrev RationalChowGroup (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (n : ℤ) : Type u :=
  TensorProduct ℤ ℚ (Stacks.Chow.chowGroup C sX n)

/-- The rational Chow group `CH^j(X) ⊗ ℚ` of codimension `j`, for `X` of dimension `d`: in the
dimension grading of this repository it is `A_{d-j}(X) ⊗ ℚ`. -/
abbrev RationalChowGroupCodim (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (d j : ℤ) : Type u :=
  RationalChowGroup C sX (d - j)

/-! ### The correspondence calculus, carried as data -/

/-- Composition of degree-zero self-correspondences and their pushforward action on rational
Chow groups — the part of the correspondence calculus of Stacks 0FFZ that the Chow groups of a
Chow motive use — carried as data over a fixed base situation.

The field `pushforward` is `c ↦ c_*`; since `c` has degree zero it preserves the grading. The
field `pushforward_comp` is the instance of Stacks 0FG0(4) saying that the action is functorial
for composition. -/
structure CorrespondenceCalculus (C : ChowSituation.{u}) where
  /-- Composition `Corr⁰(X, X) × Corr⁰(X, X) → Corr⁰(X, X)`, written `(c', c) ↦ c' ∘ c`. -/
  comp : ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (d : ℤ),
    Correspondence C sX sX d 0 → Correspondence C sX sX d 0 → Correspondence C sX sX d 0
  /-- The pushforward action `c ↦ c_*` of a degree-zero self-correspondence on the rational Chow
  groups of `X`, a `ℚ`-linear endomorphism in each degree. -/
  pushforward : ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (d n : ℤ),
    Correspondence C sX sX d 0 → RationalChowGroup C sX n →ₗ[ℚ] RationalChowGroup C sX n
  /-- The action is functorial for composition: `(c' ∘ c)_* = c'_* ∘ c_*`. -/
  pushforward_comp : ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (d n : ℤ)
      (c c' : Correspondence C sX sX d 0),
    pushforward sX d n (comp sX d c' c) = (pushforward sX d n c').comp (pushforward sX d n c)

/-! ### Chow motives -/

/-- A Chow motive `(X, p, m)` over the base situation `C`, relative to a correspondence calculus
`A`: a scheme `X` locally of finite type over the base, of dimension `dimension`, a degree-zero
self-correspondence `projector` of `X` which is idempotent for the composition of `A`, and an
integral Tate twist `twist`.

In the source `X` is required to be smooth and projective over a base field; that hypothesis is
not used by anything below and so is not imposed here. -/
structure ChowMotive (C : ChowSituation.{u}) (A : CorrespondenceCalculus C) where
  /-- The underlying scheme of the motive. -/
  X : Scheme.{u}
  /-- Its structure morphism to the base of the situation. -/
  sX : X ⟶ C.S
  /-- The structure morphism is locally of finite type, so `X` has Chow groups. -/
  [locallyOfFiniteType : LocallyOfFiniteType sX]
  /-- The dimension of `X`, which fixes the degree of a correspondence on it. -/
  dimension : ℤ
  /-- The projector `p ∈ Corr⁰(X, X)` of the motive. -/
  projector : Correspondence C sX sX dimension 0
  /-- The projector is idempotent: `p ∘ p = p`. -/
  projector_idempotent : A.comp sX dimension projector projector = projector
  /-- The Tate twist `m` of the motive. -/
  twist : ℤ

attribute [instance] ChowMotive.locallyOfFiniteType

namespace ChowMotive

variable {C : ChowSituation.{u}} {A : CorrespondenceCalculus C}

/-- The action `p_*` of the projector of a Chow motive `M = (X, p, m)` on the rational Chow
classes of `X` of codimension `i + m`. -/
def projectorAction (M : ChowMotive C A) (i : ℤ) :
    RationalChowGroupCodim C M.sX M.dimension (i + M.twist) →ₗ[ℚ]
      RationalChowGroupCodim C M.sX M.dimension (i + M.twist) :=
  A.pushforward M.sX M.dimension (M.dimension - (i + M.twist)) M.projector

/-- The action of the projector of a Chow motive is idempotent. This is the idempotence
`p ∘ p = p` of the projector, transported along the functoriality of the action. -/
theorem projectorAction_idempotent (M : ChowMotive C A) (i : ℤ) :
    (M.projectorAction i).comp (M.projectorAction i) = M.projectorAction i := by
  rw [projectorAction, ← A.pushforward_comp, M.projector_idempotent]

/-- The action of the projector of a Chow motive, applied twice, is the action applied once. -/
theorem projectorAction_projectorAction (M : ChowMotive C A) (i : ℤ)
    (α : RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :
    M.projectorAction i (M.projectorAction i α) = M.projectorAction i α :=
  DFunLike.congr_fun (M.projectorAction_idempotent i) α

/-- The `i`-th Chow group `CH^i(M)` of a Chow motive `M = (X, p, m)` relative to the carried
correspondence calculus `A`: the image of the projector `p`, acting through `A.pushforward`, on
the rational Chow classes of `X` of codimension `i + m`, as a `ℚ`-subspace of
`CH^{i+m}(X) ⊗ ℚ`. It is the Chow group of Stacks 0FGL only once `A` is the correspondence
calculus of Section 0FFZ; the unconditional definition, with that calculus constructed, is
`Stacks.WeilCohomology.SmoothProjectiveScheme.ChowMotive.chowGroup`. -/
def chowGroup (M : ChowMotive C A) (i : ℤ) :
    Submodule ℚ (RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :=
  LinearMap.range (M.projectorAction i)

/-- The Chow group of a motive is the range of the action of its projector. -/
theorem chowGroup_eq_range (M : ChowMotive C A) (i : ℤ) :
    M.chowGroup i = LinearMap.range (M.projectorAction i) :=
  rfl

/-- A rational Chow class of codimension `i + m` on `X` lies in `CH^i(M)`, relative to the
carried correspondence calculus `A`, exactly when the projector fixes it: the image of an
idempotent is its fixed subspace. For the unconditional Chow groups of Stacks 0FGL see
`Stacks.WeilCohomology.SmoothProjectiveScheme.ChowMotive.mem_chowGroup_iff`. -/
theorem mem_chowGroup_iff (M : ChowMotive C A) (i : ℤ)
    (α : RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :
    α ∈ M.chowGroup i ↔ M.projectorAction i α = α := by
  refine ⟨?_, fun hα => ⟨α, hα⟩⟩
  rintro ⟨β, rfl⟩
  exact M.projectorAction_projectorAction i β

/-- The projector of a motive takes every rational Chow class of codimension `i + m` into the
`i`-th Chow group of the motive. -/
theorem projectorAction_mem_chowGroup (M : ChowMotive C A) (i : ℤ)
    (α : RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :
    M.projectorAction i α ∈ M.chowGroup i :=
  ⟨α, rfl⟩

/-- When the projector of a motive acts as the identity on rational Chow classes of codimension
`i + m` — as it does for the unit projector, where `M = h(X)` — the `i`-th Chow group of the
motive is the whole of `CH^{i+m}(X) ⊗ ℚ`. -/
theorem chowGroup_eq_top_of_projectorAction_eq_id (M : ChowMotive C A) (i : ℤ)
    (h : M.projectorAction i = LinearMap.id) :
    M.chowGroup i = ⊤ := by
  rw [chowGroup_eq_range, h, LinearMap.range_id]

end ChowMotive

end Stacks.WeilCohomology

end
