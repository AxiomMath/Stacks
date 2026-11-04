module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPresentationTail
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardTriangle

/-!
# The sequence of Stacks 03M8 with its composites presented as single morphisms

In the notation of Stacks 03M8 — `f : X ⟶ Y`, an étale chart `τ : U ⟶ X`, `R = U ×_X U` with its
projections `t, s : R ⟶ U`, `a = τ ≫ f` and `b = ρ ≫ f` for `ρ = t ≫ τ = s ≫ τ` — the asserted
sequence

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`

has two parallel arrows `a_*(F|_U) ⟶ b_*(F|_R)`, one for `t` and one for `s`.  Each arises in two
shapes: the *natural* one the source writes — the unit of the Stacks 03D7 adjunction at the
projection, pushed forward along `a`, followed by the composition comparisons of Stacks 03LU — and
the *transported* one, the direct image along `f` of the corresponding arrow for the identity of
`X`, conjugated by the comparisons `τ_* ⋙ f_* ≅ a_*` and `ρ_* ⋙ f_* ≅ b_*`.  That the two agree
is the step that reduces the sequence for a general `f` to the sequence for the identity of `X`,
since `f_*` preserves limits, being a right adjoint.

This file proves that agreement, with **every composite presented as a single named morphism**
through `AlgebraicGeometry.Space.modulePushforwardTriangle` and
`AlgebraicGeometry.Space.modulePullbackTriangle`: `ρ`, `a` and `b` are morphisms carrying
`t ≫ τ = ρ`, `τ ≫ f = a`, `t ≫ a = b` and `ρ ≫ f = b` as hypotheses.  Two consequences, and they
are the whole reason for the vocabulary:

* the two comparisons that meet at the triple composite meet at the *single* functor `b_*`, so the
  identification of the spellings `(t ≫ τ) ≫ f` and `t ≫ (τ ≫ f)` never enters a statement — which
  is what makes the agreement provable at all; see the implementation notes;
* the two parallel arrows attached to `t` and to `s` have *literally the same source and target*,
  so the fork condition is an equality of morphisms with no `eqToHom` transport in it, where the
  version of `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackPresentationComplex.lean` needs
  one.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackUnitApp`: the unit of
  `AlgebraicGeometry.Space.modulePullbackAdjunction` at a single module, with its type written in
  the uncomposed spelling `M ⟶ h_*(h^*M)`.
* `AlgebraicGeometry.Space.modulePullbackTriangleInvApp`: the comparison
  `h^*(τ^*F) ⟶ ρ^*F` of `AlgebraicGeometry.Space.modulePullbackTriangle` at a single module, with
  its type written in the uncomposed spelling.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardPresentationTail`: **the natural shape of the second
  arrow is the transported shape** — the clause the transport
  `CategoryTheory.Limits.isLimitForkOfMap` consumes.  This is the fourth of the four formal
  transports of Stacks 03M8, and it was *not available* before the triangle vocabulary existed;
  see the implementation notes.
* `AlgebraicGeometry.Space.modulePullbackUnitApp_comp`: the composition law for the units of
  Stacks 03LU, read through the second arrow for the identity of `X`.
* `AlgebraicGeometry.Space.modulePushforwardPresentationComplex`: **the sequence is a complex**:
  the first arrow followed by the second is the first arrow attached to `ρ`, so it does not depend
  on which projection built the second arrow.
* `AlgebraicGeometry.Space.modulePushforwardPresentationFork`: the two parallel arrows attached to
  `t` and to `s` agree after the first arrow — the fork condition, with no transport in it.

## Implementation notes

**What the triangle vocabulary removed.**  Stated with the composites written out, the agreement
of the two shapes needs the identification of `t_* ⋙ (τ ≫ f)_* ≅ (t ≫ τ ≫ f)_*` with
`(t ≫ τ)_* ⋙ f_* ≅ ((t ≫ τ) ≫ f)_*` *inside* a composition of morphisms of `𝒪`-modules.  That
identification is cheap on its own — `(t ≫ τ ≫ f)_* = ((t ≫ τ) ≫ f)_*` by `Eq.refl` is checked in
a fifth of a second — and ruinous as part of matching an instantiated generic type against a
declared one: the elaborator reached

`error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached`

on exactly that match, and in a scratch probe at an eightfold budget it still had not finished
after 73.6 seconds, so the reduction diverges rather than merely costing more than the default
allows.  The measurement is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackPresentationTail.lean`, which reduced the
clause to that one unavailable instantiation.

With `ρ`, `a` and `b` named and the two comparisons taken as
`AlgebraicGeometry.Space.modulePushforwardTriangle`, both of them land on `b_*` and there is
nothing to identify: `AlgebraicGeometry.Space.modulePushforwardPresentationTail` below is
`CategoryTheory.Functor.compIso_comp_unitArrow_tail` instantiated at the four triangles, and it is
elaborated and kernel-checked in a fifth of a second.  The spelling identification survives in one
place only, the `rfl` inside the proof of
`AlgebraicGeometry.Space.modulePushforwardTriangle_assoc`, where it is an equality of *functors*.

**Why the unit and the inverse-image comparison are given names.**  Removing the composites was
necessary and not sufficient.  The generic clause types its two arrow arguments as `M ⟶ p.obj N`
and `N ⟶ N'`, while `(modulePullbackAdjunction B S hS h).unit.app M` is typed
`(𝟭 _).obj M ⟶ (h^* ⋙ h_*).obj M` and `(modulePullbackTriangle B S hS hρ).inv.app F` is typed
`(τ^* ⋙ h^*).obj F ⟶ ρ^*.obj F`.  Passing those spellings makes the instantiated conclusion carry
`(𝟭 _).obj` and `(· ⋙ ·).obj` where the declared clause carries the uncomposed objects, and
reconciling *those* is again a reduction that does not come back: with the arrows passed raw the
same `exact` reached

`error: (deterministic) timeout at 'isDefEq', maximum number of heartbeats (200000) has been
reached`

even with all six functors and all three module arguments supplied explicitly.  Naming the two
arrows, so that their declared types are the uncomposed ones, is what makes the clause match; the
two spellings are then reconciled once, in the body of each definition, on the `Hom` type alone.

Nothing here raises a compiler limit or disables a linter.

## What is not done

**The exactness assertion of Stacks 03M8 is not reached**, and what it still needs is the
geometric input: that a *surjective* étale chart `τ` and the cartesian square `R = U ×_X U` make
the fork

`F → τ_*(F|_U) ⇉ ρ_*(F|_R)`

in `Mod(𝒪_X)` a limit.  Nothing in this file assumes surjectivity or the cartesian square, and
nothing here can: the four clauses above are the formal half, and
`AlgebraicGeometry.Space.modulePushforwardPresentationFork` is the "complex" half of the source's
exactness assertion and not the exactness itself.

Granted that input, the remaining step is formal — `CategoryTheory.Limits.isLimitForkOfMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePresentationForkTransports.lean`) at the direct
image along `f`, which preserves limits by
`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`, with the two comparisons read at a
module by `AlgebraicGeometry.Space.modulePushforwardTriangleApp`, its hypotheses `ht` and `hs`
supplied by `AlgebraicGeometry.Space.modulePushforwardPresentationTail` above and its `h` by
`AlgebraicGeometry.Space.modulePushforwardPresentationFork`.  That instantiation **elaborates**
and then exceeds the *kernel's* budget rather than the elaborator's: it reports

`error: (kernel) deterministic timeout`

on a lifted auxiliary proof of the instantiation, `_proof_1`.  It does so both with the fork
condition inlined in the statement and with it taken as a hypothesis, and both with the `he`
clause inlined as `Eq.refl` and with that clause lifted into a declaration of its own so as to
get its own kernel budget.  The remaining candidate, not tried, is to name the preservation
instance `PreservesLimit (parallelPair _ _) (modulePushforward B S hS f)` as a declaration of its
own: the instance term synthesized from the adjunction is where the lifted proof comes from, and
the kernel budget is per declaration.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U X Y : AlgebraicSpaces B S hS}

/-! ### The two arrows, with their types in the uncomposed spelling -/

/-- **The unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` at a single module**, with its
type written as `M ⟶ h_*(h^*M)` rather than as
`(𝟭 _).obj M ⟶ (h^* ⋙ h_*).obj M`.

The two spellings are definitionally equal, and the uncomposed one is what a consumer typing its
arrow arguments as `M ⟶ p.obj N` needs; see this file's implementation notes. -/
def modulePullbackUnitApp (h : R ⟶ U) (M : Modules.{u, u} B S hS U.1 U.2) :
    M ⟶ (modulePushforward B S hS h).obj ((modulePullback B S hS h).obj M) :=
  (modulePullbackAdjunction B S hS h).unit.app M

/-- `AlgebraicGeometry.Space.modulePullbackUnitApp` is the unit of
`AlgebraicGeometry.Space.modulePullbackAdjunction`. -/
theorem modulePullbackUnitApp_eq (h : R ⟶ U) (M : Modules.{u, u} B S hS U.1 U.2) :
    modulePullbackUnitApp B S hS h M = (modulePullbackAdjunction B S hS h).unit.app M := rfl

/-- **The comparison `h^*(τ^*F) ⟶ ρ^*F` of inverse images of Stacks 03LU at a single module**, for
a morphism `ρ : R ⟶ X` with `h ≫ τ = ρ`, with its type written as `h^*(τ^*F) ⟶ ρ^*F` rather than as
`(τ^* ⋙ h^*).obj F ⟶ ρ^*.obj F`.

It is `AlgebraicGeometry.Space.modulePullbackTriangle` read at `F`. -/
def modulePullbackTriangleInvApp (τ : U ⟶ X) (h : R ⟶ U) {ρ : R ⟶ X} (hρ : h ≫ τ = ρ)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F) ⟶
      (modulePullback B S hS ρ).obj F :=
  (modulePullbackTriangle B S hS hρ).inv.app F

/-- `AlgebraicGeometry.Space.modulePullbackTriangleInvApp` is
`AlgebraicGeometry.Space.modulePullbackTriangle` read at a module. -/
theorem modulePullbackTriangleInvApp_eq (τ : U ⟶ X) (h : R ⟶ U) {ρ : R ⟶ X} (hρ : h ≫ τ = ρ)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    modulePullbackTriangleInvApp B S hS τ h hρ F =
      (modulePullbackTriangle B S hS hρ).inv.app F := rfl

/-! ### The natural shape of the second arrow is the transported shape -/

/-- **The fourth transport of Stacks 03M8: the natural shape of the second arrow is the
transported shape.**  For `f : X ⟶ Y`, a chart `τ : U ⟶ X`, a morphism `h : R ⟶ U` and morphisms
`ρ : R ⟶ X`, `a : U ⟶ Y`, `b : R ⟶ Y` with `h ≫ τ = ρ`, `τ ≫ f = a`, `h ≫ a = b` and `ρ ≫ f = b`:
the comparison `τ_* ⋙ f_* ≅ a_*` followed by the second arrow `a_*(F|_U) ⟶ b_*(F|_R)` in its
natural shape is the direct image along `f` of the corresponding arrow
`τ_*(F|_U) ⟶ ρ_*(F|_R)` for the identity of `X`, followed by the comparison `ρ_* ⋙ f_* ≅ b_*`.

This is the hypothesis `ht` — and, for the other projection, `hs` — of
`CategoryTheory.Limits.isLimitForkOfMap`, so it is the step that carries a limiting fork for the
identity of `X` over to one for `f`.

It is `CategoryTheory.Functor.compIso_comp_unitArrow_tail` instantiated at the four triangles
`h_* ⋙ τ_* ≅ ρ_*`, `τ_* ⋙ f_* ≅ a_*`, `ρ_* ⋙ f_* ≅ b_*` and `h_* ⋙ a_* ≅ b_*`, whose cocycle law
is `AlgebraicGeometry.Space.modulePushforwardTriangle_assoc`.  Because the two comparisons that
meet at the triple composite both land on `b_*`, no identification of the spellings `(h ≫ τ) ≫ f`
and `h ≫ (τ ≫ f)` arises; with the composites written out the instantiation does not terminate,
and with the unit and the inverse-image comparison passed in their composed spellings the match
does not terminate either.  Both measurements are in this file's implementation notes. -/
theorem modulePushforwardPresentationTail (f : X ⟶ Y) (τ : U ⟶ X) (h : R ⟶ U) {ρ : R ⟶ X}
    (hρ : h ≫ τ = ρ) {a : U ⟶ Y} (ha : τ ≫ f = a) {b : R ⟶ Y} (hb : h ≫ a = b) (hb' : ρ ≫ f = b)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardTriangle B S hS ha).hom.app ((modulePullback B S hS τ).obj F) ≫
        ((modulePushforward B S hS a).map
              (modulePullbackUnitApp B S hS h ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hb).hom.app
              ((modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F))) ≫
          (modulePushforward B S hS b).map
            (modulePullbackTriangleInvApp B S hS τ h hρ F) =
      (modulePushforward B S hS f).map
          ((modulePushforward B S hS τ).map
              (modulePullbackUnitApp B S hS h ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hρ).hom.app
                ((modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F)) ≫
              (modulePushforward B S hS ρ).map
                (modulePullbackTriangleInvApp B S hS τ h hρ F)) ≫
        (modulePushforwardTriangle B S hS hb').hom.app ((modulePullback B S hS ρ).obj F) :=
  Functor.compIso_comp_unitArrow_tail (modulePushforwardTriangle B S hS hρ)
    (modulePushforwardTriangle B S hS ha) (modulePushforwardTriangle B S hS hb')
    (modulePushforwardTriangle B S hS hb) (modulePushforwardTriangle_assoc hρ ha hb hb')
    (modulePullbackUnitApp B S hS h ((modulePullback B S hS τ).obj F))
    (modulePullbackTriangleInvApp B S hS τ h hρ F)

/-! ### The sequence is a complex -/

/-- **The composition law for the units of the Stacks 03LU adjunction, read through the second
arrow for the identity of `X`.**  The unit at `τ`, followed by the direct image along `τ` of the
unit at `h`, the comparison `h_* ⋙ τ_* ≅ ρ_*` of direct images and the direct image along `ρ` of
the comparison `h^*(τ^*F) ⟶ ρ^*F` of inverse images, is the unit at `ρ`.

It is `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app`, the same law with the
composite written out, read through the two triangles at the composite itself. -/
theorem modulePullbackUnitApp_comp (τ : U ⟶ X) (h : R ⟶ U) {ρ : R ⟶ X} (hρ : h ≫ τ = ρ)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    modulePullbackUnitApp B S hS τ F ≫
        ((modulePushforward B S hS τ).map
              (modulePullbackUnitApp B S hS h ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hρ).hom.app
                ((modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F)) ≫
              (modulePushforward B S hS ρ).map
                (modulePullbackTriangleInvApp B S hS τ h hρ F)) =
      modulePullbackUnitApp B S hS ρ F := by
  subst hρ
  simpa only [modulePullbackUnitApp, modulePullbackTriangleInvApp,
    modulePushforwardTriangle_rfl, modulePullbackTriangle_rfl, Iso.symm_inv] using
    modulePullbackAdjunction_unit_comp_app B S hS h τ F

/-- **The sequence of Stacks 03M8 is a complex.**  The first arrow `f_*F ⟶ a_*(F|_U)` — the direct
image along `f` of the unit at `τ`, followed by the comparison `τ_* ⋙ f_* ≅ a_*` — followed by the
second arrow `a_*(F|_U) ⟶ b_*(F|_R)` attached to `h : R ⟶ U` is the first arrow attached to `ρ`, so
the composite does not depend on which factorization of `b` through `a` built the second arrow.

With `R = U ×_X U` and `t, s : R ⟶ U` its two projections, this is what makes the source's
difference `t^* - s^*` vanish on the image of `f_*F`; see
`AlgebraicGeometry.Space.modulePushforwardPresentationFork`.

It is `AlgebraicGeometry.Space.modulePushforwardPresentationTail` followed by
`AlgebraicGeometry.Space.modulePullbackUnitApp_comp` under the direct image along `f`. -/
theorem modulePushforwardPresentationComplex (f : X ⟶ Y) (τ : U ⟶ X) (h : R ⟶ U) {ρ : R ⟶ X}
    (hρ : h ≫ τ = ρ) {a : U ⟶ Y} (ha : τ ≫ f = a) {b : R ⟶ Y} (hb : h ≫ a = b) (hb' : ρ ≫ f = b)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).map (modulePullbackUnitApp B S hS τ F) ≫
          (modulePushforwardTriangle B S hS ha).hom.app ((modulePullback B S hS τ).obj F)) ≫
        ((modulePushforward B S hS a).map
              (modulePullbackUnitApp B S hS h ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hb).hom.app
              ((modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F))) ≫
          (modulePushforward B S hS b).map
            (modulePullbackTriangleInvApp B S hS τ h hρ F) =
      (modulePushforward B S hS f).map (modulePullbackUnitApp B S hS ρ F) ≫
        (modulePushforwardTriangle B S hS hb').hom.app ((modulePullback B S hS ρ).obj F) := by
  rw [Category.assoc, modulePushforwardPresentationTail B S hS f τ h hρ ha hb hb' F,
    ← Category.assoc, ← (modulePushforward B S hS f).map_comp,
    modulePullbackUnitApp_comp B S hS τ h hρ F]

/-- **The fork condition of Stacks 03M8.**  For a chart `τ : U ⟶ X` and two morphisms
`t, s : R ⟶ U` with `t ≫ τ = s ≫ τ = ρ` — in Stacks 03M8, `R = U ×_X U` with its two projections —
the two parallel arrows `a_*(F|_U) ⟶ b_*(F|_R)` attached to `t` and to `s` agree after the first
arrow `f_*F ⟶ a_*(F|_U)`:

`f_*F → a_*(F|_U) ⇉ b_*(F|_R)`

is a fork.  Equivalently the source's difference `t^* - s^*` vanishes on the image of `f_*F`,
which is the "complex" half of the source's exactness assertion — the half that needs neither
surjectivity of `τ` nor the cartesian square `R = U ×_X U`.

Both parallel arrows have the same source and the same target, because `ρ` and `b` are single
named morphisms, so this is an equality of morphisms of `𝒪_Y`-modules with no transport in it;
compare `AlgebraicGeometry.Space.modulePullbackPresentationComplex_eq`, which needs one.  Both
composites are the first arrow attached to `ρ`, by
`AlgebraicGeometry.Space.modulePushforwardPresentationComplex`. -/
theorem modulePushforwardPresentationFork (f : X ⟶ Y) (τ : U ⟶ X) (t s : R ⟶ U) {ρ : R ⟶ X}
    (hρt : t ≫ τ = ρ) (hρs : s ≫ τ = ρ) {a : U ⟶ Y} (ha : τ ≫ f = a) {b : R ⟶ Y}
    (hbt : t ≫ a = b) (hbs : s ≫ a = b) (hb' : ρ ≫ f = b)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).map (modulePullbackUnitApp B S hS τ F) ≫
          (modulePushforwardTriangle B S hS ha).hom.app ((modulePullback B S hS τ).obj F)) ≫
        ((modulePushforward B S hS a).map
              (modulePullbackUnitApp B S hS t ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hbt).hom.app
              ((modulePullback B S hS t).obj ((modulePullback B S hS τ).obj F))) ≫
          (modulePushforward B S hS b).map
            (modulePullbackTriangleInvApp B S hS τ t hρt F) =
      ((modulePushforward B S hS f).map (modulePullbackUnitApp B S hS τ F) ≫
            (modulePushforwardTriangle B S hS ha).hom.app ((modulePullback B S hS τ).obj F)) ≫
          ((modulePushforward B S hS a).map
                (modulePullbackUnitApp B S hS s ((modulePullback B S hS τ).obj F)) ≫
              (modulePushforwardTriangle B S hS hbs).hom.app
                ((modulePullback B S hS s).obj ((modulePullback B S hS τ).obj F))) ≫
            (modulePushforward B S hS b).map
              (modulePullbackTriangleInvApp B S hS τ s hρs F) :=
  (modulePushforwardPresentationComplex B S hS f τ t hρt ha hbt hb' F).trans
    (modulePushforwardPresentationComplex B S hS f τ s hρs ha hbs hb' F).symm

end AlgebraicGeometry.Space

end
