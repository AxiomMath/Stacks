module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePresentationForkTransports
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardPresentationTriangle

/-!
# The clauses the transport of Stacks 03M8 to a general morphism consumes

In the notation of Stacks 03M8 — `f : X ⟶ Y`, a chart `τ : U ⟶ X`, two morphisms
`t, s : R ⟶ U` with `t ≫ τ = s ≫ τ = ρ`, and `a = τ ≫ f`, `b = ρ ≫ f` — the sequence
`0 → f_*F → a_*(F|_U) → b_*(F|_R)` is, by
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationTriangle.lean`, the direct
image along `f` of the corresponding sequence for the identity of `X`, conjugated by the two
comparisons `τ_* ⋙ f_* ≅ a_*` and `ρ_* ⋙ f_* ≅ b_*` of Stacks 03LU.  Since `f_*` is a right
adjoint it preserves limits, so a limiting fork for the identity of `X` should carry over.

This file collects the clauses that the transport
`CategoryTheory.Limits.isLimitForkOfMap` consumes at those data, each in the spelling the
transport's declared type asks for, and the preservation instance it needs, named.  The
transport itself does *not* land: see "What is not done", which records the measurement.

## Main definitions

* `CategoryTheory.Limits.isLimitForkMapComp` is
  `CategoryTheory.Limits.isLimitForkOfMap` with the first arrow of the transported fork written
  out as `P.map e₀ ≫ γ.hom` instead of pinned down by an equation.  A consumer whose first
  arrow is literally that composite then has nothing to substitute away.
* `AlgebraicGeometry.Space.preservesLimit_parallelPair_modulePushforward`: the direct image of
  `𝒪`-modules preserves the limit of a parallel pair, as a declaration of its own rather than a
  term synthesized at the point of use.

## Main results

* `AlgebraicGeometry.Space.modulePullbackUnitApp_fork`: **the fork condition for the identity
  of `X`.**  The unit at `τ` followed by the second arrow `τ_*(F|_U) ⟶ ρ_*(F|_R)` attached to
  `t` agrees with the same for `s`, both composites being the unit at `ρ` by
  `AlgebraicGeometry.Space.modulePullbackUnitApp_comp`.  This is the commutation that the fork
  of the geometric input of Stacks 03M8 is stated at, and it needs neither surjectivity of `τ`
  nor the cartesian square `R = U ×_X U`.
* `AlgebraicGeometry.Space.modulePushforwardPresentationTailApp` and
  `AlgebraicGeometry.Space.modulePushforwardPresentationForkApp` are
  `AlgebraicGeometry.Space.modulePushforwardPresentationTail` and
  `AlgebraicGeometry.Space.modulePushforwardPresentationFork` with the two comparisons that play
  the role of the transport's isomorphisms written as
  `AlgebraicGeometry.Space.modulePushforwardTriangleApp`, which is the spelling whose declared
  type is the uncomposed one.

## Implementation notes

The comparisons are passed to the transport as isomorphisms `P.obj M ≅ M'`, so they have to be
read at a module, where
`AlgebraicGeometry.Space.modulePushforwardTriangleApp` has the uncomposed declared type; but the
clauses `ht`, `hs` and the fork condition mention their `hom`, and
`(modulePushforwardTriangleApp B S hS hk N).hom` is *not syntactically*
`(modulePushforwardTriangle B S hS hk).hom.app N`, only definitionally so.  Reconciling the two
is affordable in a declaration of its own — that is what the two restatements below are — and
the measurement in "What is not done" shows it is not affordable as part of the transport.

Nothing here raises a compiler limit or disables a linter.

## What is not done

**The transport does not land**, and the obstruction is the *kernel's* budget, not the
elaborator's.  Instantiating `CategoryTheory.Limits.isLimitForkOfMap` at the direct image along
`f`, with the fork for the identity of `X` as a hypothesis, the comparisons read by
`AlgebraicGeometry.Space.modulePushforwardTriangleApp`, the clauses `ht` and `hs` supplied by
`AlgebraicGeometry.Space.modulePushforwardPresentationTail` and the commutation by
`AlgebraicGeometry.Space.modulePushforwardPresentationFork`, elaborates and then reports

`error: (kernel) deterministic timeout`

The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationTriangle.lean` record that
this happens with the fork condition inlined and with it taken as a hypothesis, and with the
`he` clause inlined as `Eq.refl` and lifted into a declaration of its own; naming the
preservation instance, from whose synthesized term the lifted proof comes, does not help
either.  With
`AlgebraicGeometry.Space.preservesLimit_parallelPair_modulePushforward` named and supplied, the
instantiation still reports `(kernel) deterministic timeout`, three times — once for the
declaration and once for each of two lifted auxiliary proofs.

Two further observations, which locate the cost in the *statement* and not in the instance:

* routing the instantiation through `CategoryTheory.Limits.isLimitForkMapComp` below, so that
  the `he` clause disappears and the first arrow of the fork is written out rather than
  unified, reduces the three kernel timeouts to **one**;
* restating the clauses in the `AlgebraicGeometry.Space.modulePushforwardTriangleApp` spelling,
  so that every argument matches the declared type syntactically — which is what the two
  restatements below are for, and each of them compiles in its own declaration — does *not*
  remove that last one: it reports two.

So the remaining obstruction is the kernel's reduction of the fork's type at these categories of
sheaves of modules, and raising a limit is not available in this repository.

**The transport is not the only route, and the conclusion it is for is proved.**  The
geometric input — that a *surjective* étale chart `τ` and the cartesian
square `R = U ×_X U` make the fork `F → τ_*(F|_U) ⇉ ρ_*(F|_R)` a limit — is available: the
limiting fork is proved, for an arbitrary morphism `f : X ⟶ Y`
and hence also for `f = 𝟙 X`, as
`AlgebraicGeometry.Space.nonempty_isLimitForkModuleChartDirectImage`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationExactSequence.lean:406`), at
exactly those two hypotheses, and the exactness it yields carries `@[stacks 03M8]` as
`AlgebraicGeometry.Space.exact_moduleChartDirectImage` (line 451 of that file).  The route taken
there is not the transport along `f_*` but a reflection: the fork is proved for sheaves of
*sets* and reflected back to modules by
`Stacks.Sheaves.RingedToposModules.isLimitForkOfIsLimitForkModuleSheaf`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ModuleSheafForkReflection.lean:158`), so the
kernel is never presented with the cone over sheaves of modules that the observations above are
about.  Whether `SheafOfModules.nonempty_isLimit_fork_of_sections`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePresentationForkTransports.lean:34`) would do it
as well is not known.

What separates that statement from `AlgebraicGeometry.Space.modulePullbackUnitApp_fork` below is
spelling rather than mathematics: there the chart is an object of the small étale site of `X` and
the two arrows are named `AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow` and
`AlgebraicGeometry.Space.moduleChartDirectImageParallelArrow`, whereas here the chart is a
morphism `τ : U ⟶ X` of algebraic spaces and the arrows are written out as composites of the
unit with the comparisons of Stacks 03LU.  Nothing in this file assumes the limit statement and
nothing here proves it.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v v₂ u u₂

/-- **Transport of a limiting fork along a limit-preserving functor and two isomorphisms**, with
the first arrow of the transported fork written out.

This is `CategoryTheory.Limits.isLimitForkOfMap` with its clause `he : e = P.map e₀ ≫ γ.hom`
removed and `e` replaced by that composite throughout.  A consumer whose first arrow is literally
`P.map e₀ ≫ γ.hom` has then nothing to substitute away, which matters: at the direct images of
`𝒪`-modules of Stacks 03LU the substitution costs three kernel timeouts rather than one; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationTransport.lean`. -/
noncomputable def isLimitForkMapComp {C : Type u} {D : Type u₂} [Category.{v} C]
    [Category.{v₂} D] (P : C ⥤ D) {A M N : C} {e₀ : A ⟶ M} {t₀ s₀ : M ⟶ N}
    (h₀ : e₀ ≫ t₀ = e₀ ≫ s₀) [PreservesLimit (parallelPair t₀ s₀) P]
    (hl : IsLimit (Fork.ofι e₀ h₀)) {M' N' : D} (γ : P.obj M ≅ M') (δ : P.obj N ≅ N')
    {t s : M' ⟶ N'} (ht : γ.hom ≫ t = P.map t₀ ≫ δ.hom)
    (hs : γ.hom ≫ s = P.map s₀ ≫ δ.hom)
    (h : (P.map e₀ ≫ γ.hom) ≫ t = (P.map e₀ ≫ γ.hom) ≫ s) :
    IsLimit (Fork.ofι (P.map e₀ ≫ γ.hom) h) :=
  isLimitForkOfMap P h₀ hl γ δ rfl ht hs h

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U X Y : AlgebraicSpaces B S hS}

/-! ### The preservation instance, named -/

/-- The direct image of `𝒪`-modules along a morphism of algebraic spaces preserves the limit of
a parallel pair, because it is a right adjoint by
`AlgebraicGeometry.Space.modulePullbackAdjunction`.

It is recorded as a declaration of its own, rather than left to instance search at the point of
use, because the kernel's budget is per declaration and the term search synthesizes is where a
lifted auxiliary proof of a consumer comes from.  That does not in fact remove the kernel
timeout of the transport; see this file's "What is not done". -/
instance preservesLimit_parallelPair_modulePushforward (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2} (t s : M ⟶ N) :
    PreservesLimit (parallelPair t s) (modulePushforward B S hS f) :=
  ((modulePullbackAdjunction B S hS f).rightAdjoint_preservesLimits.preservesLimitsOfShape
    (J := WalkingParallelPair)).preservesLimit

/-! ### The fork condition for the identity of `X` -/

/-- **The fork condition of Stacks 03M8 for the identity of `X`.**  For a chart `τ : U ⟶ X` and
two morphisms `t, s : R ⟶ U` with `t ≫ τ = s ≫ τ = ρ` — in Stacks 03M8, `R = U ×_X U` with its
two projections — the unit `F ⟶ τ_*(F|_U)` of Stacks 03LU followed by the second arrow
`τ_*(F|_U) ⟶ ρ_*(F|_R)` attached to `t` agrees with the same composite for `s`:

`F → τ_*(F|_U) ⇉ ρ_*(F|_R)`

is a fork in `Mod(𝒪_X)`.

Both composites are the unit at `ρ`, by
`AlgebraicGeometry.Space.modulePullbackUnitApp_comp`, so this needs neither surjectivity of `τ`
nor the cartesian square `R = U ×_X U`; it is the commutation that the geometric input of
Stacks 03M8 — that this fork is a *limit* — is stated at.  It is the case `f = 𝟙 X` of
`AlgebraicGeometry.Space.modulePushforwardPresentationFork`, with the composites `τ ≫ 𝟙` and
`ρ ≫ 𝟙` not written. -/
theorem modulePullbackUnitApp_fork (τ : U ⟶ X) (t s : R ⟶ U) {ρ : R ⟶ X}
    (hρt : t ≫ τ = ρ) (hρs : s ≫ τ = ρ) (F : Modules.{u, u} B S hS X.1 X.2) :
    modulePullbackUnitApp B S hS τ F ≫
        ((modulePushforward B S hS τ).map
              (modulePullbackUnitApp B S hS t ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hρt).hom.app
                ((modulePullback B S hS t).obj ((modulePullback B S hS τ).obj F)) ≫
              (modulePushforward B S hS ρ).map
                (modulePullbackTriangleInvApp B S hS τ t hρt F)) =
      modulePullbackUnitApp B S hS τ F ≫
        ((modulePushforward B S hS τ).map
              (modulePullbackUnitApp B S hS s ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hρs).hom.app
                ((modulePullback B S hS s).obj ((modulePullback B S hS τ).obj F)) ≫
              (modulePushforward B S hS ρ).map
                (modulePullbackTriangleInvApp B S hS τ s hρs F)) :=
  (modulePullbackUnitApp_comp B S hS τ t hρt F).trans
    (modulePullbackUnitApp_comp B S hS τ s hρs F).symm

/-! ### The clauses in the spelling the transport asks for -/

/-- `AlgebraicGeometry.Space.modulePushforwardPresentationTail` with the two comparisons of
direct images read by `AlgebraicGeometry.Space.modulePushforwardTriangleApp`, whose declared type
is the uncomposed one and which is therefore the spelling a transport typing its isomorphism
arguments as `P.obj M ≅ M'` produces.

The two spellings of each comparison are definitionally equal; this reconciles them in a
declaration of its own, which is what makes the reconciliation affordable at all. -/
theorem modulePushforwardPresentationTailApp (f : X ⟶ Y) (τ : U ⟶ X) (h : R ⟶ U) {ρ : R ⟶ X}
    (hρ : h ≫ τ = ρ) {a : U ⟶ Y} (ha : τ ≫ f = a) {b : R ⟶ Y} (hb : h ≫ a = b)
    (hb' : ρ ≫ f = b) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardTriangleApp B S hS ha ((modulePullback B S hS τ).obj F)).hom ≫
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
        (modulePushforwardTriangleApp B S hS hb' ((modulePullback B S hS ρ).obj F)).hom :=
  modulePushforwardPresentationTail B S hS f τ h hρ ha hb hb' F

/-- `AlgebraicGeometry.Space.modulePushforwardPresentationFork` with the comparison
`τ_* ⋙ f_* ≅ a_*` read by `AlgebraicGeometry.Space.modulePushforwardTriangleApp`, which is the
spelling the first arrow of a transported fork carries. -/
theorem modulePushforwardPresentationForkApp (f : X ⟶ Y) (τ : U ⟶ X) (t s : R ⟶ U) {ρ : R ⟶ X}
    (hρt : t ≫ τ = ρ) (hρs : s ≫ τ = ρ) {a : U ⟶ Y} (ha : τ ≫ f = a) {b : R ⟶ Y}
    (hbt : t ≫ a = b) (hbs : s ≫ a = b) (hb' : ρ ≫ f = b)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).map (modulePullbackUnitApp B S hS τ F) ≫
          (modulePushforwardTriangleApp B S hS ha
            ((modulePullback B S hS τ).obj F)).hom) ≫
        ((modulePushforward B S hS a).map
              (modulePullbackUnitApp B S hS t ((modulePullback B S hS τ).obj F)) ≫
            (modulePushforwardTriangle B S hS hbt).hom.app
              ((modulePullback B S hS t).obj ((modulePullback B S hS τ).obj F))) ≫
          (modulePushforward B S hS b).map
            (modulePullbackTriangleInvApp B S hS τ t hρt F) =
      ((modulePushforward B S hS f).map (modulePullbackUnitApp B S hS τ F) ≫
            (modulePushforwardTriangleApp B S hS ha
              ((modulePullback B S hS τ).obj F)).hom) ≫
          ((modulePushforward B S hS a).map
                (modulePullbackUnitApp B S hS s ((modulePullback B S hS τ).obj F)) ≫
              (modulePushforwardTriangle B S hS hbs).hom.app
                ((modulePullback B S hS s).obj ((modulePullback B S hS τ).obj F))) ≫
            (modulePushforward B S hS b).map
              (modulePullbackTriangleInvApp B S hS τ s hρs F) :=
  modulePushforwardPresentationFork B S hS f τ t s hρt hρs ha hbt hbs hb' F

end AlgebraicGeometry.Space

end
