module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.MayerVietorisTriangle
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Boundedness of the coherator

Let `X` be a quasi-compact and quasi-separated scheme and let `DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` be a
coherator of `X`, i.e. a right adjoint of the inclusion `ι : D_QCoh(𝒪_X) ⥤ D(𝒪_X)`
([Stacks, Tag 0CR0]). This file proves the boundedness property of [Stacks, Tag 0CSA]: there is
an integer `N` depending only on `X` such that for every `K` in `D(𝒪_X)` and all integers `a`,
`b`, if `H^i(U, K) = 0` for every affine open `U ⊆ X` and every `i ∉ [a, b]`, then the cohomology
sheaves of `DQ_X(K)` vanish outside `[a, b + N]`.

The order of the quantifiers is the content of the tag: the integer `N` is chosen *before* `K`,
`a` and `b`, so it depends on `X` (and on the coherator, which is unique up to isomorphism) and
on nothing else.

## Main definitions

* `Stacks.Duality.Coherator.derivedSectionsLocallySmall` — `RΓ(U, -) : D(𝒪_X) ⥤ D(Γ(X, U))`, the
  unbounded derived sections over an open `U`, whose cohomology objects are the `H^i(U, -)` of
  the tag.
* `Stacks.Duality.Coherator.AffineAmplitudeIn` — the hypothesis of the tag: `H^i(U, K) = 0` for
  every affine open `U` of `X` and every `i ∉ [a, b]`.
* `Stacks.Duality.Coherator.IsMayerVietorisApex` — the property of an object of `D(𝒪_X)` of
  sitting in a Mayer–Vietoris triangle for a pair of opens `U`, `V` and an object `K`; it is the
  shape in which [Stacks, Tag 08BV] is used below.
* `Stacks.Duality.Coherator.HasCoheratorBoundAt` — the boundedness property of the tag localized
  at an open `W` of `X`, i.e. for `DQ_X(Rj_{W,*}(K|_W))` in place of `DQ_X(K)`. This is the
  predicate the induction of [Stacks, Tag 08DR] runs on.

## Main results

* `Stacks.Duality.Coherator.isGE_isLE_coherator_of_isMayerVietorisApex` — the amplitude estimate
  along a Mayer–Vietoris triangle: if the coherator of the three terms
  `Rj_{U,*}(K|_U)`, `Rj_{V,*}(K|_V)`, `Rj_{U ∩ V,*}(K|_{U ∩ V})` lives in `[a, c]`, then the
  coherator of an apex of the triangle lives in `[a, c + 1]`.
* `Stacks.Duality.Coherator.hasCoheratorBoundAt_sup` — the inductive step: the localized bound
  at `U` and at `V` and at `U ⊓ V` gives the localized bound at `U ⊔ V`.
* `Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj` — the induction of
  [Stacks, Tag 0CSA], with its three inputs as arguments. The tag itself, with all three
  supplied, is `Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs` in
  `StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/UnconditionalBoundedness.lean`.

## The shape of the proof

The source's proof is an induction over the quasi-compact opens of `X`
([Stacks, Tag 08DR]) with the affine opens as the base case and a Mayer–Vietoris triangle
([Stacks, Tag 0CR2], built from [Stacks, Tag 08BV]) controlling the amplitude at each step. That
is the proof carried out here, with one reorganisation: the source's inductive statement is about
the coherator `DQ_W` of the *open subscheme* `W`, and relating `DQ_W` for the various `W` would
require transporting coherators along the isomorphisms `(j_{U ⊔ V}^{-1}U).toScheme ≅ U.toScheme`.
Instead the inductive statement here, `HasCoheratorBoundAt`, is about `DQ_X` applied to
`Rj_{W,*}(K|_W)`, an object of `D(𝒪_X)`; by the commutation of the coherator with derived direct
image ([Stacks, Tag 0CR1], `Stacks.Duality.coheratorDerivedPushforwardIso`) the two statements
agree, and the reorganised one mentions only the single coherator `DQ_X`. Every step of the
induction then takes place in `D(𝒪_X)` and in `D_QCoh(𝒪_X)`, and the only inputs are the
Mayer–Vietoris triangles and exactness of `DQ_X`.

The amplitude estimate itself is the long exact cohomology sequence of the triangle, in the
`IsGE`/`IsLE` packaging: in a distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧`, if `B` and `C` live in
`[a, c]` then `A` lives in `[a, c + 1]`, because `H^i(A)` sits between `H^{i-1}(C)` and `H^i(B)`.
The loss of one degree at the top is harmless: the conclusion of the tag is the mere existence of
`N`, and the finitely many steps of the induction at a fixed open each cost one degree.

## The three inputs of the induction, and where they are proved

`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj` below takes three inputs of the
source's proof as arguments, and
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/UnconditionalBoundedness.lean` supplies
all three and carries [Stacks, Tag 0CSA]. None of the three mentions a bound on `DQ_X`: the
conclusion is an estimate on the cohomology sheaves of `DQ_X(K)` for all `K`, `a`, `b` at once
with a single `N`, and the inputs are two statements about restriction and derived direct image
in `D(𝒪_X)` with no coherator in them at all, together with the base case of the induction at the
affine opens.

*The coherator, [Stacks, Tag 0CR0].* `DQ_X` and the adjunction `ι ⊣ DQ_X` are arguments, with the
adjunction required to be triangulated — that is the "exact functor `DQ_X`" the source uses, and
"let `DQ_X` be as in Lemma 0CR0" is how the source's statement begins. A coherator exists for
every quasi-compact quasi-separated scheme, with no further hypothesis, by
`Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_quasiCoherentι`, and
`Stacks.Duality.Coherator.exists_coherator_isGE_isLE_obj_of_qcqs` is the tag with that coherator
produced rather than given. Taking the coherator as an argument is also what [Stacks, Tag 0CR2]
does in `Stacks.Duality.Coherator.mayerVietorisTriangle`.

*The Mayer–Vietoris triangles, [Stacks, Tag 08BV].* `hmv` is the triangle attached to a pair of
opens `U`, `V` of `X` inside their union, and `hmvTop` the triangle attached to a pair of opens
covering `X`. They are
`Stacks.Duality.Coherator.isMayerVietorisApex_restrictPushforward_sup` and
`Stacks.Duality.Coherator.isMayerVietorisApex_self`, in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/UnboundedMayerVietoris.lean`, which
imports this module — which is why they are arguments here and not instances of the
construction. Only the *existence* of the three maps is asked for, not their identification with
the canonical ones, which makes the argument as weak as the estimate allows.

*The affine base case, [Stacks, Tag 06Z0] and [Stacks, Tag 08D9] with [Stacks, Tag 08D5].*
`haffine` is `HasCoheratorBoundAt` at the affine opens of `X`. On an affine `W` the source takes
`N(W) = 0` because `DQ_W` is there computed by forming the quasi-coherent complex attached to
`RΓ(W, K)` (Tags 06Z0 and 08D9), and `Rj_{W,*}` then costs the finitely many degrees of
Tag 08D5. That is `Stacks.Duality.Coherator.hasCoheratorBoundAt_of_isAffineOpen`, carried out on
`Spec Γ(X, U)` rather than on the affine open subscheme `U`, where the coherator is derived
global sections followed by sheafification.

## Implementation notes

`Stacks.Duality.Coherator.derivedSectionsLocallySmall` is a fourth `RΓ(U, -)` in this
repository, and it exists for the model, not for the mathematics.
`Stacks.Cohomology.derivedSections` is the
bounded below one, `AlgebraicGeometry.derivedSectionsUnbounded` and
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen` are unbounded, and all three are
elaborated under a file-level `attribute [local instance] HasDerivedCategory.standard`, so their
source is `D(𝒪_X)` at the standard model. The vocabulary of [Stacks, Tag 0CR2] — in particular
`Stacks.Duality.Coherator.restrictPushforward` and `Stacks.Duality.Coherator.quasiCoherentι` —
resolves `HasDerivedCategory` at definition time to the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and a statement at one model says nothing
about the other. The functor here is the same total right derived functor of
`Stacks.Cohomology.sectionsFunctor`, built at the locally small model so that it can appear in
the same statement as the coherator; it exists there because `𝒪_X`-modules are Grothendieck
abelian, which is `AlgebraicGeometry.Scheme.Modules.hasRightDerivedFunctor`.

## References

* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 0CR2](https://stacks.math.columbia.edu/tag/0CR2)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Duality.Coherator

variable (X : Scheme.{u})

/-! ### Derived sections over an open, at the locally small model -/

/-- Sections over an open `U` of `X`, read on the homotopy category of cochain complexes of
`𝒪_X`-modules. This is the functor whose right derived functor is
`Stacks.Duality.Coherator.derivedSectionsLocallySmall`. -/
abbrev homotopySectionsLocallySmall (U : X.Opens) :
    HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  (Stacks.Cohomology.sectionsFunctor X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Sections over an open have an unbounded right derived functor: `𝒪_X`-modules form a
Grothendieck abelian category, so every cochain complex of them has a K-injective resolution. -/
instance homotopySectionsLocallySmall_hasRightDerivedFunctor (U : X.Opens) :
    (homotopySectionsLocallySmall X U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Scheme.Modules.hasRightDerivedFunctor X _

/-- **`RΓ(U, -)`, the unbounded derived sections over an open `U` of `X`**, as a functor
`D(𝒪_X) ⥤ D(Γ(X, U))` at the locally small model of both derived categories. Its cohomology
objects are the cohomology modules `H^i(U, -)` appearing in the hypothesis of
[Stacks, Tag 0CSA]. -/
abbrev derivedSectionsLocallySmall (U : X.Opens) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  (homotopySectionsLocallySmall X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The canonical comparison from termwise sections over `U` to their unbounded right derived
functor. It is the unit exhibiting `Stacks.Duality.Coherator.derivedSectionsLocallySmall` as a
right derived functor, which is the universal property that pins that functor down. -/
abbrev derivedSectionsLocallySmallUnit (U : X.Opens) :
    homotopySectionsLocallySmall X U ⟶ DerivedCategory.Qh ⋙ derivedSectionsLocallySmall X U :=
  (homotopySectionsLocallySmall X U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- `Stacks.Duality.Coherator.derivedSectionsLocallySmall` together with its unit is a right
derived functor of sections over `U`. -/
instance derivedSectionsLocallySmall_isRightDerivedFunctor (U : X.Opens) :
    (derivedSectionsLocallySmall X U).IsRightDerivedFunctor (derivedSectionsLocallySmallUnit X U)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  inferInstance

/-! ### The hypothesis and the localized conclusion of the tag -/

/-- **The hypothesis of [Stacks, Tag 0CSA]**: the hypercohomology of `K` over every affine open
of `X` is concentrated in the interval `[a, b]`, i.e. `H^i(U, K) = 0` for every affine open
`U ⊆ X` and every `i ∉ [a, b]`. -/
def AffineAmplitudeIn (a b : ℤ) (K : DerivedCategory X.Modules) : Prop :=
  ∀ (U : X.affineOpens) (i : ℤ), i < a ∨ b < i →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) i).obj
      ((derivedSectionsLocallySmall X U.1).obj K))

/-- `A` is a **Mayer–Vietoris apex** for the pair of opens `U`, `V` of `X` and the object `K` of
`D(𝒪_X)`: there is a distinguished triangle

`A ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶ A⟦1⟧`

in `D(𝒪_X)`. For `A = Rj_{U ∪ V,*}(K|_{U ∪ V})` and for `A = K` when `U ∪ V = X` these are the
Mayer–Vietoris triangles of [Stacks, Tag 08BV]. Only existence of the three maps is asked for;
the amplitude estimate of
`Stacks.Duality.Coherator.isGE_isLE_coherator_of_isMayerVietorisApex` uses nothing else. -/
def IsMayerVietorisApex (U V : X.Opens) (K A : DerivedCategory X.Modules) : Prop :=
  ∃ (f : A ⟶ restrictPushforward U K ⊞ restrictPushforward V K)
    (g : restrictPushforward U K ⊞ restrictPushforward V K ⟶ restrictPushforward (U ⊓ V) K)
    (h : restrictPushforward (U ⊓ V) K ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang (DerivedCategory X.Modules)

variable (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)

/-- **The boundedness property of [Stacks, Tag 0CSA], localized at an open `W` of `X`**: there is
an integer `N`, depending on `W` but not on `K`, `a` or `b`, such that the cohomology sheaves of
`DQ_X(Rj_{W,*}(K|_W))` vanish outside `[a, b + N]` whenever the hypercohomology of `K` over the
affine opens of `X` is concentrated in `[a, b]`.

For `W = ⊤` this is the conclusion of the tag up to the identification `Rj_{⊤,*}(K|_⊤) ≅ K`, and
by the commutation of the coherator with derived direct image ([Stacks, Tag 0CR1]) it agrees with
the source's inductive statement, which is about the coherator `DQ_W` of the open subscheme `W`:
`Rj_{W,*}DQ_W(K|_W) ≅ DQ_X(Rj_{W,*}(K|_W))`. -/
def HasCoheratorBoundAt (W : X.Opens) : Prop :=
  ∃ N : ℤ, ∀ (a b : ℤ) (K : DerivedCategory X.Modules), AffineAmplitudeIn X a b K →
    ((quasiCoherentι X).obj (DQ.obj (restrictPushforward W K))).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj (restrictPushforward W K))).IsLE (b + N)

/-! ### The amplitude estimate along a Mayer–Vietoris triangle -/

section Estimate

/-- Monotonicity of `DerivedCategory.IsLE` in the bound, with the hypothesis as an argument
rather than an instance. -/
private theorem isLE_mono {X : Scheme.{u}} {Y : DerivedCategory X.Modules} {p q : ℤ}
    (h : Y.IsLE p) (hpq : p ≤ q) : Y.IsLE q :=
  have := h
  DerivedCategory.TStructure.t.isLE_of_le _ p q hpq

/-- Weakening the upper bound of an amplitude estimate `IsGE a ∧ IsLE p`. -/
private theorem isGE_and_isLE_mono {X : Scheme.{u}} {Y : DerivedCategory X.Modules} {a p q : ℤ}
    (h : Y.IsGE a ∧ Y.IsLE p) (hpq : p ≤ q) : Y.IsGE a ∧ Y.IsLE q :=
  ⟨h.1, isLE_mono h.2 hpq⟩

variable {X} {DQ} (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]

include adj

/-- The composite `ι ∘ DQ_X : D(𝒪_X) ⥤ D(𝒪_X)` is exact: `DQ_X` is exact because the adjunction
`ι ⊣ DQ_X` is triangulated, and `ι` is exact because `D_QCoh(𝒪_X)` is a triangulated
subcategory. -/
theorem isTriangulated_comp_quasiCoherentι : (DQ ⋙ quasiCoherentι X).IsTriangulated :=
  have : DQ.IsTriangulated := inferInstance
  inferInstance

/-- Exactness of `ι ∘ DQ_X` turns a biproduct in `D(𝒪_X)` into a distinguished triangle, which
gives the amplitude of `ι(DQ_X(A ⊕ B))` from the amplitudes of `ι(DQ_X A)` and `ι(DQ_X B)`. -/
theorem isGE_isLE_coherator_biprod (A B : DerivedCategory X.Modules) (a c : ℤ)
    (hA : ((quasiCoherentι X).obj (DQ.obj A)).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj A)).IsLE c)
    (hB : ((quasiCoherentι X).obj (DQ.obj B)).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj B)).IsLE c) :
    ((quasiCoherentι X).obj (DQ.obj (A ⊞ B))).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj (A ⊞ B))).IsLE c := by
  have : (DQ ⋙ quasiCoherentι X).IsTriangulated := isTriangulated_comp_quasiCoherentι adj
  have hT := (DQ ⋙ quasiCoherentι X).map_distinguished _
    (binaryBiproductTriangle_distinguished A B)
  obtain ⟨hA₁, hA₂⟩ := hA
  obtain ⟨hB₁, hB₂⟩ := hB
  exact ⟨DerivedCategory.TStructure.t.isGE₂ _ hT a hA₁ hB₁,
    DerivedCategory.TStructure.t.isLE₂ _ hT c hA₂ hB₂⟩

/-- **The amplitude estimate along a Mayer–Vietoris triangle.** Let `U`, `V` be opens of `X`, let
`K` be an object of `D(𝒪_X)` and let `A` be a Mayer–Vietoris apex for them. If the coherator of
each of the three terms `Rj_{U,*}(K|_U)`, `Rj_{V,*}(K|_V)`, `Rj_{U ∩ V,*}(K|_{U ∩ V})` has its
cohomology sheaves in `[a, c]`, then those of `DQ_X(A)` lie in `[a, c + 1]`.

This is the long exact cohomology sequence of the triangle: the exact functor `ι ∘ DQ_X` carries
the apex triangle to a distinguished triangle, whose inverse rotation has `ι(DQ_X A)` as its
middle term, and the middle term of a distinguished triangle inherits bounds from the two outer
ones. The outer term `ι(DQ_X(Rj_{U ∩ V,*}(K|_{U ∩ V})))⟦-1⟧` is what costs the extra degree at
the top. -/
theorem isGE_isLE_coherator_of_isMayerVietorisApex {U V : X.Opens}
    {K A : DerivedCategory X.Modules} (hA : IsMayerVietorisApex X U V K A) (a c : ℤ)
    (hU : ((quasiCoherentι X).obj (DQ.obj (restrictPushforward U K))).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj (restrictPushforward U K))).IsLE c)
    (hV : ((quasiCoherentι X).obj (DQ.obj (restrictPushforward V K))).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj (restrictPushforward V K))).IsLE c)
    (hUV : ((quasiCoherentι X).obj (DQ.obj (restrictPushforward (U ⊓ V) K))).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj (restrictPushforward (U ⊓ V) K))).IsLE c) :
    ((quasiCoherentι X).obj (DQ.obj A)).IsGE a ∧
      ((quasiCoherentι X).obj (DQ.obj A)).IsLE (c + 1) := by
  have : (DQ ⋙ quasiCoherentι X).IsTriangulated := isTriangulated_comp_quasiCoherentι adj
  obtain ⟨f, g, h, hT⟩ := hA
  obtain ⟨hmid₁, hmid₂⟩ := isGE_isLE_coherator_biprod adj _ _ a c hU hV
  obtain ⟨hthd₁, hthd₂⟩ := hUV
  have hdist := inv_rot_of_distTriang _
    ((DQ ⋙ quasiCoherentι X).map_distinguished _ hT)
  refine ⟨DerivedCategory.TStructure.t.isGE₂ _ hdist a ?_ hmid₁,
    DerivedCategory.TStructure.t.isLE₂ _ hdist (c + 1) ?_ (isLE_mono hmid₂ (by omega))⟩
  · have := hthd₁
    have := DerivedCategory.TStructure.t.isGE_shift
      ((quasiCoherentι X).obj (DQ.obj (restrictPushforward (U ⊓ V) K))) a (-1) (a + 1) (by omega)
    exact DerivedCategory.TStructure.t.isGE_of_ge
      (((quasiCoherentι X).obj (DQ.obj (restrictPushforward (U ⊓ V) K)))⟦(-1 : ℤ)⟧) a (a + 1)
      (by omega)
  · have := hthd₂
    exact DerivedCategory.TStructure.t.isLE_shift
      ((quasiCoherentι X).obj (DQ.obj (restrictPushforward (U ⊓ V) K))) c (-1) (c + 1) (by omega)

end Estimate

/-! ### The induction of Stacks 08DR -/

/-- **The inductive step of [Stacks, Tag 0CSA].** If the localized bound holds at a quasi-compact
open `U`, at an open `V` and at `U ⊓ V`, then it holds at `U ⊔ V`.

Take for `N(U ⊔ V)` the largest of the three constants, increased by one; the Mayer–Vietoris
triangle for `U`, `V` with apex `Rj_{U ⊔ V,*}(K|_{U ⊔ V})` then gives the bound by
`Stacks.Duality.Coherator.isGE_isLE_coherator_of_isMayerVietorisApex`. -/
theorem hasCoheratorBoundAt_sup {X : Scheme.{u}}
    {DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]
    (hmv : ∀ (U V : X.Opens) (K : DerivedCategory X.Modules),
      IsMayerVietorisApex X U V K (restrictPushforward (U ⊔ V) K))
    (U V : X.Opens) (hU : HasCoheratorBoundAt X DQ U) (hV : HasCoheratorBoundAt X DQ V)
    (hUV : HasCoheratorBoundAt X DQ (U ⊓ V)) :
    HasCoheratorBoundAt X DQ (U ⊔ V) := by
  obtain ⟨N₁, h₁⟩ := hU
  obtain ⟨N₂, h₂⟩ := hV
  obtain ⟨N₃, h₃⟩ := hUV
  refine ⟨max N₁ (max N₂ N₃) + 1, fun a b K hK => ?_⟩
  have key := isGE_isLE_coherator_of_isMayerVietorisApex adj (hmv U V K) a
    (b + max N₁ (max N₂ N₃))
    (isGE_and_isLE_mono (h₁ a b K hK) (by omega))
    (isGE_and_isLE_mono (h₂ a b K hK) (by omega))
    (isGE_and_isLE_mono (h₃ a b K hK) (by omega))
  exact isGE_and_isLE_mono key (by omega)

/-- **[Stacks, Tag 0CSA].** Let `X` be a quasi-compact and quasi-separated scheme and let
`DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` be a coherator of `X`, with the adjunction `ι ⊣ DQ_X`
triangulated. Then there is an integer `N`, depending only on `X` and on `DQ_X` and in particular
not on `K`, `a` or `b`, such that for every object `K` of `D(𝒪_X)` and all integers `a`, `b`, if
`H^i(U, K) = 0` for every affine open `U ⊆ X` and every `i ∉ [a, b]`, then the cohomology sheaves
`H^i(DQ_X(K))` vanish for `i ∉ [a, b + N]`.

The proof is the source's: the induction principle for the quasi-compact opens of `X`
([Stacks, Tag 08DR], `Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open`)
applied to the localized statement `Stacks.Duality.Coherator.HasCoheratorBoundAt`, with
`Stacks.Duality.Coherator.hasCoheratorBoundAt_sup` for the inductive step, followed by one more
Mayer–Vietoris triangle — the one for the cover of `X` by `⊤` and `⊤` — to pass from the bound at
`⊤` to the bound on `DQ_X(K)` itself.

The arguments `hmv` and `hmvTop` are the Mayer–Vietoris triangles of [Stacks, Tag 08BV] and
`haffine` is the affine base case, which the source gets from [Stacks, Tag 06Z0] and
[Stacks, Tag 08D9] together with [Stacks, Tag 08D5]. All three are proved in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/UnconditionalBoundedness.lean`, which
feeds them in and carries the tag, as
`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs`; they are arguments here
because the Mayer–Vietoris triangles are constructed in a module that imports this one, and
because a consumer in the Grothendieck existence development passes its own. -/
theorem exists_isGE_isLE_coherator_obj (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
    (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]
    (hmv : ∀ (U V : X.Opens) (K : DerivedCategory X.Modules),
      IsMayerVietorisApex X U V K (restrictPushforward (U ⊔ V) K))
    (hmvTop : ∀ (U V : X.Opens), U ⊔ V = ⊤ → ∀ K : DerivedCategory X.Modules,
      IsMayerVietorisApex X U V K K)
    (haffine : ∀ U : X.affineOpens, HasCoheratorBoundAt X DQ (U : X.Opens)) :
    ∃ N : ℤ, ∀ (a b : ℤ) (K : DerivedCategory X.Modules), AffineAmplitudeIn X a b K →
      ((quasiCoherentι X).obj (DQ.obj K)).IsGE a ∧
        ((quasiCoherentι X).obj (DQ.obj K)).IsLE (b + N) := by
  have htop : HasCoheratorBoundAt X DQ ⊤ :=
    Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
      (HasCoheratorBoundAt X DQ) (fun U hU => haffine ⟨U, hU⟩)
      (fun U V _ _ hU hV hUV => hasCoheratorBoundAt_sup adj hmv U V hU hV hUV) ⊤
      (by simpa using isCompact_univ (X := X))
  obtain ⟨N, hN⟩ := htop
  refine ⟨N + 1, fun a b K hK => ?_⟩
  have hinf : (⊤ : X.Opens) ⊓ (⊤ : X.Opens) = ⊤ := inf_idem _
  have key := isGE_isLE_coherator_of_isMayerVietorisApex adj
    (hmvTop ⊤ ⊤ (by simp) K) a (b + N) (hN a b K hK) (hN a b K hK) (by
      rw [hinf]; exact hN a b K hK)
  exact isGE_and_isLE_mono key (by omega)

end Stacks.Duality.Coherator

end
