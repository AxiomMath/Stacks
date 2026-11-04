module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal lifting criterion for smoothness

The scheme-theoretic infinitesimal lifting criterion for smoothness over a locally
Noetherian base.

Let `f : X → S` be a morphism of schemes and `x ∈ X` a point. Assume that `S` is
locally Noetherian and that `f` is locally of finite type. Then the following
four conditions are equivalent:

1. `f` is smooth at `x` (i.e. smooth on some open neighbourhood of `x`).
2. The infinitesimal lifting property holds against every square-zero surjection
   of local rings.
3. The same lifting property restricted to small extensions.
4. The same lifting property restricted to residually trivial small extensions
   (those for which the induced residue-field map is an isomorphism).

## Definitions used

A ring map `φ : B' → B` between local rings is a *square-zero surjection* if `φ`
is surjective and `(ker φ)^2 = 0`.

A ring map `φ : B' → B` is a *small extension* if `B'`, `B` are local Artinian
rings, `φ` is surjective, and `ker φ` has length `1` as a `B'`-module
(equivalently `ker φ` is a simple `B'`-module, which forces `(ker φ)^2 = 0`).

## Notation / setup for the lifting diagram

A ring surjection `φ : B' → B` induces a closed immersion of affine schemes
`i = Spec(φ) : Spec B → Spec B'`.

A *solid commutative diagram* consists of morphisms `α : Spec B → X` and
`β : Spec B' → S` with `f ∘ α = β ∘ i` and with `α` sending the closed point of
`Spec B` (the maximal ideal `𝔪 ⊆ B`) to `x`.

A *dotted arrow making the diagram commute* is a morphism `γ : Spec B' → X` with
`γ ∘ i = α` and `f ∘ γ = β`.

Pictorially (Stacks horizontal arrows point to the left):

  X ←α─ Spec B
  │f      │i
  S ←β─ Spec B'   with the dotted lift γ : Spec B' → X.

In Lean's left-to-right composition `g ∘ h = h ≫ g`, the compatibility
`f ∘ α = β ∘ i` reads `α ≫ f = Spec.map φ ≫ β`, and the lift conditions
`γ ∘ i = α`, `f ∘ γ = β` read `Spec.map φ ≫ γ = α` and `γ ≫ f = β`.
-/

@[expose] public section
-- needed file-wide: `stalkClosedPointTo_specMap`,
-- `formallySmooth_stalkMap_liftsAgainstSquareZero`, `otilde_smul_mP_eq_zero`, `otilde_smul`,
-- `defect_link`, `residueFieldMap_isIso_of_surjective`,
-- `LiftsAgainstResiduallyTrivialSmallExtension.algLiftsResTrivSmall_of_lifts` and
-- `formallySmooth_stalkMap_smoothAt` all rewrite (or synthesize instances) through the
-- `CommRingCat`/`Scheme.presheaf.stalk`/`TrivSqZeroExt` bundling, which only unfolds with defeq
-- transparency relaxed.
-- (`backward.isDefEq.respectTransparency.types` was also set here and was not needed.)
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace InfinitesimalLifting

universe u

/-- A ring map `φ : B' → B` between commutative rings is a *square-zero
surjection of local rings* if `B'` and `B` are local rings, `φ` is surjective,
and the kernel `ker φ` has square zero. -/
def IsSquareZeroSurjection {B' B : CommRingCat.{u}} (φ : B' ⟶ B) : Prop :=
  IsLocalRing B' ∧ IsLocalRing B ∧
  Function.Surjective φ.hom ∧
  (RingHom.ker φ.hom) ^ 2 = ⊥

/-- A ring map `φ : B' → B` is a *small extension* (Stacks tag 02HS) if `B'` and
`B` are local Artinian rings, `φ` is surjective, and the kernel `ker φ` has
length `1` as a `B'`-module. -/
@[stacks 02HS, sga "7 VI 1.4" "more general"]
def IsSmallExtension {B' B : CommRingCat.{u}} (φ : B' ⟶ B) : Prop :=
  IsLocalRing B' ∧ IsLocalRing B ∧ IsArtinianRing B' ∧ IsArtinianRing B ∧
  Function.Surjective φ.hom ∧
  Module.length B' (RingHom.ker φ.hom) = 1

/- Smoothness on a neighbourhood of `x`, not a lifting property at `x`: the three
`LiftsAgainst…` conditions below quantify over square-zero surjections of local rings and
over morphisms out of their spectra, and this condition meets them only through the file's
equivalence theorem, not by unfolding. -/

/-- `f` is *smooth at* `x` if there is an open neighbourhood `U` of `x` such that
the restricted morphism `f|_U : U → S` is smooth. -/
@[ega "IV 17.3.7",
  sga "1 II 1.1",
  sga "3 VIB 1.3",
  sga "3 XI 1.2",
  sga "3 XI 1.5",
  sga "4 XI 2.1",
  sga "7 VI 4.5"]
def SmoothAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ Smooth (f.resLE ⊤ U le_top)

/-- A smooth morphism is smooth at every point of its source: the whole source serves as the
open neighbourhood, on which the restricted morphism is `f` itself up to the isomorphisms
identifying a scheme with its top open. -/
theorem smoothAt_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X) :
    SmoothAt f x := by
  refine ⟨⊤, trivial, ?_⟩
  have he : f.resLE ⊤ ⊤ le_top = (⊤ : X.Opens).ι ≫ f ≫ S.topIso.inv := by
    apply (cancel_mono (⊤ : S.Opens).ι).1
    simp only [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
    exact Scheme.Hom.resLE_comp_ι f le_top
  rw [he]
  infer_instance

/-- The infinitesimal lifting property against square-zero surjections of local
rings (condition 2). For every square-zero surjection `φ : B' → B` of local
rings and every solid commutative diagram with `α` sending the closed point of
`Spec B` to `x`, there is a dotted lift `γ`. -/
@[ega "IV 17.14.1" "partial", sga "3 XI 1.7" "special case"]
def LiftsAgainstSquareZero {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∀ ⦃B' B : CommRingCat.{u}⦄ (φ : B' ⟶ B), IsSquareZeroSurjection φ →
    ∀ [IsLocalRing B] (α : Spec B ⟶ X) (β : Spec B' ⟶ S),
      α ≫ f = Spec.map φ ≫ β →
      α.base (IsLocalRing.closedPoint B) = x →
      ∃ γ : Spec B' ⟶ X, Spec.map φ ≫ γ = α ∧ γ ≫ f = β

/-- The infinitesimal lifting property against small extensions (condition 3). -/
@[sga "3 XI 1.8" "special case", sga "4 XIII 1.5"]
def LiftsAgainstSmallExtension {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∀ ⦃B' B : CommRingCat.{u}⦄ (φ : B' ⟶ B), IsSmallExtension φ →
    ∀ [IsLocalRing B] (α : Spec B ⟶ X) (β : Spec B' ⟶ S),
      α ≫ f = Spec.map φ ≫ β →
      α.base (IsLocalRing.closedPoint B) = x →
      ∃ γ : Spec B' ⟶ X, Spec.map φ ≫ γ = α ∧ γ ≫ f = β

/-- The infinitesimal lifting property against residually trivial small
extensions (condition 4): small extensions for which, in addition, `α` induces
an isomorphism of residue fields `κ(x) ≅ κ(𝔪)` at the closed point. -/
def LiftsAgainstResiduallyTrivialSmallExtension
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∀ ⦃B' B : CommRingCat.{u}⦄ (φ : B' ⟶ B), IsSmallExtension φ →
    ∀ [IsLocalRing B] (α : Spec B ⟶ X) (β : Spec B' ⟶ S),
      α ≫ f = Spec.map φ ≫ β →
      α.base (IsLocalRing.closedPoint B) = x →
      IsIso (α.residueFieldMap (IsLocalRing.closedPoint B)) →
      ∃ γ : Spec B' ⟶ X, Spec.map φ ≫ γ = α ∧ γ ≫ f = β

/-- A small extension is in particular a square-zero surjection of local rings.
The key point is that a length-one (hence simple) kernel ideal `I` satisfies
`I^2 = 0`: `I ⊆ 𝔪` and `𝔪 I` is a proper submodule of the simple module `I`,
forcing `𝔪 I = 0`, so `I^2 ⊆ 𝔪 I = 0`. -/
theorem IsSmallExtension.isSquareZeroSurjection
    {B' B : CommRingCat.{u}} (φ : B' ⟶ B) (hφ : IsSmallExtension φ) :
    IsSquareZeroSurjection φ := by
  obtain ⟨hB', hB, hArtB', hArtB, hsurj, hlen⟩ := hφ
  refine ⟨hB', hB, hsurj, ?_⟩
  set I : Ideal B' := RingHom.ker φ.hom with hI
  have hsimple : IsSimpleModule B' I := Module.length_eq_one_iff.mp hlen
  -- `I` is nonzero
  have hInz : I ≠ ⊥ := by
    intro h
    have : Module.length B' I = 0 := by rw [h]; simp
    rw [hlen] at this; exact one_ne_zero this
  -- `I ⊆ 𝔪`
  have : Nontrivial B := hB.toNontrivial
  have hIne : I ≠ ⊤ := by
    intro h
    -- `I = ⊤ = ker φ` and `φ` surjective forces `B` to be trivial
    have hone : (1 : B) = 0 := by
      obtain ⟨b', hb'⟩ := hsurj (1 : B)
      have : b' ∈ I := by rw [h]; trivial
      rw [hI, RingHom.mem_ker] at this
      rw [← hb', this]
    exact one_ne_zero hone
  have hImax : I ≤ IsLocalRing.maximalIdeal B' :=
    IsLocalRing.le_maximalIdeal hIne
  -- `𝔪 * I = ⊥` by Nakayama / simplicity
  have hmul : IsLocalRing.maximalIdeal B' * I = ⊥ := by
    -- Work inside the simple module `↥I`. The submodule `𝔪 • ⊤` is either ⊥ or ⊤;
    -- Nakayama rules out ⊤ (as `↥I ≠ 0`), so it is ⊥. Pushing forward via the
    -- inclusion `I.subtype` gives `𝔪 • I = ⊥`, i.e. `𝔪 * I = ⊥`.
    have hfg : (⊤ : Submodule B' I).FG := by
      have : IsNoetherianRing B' := inferInstance
      have : Module.Finite B' I :=
        Module.Finite.of_injective I.subtype I.subtype_injective
      exact Module.Finite.fg_top
    set N : Submodule B' I := IsLocalRing.maximalIdeal B' • (⊤ : Submodule B' I) with hN
    have hNtop : N ≠ ⊤ := by
      intro h
      have hle : (⊤ : Submodule B' I) ≤ Ring.jacobson B' • (⊤ : Submodule B' I) := by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal B']
        rw [← hN, h]
      have : (⊤ : Submodule B' I) = ⊥ := hfg.eq_bot_of_le_jacobson_smul hle
      rw [Submodule.eq_bot_iff] at this
      -- `↥I` nonzero since `I ≠ ⊥`
      obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hInz
      have := this ⟨y, hyI⟩ trivial
      exact hy0 (congrArg Subtype.val this)
    have hNbot : N = ⊥ := (eq_bot_or_eq_top N).resolve_right hNtop
    -- push forward through `I.subtype`
    have hpush : Submodule.map I.subtype N = IsLocalRing.maximalIdeal B' * I := by
      rw [hN, Submodule.map_smul'']
      congr 1
      simp [Submodule.map_top, Submodule.range_subtype]
    rw [hNbot, Submodule.map_bot] at hpush
    exact hpush.symm
  -- conclude
  have : I ^ 2 ≤ IsLocalRing.maximalIdeal B' * I := by
    rw [pow_two]
    exact Ideal.mul_mono_left hImax
  rw [hmul] at this
  exact le_bot_iff.mp this

/-! ## Reduction to the local ring at `x`

Both substantive directions of Stacks 02HX are proved by passing to the local
rings at `x` and `f(x)`.  Write `A := 𝒪_{X,x}` (the stalk `X.presheaf.stalk x`)
and `R := 𝒪_{S,f(x)}`; the morphism `f` induces, at the level of stalks, a
**local** ring homomorphism `R ⟶ A` (`f.stalkMap x`, local by
`AlgebraicGeometry.Scheme.Hom.isLocalHom_stalkMap`).  We regard `A` as an
`R`-algebra via this map.

The bridge that converts the scheme-theoretic lifting diagrams into ring-theoretic
ones is `AlgebraicGeometry.SpecToEquivOfLocalRing X B`, the natural bijection
`(Spec B ⟶ X) ≃ Σ y, {ψ : 𝒪_{X,y} ⟶ B // IsLocalHom ψ}` valid for any local ring
`B`.  Under it:
* `α : Spec B ⟶ X` with `α.base (closedPoint B) = x` corresponds to a local hom
  `a : A = 𝒪_{X,x} ⟶ B`;
* `β : Spec B' ⟶ S` corresponds to a local hom `b : R = 𝒪_{S,f(x)} ⟶ B'` (after
  identifying `β.base (closedPoint B') = f(x)`, which follows from the
  compatibility `α ≫ f = Spec.map φ ≫ β` together with `α (closedPoint) = x`);
* the compatibility `α ≫ f = Spec.map φ ≫ β` becomes the commuting square of
  ring maps `a ∘ (f.stalkMap x) = φ ∘ b` (i.e. `a` is an `R`-algebra map to `B`
  and reduces, mod `ker φ`, the `R`-algebra map `b`);
* a lift `γ : Spec B' ⟶ X` with `Spec.map φ ≫ γ = α`, `γ ≫ f = β` corresponds to
  a local `R`-algebra hom `c : A ⟶ B'` with `φ ∘ c = a`.

Thus the scheme lifting problem against `φ : B' ⟶ B` is *equivalent* to the
algebraic lifting problem for the `R`-algebra `A` against the surjection
`φ : B' ⟶ B`. -/

/-- Formal smoothness of the stalk map at a point `y` of an open `U` of the source is unchanged
by restricting `f` to `U`. -/
private theorem formallySmooth_resLE_stalkMap_iff {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (y : U) : ((f.resLE ⊤ U le_top).stalkMap y).hom.FormallySmooth ↔
      (f.stalkMap (U.ι.base y)).hom.FormallySmooth :=
  RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (f.resLEStalkMap (U := ⊤) (V := U) le_top y)

/-- If `f` is smooth at `x`, then
the stalk map `𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` is formally smooth as an `R`-algebra.

*Informal proof.*  Smoothness of `f` at `x` means `f` is a smooth morphism on an
open neighbourhood `U ∋ x`.  By `AlgebraicGeometry.smooth_iff` /
`Scheme.Hom.smooth_appLE`, choosing affine opens `Spec R₀ ⊆ S` around `f(x)` and
`Spec A₀ ⊆ U` around `x` with `A₀` mapping into `R₀`, the ring map
`R₀ ⟶ A₀` is `Smooth`, hence `FormallySmooth` (`RingHom.Smooth.formallySmooth`).
Formal smoothness is preserved under the localizations `R₀ ⟶ 𝒪_{S,f(x)} = R` and
`A₀ ⟶ 𝒪_{X,x} = A` at the points `f(x)`, `x` (localization is formally smooth,
`Algebra.FormallySmooth.localization_base` / `…of_isLocalization`, and formal
smoothness composes, `Algebra.FormallySmooth.comp`), so the induced local map
`R ⟶ A` is formally smooth. -/
@[ega "0 19.0.2" "IV",
  ega "0 22.6.4" "special case",
  ega "IV 17.5.1" "a ⇒ c",
  ega "IV 17.5.3" "partial",
  ega "IV 6.8.6" "a ⇒ c′"]
theorem SmoothAt.formallySmooth_stalkMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (hf : SmoothAt f x) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  -- direction 1→2: a smooth morphism's stalk map is formally smooth.
  obtain ⟨U, hxU, hsmooth⟩ := hf
  set g := f.resLE ⊤ U le_top with hg
  -- the point `x` as an element of `U`
  set y : (U : X.Opens) := ⟨x, hxU⟩ with hy
  -- `g.stalkMap y` is formally smooth since `g` is smooth (smooth locus is ⊤)
  have hmem : y ∈ g.smoothLocus := by
    rw [g.smoothLocus_eq_top]; trivial
  have hsm : (g.stalkMap y).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp hmem
  -- transfer to `f.stalkMap x` via the `resLEStalkMap` arrow isomorphism
  have key : (f.stalkMap (↑y)).hom.FormallySmooth :=
    (formallySmooth_resLE_stalkMap_iff f U y).mp hsm
  -- `↑y = x` definitionally, so this matches the algebra structure in the goal
  exact RingHom.FormallySmooth.toAlgebra key

/-- Formal smoothness of the
stalk map upgrades the scheme-theoretic lifting against square-zero surjections.

*Informal proof.*  Fix a square-zero surjection `φ : B' ⟶ B` of local rings and
a solid diagram `α : Spec B ⟶ X`, `β : Spec B' ⟶ S` with
`α ≫ f = Spec.map φ ≫ β` and `α.base (closedPoint B) = x`.  Translate through
`SpecToEquivOfLocalRing` (see the section comment above):
`α ↦ a : A ⟶ B` (local), `β ↦ b : R ⟶ B'` (local), with the compatibility
becoming `a` being the reduction mod `I := ker φ` of an `R`-algebra structure;
concretely `a : A ⟶ B = B'/I` is an `R`-algebra hom where `A` is the `R`-algebra
`𝒪_{X,x}` and `R ⟶ B'` is `b`.  As `I² = 0`, formal smoothness of `A/R`
(`Algebra.FormallySmooth.comp_surjective`, equivalently `…exists_lift` with `I`
nilpotent) yields an `R`-algebra lift `c : A ⟶ B'` with `φ ∘ c = a`.  Since `A`,
`B'` are local and `c` is a local hom (it lifts the local hom `a`; the kernel is
nilpotent so units lift to units), `SpecToEquivOfLocalRing.symm (x, c)` produces
`γ : Spec B' ⟶ X`.  Unwinding the bijection (`SpecToEquivOfLocalRing_symm_apply`,
`…_eq_iff`) gives `Spec.map φ ≫ γ = α` and `γ ≫ f = β`, i.e. the required lift. -/
/- Auxiliary: the closed-point stalk map of `Spec.map φ` for a local ring hom `φ`,
identified (after transporting the base point) with `φ` precomposed with the
stalk-to-ring isomorphism. -/
theorem stalkClosedPointTo_specMap {B' B : CommRingCat.{u}} (φ : B' ⟶ B)
    [IsLocalRing B] [IsLocalRing B'] [IsLocalHom φ.hom] :
    Scheme.stalkClosedPointTo (Spec.map φ) =
      (Spec B').presheaf.stalkSpecializes
          (Specializes.of_eq (AlgebraicGeometry.Spec_closedPoint (f := φ)).symm) ≫
        (AlgebraicGeometry.stalkClosedPointIso B').hom ≫ φ := by
  have hgerm :
      IsIso ((Spec B').presheaf.germ ⊤
        ((Spec.map φ).base (IsLocalRing.closedPoint B)) trivial) := by
    have he : (Spec.map φ).base (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint B' :=
      AlgebraicGeometry.Spec_closedPoint (f := φ)
    rw [he, ← AlgebraicGeometry.ΓSpecIso_hom_stalkClosedPointIso_inv]
    infer_instance
  apply (CategoryTheory.cancel_epi ((Spec B').presheaf.germ ⊤ ((Spec.map φ).base
      (IsLocalRing.closedPoint B)) trivial)).mp
  rw [AlgebraicGeometry.Scheme.germ_stalkClosedPointTo_Spec]
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  rw [AlgebraicGeometry.germ_stalkClosedPointIso_hom_assoc]

/-- Auxiliary: translating the scheme compatibility square `α ≫ f = Spec.map φ ≫ β`
through `SpecToEquivOfLocalRing` yields the commuting square of local ring maps
`(f.stalkMap _) ≫ a = b ≫ φ`, where `a = stalkClosedPointTo α` and `b` is
`stalkClosedPointTo β` transported to the stalk at `f(x)`. -/
theorem stalkMap_stalkClosedPointTo_comm {X S : Scheme.{u}} (f : X ⟶ S)
    {B' B : CommRingCat.{u}} (φ : B' ⟶ B)
    [IsLocalRing B] [IsLocalRing B'] [IsLocalHom φ.hom]
    (α : Spec B ⟶ X) (β : Spec B' ⟶ S)
    (hcomm : α ≫ f = Spec.map φ ≫ β)
    (hpt : β.base (IsLocalRing.closedPoint B') = f.base (α.base (IsLocalRing.closedPoint B))) :
    f.stalkMap (α.base (IsLocalRing.closedPoint B)) ≫ Scheme.stalkClosedPointTo α =
      (S.presheaf.stalkSpecializes (Specializes.of_eq hpt) ≫ Scheme.stalkClosedPointTo β) ≫ φ := by
  have key := congrArg (SpecToEquivOfLocalRing S B) hcomm
  rw [SpecToEquivOfLocalRing_eq_iff] at key
  obtain ⟨hfst, hsnd⟩ := key
  rw [SpecToEquivOfLocalRing_apply_snd_coe, SpecToEquivOfLocalRing_apply_snd_coe] at hsnd
  rw [Scheme.stalkClosedPointTo_comp α f, Scheme.stalkClosedPointTo_comp (Spec.map φ) β] at hsnd
  rw [hsnd, stalkClosedPointTo_specMap φ]
  rw [Scheme.stalkClosedPointTo]
  simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc β (IsLocalRing.closedPoint B')
      ((Spec.map φ).base (IsLocalRing.closedPoint B)) (Specializes.of_eq
          (AlgebraicGeometry.Spec_closedPoint (f := φ)).symm)]
  generalize_proofs p1 p2 p3
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp S.presheaf p2 p1]

/-- If the stalk map of `f` at `x` is formally smooth, then `f` lifts against every
square-zero surjection at `x`. -/
@[sga "3 III 2.5" "(a), special case", sga "3 IX 3.3" "special case"]
theorem formallySmooth_stalkMap_liftsAgainstSquareZero
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hfs : letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :
    LiftsAgainstSquareZero f x := by
  intro B' B φ hφ hlocB α β hcomm hclosed
  obtain ⟨hB', hB, hsurj, hsq⟩ := hφ
  have : Nontrivial B := hB.toNontrivial
  have hφloc : IsLocalHom φ.hom := Function.Surjective.isLocalHom φ.hom hsurj
  subst hclosed
  -- point identification: `β` sends the closed point to `f(x)`
  have hpt : β.base (IsLocalRing.closedPoint B') = f.base (α.base (IsLocalRing.closedPoint B)) := by
    have h1 := congrArg (fun g => g.base (IsLocalRing.closedPoint B)) hcomm
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
    rw [AlgebraicGeometry.Spec_closedPoint] at h1
    exact h1.symm
  -- the local homs `a : 𝒪_{X,x} ⟶ B` and `b : 𝒪_{S,f(x)} ⟶ B'`
  set a : X.presheaf.stalk (α.base (IsLocalRing.closedPoint B)) ⟶ B :=
    Scheme.stalkClosedPointTo α with ha
  set b : S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B))) ⟶ B' :=
    S.presheaf.stalkSpecializes (Specializes.of_eq hpt) ≫ Scheme.stalkClosedPointTo β with hb
  -- the compatibility square of ring maps
  have hcompat : f.stalkMap (α.base (IsLocalRing.closedPoint B)) ≫ a = b ≫ φ :=
    stalkMap_stalkClosedPointTo_comm f φ α β hcomm hpt
  -- give `A`, `B'`, `B` their `R`-algebra structures (`R = 𝒪_{S,f(x)}`)
  let algRA : Algebra (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B))))
      (X.presheaf.stalk (α.base (IsLocalRing.closedPoint B))) :=
    (f.stalkMap (α.base (IsLocalRing.closedPoint B))).hom.toAlgebra
  let algRB' : Algebra (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))) B' :=
    b.hom.toAlgebra
  let algRB : Algebra (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))) B :=
    (b ≫ φ).hom.toAlgebra
  -- `A` is formally smooth over `R` (the hypothesis, at the point `α(closedPoint)`)
  have : Algebra.FormallySmooth (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B))))
      (X.presheaf.stalk (α.base (IsLocalRing.closedPoint B))) := hfs
  -- promote `a` and `φ` to `R`-algebra homs
  let aA : (X.presheaf.stalk (α.base (IsLocalRing.closedPoint B))) →ₐ[
      S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))] B :=
    { a.hom with
      commutes' := fun r => by
        show a.hom ((f.stalkMap (α.base (IsLocalRing.closedPoint B))).hom r) = (b ≫ φ).hom r
        simpa using congrArg (fun (g : _ ⟶ B) => g.hom r) hcompat }
  let φA : (B' : CommRingCat) →ₐ[
      S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))] B :=
    { φ.hom with
      commutes' := fun _ => rfl }
  -- `ker φ` is nilpotent (square zero)
  have hnil : IsNilpotent (RingHom.ker (φA : B' →+* B)) := ⟨2, hsq⟩
  have hsurjA : Function.Surjective (φA : B' →ₐ[_] B) := hsurj
  -- formal smoothness yields the lift `c : A →ₐ[R] B'` with `φ ∘ c = a`
  let c := Algebra.FormallySmooth.liftOfSurjective aA φA hsurjA hnil
  have hcφ : (φA.comp c) = aA := Algebra.FormallySmooth.comp_liftOfSurjective aA φA hsurjA hnil
  let cR : (X.presheaf.stalk (α.base (IsLocalRing.closedPoint B))) ⟶ B' := CommRingCat.ofHom
      c.toRingHom
  -- `c ≫ φ = a` and `f.stalkMap ≫ c = b`
  have hcφ' : cR ≫ φ = a := by
    apply CommRingCat.hom_ext
    ext y
    exact AlgHom.congr_fun hcφ y
  have hbc : f.stalkMap (α.base (IsLocalRing.closedPoint B)) ≫ cR = b := by
    apply CommRingCat.hom_ext
    ext r
    have hc := c.commutes r
    rwa [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra] at hc
  -- the lift `γ := Spec.map c ≫ fromSpecStalk x`
  refine ⟨Spec.map cR ≫ X.fromSpecStalk (α.base (IsLocalRing.closedPoint B)), ?_, ?_⟩
  · -- `Spec.map φ ≫ γ = α`
    rw [← Category.assoc, ← Spec.map_comp, hcφ', ha]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk α
  · -- `γ ≫ f = β`
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f, ← Spec.map_comp_assoc, hbc,
      hb, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk β

/- **Helper (direction 4 ⇒ 1), algebraic core: the affine criterion, tag 02HT.**
If the residually-trivial small-extension lifting property holds at `x`, then the
stalk map `𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` is formally smooth as an `R`-algebra.

*Informal proof (Algebra Lemma 10.141.2 / Stacks 02HT, the substantive converse).*
Set `R := 𝒪_{S,f(x)}`, `A := 𝒪_{X,x}`, `k := κ(x) = A/𝔪_A` the residue field.
Because `f` is locally of finite type and `S` is locally Noetherian, `A` is a
finitely presented `R`-algebra (`R` Noetherian + finite type ⇒ finite
presentation, `Algebra.FiniteType.isNoetherianRing` and finite presentation over
Noetherian).  Choose a finite presentation, i.e. a surjection `π : P ⟶ A` from a
(localized) polynomial `R`-algebra `P` with `P` formally smooth and `Ω_{P/R}`
finite free, and `I := ker π` finitely generated.  By the local criterion
`Algebra.FormallySmooth.iff_injective_lTensor_residueField`, `A` is formally
smooth over `R` iff the cotangent-complex map
  `δ ⊗ k : (I/I²) ⊗_A k ⟶ (A ⊗_P Ω_{P/R}) ⊗_A k`
is injective.

The lifting hypothesis (4) furnishes exactly this injectivity.  Apply (4) to the
*residually trivial small extensions* `B' := P/(I·𝔪 + I_j) ⟶ B := P/(I + I_j)`
obtained by killing all but a one-dimensional piece of `I/𝔪I` (these are small
extensions with kernel a `k`-line on which `B` acts through `k`, hence residually
trivial), together with the tautological diagram `α : Spec B ⟶ X` induced by
`A ⟶ B` and `β` induced by `R ⟶ B'`.  A lift `γ`, translated back through
`SpecToEquivOfLocalRing` to a local `R`-algebra section `c : A ⟶ B'` of
`φ : B' ⟶ B`, splits the corresponding line in the conormal map; ranging over all
lines shows `δ ⊗ k` is injective.  (This is where Artin–Rees,
`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` / `Ideal.exists_pow_inf_eq_pow_smul`,
is used to pass from the Artinian quotients `P/(I+𝔪^n)` back to `A`, i.e. to see
that an element of `I/I²` killed at every finite level is zero.)  Injectivity of
`δ ⊗ k` then gives formal smoothness of `A/R`. -/
/- **Sub-lemma A (02HT, cotangent-vanishing core).** Under the residually-trivial
small-extension lifting hypothesis, the first cotangent cohomology of the stalk
algebra `A = 𝒪_{X,x}` over `R = 𝒪_{S,f(x)}` vanishes.

This is the substantive analytic kernel of tag 02HT: choose a finite presentation
`π : P ↠ A` (`A` is finitely presented over the Noetherian local `R` since `f` is
locally of finite type), and use the criterion
`Algebra.Extension.cotangentComplex_injective_iff` /
`Algebra.FormallySmooth.kerCotangentToTensor_injective_iff` to reduce
`Subsingleton (H1Cotangent R A)` to injectivity of the conormal map `δ : I/I² → A ⊗_P Ω_{P/R}`.
The lifting hypothesis `h`, applied to the residually-trivial small extensions
`P/(I·𝔪 + I_j) ↠ P/(I + I_j)` and translated back through
`SpecToEquivOfLocalRing` into local `R`-algebra sections, splits each line of the
conormal map; an Artin–Rees (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) descent
from the finite Artinian levels then gives injectivity, hence the vanishing. -/
/- **Analytic kernel of 02HT (per-level lifting + Artin–Rees), the conormal-injectivity
obligation.** With `R = 𝒪_{S,f(x)}`, `A = 𝒪_{X,x}` and the canonical presentation
`P := Algebra.Generators.self R A` (the tautological generators of `A` by itself),
the conormal / cotangent-complex map
`δ = P.toExtension.cotangentComplex : I/I² → Ω_{P/R} ⊗_P A` is injective.

*Proof outline (Stacks 02HT — NOT yet a single Mathlib lemma; this is the genuine
analytic heart that must be developed).*  Reduce to a finite presentation
`R[x₁,…,xₙ] ↠ A` (finite presentation since `f` is locally of finite type and `R`
is Noetherian, `Algebra.FinitePresentation.ker_fg_of_mvPolynomial`).  The conormal
module `I/I²` is then a finitely generated `A`-module.  Given `ξ̄ ∈ ker δ`, for each
`n` truncate to the local Artinian level `Aₙ := P/(I + 𝔪ⁿ)` and consider the
square-zero surjection `πₙ : P/(I² + 𝔪ⁿ) ↠ Aₙ`.  Filtering its kernel by length-one
residually-trivial steps and feeding each rung to the lifting hypothesis `h`
(translated through `SpecToEquivOfLocalRing` into local `R`-algebra sections of
`πₙ`) shows `ξ̄ ∈ 𝔪_A ⁿ · (I/I²)` for every `n`.  Krull's intersection theorem on
the Noetherian local ring `A` applied to the finitely generated module `I/I²`
(`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`, Stacks 00IP; resp.
`Ideal.exists_pow_inf_eq_pow_smul`, 00IN) then forces `ξ̄ = 0`, i.e. `δ` injective.

The per-level step — building the residually-trivial length-one square-zero
filtration of `ker πₙ` and matching it with `h`'s small-extension hypotheses — is
the substantive content and is itself the next decomposition target. -/
/- **Sub-lemma A′ (02HT analytic kernel, presentation-independent form).** Under
the residually-trivial small-extension lifting hypothesis, the first André–Quillen
cohomology `H¹(L_{A/R})` of the stalk algebra `A = 𝒪_{X,x}` over `R = 𝒪_{S,f(x)}`
vanishes (`Subsingleton (Algebra.H1Cotangent R A)`).

This is the genuine analytic heart of Stacks 02HT, stated for the
presentation-independent `Algebra.H1Cotangent` (`Algebra.equivH1Cotangent` shows
it does not depend on the choice of presentation, so we are free to compute it on a
FINITE presentation — crucially NOT on `Generators.self R A`, whose `Cotangent`
module is *not* finitely generated, so Krull/Artin–Rees does not apply there).

*Proof outline.*  Since `f` is locally of finite type and `S` is locally
Noetherian, `A` is a finitely presented `R`-algebra; pick a FINITE presentation
`P_fin : R[x₁,…,xₙ] ↠ A` with `I := ker` finitely generated, so
`Algebra.Extension.Cotangent.finite` makes `P_fin.Cotangent = I/I²` a finite
`A`-module.  Transfer the vanishing of `H¹` to `P_fin` via
`Algebra.Generators.equivH1Cotangent` / `Algebra.Generators.H1Cotangent.equiv`.
Given `ξ̄ ∈ H¹(P_fin) = ker(δ_fin)`, the residually-trivial small extensions
`P_fin/(I·𝔪 + I_j) ↠ P_fin/(I + I_j)` fed to `h` through `SpecToEquivOfLocalRing`
split each line of the conormal map, forcing `ξ̄ ∈ 𝔪_A^n · (I/I²)` for all `n`;
Krull intersection (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) on the *finite*
module `I/I²` over the Noetherian local `A` then forces `ξ̄ = 0`.
-/
/-- **Algebra-level residually-trivial small-extension lifting.** This is the
ring-theoretic shadow (under `SpecToEquivOfLocalRing`) of the scheme-level
hypothesis `LiftsAgainstResiduallyTrivialSmallExtension`: for every surjective
`R`-algebra map `φ : B' → B` between local Artinian `R`-algebras whose kernel is
square-zero of length `1` (a *small extension*), every **surjective** `R`-algebra
map `a : A → B` lifts along `φ` to an `R`-algebra map `c : A → B'`.

The surjectivity hypothesis on `a` is the faithful algebra-level mirror of the
*residual triviality* side condition in `LiftsAgainstResiduallyTrivialSmallExtension`
(`IsIso (α.residueFieldMap _)`): a surjective map of local rings is automatically
local and induces an isomorphism of residue fields, which is precisely what makes
the scheme lifting hypothesis applicable. Without it, `AlgLiftsResTrivSmall` would
be strictly stronger than what the scheme hypothesis provides: a non-local or
residually nontrivial `a` cannot be reached by the scheme diagram.  The downstream
consumer only ever feeds the canonical
truncation quotients `a : A → A/𝔪^{m+1}`, which are surjective, so no strength is
lost. -/
def AlgLiftsResTrivSmall (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [Algebra R B'] [Algebra R B]
    [IsLocalRing B'] [IsLocalRing B] [IsArtinianRing B'] [IsArtinianRing B]
    (φ : B' →ₐ[R] B), Function.Surjective φ →
    (RingHom.ker φ.toRingHom) ^ 2 = ⊥ →
    Module.length B' (RingHom.ker φ.toRingHom) = 1 →
    ∀ (a : A →ₐ[R] B), Function.Surjective a → ∃ c : A →ₐ[R] B', φ.comp c = a

/-!
### The obstruction calculus behind Stacks 02HT

The results in this section isolate the deformation-theoretic heart of Algebra Lemma 10.141.2
as self-contained ring theory, with no scheme machinery.

Let `A` be a local algebra of finite presentation over a Noetherian local ring `R` that lifts
against residually trivial small extensions, i.e. satisfies `AlgLiftsResTrivSmall R A`.  Then
`A` is formally smooth over `R`.  Fix a finite presentation `P = R[x₁,…,xₙ] ↠ A` with
`I = ker f`, which is finitely generated, and write `P := Algebra.Extension.ofSurjective f hf`,
so `P.Ring = MvPolynomial (Fin n) R` and `P.ker = I`.  By
`Algebra.Extension.subsingleton_h1Cotangent` it suffices to show that the conormal map
`d : I/I² → Ω_{P/R} ⊗_P A` is injective, equivalently that its base change to the residue
field `κ = κ(A)`,

```
    P.cotangentComplex.baseChange κ : κ ⊗_A (I/I²) → κ ⊗_A (A ⊗_P Ω_{P/R})
```

is injective, equivalently that `P.cotangentComplex` admits an `A`-linear retraction.

The argument is a contradiction.  The conormal module `N = I/I²` is a *finite* `A`-module, so
Krull's intersection theorem `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` detects a nonzero
kernel class `ξ` at a finite truncation level `n₀`: there is an `n₀` with `ξ ∉ 𝔪^{n₀}·N`.  A
length-one simple quotient `q : N ↠ V ≅ κ` with `q(ξ) ≠ 0` classifies a residually trivial
length-one square-zero small extension `B'_q ↠ A/𝔪^{n₀+1}` of local Artinian `R`-algebras,
along which the truncation `a : A → A/𝔪^{n₀+1}` lifts exactly when `q ∈ Im(dᵛ)`.  But every
`δ∘d` kills `ξ ∈ ker d` while `q(ξ) ≠ 0`, so no lift exists, contradicting the hypothesis.
Hence `ker d = 0`.  The identification of lifting with the cocycle lying in the image uses the
conormal–Kähler exact sequence `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`
and `Algebra.H1Cotangent.exact_δ_mapBaseChange`, together with formal smoothness of the
polynomial ring `P`.  Splitness over the local ring `A` is the André–Quillen expression of
formal smoothness, and the passage from the retraction to the κ-base-change injectivity is
`IsLocalRing.split_injective_iff_lTensor_residueField_injective`, which needs `P.Cotangent`
finite and `P.CotangentSpace` finite and free — both supplied by `hker` and the polynomial
presentation.

The statement actually proved in the substantive step is that *every* `A`-linear functional
`o : P.Cotangent → κ` on the conormal module factors through `d`, that is `o = δ ∘ₗ d` for
some `A`-linear `δ : P.CotangentSpace → κ`.  Its construction half builds, from `o`, the
classifying extension together with the data linking it back to `o`:

* lift `o` to `õ : I → κ` through `Ideal.Cotangent.lift`; then `õ` is `P`-linear and kills
  both `I²` and `𝔪·I`, the latter because `o` is `A`-linear into `κ`;
* fix `m ≥ 1` with `Ā_m := A/𝔪_A^{m+1}` Artinian local, by
  `isArtinianRing_iff_isNilpotent_maximalIdeal`, and let `P̄_m := P/𝔪^{m+1}` for
  `𝔪 = f⁻¹(𝔪_A)`, which is Artinian local and surjects onto `Ā_m`;
* build the *cocycle-twisted quotient* `B'_o := (P̄_m ⊕ κ)/K` with
  `K := ⟨(ḡ, −õ(g)) : g ∈ I⟩`, an ideal because `õ` is `P`-linear.  Its first projection
  `φ : B'_o ↠ Ā_m` has `ker φ =: J ≅ κ`, square-zero of length one and residually trivial,
  and the reference lift `q₀ : P → B'_o`, `q₀(h) := (h̄, 0) mod K`, satisfies
  `φ ∘ q₀ = a ∘ f` for the truncation `a`.

The bundle also carries the κ-isomorphism `θ : J ≃ₗ[R] κ`, the κ-coordinate of the chosen
`J`-representative, and the *defect link* `θ (q₀ g) = o([g])` for every `g ∈ ker f`, which
holds because `(ḡ, 0) ≡ (0, õ(g)) mod K` and `õ(g) = o([g])`.  The twisting is essential: for
the untwisted `TrivSqZeroExt κ κ` the defect of `q₀` on `I` is forced to be `0`, giving
`δ = 0 ≠ o`.  For the same reason `θ` and the defect link must be built alongside the ring
`B'_o` rather than afterwards — they depend on the concrete `K`, and for a degenerate bundle
such as `B' = B`, `φ = id`, `q₀ = a∘f` one has `q₀ g = 0` for `g ∈ ker f`, so
`θ (q₀ g) = 0 ≠ o([g])` whenever `o ≠ 0`.
-/

/-- **Artin–Rees corollary** (the non-degeneracy enabler for the S1 twisted-quotient construction).
Over a Noetherian ring, for ideals `𝔪`, `I`, there is `m ≥ 1` with `I ⊓ 𝔪^(m+1) ≤ 𝔪 • I`. Applied
with `𝔪 = 𝔪_P = (maximalIdeal A).comap f` and `I = ker f`, this guarantees that, in the truncated
ring `P̄_m = P/𝔪_P^{m+1}`, an element `i ∈ ker f` with `ī = 0` (i.e. `i ∈ I ⊓ 𝔪_P^{m+1}`) lies in
`𝔪_P • I ⊆ ker õ`, which is exactly the non-degeneracy `K ∩ inr(κ) = ⊥` for the cocycle-twisted
quotient. Crucially the bound depends only on `(P, 𝔪_P, I)`, not on `o` — one `m` works for all
`o`. -/
theorem artinRees_inf_pow_le_smul
    (R : Type u) [CommRing R] [IsNoetherianRing R] (𝔪 I : Ideal R) :
    ∃ m : ℕ, 1 ≤ m ∧ (I ⊓ 𝔪 ^ (m + 1)) ≤ 𝔪 • I := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔪 (I.restrictScalars R)
  refine ⟨k + 1, by omega, ?_⟩
  intro x hx
  have hx' : x ∈ 𝔪 ^ (k + 1 + 1) • (⊤ : Submodule R R) ⊓ I.restrictScalars R := by
    constructor
    · have hsm : 𝔪 ^ (k + 1 + 1) • (⊤ : Submodule R R) = (𝔪 ^ (k + 1 + 1)).restrictScalars R := by
        rw [Ideal.smul_top_eq_map]
        simp
      rw [hsm]
      simpa using hx.right
    · simpa using hx.left
  rw [hk (k + 1 + 1) (by omega)] at hx'
  have hsub : (𝔪 ^ (k + 1 + 1 - k)) • (𝔪 ^ k • (⊤ : Submodule R R) ⊓ I.restrictScalars R)
      ≤ 𝔪 • I :=
    calc (𝔪 ^ (k + 1 + 1 - k)) • (𝔪 ^ k • (⊤ : Submodule R R) ⊓ I.restrictScalars R)
        ≤ (𝔪 ^ (k + 1 + 1 - k)) • I.restrictScalars R := Submodule.smul_mono le_rfl inf_le_right
      _ ≤ 𝔪 • I := Submodule.smul_mono (Ideal.pow_le_self (by omega)) le_rfl
  exact hsub hx'

/-- In the cotangent module of `ofSurjective f hf`, the class of `p • j` is `f p • [j]`. -/
private theorem cotangent_of_toCotangent_smul {R A P : Type u} [CommRing R] [CommRing A]
    [CommRing P] [Algebra R A] [Algebra R P] (f : P →ₐ[R] A) (hf : Function.Surjective f) (p : P)
    (j : RingHom.ker f.toRingHom) :
    Algebra.Extension.Cotangent.of (P := Algebra.Extension.ofSurjective f hf)
        (Ideal.toCotangent (RingHom.ker f.toRingHom) (p • j))
      = f.toRingHom p • Algebra.Extension.Cotangent.of (P := Algebra.Extension.ofSurjective f hf)
          (Ideal.toCotangent (RingHom.ker f.toRingHom) j) := by
  rw [map_smul]
  have hinj : Function.Injective
      (Algebra.Extension.Cotangent.val (P := Algebra.Extension.ofSurjective f hf)) := by
    intro a b hab
    rw [← Algebra.Extension.Cotangent.of_val a, ← Algebra.Extension.Cotangent.of_val b, hab]
  apply hinj
  rw [Algebra.Extension.Cotangent.val_of,
    Algebra.Extension.Cotangent.val_smul''', Algebra.Extension.Cotangent.val_of,
    Algebra.algebraMap_self_apply]
  set q : P := (Algebra.Extension.ofSurjective f hf).σ (f.toRingHom p) with hq
  have hfq : f.toRingHom q = f.toRingHom p :=
    Algebra.Extension.algebraMap_σ (Algebra.Extension.ofSurjective f hf) (f.toRingHom p)
  have hdiff : p - q ∈ RingHom.ker f.toRingHom := by
    rw [RingHom.mem_ker, map_sub, hfq, sub_self]
  have hz := Ideal.Cotangent.smul_eq_zero_of_mem hdiff
    ((Ideal.toCotangent (RingHom.ker f.toRingHom)) j)
  rw [sub_smul, sub_eq_zero] at hz
  exact hz

/-! ### S1 cocycle-twisted quotient construction (formal sketch)

The construction is `B'_o = (TrivSqZeroExt P̄ κ)/K` (the `Module Pbarᵐᵒᵖ κ` and
`IsCentralScalar` friction is
tamed via `opToPbar`, a comm-ring `unop` ring hom).  The sub-lemmas below are the
RingTheory content (II)–(V) together with the defect link. -/
section S1Construct
namespace S1Construct

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
  (P : Type u) [CommRing P] [Algebra R P] [IsNoetherianRing P]
  (f : P →ₐ[R] A) (hf : Function.Surjective f)
  (m : ℕ)

/-- `𝔪_P = (maximalIdeal A).comap f`, the pullback maximal ideal of `P`. -/
noncomputable def mP : Ideal (P) :=
  (IsLocalRing.maximalIdeal A).comap f.toRingHom
/-- `P̄ = P / 𝔪_P^{m+1}`. -/
noncomputable abbrev Pbar : Type u :=
  P ⧸ (mP R A P f) ^ (m + 1)
/-- The descended map `P̄ → κ`, well defined because `𝔪_P^{m+1} ⊆ ker (residue ∘ f)`. -/
noncomputable def PbarToKappa : Pbar R A P f m →+* IsLocalRing.ResidueField A :=
  Ideal.Quotient.lift ((mP R A P f) ^ (m + 1))
    ((IsLocalRing.residue A).comp f.toRingHom) (fun p hp => by
      simp only [RingHom.comp_apply]
      rw [IsLocalRing.residue_eq_zero_iff]
      have hle : (mP R A P f) ^ (m + 1) ≤ mP R A P f := by
        calc (mP R A P f) ^ (m + 1) ≤ (mP R A P f) ^ 1 := Ideal.pow_le_pow_right (by omega)
          _ = mP R A P f := pow_one _
      have hp' : p ∈ mP R A P f := hle hp
      rwa [mP, Ideal.mem_comap] at hp')
/-- The `P̄`-module structure on `κ` obtained by restricting scalars along `P̄ → κ`. -/
noncomputable instance modPbarKappa : Module (Pbar R A P f m) (IsLocalRing.ResidueField A) :=
  Module.compHom _ (PbarToKappa R A P f m)
/-- The `unop` ring hom `P̄ᵐᵒᵖ → P̄` (a ring hom since `P̄` is commutative). -/
noncomputable def opToPbar : (Pbar R A P f m)ᵐᵒᵖ →+* (Pbar R A P f m) :=
  RingHom.fromOpposite (RingHom.id _) (fun x y => mul_comm x y)
/-- The `P̄ᵐᵒᵖ`-module structure on `κ` obtained by restricting scalars along `P̄ᵐᵒᵖ → P̄ → κ`. -/
noncomputable instance modPbarMopKappa :
    Module (Pbar R A P f m)ᵐᵒᵖ (IsLocalRing.ResidueField A) :=
  Module.compHom _ ((PbarToKappa R A P f m).comp (opToPbar R A P f m))
/-- The left and right `P̄`-actions on `κ` agree. -/
instance cs : IsCentralScalar (Pbar R A P f m) (IsLocalRing.ResidueField A) := ⟨fun _ _ => rfl⟩
/-- `T = TrivSqZeroExt P̄ κ`, the trivial square-zero extension. -/
noncomputable abbrev T : Type u := TrivSqZeroExt (Pbar R A P f m) (IsLocalRing.ResidueField A)
/-- The commutative ring structure on `T`. -/
noncomputable instance ctT : CommRing (T R A P f m) := inferInstance
/-- `R → T` ring hom (`R → P̄ → inl → T`), giving `T` an `R`-algebra structure. -/
noncomputable def RtoT : R →+* T R A P f m :=
  (TrivSqZeroExt.inlHom (Pbar R A P f m) (IsLocalRing.ResidueField A)).comp
    (algebraMap R (Pbar R A P f m))
/-- The `R`-algebra structure on `T` given by `R → P̄ → T`. -/
noncomputable instance algRT : Algebra R (T R A P f m) := (RtoT R A P f m).toAlgebra

/-- `B = Ā = A / 𝔪_A^{m+1}`. -/
@[ega "0 22.5.2",
  ega "III 7.5.1",
  ega "IV 16.1.2" "special case",
  sga "3 X 4.3",
  sga "3 XI 4.4" "partial",
  sga "3 XV 2.8",
  sga "3 XX 1.10"]
noncomputable abbrev Abar : Type u := A ⧸ (IsLocalRing.maximalIdeal A) ^ (m + 1)
/-- The commutative ring structure on `Ā`. -/
noncomputable instance ctAbar : CommRing (Abar A m) := inferInstance
/-- The `R`-algebra structure on `Ā` inherited from `A`. -/
noncomputable instance algAbar : Algebra R (Abar A m) := inferInstance
/-- `a : A →ₐ[R] Ā`, the truncation quotient. -/
@[sga "3 XV 2.8"]
noncomputable def aMap : A →ₐ[R] Abar A m := Ideal.Quotient.mkₐ R _
/-- The map `P̄ → Ā` induced by `f`, well defined because
`f(𝔪_P^{m+1}) ⊆ 𝔪_A^{m+1}`. -/
noncomputable def PbarToAbar : Pbar R A P f m →+* Abar A m :=
  Ideal.Quotient.lift ((mP R A P f) ^ (m + 1))
    ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (m + 1))).comp f.toRingHom)
    (fun p hp => by
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hmap : Ideal.map f.toRingHom ((mP R A P f) ^ (m + 1))
          ≤ (IsLocalRing.maximalIdeal A) ^ (m + 1) := by
        rw [Ideal.map_pow, mP]
        exact Ideal.pow_right_mono Ideal.map_comap_le (m + 1)
      exact hmap (Ideal.mem_map_of_mem _ hp))
/-- `T → Ā` via first projection then `P̄ → Ā`. -/
noncomputable def TtoAbar : T R A P f m →+* Abar A m :=
  (PbarToAbar R A P f m).comp
    (TrivSqZeroExt.fstHom (Pbar R A P f m) (Pbar R A P f m)
      (IsLocalRing.ResidueField A)).toRingHom

omit [IsNoetherianRing A] in
/-- **(V) `Ā` is local** (nilpotent maximal ideal). -/
theorem isLocalRing_Abar : IsLocalRing (Abar A m) := by
  have hne : ((IsLocalRing.maximalIdeal A) ^ (m + 1)) ≠ ⊤ := by
    intro h
    have hle := Ideal.pow_le_self (I := IsLocalRing.maximalIdeal A) (n := m + 1) (by omega)
    rw [h] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp hle)
  have : Nontrivial (Abar A m) := (Ideal.Quotient.nontrivial_iff).mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- **(V) `Ā` is Artinian** (Noetherian + nilpotent maximal ideal). -/
@[ega "III 5.1.7" "partial", sga "7 IX 5.1" "partial"]
theorem isArtinianRing_Abar : IsArtinianRing (Abar A m) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal A).isPrime, ?_⟩, ?_⟩
  · exact Ideal.pow_le_self (by omega)
  · intro q hq _
    have := hq.left
    exact Ideal.IsPrime.le_of_pow_le hq.right

section WithO
variable [Algebra P A]
  (o : (Algebra.Extension.ofSurjective f hf).Cotangent →ₗ[A] IsLocalRing.ResidueField A)

/-- The lifted functional `õ : ker f → κ`, `i ↦ o([i])` (Step 0). -/
noncomputable def otilde (i : (RingHom.ker f.toRingHom)) : IsLocalRing.ResidueField A :=
  o (Algebra.Extension.Cotangent.of ((Ideal.toCotangent (RingHom.ker f.toRingHom)) i))
/-- Image of `i ∈ P` in `P̄`. -/
noncomputable def ibar (i : P) : Pbar R A P f m :=
  Ideal.Quotient.mk _ i
/-- The graph generator set `S = {(ī, -õ i) : i ∈ ker f}`. -/
noncomputable def Kgen : Set (T R A P f m) :=
  Set.range (fun i : (RingHom.ker f.toRingHom) =>
    (TrivSqZeroExt.inl (ibar R A P f m (i : P))
      - TrivSqZeroExt.inr (otilde R A P f hf o i) : T R A P f m))
/-- The ideal `K = ⟨(ī, -õ i) : i ∈ ker f⟩`. -/
noncomputable def Kideal : Ideal (T R A P f m) := Ideal.span (Kgen R A P f hf m o)
/-- `B'_o = T / K`. -/
noncomputable abbrev Bo : Type u := (T R A P f m) ⧸ (Kideal R A P f hf m o)
/-- The commutative ring structure on `B'_o`. -/
noncomputable instance ctBo : CommRing (Bo R A P f hf m o) := inferInstance
/-- The `R`-algebra structure on `B'_o` inherited from `T`. -/
noncomputable instance algBo : Algebra R (Bo R A P f hf m o) := inferInstance

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(I)/(II) helper**: `T → Ā` kills `K` (each generator's first coord is `ī ↦ f(i)=0`). -/
theorem TtoAbar_kills_Kideal :
    (Kideal R A P f hf m o) ≤ RingHom.ker (TtoAbar R A P f m) := by
  rw [Kideal, Ideal.span_le]
  rintro x ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, map_sub]
  have h1 : TtoAbar R A P f m (TrivSqZeroExt.inl (ibar R A P f m (i : P))) = 0 := by
    rw [TtoAbar, RingHom.comp_apply]
    rw [show (TrivSqZeroExt.fstHom (Pbar R A P f m) (Pbar R A P f m)
        (IsLocalRing.ResidueField A)).toRingHom (TrivSqZeroExt.inl (ibar R A P f m (i : P)))
        = ibar R A P f m (i : P) from rfl]
    rw [ibar, PbarToAbar, Ideal.Quotient.lift_mk, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    have hi : f.toRingHom (i : P) = 0 := RingHom.mem_ker.mp i.property
    rw [hi]
    exact Ideal.zero_mem _
  have h2 : TtoAbar R A P f m (TrivSqZeroExt.inr (otilde R A P f hf o i)) = 0 := by
    rw [TtoAbar, RingHom.comp_apply]
    rw [show (TrivSqZeroExt.fstHom (Pbar R A P f m) (Pbar R A P f m)
        (IsLocalRing.ResidueField A)).toRingHom (TrivSqZeroExt.inr (otilde R A P f hf o i))
        = (0 : Pbar R A P f m) from rfl]
    rw [map_zero]
  rw [h1, h2, sub_zero]

/-- `φ : B'_o → Ā`, induced by `T → Ā` over `K`. -/
noncomputable def phiMap : Bo R A P f hf m o →+* Abar A m :=
  Ideal.Quotient.lift _ (TtoAbar R A P f m)
    (fun t ht => by
      have := TtoAbar_kills_Kideal R A P f hf m o ht
      simpa [RingHom.mem_ker] using this)

/-- `q₀ : P → B'_o`, `g ↦ [(ḡ, 0)]`. -/
noncomputable def q0Map : P →+* Bo R A P f hf m o :=
  (Ideal.Quotient.mk (Kideal R A P f hf m o)).comp
    ((TrivSqZeroExt.inlHom (Pbar R A P f m) (IsLocalRing.ResidueField A)).comp
      (Ideal.Quotient.mk ((mP R A P f) ^ (m + 1))))

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- The `R`-algebra compatibility of `φ` (`commutes'`). -/
theorem phiMap_commutes (r : R) :
    phiMap R A P f hf m o ((algebraMap R (Bo R A P f hf m o)) r)
      = (algebraMap R (Abar A m)) r := by
  have hbo : (algebraMap R (Bo R A P f hf m o)) r
      = Ideal.Quotient.mk (Kideal R A P f hf m o)
          (TrivSqZeroExt.inl ((algebraMap R (Pbar R A P f m)) r)) := rfl
  rw [hbo]
  show (PbarToAbar R A P f m) ((algebraMap R (Pbar R A P f m)) r)
    = (algebraMap R (Abar A m)) r
  show (Ideal.Quotient.mk _) (f.toRingHom ((algebraMap R (P)) r))
    = (algebraMap R (Abar A m)) r
  rw [show f.toRingHom ((algebraMap R (P)) r)
        = algebraMap R A r from f.commutes r]
  rfl

/-- `φ` as an `R`-algebra homomorphism. -/
noncomputable def phiAlg : Bo R A P f hf m o →ₐ[R] Abar A m :=
  { phiMap R A P f hf m o with commutes' := phiMap_commutes R A P f hf m o }

/-- `q₀` as an `R`-algebra homomorphism. -/
noncomputable def q0Alg : P →ₐ[R] Bo R A P f hf m o :=
  { q0Map R A P f hf m o with commutes' := fun _ => rfl }

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(III) surjectivity** of `φ`. -/
theorem phiAlg_surjective : Function.Surjective (phiAlg R A P f hf m o) := by
  show Function.Surjective (phiMap R A P f hf m o)
  apply Ideal.Quotient.lift_surjective_of_surjective
  rw [TtoAbar, RingHom.coe_comp]
  apply Function.Surjective.comp
  · apply Ideal.Quotient.lift_surjective_of_surjective
    exact Ideal.Quotient.mk_surjective.comp hf
  · exact TrivSqZeroExt.fst_surjective

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(III) square-zero**: `(ker φ)² = ⊥`. -/
theorem phiAlg_ker_sq :
    (RingHom.ker (phiMap R A P f hf m o)) ^ 2 = ⊥ := by
  -- The kernel of `phiMap` is the pushforward of `ker TtoAbar`.
  have hker : RingHom.ker (phiMap R A P f hf m o)
      = Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o)) (RingHom.ker (TtoAbar R A P f m)) :=
    Ideal.ker_quotient_lift (TtoAbar R A P f m) (TtoAbar_kills_Kideal R A P f hf m o)
  -- Key arithmetic: `f⁻¹(𝔪_A^{m+1}) ≤ ker f ⊔ 𝔪_P^{m+1}` (surjectivity of `f`).
  have hcore : Ideal.comap f.toRingHom ((IsLocalRing.maximalIdeal A) ^ (m+1))
      ≤ RingHom.ker f.toRingHom ⊔ (mP R A P f) ^ (m+1) := by
    have hmap : Ideal.map f.toRingHom ((mP R A P f) ^ (m+1))
        = (IsLocalRing.maximalIdeal A) ^ (m+1) := by
      rw [Ideal.map_pow, mP, Ideal.map_comap_of_surjective f.toRingHom hf]
    intro p hp
    rw [Ideal.mem_comap] at hp
    rw [show (mP R A P f) = Ideal.comap f.toRingHom (IsLocalRing.maximalIdeal A) from rfl] at hmap
    rw [← hmap, Ideal.mem_map_iff_of_surjective f.toRingHom hf] at hp
    obtain ⟨q, hq, hfq⟩ := hp
    have hpq : p = (p - q) + q := by ring
    rw [hpq]
    exact add_mem (Ideal.mem_sup_left (by rw [RingHom.mem_ker, map_sub, hfq, sub_self]))
      (Ideal.mem_sup_right hq)
  -- `ker PbarToAbar ≤ Ī` (image of `ker f` in `P̄`).
  have hPbarKer : RingHom.ker (PbarToAbar R A P f m)
      ≤ Ideal.map (Ideal.Quotient.mk ((mP R A P f) ^ (m+1))) (RingHom.ker f.toRingHom) := by
    have hk2 : RingHom.ker (PbarToAbar R A P f m)
        = Ideal.map (Ideal.Quotient.mk ((mP R A P f) ^ (m+1)))
            (RingHom.ker ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (m + 1))).comp
              f.toRingHom)) := by
      rw [PbarToAbar]
      exact Ideal.ker_quotient_lift _ _
    rw [hk2, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hp
    have hsup := hcore (by rwa [Ideal.mem_comap])
    rcases Submodule.mem_sup.mp hsup with ⟨a, ha, b, hb, hab⟩
    rw [Ideal.mem_comap]
    have heq : (Ideal.Quotient.mk ((mP R A P f) ^ (m+1))) p
        = (Ideal.Quotient.mk ((mP R A P f) ^ (m+1))) a := by
      rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero]
    rw [heq]
    exact Ideal.mem_map_of_mem _ ha
  -- Sub-lemma: `ker TtoAbar ≤ kerIdeal ⊔ K`.
  have hsub : RingHom.ker (TtoAbar R A P f m)
      ≤ TrivSqZeroExt.kerIdeal (Pbar R A P f m) (IsLocalRing.ResidueField A)
          ⊔ Kideal R A P f hf m o := by
    intro t ht
    -- `t.fst ∈ ker PbarToAbar`
    have hfst : (TrivSqZeroExt.fst t) ∈ RingHom.ker (PbarToAbar R A P f m) := by
      rw [RingHom.mem_ker]
      rw [RingHom.mem_ker, TtoAbar, RingHom.comp_apply] at ht
      exact ht
    have hmem := hPbarKer hfst
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hmem
    obtain ⟨i, hi, hieq⟩ := hmem
    -- decompose `t = inl t.fst + inr t.snd`
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq t]
    refine add_mem ?_ ?_
    · -- `inl t.fst = inr (õ ⟨i,hi⟩) + (inl ī - inr (õ ⟨i,hi⟩)) ∈ kerIdeal ⊔ K`
      have hgen : (TrivSqZeroExt.inl (ibar R A P f m i)
          - TrivSqZeroExt.inr (otilde R A P f hf o ⟨i, hi⟩) : T R A P f m)
            ∈ Kideal R A P f hf m o :=
        Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩
      have hdecomp : (TrivSqZeroExt.inl (TrivSqZeroExt.fst t) : T R A P f m)
          = TrivSqZeroExt.inr (otilde R A P f hf o ⟨i, hi⟩)
            + (TrivSqZeroExt.inl (ibar R A P f m i)
              - TrivSqZeroExt.inr (otilde R A P f hf o ⟨i, hi⟩)) := by
        rw [← hieq]
        rw [ibar]
        ring
      rw [hdecomp]
      exact add_mem (Ideal.mem_sup_left
        ((TrivSqZeroExt.mem_kerIdeal_iff_inr _ _ _).mpr rfl))
        (Ideal.mem_sup_right hgen)
    · exact Ideal.mem_sup_left ((TrivSqZeroExt.mem_kerIdeal_iff_inr _ _ _).mpr rfl)
  -- Conclude.
  have hle : RingHom.ker (phiMap R A P f hf m o)
      ≤ Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o))
          (TrivSqZeroExt.kerIdeal (Pbar R A P f m) (IsLocalRing.ResidueField A)) := by
    rw [hker]
    calc Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o)) (RingHom.ker (TtoAbar R A P f m))
        ≤ Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o))
            (TrivSqZeroExt.kerIdeal (Pbar R A P f m) (IsLocalRing.ResidueField A)
              ⊔ Kideal R A P f hf m o) := Ideal.map_mono hsub
      _ = Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o))
            (TrivSqZeroExt.kerIdeal (Pbar R A P f m) (IsLocalRing.ResidueField A))
          ⊔ Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o)) (Kideal R A P f hf m o) :=
            Ideal.map_sup _ _ _
      _ = Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o))
            (TrivSqZeroExt.kerIdeal (Pbar R A P f m) (IsLocalRing.ResidueField A)) := by
            rw [Ideal.map_quotient_self, sup_bot_eq]
  -- the squared kernel is ≤ map π (kerIdeal²) = ⊥
  rw [← le_bot_iff]
  calc (RingHom.ker (phiMap R A P f hf m o)) ^ 2
      ≤ (Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o))
          (TrivSqZeroExt.kerIdeal (Pbar R A P f m) (IsLocalRing.ResidueField A))) ^ 2 :=
        pow_le_pow_left' hle 2
    _ = Ideal.map (Ideal.Quotient.mk (Kideal R A P f hf m o))
          ((TrivSqZeroExt.kerIdeal (Pbar R A P f m) (IsLocalRing.ResidueField A)) ^ 2) :=
        (Ideal.map_pow _ _ 2).symm
    _ = ⊥ := by
          rw [TrivSqZeroExt.kerIdeal_sq, Ideal.map_bot]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- õ additive. -/
theorem otilde_add (i j : (RingHom.ker f.toRingHom)) :
    otilde R A P f hf o (i + j) = otilde R A P f hf o i + otilde R A P f hf o j := by
  unfold otilde
  rw [(Ideal.toCotangent (RingHom.ker f.toRingHom)).map_add]
  rw [show Algebra.Extension.Cotangent.of (P := Algebra.Extension.ofSurjective f hf)
        ((Ideal.toCotangent (RingHom.ker f.toRingHom)) i
          + (Ideal.toCotangent (RingHom.ker f.toRingHom)) j)
      = Algebra.Extension.Cotangent.of (P := Algebra.Extension.ofSurjective f hf)
          ((Ideal.toCotangent (RingHom.ker f.toRingHom)) i)
        + Algebra.Extension.Cotangent.of (P := Algebra.Extension.ofSurjective f hf)
          ((Ideal.toCotangent (RingHom.ker f.toRingHom)) j)
      from Algebra.Extension.Cotangent.of_add _ _]
  rw [map_add]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- õ(0) = 0. -/
theorem otilde_zero : otilde R A P f hf o 0 = 0 := by
  unfold otilde
  rw [map_zero]
  show o 0 = 0
  rw [map_zero]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **otilde vanishing on a single `p • j` generator with `p ∈ mP`** (the analytic kernel
of (II)). -/
theorem otilde_smul_mP_eq_zero
    (p : P) (hp : p ∈ mP R A P f)
    (j : (RingHom.ker f.toRingHom)) :
    otilde R A P f hf o (p • j) = 0 := by
  unfold otilde
  rw [cotangent_of_toCotangent_smul f hf, map_smul, Algebra.smul_def,
    show (algebraMap A (IsLocalRing.ResidueField A)) (f.toRingHom p) = 0 from
      (IsLocalRing.residue_eq_zero_iff _).mpr (by rwa [mP, Ideal.mem_comap] at hp), zero_mul]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **otilde vanishes on `mP • ker f`** (extends the single-generator vanishing additively). -/
theorem otilde_vanish_mP_smul
    (i : (RingHom.ker f.toRingHom))
    (hi : (i : P) ∈ (mP R A P f) • (RingHom.ker f.toRingHom)) :
    otilde R A P f hf o i = 0 := by
  -- predicate on the carrier: in ker f AND otilde vanishes
  set Q : P → Prop :=
    fun x => ∃ (hx : x ∈ RingHom.ker f.toRingHom), otilde R A P f hf o ⟨x, hx⟩ = 0 with hQ
  have hgoal : Q (i : P) := by
    refine Submodule.smul_induction_on hi (p := Q) ?_ ?_
    · -- generators r • s, r ∈ mP, s ∈ ker f
      intro r hr s hs
      have hmem : r • s ∈ RingHom.ker f.toRingHom := (RingHom.ker f.toRingHom).smul_mem r hs
      refine ⟨hmem, ?_⟩
      have heq : (⟨r • s, hmem⟩ : (RingHom.ker f.toRingHom)) = r • (⟨s, hs⟩ : (RingHom.ker
          f.toRingHom)) := rfl
      rw [heq]
      exact otilde_smul_mP_eq_zero R A P f hf o r hr ⟨s, hs⟩
    · -- additivity
      rintro x y ⟨hx, hxo⟩ ⟨hy, hyo⟩
      refine ⟨add_mem hx hy, ?_⟩
      have heq : (⟨x + y, add_mem hx hy⟩ : (RingHom.ker f.toRingHom))
          = (⟨x, hx⟩ : (RingHom.ker f.toRingHom)) + ⟨y, hy⟩ := rfl
      rw [heq, otilde_add, hxo, hyo, add_zero]
  obtain ⟨hi', hio⟩ := hgoal
  -- the membership proof is unique
  convert hio using 2

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **otilde P-linearity**: `õ(p • j) = residue(f p) • õ j`. -/
theorem otilde_smul
    (p : P)
    (j : (RingHom.ker f.toRingHom)) :
    otilde R A P f hf o (p • j)
      = (IsLocalRing.residue A (f.toRingHom p)) • otilde R A P f hf o j := by
  unfold otilde
  rw [cotangent_of_toCotangent_smul f hf, map_smul, Algebra.smul_def, smul_eq_mul]
  rfl


omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- ibar p • c = residue (f p) • c  (κ-action of Pbar via PbarToKappa). -/
theorem ibar_smul_kappa (p : P) (c : IsLocalRing.ResidueField A) :
    (ibar R A P f m p) • c = (IsLocalRing.residue A (f.toRingHom p)) • c := by
  show (PbarToKappa R A P f m) (ibar R A P f m p) • c = _
  rw [ibar, PbarToKappa, Ideal.Quotient.lift_mk, RingHom.comp_apply]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- ī • c = 0 for i ∈ ker f. -/
theorem ibar_ker_smul_kappa_zero (i : (RingHom.ker f.toRingHom)) (c : IsLocalRing.ResidueField A) :
    (ibar R A P f m (i : P)) • c = 0 := by
  rw [ibar_smul_kappa]
  have : f.toRingHom (i : P) = 0 := RingHom.mem_ker.mp i.property
  rw [this, map_zero, zero_smul]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- Multiplication closure of the graph: t * (inl ī - inr õi) is again of graph form. -/
theorem Kgen_smul_closed
    (t : T R A P f m) (i : (RingHom.ker f.toRingHom)) :
    ∃ k : (RingHom.ker f.toRingHom),
      t * (TrivSqZeroExt.inl (ibar R A P f m (i : P))
        - TrivSqZeroExt.inr (otilde R A P f hf o i))
      = TrivSqZeroExt.inl (ibar R A P f m (k : P))
        - TrivSqZeroExt.inr (otilde R A P f hf o k) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := (mP R A P f) ^ (m + 1)) (TrivSqZeroExt.fst t)
  -- k = p • i
  refine ⟨p • i, ?_⟩
  apply TrivSqZeroExt.ext
  · -- fst
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, sub_zero, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, sub_zero]
    -- t.fst * ibar i = ibar (p • i)
    rw [show TrivSqZeroExt.fst t = ibar R A P f m p from hp.symm]
    show (Ideal.Quotient.mk _) p * (Ideal.Quotient.mk _) (i : P)
      = (Ideal.Quotient.mk _) ((p • i : (RingHom.ker f.toRingHom)) : P)
    rw [← map_mul]
    rfl
  · -- snd
    rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_sub, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, sub_zero, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_sub]
    -- t.fst • (-õi) + op(ī) • t.snd = -õ(p•i)
    rw [show TrivSqZeroExt.fst t = ibar R A P f m p from hp.symm]
    have hop : (MulOpposite.op (ibar R A P f m (i : P))) • (TrivSqZeroExt.snd t)
        = (ibar R A P f m (i : P)) • (TrivSqZeroExt.snd t) := rfl
    rw [hop, ibar_ker_smul_kappa_zero, add_zero, smul_neg]
    rw [ibar_smul_kappa, ← otilde_smul R A P f hf o]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(I) graph characterization**: every element of `Kideal` is of graph form
`inl(ī) - inr(õi)`. -/
theorem mem_Kideal_iff
    (x : T R A P f m) :
    x ∈ Kideal R A P f hf m o ↔
      ∃ i : (RingHom.ker f.toRingHom),
        x = TrivSqZeroExt.inl (ibar R A P f m (i : P))
          - TrivSqZeroExt.inr (otilde R A P f hf o i) := by
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun y _ =>
        ∃ i : (RingHom.ker f.toRingHom),
          y = TrivSqZeroExt.inl (ibar R A P f m (i : P))
            - TrivSqZeroExt.inr (otilde R A P f hf o i)) ?_ ?_ ?_ ?_ hx
    · -- generators
      rintro y ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · -- zero
      refine ⟨0, ?_⟩
      have h0 : (ibar R A P f m ((0 : (RingHom.ker f.toRingHom)) : P)) = 0 := by
        rw [ZeroMemClass.coe_zero, ibar, map_zero]
      rw [h0, otilde_zero]
      simp
    · -- add
      rintro y z _ _ ⟨iy, rfl⟩ ⟨iz, rfl⟩
      refine ⟨iy + iz, ?_⟩
      have hib : (ibar R A P f m ((iy + iz : (RingHom.ker f.toRingHom)) : P))
          = ibar R A P f m (iy : P) + ibar R A P f m (iz : P) := by
        rw [show ((iy + iz : (RingHom.ker f.toRingHom)) : P)
              = (iy : P) + iz from rfl, ibar, ibar, ibar, map_add]
      rw [hib, otilde_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
      abel
    · -- smul (T-mult)
      rintro a y _ ⟨iy, rfl⟩
      obtain ⟨k, hk⟩ := Kgen_smul_closed R A P f hf m o a iy
      exact ⟨k, by rwa [smul_eq_mul]⟩
  · rintro ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(II) non-degeneracy**: `inr c ∈ Kideal → c = 0` (uses `hAR`). -/
theorem inr_mem_Kideal_imp_zero
    (hAR : (RingHom.ker f.toRingHom) ⊓ (mP R A P f) ^ (m + 1) ≤ (mP R A P f) • (RingHom.ker
        f.toRingHom))
    (c : IsLocalRing.ResidueField A)
    (hc : TrivSqZeroExt.inr c ∈ Kideal R A P f hf m o) :
    c = 0 := by
  obtain ⟨i, hi⟩ := (mem_Kideal_iff R A P f hf m o _).mp hc
  -- inr c = inl(ī) - inr(õi); compare fst and snd
  have hfst : (ibar R A P f m (i : P)) = 0 := by
    have := congrArg TrivSqZeroExt.fst hi
    rw [TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, sub_zero] at this
    exact this.symm
  have hsnd : c = - otilde R A P f hf o i := by
    have := congrArg TrivSqZeroExt.snd hi
    rwa [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_sub] at this
  -- ī = 0 means i ∈ 𝔪_P^{m+1}
  have hi_pow : (i : P) ∈ (mP R A P f) ^ (m + 1) := by
    rwa [ibar, Ideal.Quotient.eq_zero_iff_mem] at hfst
  -- i ∈ ker f ⊓ 𝔪_P^{m+1} ⊆ mP • ker f
  have hi_smul : (i : P) ∈ (mP R A P f) • (RingHom.ker f.toRingHom) :=
    hAR ⟨i.property, hi_pow⟩
  -- õ i = 0
  have hoz : otilde R A P f hf o i = 0 := otilde_vanish_mP_smul R A P f hf o i hi_smul
  rw [hsnd, hoz, neg_zero]

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- `π(inr c) ∈ ker φ` (lands in the kernel since `fst (inr c) = 0`). -/
theorem inr_mem_ker_phi (c : IsLocalRing.ResidueField A) :
    Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inr c)
      ∈ RingHom.ker (phiMap R A P f hf m o) := by
  rw [RingHom.mem_ker]
  show phiMap R A P f hf m o (Ideal.Quotient.mk _ (TrivSqZeroExt.inr c)) = 0
  rw [phiMap, Ideal.Quotient.lift_mk, TtoAbar, RingHom.comp_apply]
  rw [show (TrivSqZeroExt.fstHom (Pbar R A P f m) (Pbar R A P f m)
      (IsLocalRing.ResidueField A)).toRingHom (TrivSqZeroExt.inr c) = (0 : Pbar R A P f m) from rfl]
  rw [map_zero]

/-- The R-linear map `κ → ker φ`, `c ↦ ⟨π(inr c), _⟩`. -/
noncomputable def kappaToKer :
    IsLocalRing.ResidueField A →ₗ[R] (RingHom.ker (phiMap R A P f hf m o)) where
  toFun c := ⟨Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inr c),
    inr_mem_ker_phi R A P f hf m o c⟩
  map_add' c d := by
    apply Subtype.ext
    change Ideal.Quotient.mk _ (TrivSqZeroExt.inr (c + d))
      = Ideal.Quotient.mk _ (TrivSqZeroExt.inr c) + Ideal.Quotient.mk _ (TrivSqZeroExt.inr d)
    rw [TrivSqZeroExt.inr_add, map_add]
  map_smul' r c := by
    apply Subtype.ext
    change Ideal.Quotient.mk _ (TrivSqZeroExt.inr (r • c))
      = r • Ideal.Quotient.mk _ (TrivSqZeroExt.inr c)
    have halgBo : (algebraMap R (Bo R A P f hf m o)) r
        = Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inl ((algebraMap R (Pbar R A P f
            m)) r)) := rfl
    conv_rhs => rw [Algebra.smul_def, halgBo, ← map_mul, TrivSqZeroExt.inl_mul_inr]
    congr 2
    change r • c = (PbarToKappa R A P f m) ((algebraMap R (Pbar R A P f m)) r) • c
    have hak : (PbarToKappa R A P f m) ((algebraMap R (Pbar R A P f m)) r)
        = (algebraMap R (IsLocalRing.ResidueField A)) r := by
      rw [show (algebraMap R (Pbar R A P f m)) r
            = Ideal.Quotient.mk _ ((algebraMap R (P)) r) from rfl,
        PbarToKappa, Ideal.Quotient.lift_mk, RingHom.comp_apply]
      rw [show f.toRingHom ((algebraMap R (P)) r) = algebraMap R A r from f.commutes r]
      rfl
    rw [hak]
    exact algebra_compatible_smul (IsLocalRing.ResidueField A) r c

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- The comparison map `κ → ker φ` is injective, given the Artin–Rees bound
`ker f ⊓ 𝔪_P^(m+1) ≤ 𝔪_P • ker f`. -/
theorem kappaToKer_injective
    (hAR : (RingHom.ker f.toRingHom) ⊓ (mP R A P f) ^ (m + 1) ≤ (mP R A P f) • (RingHom.ker
        f.toRingHom)) :
    Function.Injective (kappaToKer R A P f hf m o) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hc' : Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inr c) = 0 :=
    congrArg Subtype.val hc
  rw [Ideal.Quotient.eq_zero_iff_mem] at hc'
  exact inr_mem_Kideal_imp_zero R A P f hf m o hAR c hc'

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- The comparison map `κ → ker φ` is surjective. -/
theorem kappaToKer_surjective :
    Function.Surjective (kappaToKer R A P f hf m o) := by
  rintro ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  have hfst : (PbarToAbar R A P f m) (TrivSqZeroExt.fst t) = 0 := by
    have : phiMap R A P f hf m o (Ideal.Quotient.mk _ t) = 0 := hx
    rwa [phiMap, Ideal.Quotient.lift_mk, TtoAbar, RingHom.comp_apply] at this
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := (mP R A P f) ^ (m + 1)) (TrivSqZeroExt.fst t)
  have hfp : (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (m + 1))) (f.toRingHom p) = 0 := by
    have : (PbarToAbar R A P f m) (Ideal.Quotient.mk _ p) = 0 := by rwa [hp]
    rwa [PbarToAbar, Ideal.Quotient.lift_mk, RingHom.comp_apply] at this
  rw [Ideal.Quotient.eq_zero_iff_mem] at hfp
  have hmaps : Ideal.map f.toRingHom ((mP R A P f) ^ (m + 1))
      = (IsLocalRing.maximalIdeal A) ^ (m + 1) := by
    rw [Ideal.map_pow, mP, Ideal.map_comap_of_surjective f.toRingHom hf]
  rw [← hmaps, Ideal.mem_map_iff_of_surjective f.toRingHom hf] at hfp
  obtain ⟨s, hs, hfs⟩ := hfp
  have hi_ker : p - s ∈ RingHom.ker f.toRingHom := by
    rw [RingHom.mem_ker, map_sub, hfs, sub_self]
  set i : (RingHom.ker f.toRingHom) := ⟨p - s, hi_ker⟩ with hidef
  -- ibar i = fst t  (since s ∈ 𝔪_P^{m+1})
  have hibar : ibar R A P f m (i : P) = TrivSqZeroExt.fst t := by
    rw [hidef]
    show (Ideal.Quotient.mk _) (p - s) = TrivSqZeroExt.fst t
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hs, sub_zero, hp]
  refine ⟨otilde R A P f hf o i + TrivSqZeroExt.snd t, ?_⟩
  apply Subtype.ext
  show Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inr (otilde R A P f hf o i +
      TrivSqZeroExt.snd t))
    = Ideal.Quotient.mk _ t
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  -- inr(õ i + snd t) - t = inr(õi) - inl(ibar i)  = -(g_i) ∈ Kideal
  have hg : (TrivSqZeroExt.inl (ibar R A P f m (i : P))
      - TrivSqZeroExt.inr (otilde R A P f hf o i) : T R A P f m) ∈ Kideal R A P f hf m o :=
    Ideal.subset_span ⟨i, rfl⟩
  have heq : (TrivSqZeroExt.inr (otilde R A P f hf o i + TrivSqZeroExt.snd t) - t : T R A P f m)
      = - (TrivSqZeroExt.inl (ibar R A P f m (i : P))
            - TrivSqZeroExt.inr (otilde R A P f hf o i)) := by
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_neg,
        TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, sub_zero,
        zero_sub, hibar]
    · rw [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_neg,
        TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_sub, neg_neg]
      abel
  rw [heq]
  exact neg_mem hg

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- Bo-action on `ker φ`: `π(inl(ibar p)) • π(inr c) = π(inr(residue(f p) • c))`. -/
theorem bo_smul_kappaToKer (p : P) (c : IsLocalRing.ResidueField A) :
    (Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inl (ibar R A P f m p)))
        • (kappaToKer R A P f hf m o c)
      = kappaToKer R A P f hf m o ((IsLocalRing.residue A (f.toRingHom p)) • c) := by
  apply Subtype.ext
  rw [SetLike.val_smul]
  show Ideal.Quotient.mk _ (TrivSqZeroExt.inl (ibar R A P f m p)) *
      Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inr c)
    = Ideal.Quotient.mk _ (TrivSqZeroExt.inr ((IsLocalRing.residue A (f.toRingHom p)) • c))
  rw [← map_mul]
  congr 1
  rw [TrivSqZeroExt.inl_mul_inr, ibar_smul_kappa]


omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(III) length one**: `length_{B'_o} (ker φ) = 1` (uses (II) non-degeneracy via `hAR`).
NOTE: `hm`/`hAR` are REQUIRED — without the Artin–Rees non-degeneracy the kernel can collapse
(length 0) for small `m`, so this would be false. (Stated with them to keep the sketch sound.) -/
theorem phiAlg_ker_length
    (hAR : (RingHom.ker f.toRingHom) ⊓ (mP R A P f) ^ (m + 1) ≤ (mP R A P f) • (RingHom.ker
        f.toRingHom)) :
    Module.length (Bo R A P f hf m o) (RingHom.ker (phiMap R A P f hf m o)) = 1 := by
  rw [Module.length_eq_one_iff]
  have hbij : Function.Bijective (kappaToKer R A P f hf m o) :=
    ⟨kappaToKer_injective R A P f hf m o hAR, kappaToKer_surjective R A P f hf m o⟩
  have hnt : Nontrivial (RingHom.ker (phiMap R A P f hf m o)) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h1 : kappaToKer R A P f hf m o 1 = kappaToKer R A P f hf m o 0 := Subsingleton.elim _ _
    have : (1 : IsLocalRing.ResidueField A) = 0 := hbij.left h1
    exact one_ne_zero this
  refine { eq_bot_or_eq_top := fun N => ?_ }
  · rcases eq_or_ne N ⊥ with hN | hN
    · exact Or.inl hN
    · refine Or.inr ?_
      rw [eq_top_iff]
      obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
      obtain ⟨c, rfl⟩ := hbij.right x
      have hc0 : c ≠ 0 := by
        intro h; apply hx0; rw [h, map_zero]
      intro y _
      obtain ⟨d, rfl⟩ := hbij.right y
      have hsurj : Function.Surjective (fun p : P => IsLocalRing.residue A (f.toRingHom p)) := by
        intro z
        obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective z
        obtain ⟨p, hp⟩ := hf a
        refine ⟨p, ?_⟩
        show IsLocalRing.residue A (f.toRingHom p) = z
        rw [show f.toRingHom p = f p from rfl, hp, ha]
      obtain ⟨p, hp⟩ := hsurj (d * c⁻¹)
      simp only at hp
      have hkey : (Ideal.Quotient.mk (Kideal R A P f hf m o) (TrivSqZeroExt.inl (ibar R A P f m p)))
          • (kappaToKer R A P f hf m o c) = kappaToKer R A P f hf m o d := by
        rw [bo_smul_kappaToKer]
        congr 1
        rw [hp, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      rw [← hkey]
      exact Submodule.smul_mem N _ hxN

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(V) `B'_o` is local**. -/
theorem isLocalRing_Bo : IsLocalRing (Bo R A P f hf m o) := by
  have : IsLocalRing (Abar A m) := isLocalRing_Abar A m
  have hsq := phiAlg_ker_sq R A P f hf m o
  -- ker phiMap ≤ jacobson ⊥
  have hnil : RingHom.ker (phiMap R A P f hf m o)
      ≤ Ideal.jacobson (⊥ : Ideal (Bo R A P f hf m o)) := by
    rw [Ideal.jacobson_bot]
    refine le_trans ?_ (nilradical_le_jacobson (Bo R A P f hf m o))
    intro x hx
    rw [mem_nilradical]
    refine ⟨2, ?_⟩
    have : x ^ 2 ∈ (RingHom.ker (phiMap R A P f hf m o)) ^ 2 := by
      rw [pow_two, pow_two]
      exact Ideal.mul_mem_mul hx hx
    rw [hsq] at this
    simpa using this
  have hlh : IsLocalHom (Ideal.Quotient.mk (RingHom.ker (phiMap R A P f hf m o))) :=
    isLocalHom_of_le_jacobson_bot _ hnil
  have hsurj : Function.Surjective (phiMap R A P f hf m o) := phiAlg_surjective R A P f hf m o
  have : IsLocalRing (Bo R A P f hf m o ⧸ RingHom.ker (phiMap R A P f hf m o)) := by
    have e : (Bo R A P f hf m o ⧸ RingHom.ker (phiMap R A P f hf m o)) ≃+* Abar A m :=
      RingHom.quotientKerEquivOfSurjective hsurj
    exact e.symm.isLocalRing
  exact RingHom.domain_isLocalRing (Ideal.Quotient.mk (RingHom.ker (phiMap R A P f hf m o)))

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [Algebra P A] in
/-- **(V) `B'_o` is Artinian**. -/
theorem isArtinianRing_Bo : IsArtinianRing (Bo R A P f hf m o) := by
  -- Step 1: mP is maximal
  have hmPmax : (mP R A P f).IsMaximal := by
    rw [mP]
    exact Ideal.comap_isMaximal_of_surjective f.toRingHom hf (K := IsLocalRing.maximalIdeal A)
  -- Step 2: Pbar is Artinian
  have hartPbar : IsArtinianRing (Pbar R A P f m) := by
    have hle : (mP R A P f) ^ (m + 1) ≤ (mP R A P f) := Ideal.pow_le_self (by omega)
    have hmapmax : (Ideal.map (Ideal.Quotient.mk ((mP R A P f) ^ (m + 1))) (mP R A P f)).IsMaximal
        :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
    have hnil : nilradical (Pbar R A P f m)
        = Ideal.map (Ideal.Quotient.mk ((mP R A P f) ^ (m + 1))) (mP R A P f) := by
      rw [show nilradical (Pbar R A P f m)
          = Ideal.radical (⊥ : Ideal (Pbar R A P f m)) from rfl]
      rw [show (⊥ : Ideal (Pbar R A P f m))
          = Ideal.map (Ideal.Quotient.mk ((mP R A P f) ^ (m + 1))) ((mP R A P f) ^ (m + 1)) by
        rw [Ideal.map_quotient_self]]
      rw [← Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker])]
      rw [Ideal.radical_pow _ (by omega)]
      rw [Ideal.IsPrime.radical (hmPmax.isPrime)]
    have : (nilradical (Pbar R A P f m)).IsMaximal := by rwa [hnil]
    have : Ring.KrullDimLE 0 (Pbar R A P f m) :=
      Ring.KrullDimLE.of_isMaximal_nilradical (R := Pbar R A P f m)
    exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  -- Step 3: κ is module-finite over Pbar
  have hfinKappa : Module.Finite (Pbar R A P f m) (IsLocalRing.ResidueField A) := by
    refine ⟨?_⟩
    refine ⟨{1}, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hPKsurj : Function.Surjective (PbarToKappa R A P f m) := by
      rw [PbarToKappa]
      apply Ideal.Quotient.lift_surjective_of_surjective
      rw [RingHom.coe_comp]
      exact IsLocalRing.residue_surjective.comp (show Function.Surjective f.toRingHom from hf)
    obtain ⟨p, hp⟩ := hPKsurj x
    rw [Finset.coe_singleton, Submodule.mem_span_singleton]
    refine ⟨p, ?_⟩
    show (PbarToKappa R A P f m) p • (1 : IsLocalRing.ResidueField A) = x
    rw [smul_eq_mul, mul_one, hp]
  -- Step 4: T is module-finite over Pbar
  have hfinT : Module.Finite (Pbar R A P f m) (T R A P f m) := by
    have e : T R A P f m ≃ₗ[Pbar R A P f m]
        (Pbar R A P f m) × (IsLocalRing.ResidueField A) :=
      { toFun := fun x => (TrivSqZeroExt.fst x, TrivSqZeroExt.snd x)
        invFun := fun p => TrivSqZeroExt.inl p.fst + TrivSqZeroExt.inr p.snd
        map_add' := by intro x y; simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
        map_smul' := by intro c x; simp
        left_inv := by intro x; simp [TrivSqZeroExt.inl_fst_add_inr_snd_eq]
        right_inv := by intro p; ext <;> simp }
    exact Module.Finite.equiv e.symm
  -- Step 5: T is Artinian
  have hartT : IsArtinianRing (T R A P f m) :=
    (Module.finite_iff_isArtinianRing (R := Pbar R A P f m) (A := T R A P f m)).mp hfinT
  -- Step 6: Bo = T/K is Artinian
  exact instIsArtinianRingQuotientIdeal (T R A P f m) (Kideal R A P f hf m o)

/-- **(II)+(III) the κ-iso** `θ : ker φ ≃ₗ[R] κ` (non-degeneracy `K ∩ inr κ = ⊥` from `hAR`).
NOTE: `hm`/`hAR` are REQUIRED for `θ` to exist (without them `ker φ` may be `0 ≠ κ`). -/
noncomputable def thetaIso
    (hAR : (RingHom.ker f.toRingHom) ⊓ (mP R A P f) ^ (m + 1) ≤ (mP R A P f) • (RingHom.ker
        f.toRingHom)) :
    (RingHom.ker (phiMap R A P f hf m o)) ≃ₗ[R] IsLocalRing.ResidueField A :=
  (LinearEquiv.ofBijective (kappaToKer R A P f hf m o)
    ⟨kappaToKer_injective R A P f hf m o hAR,
     kappaToKer_surjective R A P f hf m o⟩).symm

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(IV) compatibility** `φ ∘ q₀ = a ∘ f`. -/
theorem phi_comp_q0 :
    (phiMap R A P f hf m o).comp (q0Alg R A P f hf m o).toRingHom
      = (aMap R A m).toRingHom.comp f.toRingHom := by
  apply RingHom.ext
  intro g
  rw [RingHom.comp_apply, RingHom.comp_apply]
  show phiMap R A P f hf m o (q0Map R A P f hf m o g)
    = (aMap R A m).toRingHom (f.toRingHom g)
  rw [q0Map, RingHom.comp_apply, RingHom.comp_apply, phiMap, Ideal.Quotient.lift_mk,
    TtoAbar, RingHom.comp_apply]
  rw [show (TrivSqZeroExt.fstHom (Pbar R A P f m) (Pbar R A P f m)
      (IsLocalRing.ResidueField A)).toRingHom
      ((TrivSqZeroExt.inlHom (Pbar R A P f m) (IsLocalRing.ResidueField A))
        (Ideal.Quotient.mk ((mP R A P f) ^ (m + 1)) g))
      = (Ideal.Quotient.mk ((mP R A P f) ^ (m + 1)) g) from rfl]
  rw [PbarToAbar, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  rfl

omit [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing P] [Algebra P A] in
/-- **(IV) defect link (★)**: for `g ∈ ker f`, `θ(q₀ g) = õ g = o([g])`. -/
theorem defect_link
    (hAR : (RingHom.ker f.toRingHom) ⊓ (mP R A P f) ^ (m + 1) ≤ (mP R A P f) • (RingHom.ker
        f.toRingHom))
    (g : (RingHom.ker f.toRingHom))
    (hmem : q0Alg R A P f hf m o (g : P)
      ∈ RingHom.ker (phiMap R A P f hf m o)) :
    thetaIso R A P f hf m o hAR ⟨q0Alg R A P f hf m o (g : P), hmem⟩
      = otilde R A P f hf o g := by
  rw [thetaIso, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  apply Subtype.ext
  show Ideal.Quotient.mk (Kideal R A P f hf m o)
      (TrivSqZeroExt.inl (ibar R A P f m (g : P)))
    = Ideal.Quotient.mk (Kideal R A P f hf m o)
      (TrivSqZeroExt.inr (otilde R A P f hf o g))
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨g, rfl⟩

end WithO
end S1Construct
end S1Construct

/-- **(S1, construction GIVEN the Artin–Rees truncation level `m`).** The genuine cocycle-twisted
quotient construction `B'_o = (TrivSqZeroExt P̄_m κ)/K`, `K = ⟨(ī, -õ(i)) : i ∈ ker f⟩`, where
`P̄_m = P/𝔪_P^{m+1}` (`𝔪_P = (maximalIdeal A).comap f`). The truncation level `m` is provided
together with the Artin–Rees non-degeneracy hypothesis `hAR : ker f ⊓ 𝔪_P^{m+1} ≤ 𝔪_P • ker f`,
which is exactly what makes `K ∩ inr(κ) = ⊥` (hence `ker φ ≅ κ` of length 1, not 0) hold for the
given `o`.

This is the residual RingTheory content of S1, the Artin–Rees `m`-choice having been peeled off
into `artinRees_inf_pow_le_smul`).  Outline:
* `õ : ker f → κ` via `Ideal.Cotangent.lift (o ∘ Cotangent.of)` — `P`-linear, kills `I²` and
`𝔪_P·I`;
* `Ā := A/𝔪_A^{m+1}`, `P̄ := P/𝔪_P^{m+1}` (Artinian local via nilpotent maximal ideal), `P̄ ↠ Ā`;
* `T := TrivSqZeroExt P̄ κ`; `K := ` ideal gen by `{(ī,-õ i):i∈ker f}` (= the graph, already an
ideal
  since `ī` acts as 0 on κ and `õ` is `P`-linear — step (I)); `B'_o := T/K`;
* (II) `K ∩ inr(κ) = ⊥` from `hAR` ⟹ `θ : ker φ ≃ κ`, length 1;
* (III)–(V) `φ` surjective, `(ker φ)²=⊥`, locality+Artinian of `B'_o`, `q₀(g)=[(ḡ,0)]`, defect (★).
-/
theorem algLifts_classifyingExt_construct
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [IsNoetherianRing A]
    (P : Type u) [CommRing P] [Algebra R P] [IsNoetherianRing P]
    (f : P →ₐ[R] A) (hf : Function.Surjective f)
    (o : letI : Algebra (P) A := f.toRingHom.toAlgebra
      (Algebra.Extension.ofSurjective f hf).Cotangent →ₗ[A] IsLocalRing.ResidueField A)
    (m : ℕ)
    (hAR : (RingHom.ker f.toRingHom) ⊓
        ((IsLocalRing.maximalIdeal A).comap f.toRingHom) ^ (m + 1)
        ≤ (((IsLocalRing.maximalIdeal A).comap f.toRingHom) • (RingHom.ker f.toRingHom)
            : Ideal (P))) :
    letI : Algebra (P) A := f.toRingHom.toAlgebra
    ∃ (B' B : Type u) (_ : CommRing B') (_ : CommRing B)
      (_ : Algebra R B') (_ : Algebra R B)
      (_ : IsLocalRing B') (_ : IsLocalRing B)
      (_ : IsArtinianRing B') (_ : IsArtinianRing B)
      (φ : B' →ₐ[R] B) (_ : Function.Surjective φ)
      (_ : (RingHom.ker φ.toRingHom) ^ 2 = ⊥)
      (_ : Module.length B' (RingHom.ker φ.toRingHom) = 1)
      (a : A →ₐ[R] B)
      (q₀ : P →ₐ[R] B'),
        Function.Surjective a ∧
        φ.toRingHom.comp q₀.toRingHom = a.toRingHom.comp f.toRingHom ∧
        ∃ θ : (RingHom.ker φ.toRingHom) ≃ₗ[R] IsLocalRing.ResidueField A,
          ∀ g : (RingHom.ker f.toRingHom),
            (hmem : q₀ (g : P) ∈ RingHom.ker φ.toRingHom) →
              θ ⟨q₀ (g : P), hmem⟩
                = o (Algebra.Extension.Cotangent.of
                    ((Ideal.toCotangent (RingHom.ker f.toRingHom)) g)) := by
  -- The cocycle-twisted quotient construction, with the
  -- Artin–Rees non-degeneracy now available as `hAR`. The genuine remaining RingTheory atom.
  let : Algebra (P) A := f.toRingHom.toAlgebra
  refine ⟨S1Construct.Bo R A P f hf m o, S1Construct.Abar A m, inferInstance, inferInstance,
    inferInstance, inferInstance,
    S1Construct.isLocalRing_Bo R A P f hf m o, ?_,
    S1Construct.isArtinianRing_Bo R A P f hf m o, ?_,
    S1Construct.phiAlg R A P f hf m o, S1Construct.phiAlg_surjective R A P f hf m o,
    ?_, ?_, S1Construct.aMap R A m, S1Construct.q0Alg R A P f hf m o,
    ?_, ?_, S1Construct.thetaIso R A P f hf m o hAR, ?_⟩
  · exact S1Construct.isLocalRing_Abar A m
  · exact S1Construct.isArtinianRing_Abar A m
  · exact S1Construct.phiAlg_ker_sq R A P f hf m o
  · exact S1Construct.phiAlg_ker_length R A P f hf m o hAR
  · exact Ideal.Quotient.mkₐ_surjective R _
  · exact S1Construct.phi_comp_q0 R A P f hf m o
  · intro g hmem
    exact S1Construct.defect_link R A P f hf m o hAR g hmem

/-- The classifying small extension of a functional `o` on the cotangent module, in enriched
form: the extension together with a reference lift `q₀`, the isomorphism `θ : ker φ ≃ₗ κ`, and
the defect link `θ (q₀ g) = o [g]`. -/
theorem algLifts_classifyingExt_enriched
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [IsNoetherianRing A]
    (P : Type u) [CommRing P] [Algebra R P] [IsNoetherianRing P]
    (f : P →ₐ[R] A) (hf : Function.Surjective f)
    (o : letI : Algebra (P) A := f.toRingHom.toAlgebra
      (Algebra.Extension.ofSurjective f hf).Cotangent →ₗ[A] IsLocalRing.ResidueField A) :
    letI : Algebra (P) A := f.toRingHom.toAlgebra
    ∃ (B' B : Type u) (_ : CommRing B') (_ : CommRing B)
      (_ : Algebra R B') (_ : Algebra R B)
      (_ : IsLocalRing B') (_ : IsLocalRing B)
      (_ : IsArtinianRing B') (_ : IsArtinianRing B)
      (φ : B' →ₐ[R] B) (_ : Function.Surjective φ)
      (_ : (RingHom.ker φ.toRingHom) ^ 2 = ⊥)
      (_ : Module.length B' (RingHom.ker φ.toRingHom) = 1)
      (a : A →ₐ[R] B)
      (q₀ : P →ₐ[R] B'),
        Function.Surjective a ∧
        φ.toRingHom.comp q₀.toRingHom = a.toRingHom.comp f.toRingHom ∧
        ∃ θ : (RingHom.ker φ.toRingHom) ≃ₗ[R] IsLocalRing.ResidueField A,
          ∀ g : (RingHom.ker f.toRingHom),
            (hmem : q₀ (g : P) ∈ RingHom.ker φ.toRingHom) →
              θ ⟨q₀ (g : P), hmem⟩
                = o (Algebra.Extension.Cotangent.of
                    ((Ideal.toCotangent (RingHom.ker f.toRingHom)) g)) := by
  -- DECOMPOSITION (forward progress): the Artin–Rees `m`-choice is now discharged by the
  -- fully-proven
  -- `artinRees_inf_pow_le_smul`; the residual genuine construction (given `m` + the AR bound) is
  -- delegated to `algLifts_classifyingExt_construct`. `P` is Noetherian (R
  -- Noetherian local), so Artin–Rees applies with `𝔪_P = (maximalIdeal A).comap f`, `I = ker f`.
  let : Algebra (P) A := f.toRingHom.toAlgebra
  obtain ⟨m, _, hAR⟩ := artinRees_inf_pow_le_smul (P)
    ((IsLocalRing.maximalIdeal A).comap f.toRingHom) (RingHom.ker f.toRingHom)
  exact algLifts_classifyingExt_construct R A P f hf o m hAR

/-- Every functional `o` on the cotangent module of a surjective presentation `f : P ↠ A` is
classified by a residually trivial length-one square-zero small extension, with a reference
lift and a defect link identifying `o`.  The truncation level is supplied by Artin–Rees. -/
alias algLifts_classifyingExt := InfinitesimalLifting.algLifts_classifyingExt_enriched

/-- **(S2) The classifying square-zero extension produces the realizing derivation.**
Construction half of the Stacks 02HT obstruction atom. For the fixed finite presentation
`P := Algebra.Extension.ofSurjective f hf` and an `A`-linear cocycle
`o : P.Cotangent →ₗ[A] κ` (κ = `IsLocalRing.ResidueField A`):

* (S1) build the residually-trivial length-one square-zero small extension `B'_o` classified by
  `o` — concretely the *trivial* square-zero extension `TrivSqZeroExt (A/𝔪^{m+1}) κ` (via
  `TrivSqZeroExt.liftEquivOfComm`) whose `P.Ring`-algebra structure is twisted by the `R[x]`-linear
  cocycle `õ : I → κ` lifted from `o` through `Ideal.Cotangent.lift`. The kernel is `κ`
  (length one — `o` is `A`-linear into `κ`, so `𝔪_A·I` is killed), square-zero, residually trivial;
  `B'_o` and `A/𝔪^{m+1}` are local Artinian `R`-algebras (`A` Noetherian local);
* (S3) check those properties satisfy the hypotheses of `AlgLiftsResTrivSmall` and apply `h` to the
  quotient map `a : A → A/𝔪^{m+1}`, obtaining a lift `c : A →ₐ[R] B'_o`;
* convert `c` to a derivation `δ₀` (`Algebra.derivationToSquareZeroOfLift`, relative to the
  tautological reference lift `P.Ring → B'_o`) and transport across `ker φ_o ≅ κ` to the induced
  `A`-linear `δ : P.CotangentSpace →ₗ[A] κ` with `o = δ ∘ₗ P.cotangentComplex`.

Choosing `M = κ` and `B = A/𝔪^{m+1}` works, and
leaves as the only remaining step the final identity — sub-lemma S2, the
`derivationToSquareZeroOfLift`-versus-`cotangentComplex` naturality and normalization — which is
folded in here.  This is the André–Quillen development proper.  Relevant API:
`TrivSqZeroExt.liftEquivOfComm`,
`Ideal.Cotangent.lift` (`lift_toCotangent`, `lift_comp_toCotangent`),
`Algebra.derivationToSquareZeroOfLift` (`_apply`), `Algebra.derivationToSquareZeroEquivLift`,
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`. -/
theorem algLifts_classifying_derivation
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [IsNoetherianRing A]
    (h : AlgLiftsResTrivSmall R A)
    (P : Type u) [CommRing P] [Algebra R P] [IsNoetherianRing P]
    (f : P →ₐ[R] A) (hf : Function.Surjective f)
    (o : letI : Algebra (P) A := f.toRingHom.toAlgebra
      (Algebra.Extension.ofSurjective f hf).Cotangent →ₗ[A] IsLocalRing.ResidueField A) :
    letI : Algebra (P) A := f.toRingHom.toAlgebra
    haveI : IsScalarTower R (P) A :=
      IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
    ∃ δ : (Algebra.Extension.ofSurjective f hf).CotangentSpace →ₗ[A] IsLocalRing.ResidueField A,
      o = δ ∘ₗ (Algebra.Extension.ofSurjective f hf).cotangentComplex := by
  -- `algLifts_classifyingExt` (S1), fed to `h` (S3), yields the lift `c`, and then
  -- `derivationToSquareZeroOfLift` together with the naturality identity (S2) yields the
  -- realizing derivation; this is the Lichtenbaum–Schlessinger T¹ vanishing.
  let : Algebra (P) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (P) A :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  -- (S1) Build the classifying residually-trivial length-one square-zero small extension `B'_o`
  -- classified by `o` (a cocycle-twisted quotient), with the reference `R[x]`-algebra lift
  -- `q₀` of `a ∘ f`, the κ-iso `θ : ker φ ≃ₗ[R] κ`, and the defect link `hstar` (★):
  -- `θ (q₀ g) = o ([g])` for every `g ∈ ker f`.  The link `hstar` is exactly what lets the
  -- derivation built from the `h`-lift realize `o`; without it, S2 would be unprovable.
  obtain ⟨B', B, _, _, _, _, _, _, _, _, φ, hφ, hsq, hlen, a, q₀, ha_surj, hq₀, θ, hstar⟩ :=
    algLifts_classifyingExt R A P f hf o
  -- (S3) Feed the small-extension data to `h`, lifting the truncation `a : A → B = A/𝔪^{m+1}`,
  -- obtaining `c : A →ₐ[R] B'` with `φ ∘ c = a`.
  obtain ⟨c, hc⟩ := h B' B φ hφ hsq hlen a ha_surj
  -- (S2) Convert `c`, relative to the reference lift `q₀`, to a derivation via
  -- `Algebra.derivationToSquareZeroOfLift`, transport across `θ : ker φ ≃ₗ[R] κ`, and prove
  -- the naturality identity `o = δ ∘ₗ d` against `Algebra.Extension.cotangentComplex`.  Here
  -- `Δ := q₀ − c∘f : P → ker φ` is an R-derivation, being the difference of two lifts of
  -- `a∘f` across the square-zero `ker φ`; `θ∘Δ` evaluated on `g ∈ ker f` equals
  -- `θ (q₀ g) = o([g])` by `hstar`, since `(c∘f) g = c 0 = 0`, and also equals `±δ(d[g])`;
  -- orienting `Δ` to fix the sign gives `o = δ ∘ₗ d`.  The factorization of `δ` through
  -- `CotangentSpace` uses
  -- `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`.  This is the
  -- André–Quillen / Lichtenbaum–Schlessinger step.
  -- Step 1: algebra structure on B' over P.Ring via q₀
  let : Algebra (P) B' := q₀.toRingHom.toAlgebra
  have : IsScalarTower R (P) B' :=
    IsScalarTower.of_algebraMap_eq (fun r => (q₀.commutes r).symm)
  -- Step 2: the lift condition for c ∘ f relative to ker φ
  have e : (Ideal.Quotient.mkₐ R (RingHom.ker φ.toRingHom)).comp (c.comp f) =
      IsScalarTower.toAlgHom R (P) (B' ⧸ RingHom.ker φ.toRingHom) := by
    apply AlgHom.ext
    intro p
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    show Ideal.Quotient.mk _ (c (f p)) = _
    have hrhs : (algebraMap (P) (B' ⧸ RingHom.ker φ.toRingHom)) p
        = Ideal.Quotient.mk _ (q₀ p) := by
      rw [IsScalarTower.algebraMap_apply (P) B' (B' ⧸ RingHom.ker φ.toRingHom)]
      rfl
    rw [hrhs, Ideal.Quotient.eq]
    rw [RingHom.sub_mem_ker_iff]
    have h1 : φ (c (f p)) = a (f p) := by
      simpa using AlgHom.congr_fun hc (f p)
    have h2 : φ (q₀ p) = a (f p) := by
      simpa using RingHom.congr_fun hq₀ p
    show φ.toRingHom (c (f p)) = φ.toRingHom (q₀ p)
    rw [show φ.toRingHom (c (f p)) = φ (c (f p)) from rfl,
        show φ.toRingHom (q₀ p) = φ (q₀ p) from rfl, h1, h2]
  -- A-module structure on B' via c
  let : Algebra A B' := c.toRingHom.toAlgebra
  have htAc : IsScalarTower R A B' :=
    IsScalarTower.of_algebraMap_eq (fun r => (c.commutes r).symm)
  -- key: φ (q₀ g) = 0 for g ∈ ker f  (membership)
  have hmem0 : ∀ g : (RingHom.ker f.toRingHom), q₀ (g : P) ∈ RingHom.ker φ.toRingHom := by
    intro g
    have h2 : φ (q₀ (g:_)) = a (f (g:_)) := by
      simpa using RingHom.congr_fun hq₀ (g:_)
    have hg : f (g : P) = 0 := g.property
    rw [RingHom.mem_ker]
    rw [show φ.toRingHom (q₀ (g:_)) = φ (q₀ (g:_)) from rfl, h2, hg, map_zero]
  -- Case split on whether o is the zero functional.
  by_cases ho : o = 0
  · -- o = 0: the zero map δ = 0 works.
    refine ⟨0, ?_⟩
    rw [ho]
    ext x
    simp
  · -- o ≠ 0.  κ is a simple A-module, so range o = ⊤, giving surjectivity of q₀|ker f onto ker φ.
    have hsimp : IsSimpleModule A (IsLocalRing.ResidueField A) :=
      (isSimpleModule_iff_isCoatom).mpr (IsLocalRing.maximalIdeal.isMaximal A).out
    have hrange : LinearMap.range o = ⊤ := by
      rcases (IsSimpleModule.toIsSimpleOrder (R := A)).eq_bot_or_eq_top (LinearMap.range o) with h
          | h
      · exact absurd (LinearMap.range_eq_bot.mp h) ho
      · exact h
    -- q₀ surjects ker f onto ker φ
    have hsurj : ∀ x : ↥(RingHom.ker φ.toRingHom), ∃ g : (RingHom.ker f.toRingHom),
        (q₀ (g : P)) = (x : B') := by
      intro x
      obtain ⟨ξ, hξ⟩ : θ x ∈ LinearMap.range o := by
        rw [hrange]
        trivial
      obtain ⟨g0, hg0⟩ := Algebra.Extension.Cotangent.mk_surjective ξ
      let g : (RingHom.ker f.toRingHom) := ⟨g0.val, g0.property⟩
      refine ⟨g, ?_⟩
      have hθg : θ ⟨q₀ (g:_), hmem0 g⟩ = θ x := by
        rw [hstar g (hmem0 g)]
        have hofg : (Algebra.Extension.Cotangent.of
            ((Ideal.toCotangent (RingHom.ker f.toRingHom)) g)
            : (Algebra.Extension.ofSurjective f hf).Cotangent)
            = ξ := hg0
        rw [hofg, hξ]
      exact congrArg Subtype.val (θ.injective hθg)
    -- θ is P.Ring-linear  (key compatibility, via hsurj + P.Ring-linearity of `mk` and o)
    have hlin : ∀ (p : P) (x : ↥(RingHom.ker φ.toRingHom)),
        θ (p • x) = (algebraMap (P) A p) • θ x := by
      intro p x
      obtain ⟨g, hg⟩ := hsurj x
      have hpg : ((p • x : ↥(RingHom.ker φ.toRingHom)) : B') = q₀ (p * (g : P)) := by
        show algebraMap (P) B' p * (x : B') = _
        rw [show algebraMap (P) B' p = q₀ p from rfl, ← hg, ← map_mul]
      have hpgker : p * (g : P) ∈ RingHom.ker f.toRingHom := by
        rw [RingHom.mem_ker]
        rw [show f.toRingHom (p * (g:_)) = f (p * (g:_)) from rfl, map_mul]
        have : f (g : P) = 0 := g.property
        rw [this, mul_zero]
      let pg : (RingHom.ker f.toRingHom) := ⟨p * (g : P), hpgker⟩
      have hθpx : θ (p • x) = o (Algebra.Extension.Cotangent.of
          ((Ideal.toCotangent (RingHom.ker f.toRingHom)) pg)) := by
        have hmempg : q₀ (pg : P) ∈ RingHom.ker φ.toRingHom := hmem0 pg
        have hpxval : (p • x : ↥(RingHom.ker φ.toRingHom)) = ⟨q₀ (pg:_), hmempg⟩ :=
          Subtype.ext hpg
        rw [hpxval, hstar pg hmempg]
      -- θ x via hstar on g
      have hθx : θ x = o (Algebra.Extension.Cotangent.of
          ((Ideal.toCotangent (RingHom.ker f.toRingHom)) g)) := by
        have hmemg : q₀ (g : P) ∈ RingHom.ker φ.toRingHom := hmem0 g
        have hxval : x = ⟨q₀ (g:_), hmemg⟩ := Subtype.ext hg.symm
        rw [hxval, hstar g hmemg]
      rw [hθpx, hθx]
      show o (Algebra.Extension.Cotangent.mk pg) = (algebraMap (P) A p) •
        o (Algebra.Extension.Cotangent.mk g)
      have hmkpg : (Algebra.Extension.Cotangent.mk pg : (Algebra.Extension.ofSurjective f
          hf).Cotangent)
          = p • Algebra.Extension.Cotangent.mk g := by
        have hpgg : pg = p • g := Subtype.ext rfl
        rw [hpgg]; exact map_smul _ p g
      rw [hmkpg]
      rw [show (p • Algebra.Extension.Cotangent.mk g
            : (Algebra.Extension.ofSurjective f hf).Cotangent)
          = (algebraMap (P) A p) • Algebra.Extension.Cotangent.mk g from
          (algebraMap_smul A p _).symm]
      rw [map_smul]
    -- Bundle θ as a P.Ring-linear map  Θ : ker φ →ₗ[P.Ring] κ
    let Θ : ↥(RingHom.ker φ.toRingHom) →ₗ[P] IsLocalRing.ResidueField A :=
      { toFun := fun x => θ x
        map_add' := fun x y => by exact map_add θ x y
        map_smul' := fun p x => by
          simp only [RingHom.id_apply]
          rw [hlin p x, algebraMap_smul] }
    -- difference derivation Δ : Derivation R P.Ring (ker φ)
    let Δ : Derivation R (P) ↥(RingHom.ker φ.toRingHom) :=
      derivationToSquareZeroOfLift (RingHom.ker φ.toRingHom) hsq (c.comp f) e
    -- realizing derivation D := -(Θ ∘ Δ) : Derivation R P.Ring κ
    let D : Derivation R (P) (IsLocalRing.ResidueField A) :=
      -(Θ.compDer Δ)
    refine ⟨(D.liftKaehlerDifferential).liftBaseChange A, ?_⟩
    apply LinearMap.ext
    intro z
    obtain ⟨g0, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    show o (Algebra.Extension.Cotangent.mk g0)
        = (D.liftKaehlerDifferential).liftBaseChange A
            ((Algebra.Extension.ofSurjective f hf).cotangentComplex
              (Algebra.Extension.Cotangent.mk g0))
    rw [Algebra.Extension.cotangentComplex_mk]
    erw [LinearMap.liftBaseChange_tmul]
    rw [one_smul]
    erw [Derivation.liftKaehlerDifferential_comp_D]
    set y : P := g0.val with hy
    symm
    show (-(Θ.compDer Δ)) y = o (Algebra.Extension.Cotangent.mk g0)
    rw [Derivation.neg_apply]
    show -(Θ (Δ y)) = o (Algebra.Extension.Cotangent.mk g0)
    have hfy : f y = 0 := g0.property
    have hΔ : (Δ y : B') = - q₀ y := by
      show ((derivationToSquareZeroOfLift (RingHom.ker φ.toRingHom) hsq (c.comp f) e) y : B') = _
      rw [derivationToSquareZeroOfLift_apply]
      show (c.comp f) y - q₀ y = _
      simp only [AlgHom.comp_apply, hfy, map_zero, zero_sub]
    have hg0mem : q₀ y ∈ RingHom.ker φ.toRingHom := hmem0 ⟨y, g0.property⟩
    have hΔeq : Δ y = - ⟨q₀ y, hg0mem⟩ := by
      apply Subtype.ext
      rw [hΔ]; rfl
    rw [hΔeq, map_neg, neg_neg]
    show θ ⟨q₀ y, hg0mem⟩ = o (Algebra.Extension.Cotangent.mk g0)
    exact hstar ⟨y, g0.property⟩ hg0mem

/-- **Stacks 02HT obstruction-in-image (assembly).** Every `A`-linear functional `o` on the
conormal module `P.Cotangent` of the fixed finite presentation factors through the
cotangent-complex map `d = P.cotangentComplex` — the André–Quillen / Lichtenbaum–Schlessinger
T¹-vanishing forced by the residually-trivial small-extension lifting hypothesis `h`.

Mechanical assembly: the `∀ o` quantifier is discharged per-cocycle by
`algLifts_classifying_derivation` (which bundles the `B'_o` construction, the `h`-lift, and the
factorization identity). -/
theorem algLifts_obstruction_in_image
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [IsNoetherianRing A]
    (h : AlgLiftsResTrivSmall R A)
    (P : Type u) [CommRing P] [Algebra R P] [IsNoetherianRing P]
    (f : P →ₐ[R] A) (hf : Function.Surjective f) :
    letI : Algebra (P) A := f.toRingHom.toAlgebra
    haveI : IsScalarTower R (P) A :=
      IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
    ∀ o : (Algebra.Extension.ofSurjective f hf).Cotangent →ₗ[A] IsLocalRing.ResidueField A,
      ∃ δ : (Algebra.Extension.ofSurjective f hf).CotangentSpace →ₗ[A] IsLocalRing.ResidueField A,
        o = δ ∘ₗ (Algebra.Extension.ofSurjective f hf).cotangentComplex := by
  -- The κ-cocycle is unobstructed, hence in the image of dᵛ; this is exactly the
  -- Lichtenbaum–Schlessinger T¹ vanishing forced by lifting against small extensions.
  -- Mechanical assembly: per-cocycle delegation to the construction+identity bundle.
  intro o
  exact algLifts_classifying_derivation R A h P f hf o

/-- If every `A`-linear functional `M → κ` factors through `d : M → N`, then `d ⊗ κ` is injective
(duality over the residue field `κ`). -/
private theorem lTensor_residueField_injective_of_forall_factor {A : Type u} [CommRing A]
    [IsLocalRing A] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (d : M →ₗ[A] N)
    (atom : ∀ o : M →ₗ[A] IsLocalRing.ResidueField A,
      ∃ δ : N →ₗ[A] IsLocalRing.ResidueField A, o = δ ∘ₗ d) :
    Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField A) d) := by
  set κ := IsLocalRing.ResidueField A with hκ
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [← Module.forall_dual_apply_eq_zero_iff κ z]
  intro μ
  set o : M →ₗ[A] κ := (μ.restrictScalars A) ∘ₗ TensorProduct.mk A κ M 1 with ho
  obtain ⟨δ, hδ⟩ := atom o
  have hμ : μ = LinearMap.liftBaseChange κ o := by
    apply LinearMap.ext
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      have hsm : (TensorProduct.tmul A a m : TensorProduct A κ M)
          = a • TensorProduct.tmul A (1 : κ) m := by
        rw [TensorProduct.smul_tmul']; simp
      rw [hsm, map_smul, map_smul, LinearMap.liftBaseChange_tmul, ho,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
        TensorProduct.mk_apply, one_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hfunc : (LinearMap.liftBaseChange κ (δ ∘ₗ d)).restrictScalars A
      = ((LinearMap.liftBaseChange κ δ).restrictScalars A) ∘ₗ (LinearMap.lTensor κ d) := by
    apply TensorProduct.ext'
    intro a m
    simp [LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul]
  have hval : μ z = (LinearMap.liftBaseChange κ δ) ((LinearMap.lTensor κ d) z) := by
    rw [hμ, hδ]
    have := LinearMap.congr_fun hfunc z
    simpa using this
  rw [hval, hz, map_zero]

/-- **The κ-injectivity of the conormal map, derived from the obstruction-in-image atom by
duality over the residue field κ.** From `algLifts_obstruction_in_image` (every `A`-linear
κ-functional on `P.Cotangent` factors through `d`) one obtains injectivity of the residue-field
base change `d ⊗ κ` by a clean linear-algebra duality argument over the *field* κ: a nonzero
kernel class of `d ⊗ κ` would be detected by some κ-functional, which by the atom factors through
`d` and hence vanishes on the kernel — contradiction. Over the field κ, `Hom(-, κ)`-surjectivity
is equivalent to injectivity. This duality step is mechanical (finite-dimensional κ-vector
spaces, `P.Cotangent` finite over `A`), isolated here so the assembly verifies; it remains to be
filled. -/
theorem cotangentComplex_lTensorResidueField_injective_of_algLifts
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [Algebra.FinitePresentation R A]
    (h : AlgLiftsResTrivSmall R A)
    (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG) :
    letI : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin n) R) A :=
      IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
    Function.Injective ⇑(LinearMap.lTensor (IsLocalRing.ResidueField A)
      (Algebra.Extension.ofSurjective f hf).cotangentComplex) := by
  -- κ-injectivity of d follows from obstruction-in-image by κ-duality over the field κ.
  let : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hfin : Module.Finite A (Algebra.Extension.ofSurjective f hf).Cotangent :=
    Algebra.Extension.Cotangent.finite hker
  exact lTensor_residueField_injective_of_forall_factor _
    (algLifts_obstruction_in_image R A h (MvPolynomial (Fin n) R) f hf)

/-- The conormal map of a finite presentation of a local algebra splits if and only if its base
change to the residue field is injective. -/
private theorem split_iff_lTensor_cotangentComplex_injective
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG) :
    letI : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin n) R) A :=
      IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
    (∃ l' : (Algebra.Extension.ofSurjective f hf).CotangentSpace →ₗ[A]
        (Algebra.Extension.ofSurjective f hf).Cotangent,
      l' ∘ₗ (Algebra.Extension.ofSurjective f hf).cotangentComplex = LinearMap.id) ↔
    Function.Injective ⇑(LinearMap.lTensor (IsLocalRing.ResidueField A)
      (Algebra.Extension.ofSurjective f hf).cotangentComplex) := by
  let : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  set P := Algebra.Extension.ofSurjective f hf with hP
  have hfin : Module.Finite A P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) hker
  have hfreeCS : Module.Free A P.CotangentSpace := by
    show Module.Free A (TensorProduct (MvPolynomial (Fin n) R) A
      (KaehlerDifferential R (MvPolynomial (Fin n) R)))
    infer_instance
  have hfinCS : Module.Finite A P.CotangentSpace := by
    show Module.Finite A (TensorProduct (MvPolynomial (Fin n) R) A
      (KaehlerDifferential R (MvPolynomial (Fin n) R)))
    infer_instance
  exact IsLocalRing.split_injective_iff_lTensor_residueField_injective P.cotangentComplex

/-- If `A` lifts against residually trivial small extensions, then the cotangent complex of a
finite presentation of `A` splits. -/
@[ega "0 20.5.14" "special case", ega "IV 17.2.5" "partial"]
theorem cotangentComplex_split_of_algLifts
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [Algebra.FinitePresentation R A]
    (h : AlgLiftsResTrivSmall R A)
    (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG) :
    letI : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin n) R) A :=
      IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
    ∃ l' : (Algebra.Extension.ofSurjective f hf).CotangentSpace →ₗ[A]
        (Algebra.Extension.ofSurjective f hf).Cotangent,
      l' ∘ₗ (Algebra.Extension.ofSurjective f hf).cotangentComplex = LinearMap.id := by
  -- retraction form; under `h` formal smoothness ⇒ the conormal map splits over the local A; no
  -- counterexample — split-injectivity is equivalent to the κ-injectivity below via
  -- `IsLocalRing.split_injective_iff_lTensor_residueField_injective`).
  -- `P.Cotangent` is finite over `A` by `hker` and `P.CotangentSpace` is finite and free over
  -- `A`, so the local-ring bridge turns the κ-injectivity of `d`
  -- (`cotangentComplex_lTensorResidueField_injective_of_algLifts`) into the existence of the
  -- A-linear retraction.  That κ-injectivity is itself reduced, by κ-duality, to
  -- `algLifts_obstruction_in_image`.
  let : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  exact (split_iff_lTensor_cotangentComplex_injective R A n f hf hker).mpr
    (cotangentComplex_lTensorResidueField_injective_of_algLifts R A h n f hf hker)

/-- If `A` lifts against residually trivial small extensions, then the conormal map stays
injective after base change to the residue field. -/
theorem conormal_baseChange_residueField_injective_of_algLifts
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [Algebra.FinitePresentation R A]
    (h : AlgLiftsResTrivSmall R A)
    (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG) :
    letI : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin n) R) A :=
      IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
    Function.Injective ⇑((Algebra.Extension.ofSurjective f hf).cotangentComplex.baseChange
      (IsLocalRing.ResidueField A)) := by
  -- direction matches Mathlib's iff_injective_cotangentComplexBaseChange_residueField; all
  -- degenerate edge cases make injectivity vacuously true or A genuinely formally smooth; no
  -- counterexample).
  -- The conormal map `P.cotangentComplex` is finite
  -- (source, via `Cotangent.finite hker`) into a finite free module (`CotangentSpace = A ⊗_P Ω`,
  -- Ω free over the polynomial ring P), so over the local ring A,
  -- `IsLocalRing.split_injective_iff_lTensor_residueField_injective` turns the κ-base-change
  -- injectivity into the existence of an A-linear retraction of `P.cotangentComplex` — exactly
  -- `cotangentComplex_split_of_algLifts` (the isolated Stacks 02HT Step-3 obstruction core).
  let : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  exact (split_iff_lTensor_cotangentComplex_injective R A n f hf hker).mp
    (cotangentComplex_split_of_algLifts R A h n f hf hker)

/-- If `A` lifts against residually trivial small extensions, then the base change of the
cotangent complex to the residue field is injective. -/
theorem residueField_cotangentComplexBaseChange_injective_of_algLifts
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [Algebra.FinitePresentation R A]
    (h : AlgLiftsResTrivSmall R A)
    (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG) :
    letI : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
    Function.Injective ⇑(KaehlerDifferential.cotangentComplexBaseChange R A
      (MvPolynomial (Fin n) R) (IsLocalRing.ResidueField A)) := by
  -- This is exactly the right-hand side of
  -- `iff_injective_cotangentComplexBaseChange_residueField`; by
  -- `Algebra.Extension.cotangentComplexBaseChange_eq_lTensor_cotangentComplex`, the κ-tensored
  -- `cotangentComplexBaseChange` equals (linear iso) ∘ `P.cotangentComplex.baseChange κ` ∘
  -- (linear iso) for `P := Algebra.Extension.ofSurjective f hf`; injectivity therefore follows
  -- from injectivity of the middle map, which is the isolated obstruction core
  -- `conormal_baseChange_residueField_injective_of_algLifts`.
  let : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  have core := conormal_baseChange_residueField_injective_of_algLifts R A h n f hf hker
  show Function.Injective ⇑(KaehlerDifferential.cotangentComplexBaseChange R A
      (Algebra.Extension.ofSurjective f hf).Ring (IsLocalRing.ResidueField A))
  rw [Algebra.Extension.cotangentComplexBaseChange_eq_lTensor_cotangentComplex
      (R := R) (S := A) (P := Algebra.Extension.ofSurjective f hf) (A := IsLocalRing.ResidueField
          A)]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (LinearEquiv.injective _).comp (core.comp (LinearEquiv.injective _))

/-- A finitely presented local algebra that lifts against residually trivial small extensions
is formally smooth. -/
@[ega "0 22.1.4" "special case",
  sga "1 III 2.1" "special case",
  sga "1 III 2.2" "(i), special case"]
theorem formallySmooth_of_algLifts (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [Algebra.FinitePresentation R A]
    (h : AlgLiftsResTrivSmall R A) :
    Algebra.FormallySmooth R A := by
  -- The Artinian length-one dévissage is the standard reduction: pick a finite presentation
  -- `f : R[x₁..xₙ] ↠ A` (`Algebra.FinitePresentation.out`); `P = MvPolynomial (Fin n) R`
  -- is formally smooth over R with Ω free+finite; the residue-field cotangent criterion
  -- `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField` reduces
  -- `FormallySmooth R A` to injectivity of `cotangentComplexBaseChange R A P κ(A)`, which
  -- is exactly `residueField_cotangentComplexBaseChange_injective_of_algLifts` (the 02HT core).
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  let : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have halg : (algebraMap (MvPolynomial (Fin n) R) A) = f.toRingHom := rfl
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
    (MvPolynomial (Fin n) R) (by rwa [halg]) (by rwa [halg])]
  exact residueField_cotangentComplexBaseChange_injective_of_algLifts R A h n f hf hker

/-- **A finite formally-smooth presentation of `A` over `R`.** Bundles a (not necessarily
polynomial) `R`-algebra `Ring` that is formally smooth over `R`, has free + finite Kähler
differentials, and surjects onto `A` with a finitely generated kernel. This is precisely the
input the local residue-field criterion
`Algebra.FormallySmooth.iff_injective_lTensor_residueField` consumes — it needs only these
properties, NOT that `Ring` is a polynomial ring nor that `A` is of finite presentation. For an
`EssFiniteType` `A` such a presentation exists as a LOCALIZED polynomial ring `(MvPolynomial (Fin
n) R)_W`. -/
structure FinFSPresentation (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] where
  /-- The presenting `R`-algebra `P`. -/
  Ring : Type u
  /-- The commutative ring structure on `Ring`. -/
  commRing : CommRing Ring
  /-- The `R`-algebra structure on `Ring`. -/
  algRP : Algebra R Ring
  /-- The `Ring`-algebra structure on `A`. -/
  algPA : Algebra Ring A
  /-- The algebra structures form a scalar tower `R → Ring → A`. -/
  tower : IsScalarTower R Ring A
  /-- `Ring` is formally smooth over `R`. -/
  fs : Algebra.FormallySmooth R Ring
  /-- The module of Kähler differentials `Ω[Ring⁄R]` is free. -/
  free : Module.Free Ring (Ω[Ring⁄R])
  /-- The module of Kähler differentials `Ω[Ring⁄R]` is finite. -/
  fin : Module.Finite Ring (Ω[Ring⁄R])
  /-- `Ring` is Noetherian. -/
  noeth : IsNoetherianRing Ring
  /-- The algebra map `Ring → A` is surjective. -/
  surj : Function.Surjective (algebraMap Ring A)
  /-- The kernel of `Ring → A` is finitely generated. -/
  kerFG : (RingHom.ker (algebraMap Ring A)).FG

attribute [instance] FinFSPresentation.commRing FinFSPresentation.algRP
  FinFSPresentation.algPA FinFSPresentation.tower FinFSPresentation.fs
  FinFSPresentation.free FinFSPresentation.fin FinFSPresentation.noeth

/- **Existence of a finite formally-smooth presentation for an EssFiniteType local algebra
(Stacks 00R2, essential finiteness).** A local `R`-algebra `A`
essentially of finite type over a Noetherian local ring `R` admits a `FinFSPresentation R A`,
realized by a LOCALIZED polynomial ring `P = (MvPolynomial (Fin n) R)_W`.

*Proof outline.* `Algebra.essFiniteType_iff_exists_subalgebra` gives a finite-type subalgebra
`A₀ ⊆ A` with `IsLocalization M A` (`M ⊆ A₀`). Surject `g : MvPolynomial (Fin n) R ↠ A₀`
(finite type); since `R` is Noetherian, `B := MvPolynomial (Fin n) R` is Noetherian, so `ker g`
is f.g. Put `W := g⁻¹(M)`; localizing `g` gives `f : P := B_W ↠ (A₀)_M = A` surjective with f.g.
kernel. `P` is formally smooth over `R` (`Algebra.FormallySmooth.mvPolynomial` +
`.of_isLocalization`/`.localization_base`); `Ω[P/R]` is free + finite (localization of the free
finite `Ω[B/R]`). This is pure `EssentialFiniteness` + localization Mathlib API. -/
/-- An essentially finite type local algebra admits a finite presentation of the shape recorded
by `FinFSPresentation`: a localized polynomial presentation with finitely generated kernel. -/
theorem exists_finFSPresentation (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [Algebra.EssFiniteType R A] :
    Nonempty (FinFSPresentation R A) := by
  set A₀ := Algebra.EssFiniteType.subalgebra R A with hA₀
  set M := Algebra.EssFiniteType.submonoid R A with hM
  have hloc : IsLocalization M A := Algebra.EssFiniteType.isLocalization R A
  have hft : Algebra.FiniteType R A₀ := inferInstance
  obtain ⟨n, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A₀)).mp hft
  set B := MvPolynomial (Fin n) R with hB
  set W : Submonoid B := M.comap g.toRingHom with hW
  have hWM : W.map g.toRingHom = M := by
    rw [hW]
    exact Submonoid.map_comap_eq_of_surjective hg M
  set P := Localization W with hP
  have hlocWA : IsLocalization (W.map g.toRingHom) A := by rwa [hWM]
  have hle : W ≤ Submonoid.comap g.toRingHom (W.map g.toRingHom) := W.le_comap_map
  set f : P →+* A := IsLocalization.map A g.toRingHom hle with hf
  let algPA : Algebra P A := f.toAlgebra
  have hsurj : Function.Surjective (algebraMap P A) :=
    IsLocalization.map_surjective_of_surjective W P A (g := g.toRingHom) hg
  have towerRPA : IsScalarTower R P A := by
    refine IsScalarTower.of_algebraMap_eq' (R := R) (S := P) (A := A) ?_
    have hcomp : (algebraMap P A).comp (algebraMap R P) = algebraMap R A := by
      ext r
      show f (algebraMap R P r) = algebraMap R A r
      rw [IsScalarTower.algebraMap_apply R B P r, hf, IsLocalization.map_eq]
      show (algebraMap A₀ A) (g (algebraMap R B r)) = algebraMap R A r
      rw [g.commutes r, ← IsScalarTower.algebraMap_apply R A₀ A r]
    exact hcomp.symm
  have fsP : Algebra.FormallySmooth R P := Algebra.FormallySmooth.instLocalization W
  have : Module.Free B (Ω[B⁄R]) := inferInstance
  have : Module.Finite B (Ω[B⁄R]) :=
    Module.Finite.of_basis (KaehlerDifferential.mvPolynomialBasis R (Fin n))
  have hlm : IsLocalizedModule W (KaehlerDifferential.map R R B P) :=
    KaehlerDifferential.isLocalizedModule_map R B P W
  have freeP : Module.Free P (Ω[P⁄R]) :=
    Module.free_of_isLocalizedModule W (KaehlerDifferential.map R R B P)
  have finP : Module.Finite P (Ω[P⁄R]) :=
    Module.Finite.of_isLocalizedModule W (KaehlerDifferential.map R R B P)
  have : IsNoetherianRing P := IsLocalization.isNoetherianRing W P inferInstance
  have hkerFG : (RingHom.ker (algebraMap P A)).FG := IsNoetherian.noetherian _
  exact ⟨{
    Ring := P
    commRing := inferInstance
    algRP := inferInstance
    algPA := algPA
    tower := towerRPA
    fs := fsP
    free := freeP
    fin := finP
    noeth := inferInstance
    surj := hsurj
    kerFG := hkerFG }⟩

/- **The presentation-agnostic obstruction atom of Stacks 02HT (generalized form).** For ANY finite
formally-smooth presentation `Pr : FinFSPresentation R A`, under the lifting hypothesis `h`, every
`A`-linear functional `o` on the conormal module `P.Cotangent` (`P = ofSurjective Pr`) factors
through the conormal-to-cotangent map `d = P.cotangentComplex` into the residue field `κ(A)`:
`∃ δ, o = δ ∘ₗ d`.  This generalizes `algLifts_obstruction_in_image`, which fixes
`P = MvPolynomial (Fin n) R` and `[FinitePresentation R A]`: the `B'_o` square-zero extension
realizing `o` is built purely from data on `A` (the functional `o`, the
local-Artinian truncation of `A`), and `Pr.Ring` enters ONLY through (P1) formal smoothness (the
lifting torsor) and (P2) `Ω` free+finite (dualization) — never the polynomial structure. Proving
this is the genuine refactor of the proven `S1Construct` chain (`algLifts_classifying_derivation`
+ `algLifts_classifyingExt`/`_enriched`/`_construct`) with `MvPolynomial (Fin n) R` replaced by the
abstract `Pr.Ring`. -/
/-- Let `A` be a local `R`-algebra over a Noetherian local ring `R` satisfying
`AlgLiftsResTrivSmall R A`, and let `Pr : FinFSPresentation R A`, with extension
`P = ofSurjective Pr`. Then every `A`-linear map `o : P.Cotangent → κ(A)` factors through the
map `P.cotangentComplex` from the conormal module to the cotangent space. -/
theorem algLifts_obstruction_in_image_general
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    (h : AlgLiftsResTrivSmall R A)
    (Pr : FinFSPresentation R A) :
    ∀ o : (Algebra.Extension.ofSurjective (S := A)
            (IsScalarTower.toAlgHom R Pr.Ring A) Pr.surj).Cotangent →ₗ[A]
            IsLocalRing.ResidueField A,
      ∃ δ : (Algebra.Extension.ofSurjective (S := A)
              (IsScalarTower.toAlgHom R Pr.Ring A) Pr.surj).CotangentSpace →ₗ[A]
              IsLocalRing.ResidueField A,
        o = δ ∘ₗ (Algebra.Extension.ofSurjective (S := A)
              (IsScalarTower.toAlgHom R Pr.Ring A) Pr.surj).cotangentComplex := by
  -- Instantiate the (now presentation-agnostic) proven obstruction atom at `P := Pr.Ring`.
  have : IsNoetherianRing A :=
    isNoetherianRing_of_surjective Pr.Ring A (algebraMap Pr.Ring A) Pr.surj
  have key := algLifts_obstruction_in_image R A h Pr.Ring
    (IsScalarTower.toAlgHom R Pr.Ring A) Pr.surj
  intro o
  exact key o

/- **The presentation-agnostic analytic core of Stacks 02HT (generalized form).** For ANY finite
formally-smooth presentation `Pr : FinFSPresentation R A` of a local `R`-algebra `A` over a
Noetherian local `R`, under the residually-trivial small-extension lifting hypothesis
`AlgLiftsResTrivSmall R A`, the residue-field base change of the conormal/cotangent map of `Pr`
is injective.

This is the GENERALIZATION (away from the `MvPolynomial`-presentation, `FinitePresentation R A`
hypotheses) of `cotangentComplex_lTensorResidueField_injective_of_algLifts`.  The obstruction
core uses the presentation `Pr.Ring` only through the
three abstract properties carried by `FinFSPresentation` — (P1) formal smoothness, (P2) `Ω`
free+finite, (P3) kernel f.g. — and never the polynomial structure: the square-zero extension is
built purely from data on `A` (the functional `o` on the conormal module + the local-Artinian
truncation of `A`); `Pr.Ring` enters only as the source of the lifting problem, where formal
smoothness supplies the lifting torsor and finiteness of `Ω` the dualization. Obtaining this is a
refactor of the existing proven chain (the whole `S1Construct` subtree + the κ-duality finish)
with `MvPolynomial (Fin n) R` replaced by the abstract `Pr.Ring`. -/
/-- Let `A` be a local `R`-algebra over a Noetherian local ring `R` satisfying
`AlgLiftsResTrivSmall R A`, and let `Pr : FinFSPresentation R A`. Then the base change to the
residue field `κ(A)` of the map from the conormal module to the cotangent space of the extension
`ofSurjective Pr` is injective. -/
theorem cotangentComplex_lTensorResidueField_injective_of_algLifts_general
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    (h : AlgLiftsResTrivSmall R A)
    (Pr : FinFSPresentation R A) :
    Function.Injective
      ⇑(LinearMap.lTensor (IsLocalRing.ResidueField A)
        (Algebra.Extension.ofSurjective (S := A)
          (IsScalarTower.toAlgHom R Pr.Ring A) Pr.surj).cotangentComplex) := by
  -- κ-injectivity of the conormal map `d` from the obstruction-in-image atom by κ-duality over the
  -- field κ. This finish is presentation-AGNOSTIC: it uses only the abstract obstruction atom
  -- `algLifts_obstruction_in_image_general` and pure linear algebra over the field κ; no
  -- finiteness of `P.Cotangent` is required, `Module.forall_dual_apply_eq_zero_iff`
  -- separating points over a field.  Verbatim transfer of the proven
  -- `cotangentComplex_lTensorResidueField_injective_of_algLifts`
  -- body with `MvPolynomial (Fin n) R` replaced by the abstract `Pr.Ring`.
  exact lTensor_residueField_injective_of_forall_factor _
    (algLifts_obstruction_in_image_general R A h Pr)

/-- **The irreducible analytic core of Stacks 02HT (= Algebra Lemma 10.141.2).**
Under the residually-trivial small-extension lifting hypothesis `h`, the stalk
algebra `A = 𝒪_{X,x}` is formally smooth over `R = 𝒪_{S,f(x)}`.

This is the genuine deformation-theoretic heart of the converse direction (4 ⇒ 1)
and is *not* available in Mathlib in usable form. All three previously-explored
decompositions (per-level + Krull on a finite-presentation chart; the `of_split`
section obligation; the residue-field `cotangentComplexBaseChange` injectivity) reduce
to exactly this single statement. Both `h1Cotangent_subsingleton_aux` (vanishing of
`H¹(L_{A/R})`) and `differentials_projective` (projectivity of `Ω_{A/R}`) are immediate
corollaries via `Algebra.formallySmooth_iff`.

*Proof outline (Stacks 02HT, the substantive content — the next decomposition target).*
Set `R := 𝒪_{S,f(x)}`, `A := 𝒪_{X,x}`. Since `f` is locally of finite type and `S` is
locally Noetherian, `A` is essentially of finite presentation over `R`; choose an affine
finite-presentation chart `R₀ → A₀` with `A = (A₀)_𝔭`. On the chart the conormal /
cotangent module is finite, so Krull's intersection theorem applies. The lifting
hypothesis `h`, applied to the residually-trivial length-one square-zero truncations
`P/(I·𝔪 + Iⱼ) ↠ P/(I + Iⱼ)` (translated to local `R`-algebra sections through
`SpecToEquivOfLocalRing`), splits each rung of the conormal map; Krull descent from the
Artinian truncations forces the cotangent-complex kernel to vanish, and the same
splitting exhibits `Ω` as a direct summand of a finite free module. Transfer along the
localization (00S7 / 08JZ H1Cotangent localization compatibility, `Algebra.equivH1Cotangent`)
yields formal smoothness of the stalk `A/R`.  This is the standalone 02HT deformation core. -/
/- **The algebra-level analytic core, EssFiniteType form (Stacks 02HT for the stalk).**
A *local* `R`-algebra `A` that is *essentially of finite type* over a Noetherian local `R`
and lifts against residually-trivial small extensions (`AlgLiftsResTrivSmall R A`) is formally
smooth over `R`.

This is the form that ACTUALLY applies to the stalk `A = 𝒪_{X,x}` over `R = 𝒪_{S,f(x)}`:
the stalk is local and `EssFiniteType` (`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`), but
is NOT of finite presentation, and — crucially — there is NO chart that is simultaneously LOCAL
and FINITE-PRESENTATION localizing onto the stalk (counterexample `R = k`, `A = k[t]_(t)`:
a local finite-type `k`-algebra is Jacobson+local hence 0-dimensional, but `A = (A₀)_M` forces
`dim A₀ ≥ dim A`). So a chart-based bundle cannot work, and the argument goes directly through
the stalk.

*Proof outline (sound).* `A` EssFiniteType over `R` ⇒ there is a finite formally-smooth
presentation `P ↠ A` with `(ker (algebraMap P A)).FG`, where `P = (MvPolynomial (Fin n) R)_W`
is a LOCALIZATION of a polynomial ring (`Algebra.essFiniteType_iff_exists_subalgebra` +
`EssFiniteType.submonoid`/`FormallySmooth.of_isLocalization`); `P` is formally smooth over `R`
with `Ω[P/R]` free + finite. The local residue-field criterion
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P` (which needs
only a finite *formally smooth* `P` with the kernel f.g. — NOT `FinitePresentation R A`) reduces
`FormallySmooth R A` to injectivity of `cotangentComplexBaseChange R A P κ(A)`, which is the
`residueField_cotangentComplexBaseChange_injective_of_algLifts`, the 02HT core. -/
@[ega "0 20.4.9" "special case",
  ega "0 22.1.3" "special case",
  ega "0 22.1.4" "special case",
  sga "1 III 2.1" "special case",
  sga "1 III 2.2" "(i), special case"]
theorem formallySmooth_of_algLifts_essFiniteType (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A]
    [Algebra.EssFiniteType R A]
    (h : AlgLiftsResTrivSmall R A) :
    Algebra.FormallySmooth R A := by
  -- Stacks 02HT, EssFiniteType form: obtain a finite formally-smooth
  -- presentation `Pr` of `A` (a LOCALIZED polynomial ring; `exists_finFSPresentation`), apply the
  -- local residue-field criterion `iff_injective_lTensor_residueField` to `Pr`, and discharge the
  -- residue-field cotangent injectivity by the presentation-agnostic core
  -- `cotangentComplex_lTensorResidueField_injective_of_algLifts_general`.
  obtain ⟨Pr⟩ := exists_finFSPresentation R A
  set E := Algebra.Extension.ofSurjective (S := A) (IsScalarTower.toAlgHom R Pr.Ring A) Pr.surj
  have : Algebra.FormallySmooth R E.Ring := (inferInstance : Algebra.FormallySmooth R Pr.Ring)
  have : Module.Free E.Ring (Ω[E.Ring⁄R]) := (inferInstance : Module.Free Pr.Ring (Ω[Pr.Ring⁄R]))
  have : Module.Finite E.Ring (Ω[E.Ring⁄R]) := (inferInstance : Module.Finite Pr.Ring
      (Ω[Pr.Ring⁄R]))
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField E Pr.kerFG]
  exact cotangentComplex_lTensorResidueField_injective_of_algLifts_general R A h Pr

/- **The scheme→algebra translation of the lifting hypothesis (Stacks 02HX, on the local stalk).**
Under `h`, the *concrete local stalk* `A = 𝒪_{X,x}` over `R = 𝒪_{S,f(x)}` satisfies the
algebra-level lifting property `AlgLiftsResTrivSmall R A`.

Given a residually-trivial length-one square-zero small extension `φ : B' →ₐ[R] B` of local
Artinian `R`-algebras and `a : A →ₐ[R] B`: build `α : Spec B ⟶ X`, `β : Spec B' ⟶ S` via
`AlgebraicGeometry.SpecToEquivOfLocalRing.symm` (the local-ring↔pointed-Spec bijection — sound
because `A`, `B`, `B'` are ALL genuinely local), discharge the lifting-square + closed-point +
residual-triviality (`IsIso (residueFieldMap)`) obligations, feed the diagram to `h`, and read
the produced `γ` back through `SpecToEquivOfLocalRing` into the algebra lift `c : A →ₐ[R] B'`.
This is the converse of `formallySmooth_stalkMap_liftsAgainstSquareZero`, using the
`stalkClosedPointTo_specMap` and `stalkMap_stalkClosedPointTo_comm` helpers together with
`Algebra.FormallySmooth.{liftOfSurjective, comp_liftOfSurjective}`.  Here `A` is the stalk. -/
-- Reverse-direction helper: stalkSpecializes of an equality of points is iso
private theorem stalkSpec_isIso_of_eq {Y : Scheme.{u}} {p q : Y} (he : p = q) :
    IsIso (Y.presheaf.stalkSpecializes (Specializes.of_eq he)) := by
  subst he; simp only [TopCat.Presheaf.stalkSpecializes_refl]; infer_instance

-- Reverse-direction helper: surjectivity of a composite of CommRingCat morphisms
private theorem surjective_comp_hom {R S T : CommRingCat.{u}} (g : R ⟶ S) (k : S ⟶ T)
    (hg : Function.Surjective g.hom) (hk : Function.Surjective k.hom) :
    Function.Surjective (g ≫ k).hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact hk.comp hg

-- Reverse-direction helper: the closed-point stalk map of `Spec.map aR ≫ fromSpecStalk x`
-- is surjective when `aR` is.
private theorem stalkClosedPointTo_surjective {X : Scheme.{u}} (x : X) {B : CommRingCat.{u}}
    [IsLocalRing B]
    (aR : CommRingCat.of (X.presheaf.stalk x) ⟶ CommRingCat.of B) [IsLocalHom aR.hom]
    (hsurj : Function.Surjective aR.hom) :
    Function.Surjective (Scheme.stalkClosedPointTo (Spec.map aR ≫ X.fromSpecStalk x)).hom := by
  have hstalkMapIso :
      IsIso (Scheme.Hom.stalkMap (X.fromSpecStalk x)
        ((Spec.map aR).base (IsLocalRing.closedPoint B))) := by
    have he : (Spec.map aR).base (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint
        (X.presheaf.stalk x) :=
      AlgebraicGeometry.Spec_closedPoint (f := aR)
    rw [he]
    have hrel : Scheme.stalkClosedPointTo (X.fromSpecStalk x) =
        Scheme.Hom.stalkMap (X.fromSpecStalk x) (IsLocalRing.closedPoint (X.presheaf.stalk x)) ≫
          (stalkClosedPointIso (X.presheaf.stalk x)).hom := CommRingCat.hom_ext rfl
    have hiso : IsIso (Scheme.stalkClosedPointTo (X.fromSpecStalk x)) := by
      rw [Scheme.stalkClosedPointTo_fromSpecStalk]; infer_instance
    rw [hrel] at hiso
    exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso (X.presheaf.stalk x)).hom
  have hspecIso := stalkSpec_isIso_of_eq (Y := Spec (CommRingCat.of (X.presheaf.stalk x)))
    (AlgebraicGeometry.Spec_closedPoint (f := aR)).symm
  rw [Scheme.stalkClosedPointTo_comp (Spec.map aR) (X.fromSpecStalk x),
    stalkClosedPointTo_specMap aR]
  -- goal: Surjective (stalkMap ≫ stalkSpecializes ≫ stalkClosedPointIso ≫ aR).hom
  refine surjective_comp_hom _ _ ?_ ?_
  · exact (ConcreteCategory.isIso_iff_bijective _).mp hstalkMapIso |>.surjective
  refine surjective_comp_hom _ _ ?_ ?_
  · exact (ConcreteCategory.isIso_iff_bijective _).mp hspecIso |>.surjective
  refine surjective_comp_hom _ _ ?_ ?_
  · exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.surjective
  · exact hsurj

-- Reverse-direction helper: residue field map iso from surjective stalkClosedPointTo
private alias residueFieldMap_isIso_of_surjective :=
  AlgebraicGeometry.isIso_residueFieldMap_of_surjective_stalkClosedPointTo

-- Reverse-direction helper: residual triviality of `α = Spec.map aR ≫ fromSpecStalk x`
private theorem residueFieldMap_fromSpecStalk_isIso {X : Scheme.{u}} (x : X) {B : CommRingCat.{u}}
    [IsLocalRing B]
    (aR : CommRingCat.of (X.presheaf.stalk x) ⟶ B) [IsLocalHom aR.hom]
    (hsurj : Function.Surjective aR.hom) :
    IsIso ((Spec.map aR ≫ X.fromSpecStalk x).residueFieldMap (IsLocalRing.closedPoint B)) :=
  residueFieldMap_isIso_of_surjective (Spec.map aR ≫ X.fromSpecStalk x)
    (stalkClosedPointTo_surjective x aR hsurj)

-- Reverse-direction helper: precomposition with fromSpecStalk is injective (it is mono)
private theorem fromSpecStalk_precomp_injective {X : Scheme.{u}} (x : X) {B : CommRingCat.{u}}
    (u v : X.presheaf.stalk x ⟶ B)
    (e : Spec.map u ≫ X.fromSpecStalk x = Spec.map v ≫ X.fromSpecStalk x) : u = v := by
  have : Spec.map u = Spec.map v := (cancel_mono (X.fromSpecStalk x)).mp e
  exact Spec.map_injective this

-- this proof's elaboration needs more than the default heartbeat budget
/-- Lifting against residually trivial small extensions at a point of a scheme gives the
corresponding algebraic lifting property for the stalk map at that point. -/
theorem LiftsAgainstResiduallyTrivialSmallExtension.algLiftsResTrivSmall_of_lifts
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (h : LiftsAgainstResiduallyTrivialSmallExtension f x) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    AlgLiftsResTrivSmall (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  -- Stacks 02HX, the scheme-to-algebra translation on the concrete local stalk.
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  intro B' B _ _ _ _ _ _ _ _ φ hφsurj hsq hlen a ha
  -- CommRingCat versions
  let Φ : CommRingCat.of B' ⟶ CommRingCat.of B := CommRingCat.ofHom φ.toRingHom
  let aR : CommRingCat.of (X.presheaf.stalk x) ⟶ CommRingCat.of B := CommRingCat.ofHom a.toRingHom
  let bR : CommRingCat.of (S.presheaf.stalk (f.base x)) ⟶ CommRingCat.of B' :=
    CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f.base x)) B')
  -- `a`, `φ` surjective ⇒ local homs
  have : Nontrivial B := (‹IsLocalRing B›).toNontrivial
  have haloc : IsLocalHom a.toRingHom := Function.Surjective.isLocalHom a.toRingHom ha
  have haRloc : IsLocalHom aR.hom := haloc
  have hφloc : IsLocalHom φ.toRingHom := Function.Surjective.isLocalHom φ.toRingHom hφsurj
  have hΦloc : IsLocalHom Φ.hom := hφloc
  -- the scheme maps α and β
  let α : Spec (CommRingCat.of B) ⟶ X := Spec.map aR ≫ X.fromSpecStalk x
  let β : Spec (CommRingCat.of B') ⟶ S := Spec.map bR ≫ S.fromSpecStalk (f.base x)
  -- α sends the closed point to x
  have hclosed : α.base (IsLocalRing.closedPoint (CommRingCat.of B)) = x := by
    show (X.fromSpecStalk x).base ((Spec.map aR).base (IsLocalRing.closedPoint (CommRingCat.of
        B))) = x
    rw [AlgebraicGeometry.Spec_closedPoint (f := aR)]
    exact Scheme.fromSpecStalk_closedPoint
  -- the ring-level commuting square: f.stalkMap x ≫ aR = bR ≫ Φ
  have hring : f.stalkMap x ≫ aR = bR ≫ Φ := by
    apply CommRingCat.hom_ext
    ext r
    show a.toRingHom ((f.stalkMap x).hom r) = φ.toRingHom (algebraMap (S.presheaf.stalk (f.base
        x)) B' r)
    have hA : a.toRingHom ((f.stalkMap x).hom r)
        = algebraMap (S.presheaf.stalk (f.base x)) B r := by
      have := a.commutes r
      rwa [RingHom.algebraMap_toAlgebra] at this
    have hφc := φ.commutes r
    rw [hA, ← hφc]
    rfl
  -- the scheme-level compatibility square: α ≫ f = Spec.map Φ ≫ β
  have hcomm : α ≫ f = Spec.map Φ ≫ β := by
    show (Spec.map aR ≫ X.fromSpecStalk x) ≫ f = Spec.map Φ ≫ Spec.map bR ≫ S.fromSpecStalk
        (f.base x)
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, hring]
  -- residual triviality
  have hresIso : IsIso (α.residueFieldMap (IsLocalRing.closedPoint (CommRingCat.of B))) :=
    residueFieldMap_fromSpecStalk_isIso x aR ha
  -- IsSmallExtension Φ
  have hSmall : IsSmallExtension Φ := by
    refine ⟨‹_›, ‹_›, ‹_›, ‹_›, ?_, ?_⟩
    · exact hφsurj
    · show Module.length B' (RingHom.ker φ.toRingHom) = 1
      exact hlen
  -- apply h
  obtain ⟨γ, hγ1, hγ2⟩ := h Φ hSmall α β hcomm hclosed hresIso
  -- γ sends the closed point of Spec B' to x
  have hgammaPt : γ.base (IsLocalRing.closedPoint (CommRingCat.of B')) = x := by
    have h1 := congrArg (fun g => g.base (IsLocalRing.closedPoint (CommRingCat.of B))) hγ1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
    rw [AlgebraicGeometry.Spec_closedPoint (f := Φ)] at h1
    rw [h1]
    exact hclosed
  -- the lifted ring map cRing : A ⟶ B'
  let cRing : X.presheaf.stalk x ⟶ CommRingCat.of B' :=
    X.presheaf.stalkSpecializes (Specializes.of_eq hgammaPt) ≫ Scheme.stalkClosedPointTo γ
  -- γ = Spec.map cRing ≫ fromSpecStalk x
  have hgeq : Spec.map cRing ≫ X.fromSpecStalk x = γ := by
    show Spec.map (X.presheaf.stalkSpecializes (Specializes.of_eq hgammaPt) ≫
        Scheme.stalkClosedPointTo γ) ≫ X.fromSpecStalk x = γ
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk γ
  -- eq(1): cRing ≫ Φ = aR  (i.e. φ ∘ c = a)
  have eq1 : cRing ≫ Φ = aR := by
    apply fromSpecStalk_precomp_injective x
    rw [Spec.map_comp, Category.assoc, hgeq, hγ1]
  -- eq(2): f.stalkMap x ≫ cRing = bR  (R-compatibility of c)
  have eq2 : f.stalkMap x ≫ cRing = bR := by
    apply fromSpecStalk_precomp_injective (B := CommRingCat.of B') (f.base x)
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk f,
      ← Category.assoc, hgeq, hγ2]
  -- assemble c : A →ₐ[R] B'
  let c : (X.presheaf.stalk x) →ₐ[S.presheaf.stalk (f.base x)] B' :=
    { cRing.hom with
      commutes' := fun r => congrArg (fun (g : _ ⟶ CommRingCat.of B') => g.hom r) eq2 }
  exact ⟨c, AlgHom.ext fun y => congrArg (fun (g : _ ⟶ CommRingCat.of B) => g.hom y) eq1⟩

/-- Lifting against residually trivial small extensions at `x` makes the stalk map of `f` at
`x` formally smooth. -/
@[ega "0 22.1.3" "special case",
  sga "1 III 2.1" "special case",
  sga "1 III 2.2" "(i), special case"]
theorem LiftsAgainstResiduallyTrivialSmallExtension.formallySmooth_aux
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (h : LiftsAgainstResiduallyTrivialSmallExtension f x) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  -- Lifting against small extensions makes the stalk formally smooth.  The assembly is direct
  -- on the local stalk, with no chart: the stalk `A` is local and EssFiniteType
  -- over the Noetherian local `R`; translate `h` to the algebra-level lifting
  -- `AlgLiftsResTrivSmall R A`
  -- (`algLiftsResTrivSmall_of_lifts`), then apply the EssFiniteType algebra core
  -- `formallySmooth_of_algLifts_essFiniteType` directly; a local finite-presentation chart
  -- route cannot work, no chart being both local and of finite presentation.
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f x
  have halg : AlgLiftsResTrivSmall (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    LiftsAgainstResiduallyTrivialSmallExtension.algLiftsResTrivSmall_of_lifts f x h
  exact formallySmooth_of_algLifts_essFiniteType
    (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) halg

/-- Lifting against residually trivial small extensions at `x` makes `H¹` of the cotangent
complex of the stalk map vanish. -/
theorem LiftsAgainstResiduallyTrivialSmallExtension.h1Cotangent_subsingleton_aux
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (h : LiftsAgainstResiduallyTrivialSmallExtension f x) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Subsingleton (Algebra.H1Cotangent (S.presheaf.stalk (f.base x))
      (X.presheaf.stalk x)) := by
  -- Corollary of the 02HT analytic core: formal smoothness ⇒ vanishing of H¹(L_{A/R}).
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    LiftsAgainstResiduallyTrivialSmallExtension.formallySmooth_aux f x h
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

/-- Lifting against residually trivial small extensions at `x` makes the cotangent complex of
the stalk map injective. -/
theorem LiftsAgainstResiduallyTrivialSmallExtension.cotangentComplex_injective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (h : LiftsAgainstResiduallyTrivialSmallExtension f x) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Function.Injective
      (Algebra.Generators.self (S.presheaf.stalk (f.base x))
        (X.presheaf.stalk x)).toExtension.cotangentComplex := by
  -- Reduce injectivity of the canonical presentation's cotangent-complex map to
  -- `Subsingleton (Algebra.H1Cotangent R A)` via `cotangentComplex_injective_iff`
  -- (valid since `(Generators.self R A).Ring = MvPolynomial A R` is formally smooth).
  -- The vanishing is the presentation-independent analytic kernel `h1Cotangent_subsingleton_aux`.
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Algebra.FormallySmooth (S.presheaf.stalk (f.base x))
      (Algebra.Generators.self (S.presheaf.stalk (f.base x))
        (X.presheaf.stalk x)).toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth (S.presheaf.stalk (f.base x))
      (MvPolynomial (X.presheaf.stalk x) (S.presheaf.stalk (f.base x))))
  rw [Algebra.Extension.cotangentComplex_injective_iff]
  exact LiftsAgainstResiduallyTrivialSmallExtension.h1Cotangent_subsingleton_aux f x h

/-- Lifting against residually trivial small extensions at `x` makes `H¹` of the cotangent
complex of the stalk map vanish. -/
alias LiftsAgainstResiduallyTrivialSmallExtension.h1Cotangent_subsingleton :=
  InfinitesimalLifting.LiftsAgainstResiduallyTrivialSmallExtension.h1Cotangent_subsingleton_aux

/-- **Sub-lemma B (02HT, differentials projective).** Under the residually-trivial
small-extension lifting hypothesis, the module of Kähler differentials
`Ω_{A/R}` of the stalk algebra `A = 𝒪_{X,x}` over `R = 𝒪_{S,f(x)}` is projective.

In the 02HT argument this is the "first-order" part of the lifting criterion:
the same conormal splitting that yields cotangent-vanishing also exhibits
`Ω_{A/R}` as a direct summand of the finite free `A ⊗_P Ω_{P/R}` (equivalently,
formal smoothness against the square-zero extension `A[ε] = A ⊕ Ω`,
`Algebra.FormallySmooth`'s first-order content), so `Ω_{A/R}` is projective. -/
theorem LiftsAgainstResiduallyTrivialSmallExtension.differentials_projective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (h : LiftsAgainstResiduallyTrivialSmallExtension f x) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Module.Projective (X.presheaf.stalk x)
      (Ω[(X.presheaf.stalk x)⁄(S.presheaf.stalk (f.base x))]) := by
  -- Corollary of the 02HT analytic core: formal smoothness ⇒ Ω_{A/R} projective.
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    LiftsAgainstResiduallyTrivialSmallExtension.formallySmooth_aux f x h
  exact Algebra.FormallySmooth.projective_kaehlerDifferential

/-- Lifting against residually trivial small extensions at `x` makes the stalk map of `f` at
`x` formally smooth: the Kähler differentials are projective and `H¹Cotangent` vanishes. -/
@[ega "0 22.1.3" "special case",
  sga "1 III 2.1" "special case",
  sga "1 III 2.2" "(i), special case"]
alias LiftsAgainstResiduallyTrivialSmallExtension.formallySmooth_stalkMap :=
  InfinitesimalLifting.LiftsAgainstResiduallyTrivialSmallExtension.formallySmooth_aux

/-- Formal smoothness of the
stalk map (together with the finite-type / locally-Noetherian hypotheses) implies
`f` is smooth at `x`.

*Informal proof.*  By the previous lemma `A := 𝒪_{X,x}` is formally smooth over
`R := 𝒪_{S,f(x)}`.  Since `f` is locally of finite type and `S` is locally
Noetherian, on affine opens `Spec R₀ ⊆ S` around `f(x)` and `Spec A₀ ⊆ X` around
`x` the ring map `R₀ ⟶ A₀` is of finite presentation (finite type over the
Noetherian `R₀`).  Formal smoothness of the *localization* `R ⟶ A` spreads out:
formal smoothness at the prime `𝔭 = 𝔪_x` of `Spec A₀` is an open condition
(`Algebra.FormallySmooth` localizes, and `RingHom.smooth_def`:
`Smooth ↔ FormallySmooth ∧ FinitePresentation`), so there is a basic open
`Spec (A₀)_g ∋ x` on which `R₀ ⟶ (A₀)_g` is smooth.  By `AlgebraicGeometry.smooth_iff`
the restriction of `f` to the corresponding open `U ∋ x` of `X` is a smooth
morphism, giving `SmoothAt f x` with that `U`. -/
@[ega "0 22.6.4" "special case", ega "IV 17.5.1" "special case", ega "IV 6.8.6" "c′ ⇒ a"]
theorem formallySmooth_stalkMap_smoothAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (hfs : letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :
    SmoothAt f x := by
  -- `f` is locally of finite presentation (finite type + Noetherian base)
  have : LocallyOfFinitePresentation f :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType f
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  -- the hypothesis gives formal smoothness of the stalk map at `x`
  have hx : (f.stalkMap x).hom.FormallySmooth := hfs
  -- `x` lies in the smooth locus, which is open
  have hxmem : x ∈ f.smoothLocus := Scheme.Hom.mem_smoothLocus.mpr hx
  set U : X.Opens := f.smoothLocus with hU
  refine ⟨U, hxmem, ?_⟩
  set g := f.resLE ⊤ U le_top with hg
  -- show `g.smoothLocus = ⊤`, hence `g` is smooth
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  rw [eq_top_iff]
  rintro y -
  -- every point `y` of `U` is in the smooth locus of `g`
  rw [Scheme.Hom.mem_smoothLocus]
  -- the underlying point `↑y` is in `f.smoothLocus = U`
  have hfy : (f.stalkMap (U.ι.base y)).hom.FormallySmooth := by
    have hmem : (U.ι.base y) ∈ f.smoothLocus := by
      rw [← hU]; exact y.property
    exact Scheme.Hom.mem_smoothLocus.mp hmem
  exact (formallySmooth_resLE_stalkMap_iff f U y).mpr hfy

/-- **Stacks 02HX.** Let `f : X → S` be a morphism of schemes locally of finite
type with `S` locally Noetherian, and let `x ∈ X`. Then the four conditions
(smoothness at `x`; lifting against square-zero surjections; lifting against
small extensions; lifting against residually trivial small extensions) are all
equivalent. -/
@[ega "0 19.0.1" "partial",
  ega "IV 17.14.1" "special case",
  ega "IV 17.14.2",
  sga "3 III 2.5" "(a), special case",
  sga "3 IX 3.3" "special case",
  sga "3 XI 1.5" "partial, special case",
  sga "3 XI 1.7" "special case",
  sga "3 XI 1.8" "special case"]
theorem infinitesimal_lifting_criterion_for_smoothness
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    [SmoothAt f x,
      LiftsAgainstSquareZero f x,
      LiftsAgainstSmallExtension f x,
      LiftsAgainstResiduallyTrivialSmallExtension f x].TFAE := by
  tfae_have 1 → 2 := fun h =>
    formallySmooth_stalkMap_liftsAgainstSquareZero f x (h.formallySmooth_stalkMap f x)
  tfae_have 2 → 3 := by
    intro h B' B φ hφ _ α β hcomm hclosed
    exact h φ hφ.isSquareZeroSurjection α β hcomm hclosed
  tfae_have 3 → 4 := by
    intro h B' B φ hφ _ α β hcomm hclosed _
    exact h φ hφ α β hcomm hclosed
  tfae_have 4 → 1 := fun h =>
    formallySmooth_stalkMap_smoothAt f x (h.formallySmooth_stalkMap f x)
  tfae_finish

end InfinitesimalLifting
