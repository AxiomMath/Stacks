module

public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Very ampleness from surjectivity onto degree-two zero-dimensional subschemes

Let `k` be an algebraically closed field, let `X` be proper over `k` and let `ℒ` be an invertible
module on `X`. A closed subscheme `Z ⊆ X` is *zero-dimensional of degree `d` over `k`* if its
underlying space has topological Krull dimension at most zero and its ring of global sections is
`d`-dimensional over `k`. If `H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective for every such `Z` of degree
two, then `ℒ` is very ample.

A degree-two zero-dimensional closed subscheme over an algebraically closed field is either a
pair of distinct reduced closed points, with `H⁰(Z, 𝒪_Z) ≅ k × k`, or a single closed point
carrying a nonzero tangent direction, with `H⁰(Z, 𝒪_Z) ≅ k[ε]`. Surjectivity onto the sections of
the first kind is separation of closed points and onto the sections of the second kind is
separation of tangent vectors, so the criterion of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S) applies.

## Main definitions

* `AlgebraicGeometry.IsZeroDimensionalOfDegree`: a `k`-scheme is zero-dimensional of degree `d`
  when its space has topological Krull dimension at most zero and its global sections form a
  `d`-dimensional `k`-vector space, the `k`-structure being the one induced by the structure
  morphism.
* `AlgebraicGeometry.SurjectsOnDegreeTwo`: the hypothesis of
  [Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T), that restriction of global
  sections of `ℒ` to every zero-dimensional degree-two closed subscheme is surjective.
* `AlgebraicGeometry.HasDegreeTwoPointPairs` and `AlgebraicGeometry.HasDegreeTwoFatPoints`: the
  two halves of the classification of degree-two zero-dimensional closed subschemes, in the form
  in which the reduction below consumes them.

## Main results

* `AlgebraicGeometry.separatesClosedPoints_of_surjectsOnDegreeTwo`: surjectivity onto the
  sections on degree-two subschemes, together with the pairs of reduced points among them, makes
  a complete linear system separate the closed points of `X`.
* `AlgebraicGeometry.separatesTangentVectors_of_surjectsOnDegreeTwo`: the same with the fat
  points among them makes it separate the tangent vectors of `X` over `k`.
* `AlgebraicGeometry.isRelativelyVeryAmple_of_surjectsOnDegreeTwo`: an invertible `ℒ` whose
  complete linear system is realized by a morphism to a projective bundle and which restricts
  surjectively to every degree-two zero-dimensional closed subscheme is very ample relative to
  the structure morphism of `X`.

## Implementation notes

The linear system is required to be *complete*, by `Function.Surjective ψ`: the conditions of
Tag 0E8S ask a single member of the family to vanish at one point and not at another, which a
proper subsystem spanning a separating space of sections need not provide, whereas the hypothesis
of Tag 0E8T is about all of `H⁰(X, ℒ)`. The morphism to the projective bundle and the
identification of the pulled-back degree-one twist with `ℒ` are data here, as in the criterion of
Tag 0E8S that this file consumes; they are the morphism of
[Stacks, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY), which this repository does not
construct.

`AlgebraicGeometry.HasDegreeTwoPointPairs` and `AlgebraicGeometry.HasDegreeTwoFatPoints` are the
classification of degree-two zero-dimensional closed subschemes, which is not proved here. Both
are unconditionally true for `X` locally of finite type over an algebraically closed field and
`ℒ` invertible: a pair of distinct closed points is a closed subscheme with sections `k × k`, on
which some section vanishes at the first point and not at the second because the fibre of `ℒ` at
the second point is a one-dimensional `k`-vector space; and a nonzero tangent vector at a closed
point is a closed immersion of `Spec k[ε]` whose sections of `ℒ` form a free `k[ε]`-module of
rank one, so that restriction to the closed point has the nonzero kernel `ε · H⁰(Z, ℒ|_Z)`.

## References

* [Stacks Project, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T)
* [Stacks Project, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Ample Stacks.Tag01VMVeryAmple
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.Tag01VMRelativeVeryAmple (symAlgebra)

universe v u

namespace AlgebraicGeometry

/-! ### Degree of a zero-dimensional scheme over a field -/

/-- A scheme over `k` is *zero-dimensional of degree `d`* if its underlying space has topological
Krull dimension at most zero and its ring of global sections is a `d`-dimensional `k`-vector
space, for the `k`-algebra structure induced by the structure morphism. For a closed subscheme of
a scheme over `k` this is the notion of degree used in
[Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T). -/
def IsZeroDimensionalOfDegree {k : Type u} [Field k] {Z : Scheme.{u}}
    (z : Z ⟶ Spec (CommRingCat.of k)) (d : ℕ) : Prop :=
  letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ z.appTop).hom.toAlgebra
  topologicalKrullDim Z ≤ 0 ∧ Module.finrank k Γ(Z, ⊤) = d

/-- Pulling back global sections is additive. -/
private lemma pullbackSectionTop_sub {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s t : M.val.obj (op ⊤)) :
    pullbackSectionTop f M (s - t) = pullbackSectionTop f M s - pullbackSectionTop f M t :=
  map_sub _ _ _

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### The hypothesis of Tag 0E8T and the two kinds of degree-two subscheme -/

/-- **The hypothesis of [Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T).** For
every closed subscheme `r : Z ⟶ X` which is zero-dimensional of degree two over `k`, the
restriction map `H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective. -/
def SurjectsOnDegreeTwo (p : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) : Prop :=
  ∀ (Z : Scheme.{u}) (r : Z ⟶ X), IsClosedImmersion r →
    IsZeroDimensionalOfDegree (r ≫ p) 2 → Function.Surjective (pullbackSectionTop r L)

/-- **The reduced degree-two subschemes.** Every ordered pair of distinct closed points of `X`
lies on a zero-dimensional degree-two closed subscheme `r : Z ⟶ X`, through which both
residue-field points factor, carrying a section of `ℒ|_Z` which vanishes at the first point and
not at the second. -/
def HasDegreeTwoPointPairs (p : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) : Prop :=
  ∀ x y : X, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) → x ≠ y →
    ∃ (Z : Scheme.{u}) (r : Z ⟶ X) (a : Spec (.of (X.residueField x)) ⟶ Z)
      (b : Spec (.of (X.residueField y)) ⟶ Z),
      IsClosedImmersion r ∧ IsZeroDimensionalOfDegree (r ≫ p) 2 ∧
        a ≫ r = X.fromSpecResidueField x ∧ b ≫ r = X.fromSpecResidueField y ∧
        ∃ σ : ((Scheme.Modules.pullback r).obj L).val.obj (op ⊤),
          VanishesAlong a σ ∧ ¬ VanishesAlong b σ

/-- **The fat degree-two subschemes.** Every nonzero tangent vector `θ` at a closed point of `X`
is a closed immersion of the dual-number point which is zero-dimensional of degree two over `k`,
and restriction of the sections of `ℒ` along it to the closed point is not injective. -/
def HasDegreeTwoFatPoints (p : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → ∀ θ : DottedTangentArrow p x, θ ≠ 0 →
    IsClosedImmersion θ.val ∧ IsZeroDimensionalOfDegree (θ.val ≫ p) 2 ∧
      ¬ Function.Injective (pullbackSectionTop (dualNumberClosedPoint X x)
        ((Scheme.Modules.pullback θ.val).obj L))

/-! ### The two separation conditions of Tag 0E8S -/

/-- **From surjectivity on degree-two subschemes to condition (1) of Tag 0E8S.** A complete
linear system of an invertible module which restricts surjectively to every zero-dimensional
degree-two closed subscheme separates the closed points of `X`, given the pairs of distinct
reduced points among those subschemes. -/
theorem separatesClosedPoints_of_surjectsOnDegreeTwo (p : X ⟶ Spec (CommRingCat.of k))
    {L : X.Modules} (hsurj : SurjectsOnDegreeTwo p L) (hpair : HasDegreeTwoPointPairs p L)
    {V : Type v} {ψ : V → L.val.obj (op ⊤)} (hfull : Function.Surjective ψ) :
    SeparatesClosedPoints ψ := by
  intro x y hx hy hxy
  obtain ⟨Z, r, a, b, hr, hdeg, hax, hby, σ, hσa, hσb⟩ := hpair x y hx hy hxy
  obtain ⟨s, hs⟩ := hsurj Z r hr hdeg σ
  obtain ⟨v, hv⟩ := hfull s
  refine ⟨v, ?_, ?_⟩
  · rw [hv, ← vanishesAlong_congr_iff hax L s, vanishesAlong_comp_iff a r L s, hs]
    exact hσa
  · rw [hv, ← vanishesAlong_congr_iff hby L s, vanishesAlong_comp_iff b r L s, hs]
    exact hσb

/-- **From surjectivity on degree-two subschemes to condition (2) of Tag 0E8S.** A complete
linear system of an invertible module which restricts surjectively to every zero-dimensional
degree-two closed subscheme separates the tangent vectors of `X` over `k`, given the fat points
among those subschemes. -/
theorem separatesTangentVectors_of_surjectsOnDegreeTwo (p : X ⟶ Spec (CommRingCat.of k))
    {L : X.Modules} (hsurj : SurjectsOnDegreeTwo p L) (htan : HasDegreeTwoFatPoints p L)
    {V : Type v} {ψ : V → L.val.obj (op ⊤)} (hfull : Function.Surjective ψ) :
    SeparatesTangentVectors p ψ := by
  intro x hx θ hθ
  obtain ⟨hci, hdeg, hninj⟩ := htan x hx θ hθ
  obtain ⟨σ₁, σ₂, heq, hne⟩ := Function.not_injective_iff.mp hninj
  have hsub : pullbackSectionTop (dualNumberClosedPoint X x)
      ((Scheme.Modules.pullback θ.val).obj L) (σ₁ - σ₂) = 0 := by
    rw [pullbackSectionTop_sub, heq, sub_self]
  obtain ⟨s, hs⟩ := hsurj _ θ.val hci hdeg (σ₁ - σ₂)
  obtain ⟨v, hv⟩ := hfull s
  refine ⟨v, ?_, ?_⟩
  · rw [hv, ← vanishesAlong_congr_iff θ.property.1 L s,
      vanishesAlong_comp_iff (dualNumberClosedPoint X x) θ.val L s, hs]
    exact hsub
  · rw [hv, VanishesAlong, hs]
    exact sub_ne_zero.mpr hne

/-! ### Very ampleness -/

/-- **[Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T).** Let `k` be an
algebraically closed field, let `X` be proper over `k` through `p`, let `E` be a quasi-coherent
`k`-module and let `i : X ⟶ 𝐏(E)` be a morphism over `k` with `i^* 𝒪_{𝐏(E)}(1) ≅ ℒ` realizing the
complete linear system of an invertible `ℒ`. If `H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective for every
closed subscheme `Z ⊆ X` which is zero-dimensional of degree two over `k`, then `ℒ` is very ample
relative to `p`.

The two kinds of degree-two subscheme give the two separation conditions of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S), whose very-ampleness clause then
applies. -/
@[stacks 0E8T "the degree-two hypothesis is stated with the degree of a zero-dimensional \
subscheme as finrank over k; the classification of degree-two subschemes into point pairs and \
fat points is a hypothesis, as is the Tag 0FCY morphism to 𝐏(E) inherited from Tag 0E8S, and \
the linear system is required to be complete"]
theorem isRelativelyVeryAmple_of_surjectsOnDegreeTwo [IsAlgClosed k]
    {E : (Spec (CommRingCat.of k)).Modules} [E.IsQuasicoherent]
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (i : X ⟶ (relativeProj (symAlgebra E)).scheme)
    (h : i ≫ (relativeProj (symAlgebra E)).toBase = p)
    {L : X.Modules} [IsInvertibleModule X L]
    (e : (Scheme.Modules.pullback i).obj (twistOne E) ≅ L)
    {V : Type v} {t : V → (twistOne E).val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, e.hom.val.app (op ⊤) (pullbackSectionTop i (twistOne E) (t v)) = ψ v)
    (hfull : Function.Surjective ψ) (hsurj : SurjectsOnDegreeTwo p L)
    (hpair : HasDegreeTwoPointPairs p L) (htan : HasDegreeTwoFatPoints p L) :
    IsRelativelyVeryAmple p L :=
  isRelativelyVeryAmple_of_separatesClosedPoints_of_separatesTangentVectors p i h e htψ
    (separatesClosedPoints_of_surjectsOnDegreeTwo p hsurj hpair hfull)
    (separatesTangentVectors_of_surjectsOnDegreeTwo p hsurj htan hfull)

end AlgebraicGeometry

end
