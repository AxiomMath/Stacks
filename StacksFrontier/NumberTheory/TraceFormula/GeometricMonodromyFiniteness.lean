module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Finiteness of geometric monodromy

Let `k` be a finite field of characteristic `p`, let `X` be a smooth, geometrically irreducible,
projective curve over `k`, and let `ℓ` be a prime different from `p`. The Conjecture of the
section on automorphic forms and sheaves predicts that for every continuous representation
`ρ : π₁(X) → GL_n(F_ℓ[[t]])` the image `ρ(π₁(X_K))` of the geometric fundamental group is
finite, where `K` is an algebraically closed extension of `k`. The section states two ranges in
which the Conjecture is known: rank at most two (de Jong, Tag 03VZ) and `2n < ℓ` "modulo some
unproven things" (Gaitsgory, Tag 03W0).

Both are research theorems whose proofs the source replaces by a citation, and neither is
proved here; neither is formalized either (see "What is not proved" below). What is proved here
is the passage from the shape in which the sources leave their conclusion to the shape in which
the Conjecture states it. A source produces a finite étale
covering of the geometric curve over which the representation becomes trivial — on fundamental
groups, an open subgroup of `π₁(X_K, x)` inside the kernel of the restricted representation.
From that, and from the compactness of the étale fundamental group, it follows that the
geometric monodromy group — the image in `GL_n(F_ℓ[[t]])` of `π₁(X_K, x)` under the canonical
map to `π₁(X, x)` followed by `ρ` — is finite, which is the Conjecture's conclusion.

## Main definitions

* `Stacks.TraceFormula.specBaseChange` — the morphism `Spec K ⟶ Spec k` of a field extension,
  along which the curve is based changed to its geometric avatar.
* `Stacks.TraceFormula.geometricBaseChange` and `Stacks.TraceFormula.geometricProjection` —
  the curve `X_K = X ×_{Spec k} Spec K` over the algebraically closed field `K`, and its
  projection to `X`.
* `Stacks.TraceFormula.geometricRestriction` — the restriction of a continuous representation
  of `π₁(X)` along the canonical map from `π₁(X_K, x)`, and
  `Stacks.TraceFormula.geometricMonodromy` its image, the geometric monodromy group.
* `Stacks.TraceFormula.IsTrivialOnOpenSubgroup` — the conclusion the two sources are cited for:
  the restricted representation is trivial on an open subgroup of `π₁(X_K, x)`.
* `Stacks.TraceFormula.FSheafFormalism` and `Stacks.TraceFormula.ExtendedGeometricSatake` —
  records of some of the data of the theories Gaitsgory assumes, without their axioms.

## Main results

* `Stacks.TraceFormula.finite_range_of_isOpen_le_ker` — a homomorphism from a compact
  topological group which is trivial on an open subgroup has finite image.
* `Stacks.TraceFormula.finite_geometricMonodromy_of_isTrivialOnOpenSubgroup` — the geometric
  monodromy group is finite as soon as the restricted representation is trivial on an open
  subgroup of the geometric fundamental group.
* `Stacks.TraceFormula.finite_geometricMonodromy_of_rank_le_two` and
  `Stacks.TraceFormula.finite_geometricMonodromy_of_two_mul_lt` — the compactness step above,
  stated in the ranges of Tags 03VZ and 03W0; neither is the tagged theorem (see below).

## What is not proved

Neither de Jong's theorem nor Gaitsgory's theorem is proved or formalized. The two theorems
`finite_geometricMonodromy_of_rank_le_two` and `finite_geometricMonodromy_of_two_mul_lt` take
`IsTrivialOnOpenSubgroup` — the representation restricted to the geometric fundamental group
dies on an open subgroup — as a hypothesis. Since the geometric fundamental group is compact and
`GL_n(F_ℓ[[t]])` is Hausdorff, that hypothesis is equivalent to the finiteness of the geometric
monodromy group, which is the conclusion. So these theorems state the compactness step and
nothing of the cited theorems' content; they do not formalize Tags 03VZ and 03W0.

Tag 03W0 itself is formalized in `StacksFrontier.NumberTheory.TraceFormula.GaitsgoryFiniteness`:
from the arithmetic input of Gaitsgory's construction (the coefficients of the characteristic
polynomials of Frobenius are algebraic over `F_ℓ`), finiteness of the geometric monodromy group is
proved there by Chebotarev density, Burnside's theorem on the absolutely irreducible blocks, and
finiteness of `H¹(X_k̄, 𝐙/ℓ)` on the unipotent part. The record types `FSheafFormalism` and
`ExtendedGeometricSatake` here hold some of the data of Gaitsgory's sheaf theories but none of
their axioms, so any type can be made into an instance of them and they constrain nothing.

A third hypothesis is a gap in the library rather than in the sources: the finiteness of the
fibres of the fibre functor on finite étale covers, which is part of the Galois-category theory
of `FÉt_X` and on which the compactness instance for
`AlgebraicGeometry.EtaleFundamentalGroup` is conditional. It is carried as an instance
hypothesis `[∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)]` and is what makes the
compactness argument available.

## Implementation notes

The geometric point is `AlgebraicGeometry.GeometricPoint`, the one the fundamental-group API
consumes, and the canonical map on fundamental groups is
`AlgebraicGeometry.etaleFundamentalGroupMap` of Tag 0BND. Projectivity of the curve is
`AlgebraicGeometry.IsProjective`, the first condition of Tag 01W8, which is what the section's
setup asks for; it is a `Prop`-valued definition rather than a class, so it appears as an
explicit hypothesis.

The base field and the algebraically closed field live in one universe. This is no restriction:
the Conjecture concerns a finite `k`, whose algebraic closure can be formed in the same
universe, and taking an arbitrary algebraically closed extension in place of `k̄` only widens
the statement.

`Stacks.TraceFormula.FSheafFormalism` carries the six operations as data, and
`Stacks.TraceFormula.ExtendedGeometricSatake` is stated relative to a given formalism, its
spherical objects being objects of that formalism on an assumed presentation of the affine
Grassmannian. Neither theory is available in the library, which is why each is a record of
assumed data rather than a construction.

## References

* [Stacks Project, Tag 03VZ](https://stacks.math.columbia.edu/tag/03VZ)
* [Stacks Project, Tag 03W0](https://stacks.math.columbia.edu/tag/03W0)
* [dJ-conjecture]
* [Gaitsgory]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped PowerSeries.WithPiTopology

universe u

namespace Stacks.TraceFormula

/-- A homomorphism out of a compact topological group has finite image as soon as it is trivial
on an open subgroup: the open subgroup has finite index, and the homomorphism is constant on
each of its cosets. -/
theorem finite_range_of_isOpen_le_ker {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {H : Type*} [Group H] (φ : G →* H)
    {U : Subgroup G} (hU : IsOpen (U : Set G)) (hle : U ≤ φ.ker) :
    (Set.range φ).Finite := by
  have : Finite (G ⧸ U) := U.quotient_finite_of_isOpen hU
  refine Set.Finite.subset (Set.finite_range fun q : G ⧸ U =>
    Quotient.liftOn' q φ fun a b hab => ?_) ?_
  · have h1 : φ (a⁻¹ * b) = 1 := hle (QuotientGroup.leftRel_apply.mp hab)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  · rintro y ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩

/-- The morphism of spectra induced by a field extension `k ⊆ K`. Base change along it takes a
curve over `k` to its avatar over `K`. -/
def specBaseChange (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f]

/-- The geometric curve `X_K = X ×_{Spec k} Spec K`, the base change of `X` to the algebraically
closed field `K`. -/
abbrev geometricBaseChange : Scheme.{u} := pullback f (specBaseChange k K)

/-- The projection `X_K ⟶ X` of the geometric curve onto the curve. -/
abbrev geometricProjection : geometricBaseChange k K f ⟶ X :=
  pullback.fst f (specBaseChange k K)

variable {n ℓ : ℕ}

/-- The restriction of a continuous representation of the fundamental group of `X` to the
fundamental group of the geometric curve, along the canonical map of Tag 0BND induced by the
projection. -/
def geometricRestriction (x : GeometricPoint (geometricBaseChange k K f))
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ))) :
    EtaleFundamentalGroup (geometricBaseChange k K f) x →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)) :=
  ρ.comp (etaleFundamentalGroupMap (geometricProjection k K f) x)

/-- The geometric monodromy group of a continuous representation: the image `ρ(π₁(X_K))` of the
fundamental group of the geometric curve. The Conjecture of the section on automorphic forms and
sheaves asserts that this group is finite. -/
def geometricMonodromy (x : GeometricPoint (geometricBaseChange k K f))
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ))) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ))) :=
  (geometricRestriction k K f x ρ).toMonoidHom.range

/-- The representation becomes trivial on an open subgroup of the fundamental group of the
geometric curve. This is the conclusion both de Jong and Gaitsgory are cited for, in the form
their arguments produce it: a finite étale covering of the geometric curve over which the lisse
sheaf attached to `ρ` is constant, read on fundamental groups. -/
def IsTrivialOnOpenSubgroup (x : GeometricPoint (geometricBaseChange k K f))
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ))) : Prop :=
  ∃ U : Subgroup (EtaleFundamentalGroup (geometricBaseChange k K f) x),
    IsOpen (U : Set (EtaleFundamentalGroup (geometricBaseChange k K f) x)) ∧
      U ≤ (geometricRestriction k K f x ρ).toMonoidHom.ker

/-- **The Conjecture's conclusion from the sources' conclusion.** A representation which is
trivial on an open subgroup of the fundamental group of the geometric curve has finite geometric
monodromy: the fundamental group is compact, so the open subgroup has finite index, and the
representation is constant on each of its cosets. -/
theorem finite_geometricMonodromy_of_isTrivialOnOpenSubgroup
    (x : GeometricPoint (geometricBaseChange k K f))
    [∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)]
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (h : IsTrivialOnOpenSubgroup k K f x ρ) :
    Finite (geometricMonodromy k K f x ρ) := by
  obtain ⟨U, hUopen, hUker⟩ := h
  exact (finite_range_of_isOpen_le_ker
    (geometricRestriction k K f x ρ).toMonoidHom hUopen hUker).to_subtype

/-- Some of the data of the theory of constructible `F_ℓ((t))`-sheaves assumed in Gaitsgory
§1.4: for every scheme a type of sheaf objects, a predicate called perverse, operations named
after the six operations, and a function called the Frobenius trace, compatible with pullback
and with tensor product. Beyond those two compatibilities the record has no axioms (no
adjunctions, no triangulated structure, no sheaf–function dictionary), so it is inhabited by
degenerate data (one-point sheaf types, trace `0`) and does not model the theory. -/
structure FSheafFormalism (k : Type u) [Field k] (ℓ : ℕ) where
  /-- The objects of the constructible derived category of `F_ℓ((t))`-sheaves on a scheme. -/
  sheaf : Scheme.{u} → Type (u + 1)
  /-- The perverse objects. -/
  Perverse : ∀ Y, sheaf Y → Prop
  /-- Pullback along a morphism. -/
  pull : ∀ {Y Z : Scheme.{u}}, (Y ⟶ Z) → sheaf Z → sheaf Y
  /-- Pushforward along a morphism. -/
  push : ∀ {Y Z : Scheme.{u}}, (Y ⟶ Z) → sheaf Y → sheaf Z
  /-- Pushforward with compact support. -/
  pushCompactSupport : ∀ {Y Z : Scheme.{u}}, (Y ⟶ Z) → sheaf Y → sheaf Z
  /-- The extraordinary pullback right adjoint to pushforward with compact support. -/
  pullExtraordinary : ∀ {Y Z : Scheme.{u}}, (Y ⟶ Z) → sheaf Z → sheaf Y
  /-- Tensor product of sheaves. -/
  tensor : ∀ Y, sheaf Y → sheaf Y → sheaf Y
  /-- Internal hom of sheaves. -/
  internalHom : ∀ Y, sheaf Y → sheaf Y → sheaf Y
  /-- The function on rational points attached to a sheaf by the Frobenius-trace
  correspondence. -/
  frobeniusTrace : ∀ Y, sheaf Y → (Spec (.of k) ⟶ Y) → LaurentSeries (ZMod ℓ)
  /-- The Frobenius-trace function of a pullback is the pullback of the Frobenius-trace
  function. -/
  frobeniusTrace_pull : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z) (A : sheaf Z)
      (y : Spec (.of k) ⟶ Y), frobeniusTrace Y (pull g A) y = frobeniusTrace Z A (y ≫ g)
  /-- The Frobenius-trace function of a tensor product is the product of the Frobenius-trace
  functions. -/
  frobeniusTrace_tensor : ∀ (Y : Scheme.{u}) (A B : sheaf Y) (y : Spec (.of k) ⟶ Y),
      frobeniusTrace Y (tensor Y A B) y =
        frobeniusTrace Y A y * frobeniusTrace Y B y

/-- The extension of the geometric Satake equivalence to an arbitrary ground field required in
Gaitsgory §1.6 and Theorem 2.2: for every rank, the spherical perverse objects of a given
`F_ℓ((t))`-sheaf formalism on the affine Grassmannian are the representations of the Langlands
dual group, and the same holds with `F_ℓ[[t]]`-coefficients. The affine Grassmannian itself is
assumed here, as a scheme over the ground field together with its structure morphism, since the
library has no construction of it. The record has no axioms: the Grassmannian is an arbitrary
scheme and the equivalences are between arbitrary types, so it is inhabited by degenerate data
and does not model the Satake equivalence. -/
structure ExtendedGeometricSatake (k : Type u) [Field k] (ℓ : ℕ)
    (formalism : FSheafFormalism k ℓ) where
  /-- A presentation of the affine Grassmannian of `GL_m` over the ground field. -/
  grassmannian : ℕ → Scheme.{u}
  /-- Its structure morphism to the ground field. -/
  grassmannianToBase : ∀ m, grassmannian m ⟶ Spec (.of k)
  /-- The spherical objects of the given formalism on the affine Grassmannian. -/
  Spherical : ∀ m, formalism.sheaf (grassmannian m) → Prop
  /-- Representations of the Langlands dual group of `GL_m` over `F_ℓ((t))`. -/
  dualFraction : ℕ → Type (u + 1)
  /-- The Satake equivalence with `F_ℓ((t))`-coefficients. -/
  fractionEquiv : ∀ m, { A : formalism.sheaf (grassmannian m) //
    Spherical m A ∧ formalism.Perverse _ A } ≃ dualFraction m
  /-- The spherical objects with `F_ℓ[[t]]`-coefficients. -/
  sphericalIntegral : ℕ → Type (u + 1)
  /-- Representations of the Langlands dual group of `GL_m` over `F_ℓ[[t]]`. -/
  dualIntegral : ℕ → Type (u + 1)
  /-- The Satake equivalence with `F_ℓ[[t]]`-coefficients. -/
  integralEquiv : ∀ m, sphericalIntegral m ≃ dualIntegral m

/-- **Stacks Project, Tag 03VZ.** *The Conjecture holds if `n ≤ 2`.* For a smooth, projective,
geometrically irreducible curve over a finite field of characteristic `p` and a prime `ℓ ≠ p`,
every continuous representation of the étale fundamental group of rank at most two over
`F_ℓ[[t]]` has finite geometric monodromy.

This is not de Jong's theorem. The hypothesis `hdeJong` concludes that the representation
becomes trivial on an open subgroup of the geometric fundamental group, which by compactness is
equivalent to the finiteness of the geometric monodromy group; so the statement is the
compactness step `finite_geometricMonodromy_of_isTrivialOnOpenSubgroup` in the range `n ≤ 2`,
not Tag 03VZ, which is not formalized. -/
theorem finite_geometricMonodromy_of_rank_le_two [Finite k] [IsAlgClosed K] [Smooth f]
    (p : ℕ) [CharP k p] [Fact ℓ.Prime]
    (x : GeometricPoint (geometricBaseChange k K f))
    [∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)]
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (hproj : IsProjective f) (hℓp : ℓ ≠ p) (hn : n ≤ 2)
    (hdeJong : IsProjective f → ℓ ≠ p → n ≤ 2 → IsTrivialOnOpenSubgroup k K f x ρ) :
    Finite (geometricMonodromy k K f x ρ) :=
  finite_geometricMonodromy_of_isTrivialOnOpenSubgroup k K f x ρ (hdeJong hproj hℓp hn)

/-- **The compactness step in the range `2n < ℓ`.** For a smooth, projective, geometrically
irreducible curve over a finite field of characteristic `p` and a prime `ℓ ≠ p` with `2n < ℓ`,
a continuous representation of the étale fundamental group of rank `n` over `F_ℓ[[t]]` whose
restriction to the geometric fundamental group is trivial on an open subgroup has finite
geometric monodromy.

This is not Gaitsgory's theorem (Tag 03W0). The hypothesis `hGaitsgory` concludes that the
representation becomes trivial on an open subgroup of the geometric fundamental group, which by
compactness is equivalent to the finiteness of the geometric monodromy group; and `formalism` and
`satake` are records without axioms, which constrain nothing. Tag 03W0 is
`Stacks.TraceFormula.finite_geometricMonodromy_of_hasAlgebraicFrobeniusCharpoly` in
`StacksFrontier.NumberTheory.TraceFormula.GaitsgoryFiniteness`, which derives the finiteness from
the arithmetic input of Gaitsgory's construction by an actual argument. -/
theorem finite_geometricMonodromy_of_two_mul_lt [Finite k] [IsAlgClosed K] [Smooth f]
    (p : ℕ) [CharP k p] [Fact ℓ.Prime]
    (x : GeometricPoint (geometricBaseChange k K f))
    [∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)]
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (hproj : IsProjective f) (hℓp : ℓ ≠ p) (hn : 2 * n < ℓ)
    (formalism : FSheafFormalism k ℓ)
    (satake : ExtendedGeometricSatake k ℓ formalism)
    (hGaitsgory : ∀ F : FSheafFormalism k ℓ, ExtendedGeometricSatake k ℓ F →
      IsProjective f → ℓ ≠ p → 2 * n < ℓ → IsTrivialOnOpenSubgroup k K f x ρ) :
    Finite (geometricMonodromy k K f x ρ) :=
  finite_geometricMonodromy_of_isTrivialOnOpenSubgroup k K f x ρ
    (hGaitsgory formalism satake hproj hℓp hn)

end Stacks.TraceFormula

end
