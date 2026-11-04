module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Homology.TorAmplitude.Defs

@[expose] public section

/-!
# Tor-amplitude and distinguished triangles

Let `R` be a commutative ring and let `D(R)` denote the derived category of `R`-modules. This
file proves the three implications of Stacks Tag 0655: in a distinguished triangle `(K, L, M)`,
tor-amplitude of two of the three vertices in suitable ranges forces tor-amplitude of the third.

The Tag 0655 endpoints are stated for the Tor-amplitude predicate
`StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks 0652, that is, relative to a derived tensor
bifunctor *certified* by the comparison maps with termwise ordinary tensor product together with
the universal property making each `- ⊗ᴸ M[0]` the total left derived functor of `- ⊗ M`, with
the ring and the module carriers in independent universes.

The file also keeps a weaker auxiliary layer: the same three implications relative to a *derived
tensoring datum* `Stacks.TorAmplitudeTriangle.DerivedTensoring`, which is a bare family of
triangulated endofunctors with no comparison to the tensor product. That layer is what downstream
files in this tree (`StacksFrontier.Homology.TorAmplitude.Composition`, `.Criteria`) are phrased
against; it does *not* state Tag 0655, because nothing in it ties the functors to the tensor
product.

## Main declarations

* `StacksDraft.TorAmplitude.hasTorAmplitude_obj₃_of_obj₁_obj₂`,
  `StacksDraft.TorAmplitude.hasTorAmplitude_obj₂_of_obj₁_obj₃`,
  `StacksDraft.TorAmplitude.hasTorAmplitude_obj₁_of_obj₂_obj₃`: the three parts of Tag 0655,
  for the certified derived tensor product.
* `Stacks.TorAmplitudeTriangle.DerivedTensoring`: the datum of a triangulated endofunctor
  `- ⊗_R^L M : D(R) ⥤ D(R)` for every `R`-module `M`.
* `Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn`: tor-amplitude relative to such a datum.
* `Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₃_of_obj₁_obj₂`,
  `Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₂_of_obj₁_obj₃`,
  `Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₁_of_obj₂_obj₃`: the uncertified-datum form of
  the three implications.
* `Stacks.TorAmplitudeTriangle.DerivedTensoringLarge` and
  `Stacks.TorAmplitudeTriangle.HasTorAmplitudeInLarge`: the datum and the Tor-amplitude predicate
  with the module carriers in a universe independent of the ring's. A statement relating two rings
  that do not share a universe — Stacks 0H75 in `StacksFrontier.Homology.TorAmplitude.Nilpotent` — has
  to be phrased against these, since `DerivedCat R` puts the modules in the universe of `R`. At an
  equal module universe they are the two notions above.
-/

/-
# Problem Description

This is Stacks Project Tag 0655 (lemma `lemma-cone-tor-amplitude`).

Let `R` be a (commutative) ring and let `D(R)` denote the derived category of
`R`-modules.

## Main Definition 1 (Tor-amplitude)

An object `K ∈ D(R)` has tor-amplitude in `[a, b]` if for every `R`-module `M`
we have `Hⁱ(K ⊗_R^L M) = 0` for all `i ∉ [a, b]` (i.e. for `i < a` or `b < i`),
where `⊗_R^L` is the derived tensor product, `M` is placed in degree `0`, and
`Hⁱ` is the `i`-th cohomology of `D(R)`.

## Main Definition 2 (Distinguished triangle)

A distinguished triangle in `D(R)` is a triangle
`K → L → M → K[1]` belonging to the class of distinguished triangles of the
triangulated category `D(R)`.

## Main Statements

Given a distinguished triangle `(K, L, M, f, g, h)` in `D(R)` and `a, b ∈ ℤ`:

1. If `K` has tor-amplitude in `[a+1, b+1]` and `L` has tor-amplitude in
   `[a, b]`, then `M` has tor-amplitude in `[a, b]`.
2. If `K` and `M` both have tor-amplitude in `[a, b]`, then `L` has
   tor-amplitude in `[a, b]`.
3. If `L` has tor-amplitude in `[a+1, b+1]` and `M` has tor-amplitude in
   `[a, b]`, then `K` has tor-amplitude in `[a+1, b+1]`.

## Notes and Conventions

- Cohomological (upper) indexing is used: `Hⁱ` is cohomology in degree `i` and
  `K[1]` satisfies `Hⁱ(K[1]) = Hⁱ⁺¹(K)`.

- The key proof input is that, for any `R`-module `M`, the functor `- ⊗_R^L M`
  is an exact (triangulated) endofunctor of `D(R)`, so it maps the given
  distinguished triangle to a distinguished triangle and hence gives a long
  exact cohomology sequence. Each claim follows by tracking vanishing along
  this long exact sequence.

- The statement holds for arbitrary integers `a, b`; no assumption `a ≤ b` is
  required (if `a > b`, tor-amplitude in `[a, b]` forces the object to be zero).

## Formalization remark

Mathlib provides the derived category `DerivedCategory (ModuleCat R)`, its
`ℤ`-indexed cohomology `DerivedCategory.homologyFunctor`, the pretriangulated
structure with distinguished triangles, the fact that each cohomology functor is
homological with the associated long exact sequence
(`DerivedCategory.HomologySequence.exact₁/₂/₃`), and that a triangulated functor
maps distinguished triangles to distinguished triangles
(`Functor.map_distinguished`).

Mathlib does *not* (currently) provide the derived tensor product
`- ⊗_R^L M : D(R) ⥤ D(R)` as a packaged functor. The *proof* of Tag 0655 uses
only that `- ⊗_R^L M` is a triangulated endofunctor of `D(R)` (which yields the
long exact cohomology sequence), and the `Stacks.TorAmplitudeTriangle.DerivedTensoring` layer below
isolates exactly that: a bare family of triangulated endofunctors
`derTensor M : D(R) ⥤ D(R)` indexed by `R`-modules `M`.

That layer is, however, *not* a statement of Tag 0655: nothing in it identifies
`derTensor M` with the derived tensor product, so it says nothing about
Tor amplitude. The Tag 0655 endpoints are therefore stated separately, for the
Tor-amplitude predicate `StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks
0652, whose `comparison` and `isLeftDerived` arguments pin the bifunctor down as
*the* derived tensor product; the triangulated structure of each `- ⊗ᴸ M[0]` is
then an additional hypothesis, exactly as in the source statement.
-/

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

universe u v w

namespace Stacks.TorAmplitudeTriangle

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The derived category `D(R)` of `R`-modules. -/
abbrev DerivedCat := DerivedCategory (ModuleCat.{u} R)

/-- A *derived tensoring datum* over `R`: for every `R`-module `M`, a triangulated
endofunctor `derTensor M : D(R) ⥤ D(R)` representing `- ⊗_R^L M`.  This is the data
needed to state tor-amplitude; the genuine derived tensor product `- ⊗_R^L M` is an
instance of such a datum. -/
structure DerivedTensoring where
  /-- The functor `- ⊗_R^L M : D(R) ⥤ D(R)`. -/
  derTensor : ModuleCat.{u} R → DerivedCat R ⥤ DerivedCat R
  /-- `- ⊗_R^L M` commutes with the shift. -/
  commShift : ∀ M, (derTensor M).CommShift ℤ
  /-- `- ⊗_R^L M` is a triangulated (exact) functor. -/
  isTriangulated : ∀ M, letI := commShift M; (derTensor M).IsTriangulated

attribute [instance] DerivedTensoring.commShift DerivedTensoring.isTriangulated

variable {R}

/-- **Tor-amplitude.** An object `K ∈ D(R)` *has tor-amplitude in `[a, b]`* (with
respect to a derived tensoring datum `D`) if for every `R`-module `M` and every
integer `i` with `i < a` or `b < i`, the cohomology `Hⁱ(K ⊗_R^L M)` vanishes. -/
def HasTorAmplitudeIn (D : DerivedTensoring R) (K : DerivedCat R) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj ((D.derTensor M).obj K))

/-! ## The propagation implications over an uncertified datum

These are the long-exact-sequence implications over an arbitrary family of triangulated
endofunctors. They are **not** the Tag 0655 endpoints: a `DerivedTensoring` datum carries no
comparison with ordinary tensor product and no total-left-derived universal property, so
`HasTorAmplitudeIn` against an arbitrary such datum is not Tor amplitude. The Tag 0655
endpoints are `StacksDraft.TorAmplitude.hasTorAmplitude_obj₃_of_obj₁_obj₂` and its two
companions at the end of this file; these lemmas are the shape their downstream consumers in
this tree (`.Composition`, `.Criteria`) use.
-/

/-- In a distinguished triangle `(K, L, M)`, if `K` has tor-amplitude in `[a+1, b+1]` and `L`
has tor-amplitude in `[a, b]`, then `M` has tor-amplitude in `[a, b]`, relative to an arbitrary
derived tensoring datum.

This is the uncertified-datum helper for part (1) of Tag 0655, not the tag endpoint: the datum
`D` is an arbitrary family of triangulated endofunctors, unrelated to the tensor product. The
endpoint is `StacksDraft.TorAmplitude.hasTorAmplitude_obj₃_of_obj₁_obj₂`. -/
theorem hasTorAmplitudeIn_obj₃_of_obj₁_obj₂
    (D : DerivedTensoring R) (T : Triangle (DerivedCat R)) (hT : T ∈ distTriang (DerivedCat R))
    (a b : ℤ)
    (hK : HasTorAmplitudeIn D T.obj₁ (a + 1) (b + 1))
    (hL : HasTorAmplitudeIn D T.obj₂ a b) :
    HasTorAmplitudeIn D T.obj₃ a b := by
  intro M i hi
  -- long exact sequence: `Hⁱ(FL) → Hⁱ(FM) → Hⁱ⁺¹(FK)`
  have hex := DerivedCategory.HomologySequence.exact₃ ((D.derTensor M).mapTriangle.obj T)
    ((D.derTensor M).map_distinguished T hT) i (i + 1) rfl
  exact hex.isZero_of_both_zeros ((hL M i hi).eq_zero_of_src _)
    ((hK M (i + 1) (by omega)).eq_zero_of_tgt _)

/-- In a distinguished triangle `(K, L, M)`, if `K` and `M` both have tor-amplitude in `[a, b]`,
then `L` has tor-amplitude in `[a, b]`, relative to an arbitrary derived tensoring datum.

This is the uncertified-datum helper for part (2) of Tag 0655, not the tag endpoint: the datum
`D` is an arbitrary family of triangulated endofunctors, unrelated to the tensor product. The
endpoint is `StacksDraft.TorAmplitude.hasTorAmplitude_obj₂_of_obj₁_obj₃`. -/
theorem hasTorAmplitudeIn_obj₂_of_obj₁_obj₃
    (D : DerivedTensoring R) (T : Triangle (DerivedCat R)) (hT : T ∈ distTriang (DerivedCat R))
    (a b : ℤ)
    (hK : HasTorAmplitudeIn D T.obj₁ a b)
    (hM : HasTorAmplitudeIn D T.obj₃ a b) :
    HasTorAmplitudeIn D T.obj₂ a b := by
  intro M i hi
  -- long exact sequence: `Hⁱ(FK) → Hⁱ(FL) → Hⁱ(FM)`
  have hex := DerivedCategory.HomologySequence.exact₂ ((D.derTensor M).mapTriangle.obj T)
    ((D.derTensor M).map_distinguished T hT) i
  exact hex.isZero_of_both_zeros ((hK M i hi).eq_zero_of_src _)
    ((hM M i hi).eq_zero_of_tgt _)

/-- In a distinguished triangle `(K, L, M)`, if `L` has tor-amplitude in `[a+1, b+1]` and `M`
has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in `[a+1, b+1]`, relative to an
arbitrary derived tensoring datum.

This is the uncertified-datum helper for part (3) of Tag 0655, not the tag endpoint: the datum
`D` is an arbitrary family of triangulated endofunctors, unrelated to the tensor product. The
endpoint is `StacksDraft.TorAmplitude.hasTorAmplitude_obj₁_of_obj₂_obj₃`. -/
theorem hasTorAmplitudeIn_obj₁_of_obj₂_obj₃
    (D : DerivedTensoring R) (T : Triangle (DerivedCat R)) (hT : T ∈ distTriang (DerivedCat R))
    (a b : ℤ)
    (hL : HasTorAmplitudeIn D T.obj₂ (a + 1) (b + 1))
    (hM : HasTorAmplitudeIn D T.obj₃ a b) :
    HasTorAmplitudeIn D T.obj₁ (a + 1) (b + 1) := by
  intro M i hi
  -- long exact sequence: `Hⁱ⁻¹(FM) → Hⁱ(FK) → Hⁱ(FL)`
  have hex := DerivedCategory.HomologySequence.exact₁ ((D.derTensor M).mapTriangle.obj T)
    ((D.derTensor M).map_distinguished T hT) (i - 1) i (by omega)
  exact hex.isZero_of_both_zeros ((hM M (i - 1) (by omega)).eq_zero_of_src _)
    ((hL M i hi).eq_zero_of_tgt _)

/-! ## The datum and the Tor-amplitude predicate at an independent module universe

`DerivedTensoring` above puts the module carriers in the universe of `R`, because
`DerivedCat R` is `DerivedCategory (ModuleCat.{u} R)`. Stacks 0652 leaves the two universes
independent, and a statement relating two rings that do *not* share a universe — Stacks 0H75, for
instance — needs both derived categories in one module universe above both rings. The datum and
the predicate are therefore repeated here with the module carriers in `ModuleCat.{max u v} R`, `v`
independent of `u`. At `v = u` they are the same notions as above.
-/

section Large

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The derived category `D(R)` of `R`-modules, with the module carriers in the universe
`max u v`, independent of the universe `u` of `R`. -/
abbrev DerivedCatLarge := DerivedCategory (ModuleCat.{max u v} R)

/-- A *derived tensoring datum* over `R` with the module carriers in a universe `max u v`
independent of the universe of `R`: for every `R`-module `M`, a triangulated endofunctor
`derTensor M : D(R) ⥤ D(R)` representing `- ⊗_R^L M`. This is `DerivedTensoring` with the module
universe freed; at `v = u` it is that structure. -/
structure DerivedTensoringLarge where
  /-- The functor `- ⊗_R^L M : D(R) ⥤ D(R)`. -/
  derTensor : ModuleCat.{max u v} R → DerivedCatLarge R ⥤ DerivedCatLarge R
  /-- `- ⊗_R^L M` commutes with the shift. -/
  commShift : ∀ M, (derTensor M).CommShift ℤ
  /-- `- ⊗_R^L M` is a triangulated (exact) functor. -/
  isTriangulated : ∀ M, letI := commShift M; (derTensor M).IsTriangulated

attribute [instance] DerivedTensoringLarge.commShift DerivedTensoringLarge.isTriangulated

variable {R}

/-- **Tor amplitude, at an independent module universe.** An object `K ∈ D(R)` *has tor-amplitude
in `[a, b]`* with respect to a derived tensoring datum `D` if for every `R`-module `M` and every
integer `i` with `i < a` or `b < i`, the cohomology `Hⁱ(K ⊗_R^L M)` vanishes. This is
`HasTorAmplitudeIn` with the module carriers in a universe independent of the ring's. -/
def HasTorAmplitudeInLarge (D : DerivedTensoringLarge.{u, v, w} R)
    (K : DerivedCatLarge.{u, v, w} R) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{max u v} R) (i : ℤ), (i < a ∨ b < i) →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((D.derTensor M).obj K))

end Large

end Stacks.TorAmplitudeTriangle

namespace StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-! ## Tag 0655

The endpoints, for the Tor amplitude of Stacks 0652: the derived tensor bifunctor comes with the
comparison maps `comparison` to termwise ordinary tensor product and with `isLeftDerived`, the
universal property making each `- ⊗ᴸ M[0]` the total left derived functor of `- ⊗ M`. Those two
arguments are what identify the bifunctor with the derived tensor product, so the vanishing
condition really is Tor amplitude and not a statement about an arbitrary functor. The remaining
two hypotheses `commShift` and `triangulated` say that each `- ⊗ᴸ M[0]` is a triangulated
endofunctor of `D(R)`; they are the exactness input of the source statement, and are the only
thing the proof uses beyond the vanishing hypotheses.

The ring `R` lives in `Type u` and the module carriers in `ModuleCat.{v} R` with `v` independent
of `u`, as in Stacks 0652.
-/

section Certified

variable {R : Type u} [CommRing R]
    (derivedTensor :
      DerivedCategory (ModuleCat.{v} R) ⥤
        DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R))
    (comparison : ∀ M : ModuleCat.{v} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)))
    (commShift : ∀ M : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).CommShift ℤ)
    (triangulated : ∀ M : ModuleCat.{v} R, letI := commShift M;
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsTriangulated)

/-- Tor amplitude of Stacks 0652 written with the endofunctor `- ⊗ᴸ N[0]` in flipped form and
with the excluded degrees spelled `i < a ∨ b < i`. This is the shape in which the long exact
cohomology sequence of a distinguished triangle produces the vanishing statements.

The bridge is reproved here rather than taken from
`StacksDraft.TorAmplitude.hasTorAmplitudeIn_iff_hasTorAmplitude`, which says the same thing for
a `Stacks.TorAmplitudeTriangle.DerivedTensoring` datum, because that lemma lives in
`StacksFrontier.Homology.TorAmplitude.Composition`, which imports this file. -/
private lemma hasTorAmplitude_iff_flip (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) :
    HasTorAmplitude derivedTensor comparison isLeftDerived K a b ↔
      ∀ (N : ModuleCat.{v} R) (i : ℤ), (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
          ((derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)).obj K)) := by
  simp only [HasTorAmplitude, Set.mem_Icc, not_and_or, not_le, Functor.flip_obj_obj]

include commShift triangulated in
/-- **Stacks 0655 (1).** Let `K → L → M → K[1]` be a distinguished triangle in `D(R)`. If `K`
has Tor amplitude in `[a + 1, b + 1]` and `L` has Tor amplitude in `[a, b]`, then `M` has Tor
amplitude in `[a, b]`.

Tor amplitude is `StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks 0652, so the bifunctor
`derivedTensor` is certified by `comparison` and `isLeftDerived` to be the derived tensor
product. This is part (1) of the source statement; the mathematics is the long exact cohomology
sequence of the triangle `(K, L, M)` tensored with `M'[0]`, as in the uncertified-datum helper
`Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₃_of_obj₁_obj₂`, which this endpoint does not use
because that helper pins the module carriers to the ring universe. -/
@[stacks 0655 "(1)"]
theorem hasTorAmplitude_obj₃_of_obj₁_obj₂
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R))) (a b : ℤ)
    (hK : HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₁ (a + 1) (b + 1))
    (hL : HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₂ a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₃ a b := by
  rw [hasTorAmplitude_iff_flip] at hK hL ⊢
  intro N i hi
  let := commShift N
  have := triangulated N
  let F := derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)
  -- long exact sequence: `Hⁱ(F L) → Hⁱ(F M) → Hⁱ⁺¹(F K)`
  have hex := DerivedCategory.HomologySequence.exact₃
    (F.mapTriangle.obj T) (F.map_distinguished T hT)
    i (i + 1) rfl
  exact hex.isZero_of_both_zeros ((hL N i hi).eq_zero_of_src _)
    ((hK N (i + 1) (by omega)).eq_zero_of_tgt _)

include commShift triangulated in
/-- **Stacks 0655 (2).** Let `K → L → M → K[1]` be a distinguished triangle in `D(R)`. If `K`
and `M` both have Tor amplitude in `[a, b]`, then `L` has Tor amplitude in `[a, b]`.

Tor amplitude is `StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks 0652, so the bifunctor
`derivedTensor` is certified by `comparison` and `isLeftDerived` to be the derived tensor
product. This is part (2) of the source statement; the mathematics is the long exact cohomology
sequence of the triangle `(K, L, M)` tensored with `M'[0]`, as in the uncertified-datum helper
`Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₂_of_obj₁_obj₃`, which this endpoint does not use
because that helper pins the module carriers to the ring universe. -/
@[stacks 0655 "(2)"]
theorem hasTorAmplitude_obj₂_of_obj₁_obj₃
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R))) (a b : ℤ)
    (hK : HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₁ a b)
    (hM : HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₃ a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₂ a b := by
  rw [hasTorAmplitude_iff_flip] at hK hM ⊢
  intro N i hi
  let := commShift N
  have := triangulated N
  let F := derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)
  -- long exact sequence: `Hⁱ(F K) → Hⁱ(F L) → Hⁱ(F M)`
  have hex := DerivedCategory.HomologySequence.exact₂
    (F.mapTriangle.obj T) (F.map_distinguished T hT) i
  exact hex.isZero_of_both_zeros ((hK N i hi).eq_zero_of_src _)
    ((hM N i hi).eq_zero_of_tgt _)

include commShift triangulated in
/-- **Stacks 0655 (3).** Let `K → L → M → K[1]` be a distinguished triangle in `D(R)`. If `L`
has Tor amplitude in `[a + 1, b + 1]` and `M` has Tor amplitude in `[a, b]`, then `K` has Tor
amplitude in `[a + 1, b + 1]`.

Tor amplitude is `StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks 0652, so the bifunctor
`derivedTensor` is certified by `comparison` and `isLeftDerived` to be the derived tensor
product. This is part (3) of the source statement; the mathematics is the long exact cohomology
sequence of the triangle `(K, L, M)` tensored with `M'[0]`, as in the uncertified-datum helper
`Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₁_of_obj₂_obj₃`, which this endpoint does not use
because that helper pins the module carriers to the ring universe. -/
@[stacks 0655 "(3)"]
theorem hasTorAmplitude_obj₁_of_obj₂_obj₃
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R))) (a b : ℤ)
    (hL : HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₂ (a + 1) (b + 1))
    (hM : HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₃ a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₁ (a + 1) (b + 1) := by
  rw [hasTorAmplitude_iff_flip] at hL hM ⊢
  intro N i hi
  let := commShift N
  have := triangulated N
  let F := derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)
  -- long exact sequence: `Hⁱ⁻¹(F M) → Hⁱ(F K) → Hⁱ(F L)`
  have hex := DerivedCategory.HomologySequence.exact₁
    (F.mapTriangle.obj T) (F.map_distinguished T hT)
    (i - 1) i (by omega)
  exact hex.isZero_of_both_zeros ((hM N (i - 1) (by omega)).eq_zero_of_src _)
    ((hL N i hi).eq_zero_of_tgt _)

end Certified

/-- Tor amplitude against a derived tensoring datum only depends on the isomorphism class of the
object of the derived category. -/
public lemma hasTorAmplitudeIn_of_iso {R : Type u} [CommRing R]
    (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    {X Y : DerivedCategory (ModuleCat.{u} R)} (e : X ≅ Y) {a b : ℤ}
    (h : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D X a b) :
      Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D Y a b := by
  intro M i hi
  exact (h M i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso ((D.derTensor M).mapIso e.symm))

end StacksDraft.TorAmplitude
