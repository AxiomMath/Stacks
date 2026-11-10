module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.F6Rank201.WeilCohomologyBasePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# The cycle class of the fundamental class, and nonvanishing of cohomology

Let `H^*` be a Weil cohomology theory over `k` with coefficient field `F` of characteristic zero,
and let `X` be a nonempty smooth projective scheme over `k`. Then `γ([X]) = 1` in `H^0(X)` and
`1 ≠ 0` in `H^0(X)`. Together with the vanishing `H^*(∅) = 0` of
`Stacks.WeilCohomology.subsingleton_cohomology_of_empty` this is Stacks 0FHF. Neither clause
assumes `X` equidimensional.

Both proofs are the source's.

The first clause is the identity `[X] = p^*[Spec(k)]` for the structure morphism
`p : X ⟶ Spec(k)` — flat pullback of the fundamental class is the fundamental class, which is
`Stacks.Chow.flatPullbackChow_fundamentalChowClass` — followed by axiom `(C)(a)` for `p` and the
normalisation `γ([Spec(k)]) = 1` of Stacks 0FHE, which is
`Stacks.Weil.cycleClass_fundamentalClass_eq_one` and is applied here to the cohomology of the
base point rather than assumed. Axiom `(C)(a)` is about the Gysin map of a local
complete intersection morphism, but only a smooth `p` occurs here, and for a flat morphism the
Gysin map is flat pullback (Chow Homology, Tag 0FF4); so flat pullback is all that is needed and
no Gysin theory enters.

For the second clause, choose a closed point `x ∈ X` whose residue field is a finite separable
extension of `k`; such a point exists by Varieties, Tag 056U, which is
`AlgebraicGeometry.dense_closedPoints_with_finite_separable_residueField_of_smooth`. The source
pushes the fundamental class of `Spec(κ(x))` forward along `i : Spec(κ(x)) ⟶ X` and then along
`p`, applying `(C)(b)` twice; since `(C)(b)` for `i` rewrites `i_*γ([Spec(κ(x))])` as
`γ(i_*[Spec(κ(x))]) = γ([x])`, the same element is reached in one step from the class `[x]` of
the point in `A_0(X)`, and that is the route taken here. Pushing `[x]` forward to the base gives
`p_*[x] = [κ(x) : k] · [Spec(k)]` in `A_0(Spec(k))` — the degree computation of Stacks 0AZ1,
through `Stacks.Chow.chowGroupBaseEquivInt` and `Stacks.Chow.cycleDegree_single` — so `(C)(b)`
for `p` and `γ([Spec(k)]) = 1` give that `γ([x])` is carried by `p_*` to the degree
`[κ(x) : k]`, which is nonzero in `H^0(Spec(k))`: that ring is a nonzero algebra over the
coefficient field, so the coefficient field injects into it and carries its characteristic zero
along. Hence `γ([x])` is a nonzero element of `H^{2d}(X)(d)`, and the unit law `a ∪ 1 = a` of
the cup product then forces `1 ≠ 0` in `H^0(X)`: were the unit zero, every cohomology class
would be.

## Main results

* `Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one` — `γ([X]) = 1` in `H^0(X)`,
  for an arbitrary smooth `X`, with no equidimensionality hypothesis.
* `Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one_of_relativeDimension` — the same
  for `X` equidimensional of dimension `d`, where `CH^0(X)` is the single group `A_d(X)`.
* `Stacks.WeilCohomology.one_ne_zero_of_nonempty` — `1 ≠ 0` in `H^0(X)` for `X` nonempty.

Supporting facts proved here:

* `Stacks.WeilCohomology.schemeDeltaDimension_id_le_zero` — the base of a situation with
  vanishing dimension function has delta-dimension at most zero.
* `Stacks.WeilCohomology.residueDegree_ne_zero_of_finite` — the residue degree of the structure
  morphism at a point with finite residue field is nonzero.
* `Stacks.WeilCohomology.equidimensionalPiece` and
  `Stacks.WeilCohomology.relativeDimension_equidimensionalPiece` — the piece `X_d` of the
  source's decomposition `X = ∐_d X_d`, and its equidimensionality.
* `Stacks.WeilCohomology.degreeZeroChow`, `Stacks.WeilCohomology.fundamentalDegreeZeroChow` and
  `Stacks.WeilCohomology.structureFlatPullbackDegreeZero` — the group `CH^0(X)` of a smooth
  scheme over `k` in the product description of Stacks 0FE4, its fundamental class, and flat
  pullback along the structure morphism.
* `Stacks.WeilCohomology.structureFlatPullbackDegreeZero_fundamentalChowClass` — the identity
  `[X] = p^*[Spec(k)]` in `CH^0(X)`.

## Implementation notes

As in the rest of this directory the cohomological data is supplied as explicit arguments rather
than through a bundled Weil cohomology theory, while the cycle side uses the Chow groups of
`StacksDraft.AlgebraicGeometry.Chow` over the base situation
`Stacks.Chow.fieldChowSituation k`, whose base scheme is `Spec(k)`. The dictionary:

* `Hpt` is the graded cohomology `H^*(Spec(k))` of the base point and `HptZero` its degree-zero
  part, an `F`-algebra because `H^*(Spec(k))` is a graded `F`-algebra by `(D1)`;
  `degreeZeroPoint` is that identification. `kunnethPoint` is axiom `(B)(a)` for
  `Spec(k) ×_k Spec(k) = Spec(k)`, `integrationPoint` is `∫_{Spec(k)}` of `(D3)`,
  `integration_cycleClassPoint` is the normalisation axiom `(C)(d)`, and `cycleClassPoint_mul`
  is axiom `(C)(c)` for `[Spec(k)] · [Spec(k)] = [Spec(k)]`. Those are exactly the hypotheses of
  `Stacks.Weil.cycleClass_fundamentalClass_eq_one`, Stacks 0FHE, from which
  `γ([Spec(k)]) = 1` is obtained in each of the three proofs below.
* `HX` stands for `H^0(X)` and `one` for its unit; `cycleClassX` is the cycle class map `γ` of
  `X` in the relevant degree; `pullbackMap` is `p^* : H^0(Spec(k)) → H^0(X)`, and `pushforward`
  is `p_* : H^{2d}(X)(d) → H^0(Spec(k))`, the pushforward defined by Poincaré duality. `cup` is
  the cup product `H^{2d}(X)(d) × H^0(X) → H^{2d}(X)(d)` of the graded `F`-algebra `H^*(X)` of
  `(D1)`, and `cup_one` its unit law.
* `Stacks.Chow.chowGroup` is indexed by delta-dimension, which over a field is dimension, and
  not by codimension. The codimension-zero Chow group of a scheme whose components have
  different dimensions is therefore not one `chowGroup`, and Chapter 42 writes it as the product
  `CH^0(X) = ∏_d CH_d(X_d)` over the source's decomposition `X = ∐_d X_d` into open and closed
  subschemes equidimensional of dimension `d` (Stacks 0FE4). That decomposition is available
  here as `Stacks.WeilCohomology.equidimensionalPiece`, the locus where the structure morphism
  has relative dimension `d`, which is open and closed because that relative dimension is a
  locally constant function on a scheme smooth over a field. The group, the fundamental class
  `[X] = ([X_d])_d` and the flat pullback `p^*` are
  `Stacks.WeilCohomology.degreeZeroChow`,
  `Stacks.WeilCohomology.fundamentalDegreeZeroChow` and
  `Stacks.WeilCohomology.structureFlatPullbackDegreeZero`. The degree index on a piece is
  written `0 + d` because that is the degree the flat-pullback law produces out of
  `A_0(Spec(k))`. The second clause needs no decomposition at all: the class of a closed point
  lies in `A_0(X)` whatever the dimensions of the components of `X` are.
* The decomposition is therefore used on the cycle side only, where it is how `CH^0(X)` is
  defined. The cohomology of `X` enters the first clause through the single space `H^0(X)` and
  the single cycle class map `γ : CH^0(X) → H^0(X)` of `(D2)`, exactly as in the source: the
  restriction maps `H^0(X) → H^0(X_d)` play no part.
* The hypothesis `cycleClass_pullback` is axiom `(C)(a)` for `p` in the one degree where it is
  used, and `cycleClass_pushforward` is axiom `(C)(b)` for `p`.
* Projectivity of `X` enters only through properness of `p`, which is what the pushforward of
  cycles and the degree homomorphism require; `IsProper` is therefore the hypothesis.
* The data and the axioms are spelled out as binders rather than projected out of a bundled
  datum because Section 45.9 has no bundle in this repository that these clauses could use. The
  two candidates both package condition `(A)` of that section, and neither applies here.
  `Stacks.WeilCohomology.PoincareDualityPushforwardSetup`
  (`StacksFrontier/AlgebraicGeometry/WeilCohomology/ProjectionFormula/Setup.lean:110`, whose trace
  map is the field `integration` at line 135) and
  `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` (`ClassicalTheory.lean:158`) both
  require `[IsAlgClosed k]`, which Tag 0FHF does not assume, so routing through either would add
  a hypothesis to all three clauses. Both put cohomology on
  `(SmoothProjective k).FullSubcategory`, whose objects carry `IsProjectiveMorphism`
  (`StacksFrontier/AlgebraicGeometry/WeilCohomology/ProjectionFormula/Setup.lean:102`). And the
  cycle side of the latter is
  `Stacks.WeilCohomology.ChowCycleData` (`ClassicalTheory.lean:123`), a family of abelian groups
  with no laws of their own, whereas the clauses below are about the Chow groups of chapter 42
  and go through `Stacks.Chow.flatPullbackChow_fundamentalChowClass`,
  `Stacks.Chow.chowGroupBaseEquivInt` and `Stacks.Chow.cycleDegree_single`.
* Spelling the data out is this chapter's convention, recorded at
  `StacksFrontier/AlgebraicGeometry/WeilCohomology/SeparableExtension.lean:53`. Stacks 0FHE does it
  at `StacksFrontier/AlgebraicGeometry/F6Rank201/WeilCohomologyBasePoint.lean:91-97`, Stacks 0FHG
  in the very encoding used here at `ClosedSubschemeClass.lean:88-125`, and Stacks 0FIK at
  `TraceMap.lean:185-186`.
* Each binder is a map together with the law the source states for it: `cycleClassX` and
  `cycleClassPoint` are homomorphisms out of Chow groups, `pullbackMap`, `pushforward` and
  `integrationPoint` are linear maps, and `cycleClass_pullback`, `cycleClass_pushforward` and
  `cup_one` range over every cycle and every class rather than over one. Three binders are a
  single element or a single equation because the source states them that way: `one`, the unit
  of the graded ring of `(D1)`, pinned by `pullbackMap_one` and `cup_one`, as in 0FHG's `one` at
  `ClosedSubschemeClass.lean:110`; `integration_cycleClassPoint`, which is axiom `(C)(d)`,
  `∫_{Spec(k)} γ([Spec(k)]) = 1`; and `cycleClassPoint_mul`, which is axiom `(C)(c)` for
  `[Spec(k)] · [Spec(k)] = [Spec(k)]`. The last two go unchanged into Stacks 0FHE as its
  `trace_fundamental` and `cycleClass_fundamental_mul`
  (`StacksFrontier/AlgebraicGeometry/F6Rank201/WeilCohomologyBasePoint.lean:94`,
  `:95-97`), while `Z` and `fundamentalClass` of that theorem (`:91-92`) are instantiated here
  at `Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (𝟙 _) 0` and its own
  `Stacks.Chow.fundamentalChowClass`, so no free abelian group and no free fundamental class
  remain on the cycle side.
* Reading the normalisation at the unit instead, as `integrationPoint 1 = 1`, would be the
  fourth clause of Stacks 0FHE itself, `Stacks.Weil.trace_one_eq_one`
  (`StacksFrontier/AlgebraicGeometry/F6Rank201/WeilCohomologyBasePoint.lean:174`), and the
  identification that licenses the exchange is
  `γ([Spec(k)]) = 1`, which is what these clauses derive; so the normalisation stays at the
  fundamental class.

## References

* [Stacks Project, Tag 0FHF](https://stacks.math.columbia.edu/tag/0FHF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u v w x

namespace Stacks.WeilCohomology

/-- Over a base whose dimension function vanishes, the base scheme has delta-dimension at most
zero. -/
theorem schemeDeltaDimension_id_le_zero (C : Stacks.Chow.ChowSituation.{u})
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0) :
    schemeDeltaDimension C (𝟙 C.S) ≤ (((0 : ℤ)) : EInt) := by
  refine iSup_le fun Z ↦ ?_
  rw [deltaDimension, relativeDimension_id, hδ]

/-- At a point whose residue field is a finite extension of the base field, the residue degree
of the structure morphism is nonzero. -/
theorem residueDegree_ne_zero_of_finite (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec (.of k)) (x : X)
    (hfin : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.Finite k (X.residueField x)) :
    p.residueDegree x ≠ 0 := by
  let S := AlgebraicGeometry.Spec (CommRingCat.of k)
  let y := p.base x
  let K := S.residueField y
  let L := X.residueField x
  let : Algebra k K := (((Scheme.ΓSpecIso (.of k)).inv ≫ S.Γevaluation y).hom).toAlgebra
  let : Algebra K L := (p.residueFieldMap x).hom.toAlgebra
  let : Algebra k L :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun a ↦
    (Scheme.Γevaluation_naturality_apply p x ((Scheme.ΓSpecIso (.of k)).inv.hom a)).symm
  have : Module.Finite k L := hfin
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite k K L
  change Module.finrank K L ≠ 0
  exact Module.finrank_pos.ne'

/-! ### The decomposition into equidimensional pieces -/

/-- **The piece `X_d` of the decomposition `X = ∐_d X_d`.** For `X` smooth over `k`, the open and
closed subscheme of `X` on which the structure morphism has relative dimension `d` — that is, the
union of the `d`-dimensional connected components of `X`. -/
abbrev equidimensionalPiece {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [Smooth p] (d : ℕ) : X.Opens :=
  AlgebraicGeometry.relativeDimensionOpen p
    (AlgebraicGeometry.isCohenMacaulay_fiber_of_smooth p) d

/-- The piece `X_d` is equidimensional of dimension `d`: its structure morphism has relative
dimension `d`. -/
theorem relativeDimension_equidimensionalPiece {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [Smooth p] (d : ℕ) :
    AlgebraicGeometry.RelativeDimension ((equidimensionalPiece p d).ι ≫ p) d :=
  AlgebraicGeometry.relativeDimensionOpen_relativeDimension p _ d

/-- **`CH^0(X)` for a smooth scheme over `k`, in the product description of Stacks 0FE4.** The
degree-zero Chow group of `X` is the product `∏_d CH_d(X_d)` over the pieces `X_d` of the
canonical decomposition `X = ∐_d X_d` into open and closed subschemes equidimensional of
dimension `d`, so that on each piece the codimension-zero group is the single group
`A_d(X_d)`. Only nonnegative `d` occur, the relative dimension of a scheme smooth over a field
being nonnegative. -/
abbrev degreeZeroChow {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [Smooth p] : Type u :=
  ∀ d : ℕ, chowGroup (fieldChowSituation k) ((equidimensionalPiece p d).ι ≫ p) (0 + (d : ℤ))

/-- **The fundamental class `[X] ∈ CH^0(X)`** of a smooth scheme over `k`: the family whose
`d`th coordinate is the fundamental class `[X_d] ∈ A_d(X_d)` of the `d`-dimensional piece. -/
def fundamentalDegreeZeroChow {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [Smooth p] : degreeZeroChow p := fun d ↦
  fundamentalChowClass (fieldChowSituation k) ((equidimensionalPiece p d).ι ≫ p) (0 + (d : ℤ))

/-- **Flat pullback `p^* : CH^0(Spec(k)) → CH^0(X)` along the structure morphism.** On the piece
`X_d` it is the flat pullback of Stacks 02RB along `X_d ⟶ Spec(k)`, which is flat of relative
dimension `d`, and therefore raises the dimension index by `d`. -/
def structureFlatPullbackDegreeZero {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [Smooth p] :
    chowGroup (fieldChowSituation k) (𝟙 _) 0 →+ degreeZeroChow p :=
  AddMonoidHom.pi fun d ↦ flatPullbackChowOfRelativeDimension (fieldChowSituation k)
    ((equidimensionalPiece p d).ι ≫ p) (𝟙 _) ((equidimensionalPiece p d).ι ≫ p)
    (Category.comp_id _) d (relativeDimension_equidimensionalPiece p d) 0

/-- Flat pullback of the fundamental class of the base along a flat morphism of relative
dimension `d` is the fundamental class. -/
private theorem flatPullbackChow_fundamentalChowClass_base {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [Flat p]
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension p d) :
    flatPullbackChowOfRelativeDimension (fieldChowSituation k) p (𝟙 _) p
        (Category.comp_id p) d hd 0 (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) =
      fundamentalChowClass (fieldChowSituation k) p (0 + (d : ℤ)) :=
  flatPullbackChow_fundamentalChowClass (fieldChowSituation k) p (𝟙 _) p
    (Category.comp_id p) d hd 0 _
    (schemeDeltaDimension_id_le_zero (fieldChowSituation k) fun _ ↦ rfl)

/-- **`[X] = p^*[Spec(k)]`**: the fundamental class of a smooth scheme over `k` is the flat
pullback of the fundamental class of the base along the structure morphism. This is the
geometric step of the source's proof of the first clause of Stacks 0FHF, and it is a fact about
Chow groups alone: on each piece it is
`Stacks.Chow.flatPullbackChow_fundamentalChowClass`. -/
theorem structureFlatPullbackDegreeZero_fundamentalChowClass {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [Smooth p] :
    structureFlatPullbackDegreeZero p (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) =
      fundamentalDegreeZeroChow p := by
  funext d
  exact flatPullbackChow_fundamentalChowClass_base _ d
    (relativeDimension_equidimensionalPiece p d)

/-! ### The cohomology of the base point

The data `(D1)`, `(D2)` and `(D3)` at `Spec(k)` together with the axioms `(A)(a)`, `(B)(a)`,
`(C)(c)` and `(C)(d)` there. These are the hypotheses of
`Stacks.Weil.cycleClass_fundamentalClass_eq_one`, Stacks 0FHE, and every statement below obtains
`γ([Spec(k)]) = 1` from them by that theorem. -/

variable {k : Type u} [Field k] {F : Type v} [Field F]
  (Hpt : ℤ → Type x) [∀ i : ℤ, AddCommGroup (Hpt i)] [∀ i : ℤ, Module F (Hpt i)]
  [∀ i : ℤ, FiniteDimensional F (Hpt i)]
  (HptZero : Type x) [CommRing HptZero] [Algebra F HptZero]
  (degreeZeroPoint : Hpt 0 ≃ₗ[F] HptZero)
  (kunnethPoint : ∀ n : ℤ,
    DirectSum ℤ (fun j : ℤ ↦ TensorProduct F (Hpt j) (Hpt (n - j))) ≃ₗ[F] Hpt n)
  (cycleClassPoint : chowGroup (fieldChowSituation k) (𝟙 _) 0 →+ HptZero)
  (integrationPoint : HptZero →ₗ[F] F)
  (integration_cycleClassPoint :
    integrationPoint (cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0)) = 1)
  (cycleClassPoint_mul :
    cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) *
        cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) =
      cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0))

/-! ### The cycle class of the fundamental class -/

include degreeZeroPoint kunnethPoint integration_cycleClassPoint cycleClassPoint_mul in
/-- **The equidimensional form of the first clause of Stacks 0FHF.** Let `X` be a smooth scheme
over `k`, equidimensional of dimension `d`, with structure morphism `p : X ⟶ Spec(k)`. Then the
cycle class of the fundamental class `[X] ∈ CH^0(X) = A_d(X)` is the unit of `H^0(X)`.

The tag itself assumes no equidimensionality;
`Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one` is the same statement for an
arbitrary smooth `X`, with `CH^0(X)` written as the product over the pieces of the decomposition
`X = ∐_d X_d`, and it is that theorem which carries the tag. Here `CH^0(X)` is the single group
`A_d(X)`.

The hypotheses are axiom `(C)(a)` for `p`, that the cycle class map commutes with flat pullback,
the fact that `p^*` carries the unit to the unit, and the data and axioms at the base point from
which Stacks 0FHE gives `γ([Spec(k)]) = 1`. Nonemptiness of `X` is not needed: for `X` empty
both sides vanish. -/
theorem cycleClass_fundamentalChowClass_eq_one_of_relativeDimension
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [Flat p]
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension p d)
    {HX : Type w} [AddCommGroup HX] [Module F HX] (one : HX)
    (cycleClassX : chowGroup (fieldChowSituation k) p (0 + (d : ℤ)) →+ HX)
    (pullbackMap : HptZero →ₗ[F] HX)
    (cycleClass_pullback : ∀ α,
      cycleClassX (flatPullbackChowOfRelativeDimension (fieldChowSituation k) p (𝟙 _) p
          (Category.comp_id p) d hd 0 α) =
        pullbackMap (cycleClassPoint α))
    (pullbackMap_one : pullbackMap 1 = one) :
    cycleClassX (fundamentalChowClass (fieldChowSituation k) p (0 + (d : ℤ))) = one := by
  have hpoint : cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) = 1 :=
    Stacks.Weil.cycleClass_fundamentalClass_eq_one F Hpt kunnethPoint HptZero degreeZeroPoint
      _ _ cycleClassPoint integrationPoint integration_cycleClassPoint cycleClassPoint_mul
  rw [← flatPullbackChow_fundamentalChowClass_base p d hd, cycleClass_pullback, hpoint,
    pullbackMap_one]

include degreeZeroPoint kunnethPoint integration_cycleClassPoint cycleClassPoint_mul in
/-- **Stacks Project, Tag 0FHF**, the first clause of the nonempty case, for an arbitrary smooth
projective scheme `X` over `k`. The cycle class of the fundamental class `[X] ∈ CH^0(X)` is the
unit of `H^0(X)`.

No equidimensionality is assumed, and nothing about the cohomology of `X` beyond the cycle class
map `γ : CH^0(X) → H^0(X)` of `(D2)` enters. The proof is the source's two steps and nothing
else: `[X] = p^*[Spec(k)]`, which is
`Stacks.WeilCohomology.structureFlatPullbackDegreeZero_fundamentalChowClass`, and then axiom
`(C)(a)` for the structure morphism `p`, which is the hypothesis `cycleClass_pullback`, followed
by Stacks 0FHE, the identity `γ([Spec(k)]) = 1` in `H^0(Spec(k))`, which
`Stacks.Weil.cycleClass_fundamentalClass_eq_one` supplies from the data and axioms at the base
point, and the fact `pullbackMap_one` that `p^*` carries the unit of `H^0(Spec(k))`
to the unit of `H^0(X)`. Nonemptiness of `X` is not needed: for `X` empty both sides vanish. -/
@[stacks 0FHF "the nonempty case, first clause: `γ([X]) = 1`"]
theorem cycleClass_fundamentalChowClass_eq_one
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [Smooth p]
    {HX : Type w} [AddCommGroup HX] [Module F HX] (one : HX)
    (cycleClassX : degreeZeroChow p →+ HX)
    (pullbackMap : HptZero →ₗ[F] HX)
    (cycleClass_pullback : ∀ α,
      cycleClassX (structureFlatPullbackDegreeZero p α) = pullbackMap (cycleClassPoint α))
    (pullbackMap_one : pullbackMap 1 = one) :
    cycleClassX (fundamentalDegreeZeroChow p) = one := by
  have hpoint : cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) = 1 :=
    Stacks.Weil.cycleClass_fundamentalClass_eq_one F Hpt kunnethPoint HptZero degreeZeroPoint
      _ _ cycleClassPoint integrationPoint integration_cycleClassPoint cycleClassPoint_mul
  rw [← structureFlatPullbackDegreeZero_fundamentalChowClass p, cycleClass_pullback,
    hpoint, pullbackMap_one]

/-! ### Nonvanishing -/

include degreeZeroPoint kunnethPoint integration_cycleClassPoint cycleClassPoint_mul in
/-- **Stacks Project, Tag 0FHF**, the second clause of the nonempty case. Let `X` be a nonempty
smooth projective scheme over `k`. Then `1 ≠ 0` in `H^0(X)`.

The coefficient field `F` has characteristic zero, and `H^0(Spec(k))` is a nonzero `F`-algebra,
so `F` injects into it and `[κ(x) : k] ≠ 0` there. The hypotheses are axiom `(C)(b)` for the
structure morphism `p`, that the cycle class map commutes with proper pushforward, the data and
axioms at the base point from which Stacks 0FHE gives `γ([Spec(k)]) = 1`, and the unit law of
the cup product of `H^*(X)`. -/
@[stacks 0FHF "the nonempty case, second clause: `1 ≠ 0` in `H⁰(X)`"]
theorem one_ne_zero_of_nonempty [CharZero F]
    {X : Scheme.{u}} [Nonempty (X : Type u)] (p : X ⟶ (fieldChowSituation k).S)
    [Smooth p] [IsProper p]
    {H0 M : Type w} [AddCommGroup H0] [Module F H0] [AddCommGroup M] [Module F M]
    (one : H0) (cup : M →ₗ[F] H0 →ₗ[F] M) (cup_one : ∀ a : M, cup a one = a)
    (cycleClassX : chowGroup (fieldChowSituation k) p 0 →+ M)
    (pushforward : M →ₗ[F] HptZero)
    (cycleClass_pushforward : ∀ β,
      pushforward (cycleClassX β) =
        cycleClassPoint (properChowPushforward (fieldChowSituation k) p (𝟙 _) p
          (Category.comp_id p) 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
            p (𝟙 _) p (Category.comp_id p) 0) β)) :
    one ≠ 0 := by
  classical
  have hpoint : cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) = 1 :=
    Stacks.Weil.cycleClass_fundamentalClass_eq_one F Hpt kunnethPoint HptZero degreeZeroPoint
      _ _ cycleClassPoint integrationPoint integration_cycleClassPoint cycleClassPoint_mul
  have : Nontrivial HptZero :=
    nontrivial_of_ne (cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0)) 0
      fun h ↦ by simp [h] at integration_cycleClassPoint
  have : CharZero HptZero :=
    charZero_of_injective_algebraMap (algebraMap F HptZero).injective
  let : DecidableEq (X : Type u) := Classical.decEq _
  intro hone
  obtain ⟨x, hxc, hxfin, -⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth p).nonempty
  have hδ : ∀ s : (fieldChowSituation k).S, (fieldChowSituation k).dimensionFunction s = 0 :=
    fun _ ↦ rfl
  have hn : p.residueDegree x ≠ 0 := residueDegree_ne_zero_of_finite k p x hxfin
  set α : CycleGroup (fieldChowSituation k) p 0 :=
    ⟨Function.locallyFinsuppWithin.single x (1 : ℤ),
      single_mem_cyclesOfDimension_zero (fieldChowSituation k) p x
        (relativeDimension_eq_zero_of_residueDegree_ne_zero _ hδ p x hn)⟩
  set β := QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) p 0) α with hβdef
  set pf := properChowPushforward (fieldChowSituation k) p (𝟙 _) p (Category.comp_id p) 0
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
      p (𝟙 _) p (Category.comp_id p) 0)
  set e := chowGroupBaseEquivInt (fieldChowSituation k) hδ (p.base x)
  have hdeg : e (pf β) = (p.residueDegree x : ℤ) := by
    rw [show e (pf β) = chowDegree (fieldChowSituation k) hδ p (p.base x) β from rfl, hβdef,
      chowDegree_mk]
    exact cycleDegree_single (fieldChowSituation k) hδ p x α rfl
  have hkey : e (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) • pf β =
      e (pf β) • fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0 :=
    e.injective <| by rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, mul_comm]
  have hpt : cycleClassPoint (pf β) ≠ 0 := by
    intro h
    have hgam := congrArg cycleClassPoint hkey
    rw [map_zsmul, map_zsmul, hpoint, h, smul_zero, hdeg, zsmul_eq_mul,
      mul_one] at hgam
    exact hn (Nat.cast_eq_zero.mp
      (Int.cast_injective (α := HptZero) (by simpa using hgam.symm)))
  exact hpt (by rw [← cycleClass_pushforward β, ← cup_one (cycleClassX β), hone, map_zero,
    map_zero])

end Stacks.WeilCohomology

end
