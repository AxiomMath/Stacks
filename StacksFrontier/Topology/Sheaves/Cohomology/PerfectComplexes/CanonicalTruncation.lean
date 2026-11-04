module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Canonical truncation and perfectness

Tag 08CP deduces perfectness of a derived object `E` with Tor amplitude in `[a, b]` which is
`(a-1)`-pseudo-coherent. The source's argument has two halves. The first is formal: near every
point `E` is approximated by a strictly perfect complex `P` in degrees at least `a`, and the
canonical truncation `σ^{≥a} P` is then a model of `E` there, provided its one new term -- the
degree-`a` opcycles `coker(P^{a-1} → P^a)` -- is again a direct summand of a finite free module.
The second half is the input that this term *is* such a summand, which is where Tor amplitude
enters. This file proves the first half.

## Main results

* `Stacks.Cohomology.PerfectCanonicalTruncation.quasiIso_truncGEMap`: a map of complexes which is
  an isomorphism on cohomology in
  all degrees at least `n` becomes a quasi-isomorphism after canonical truncation at `n`.
* `Stacks.Cohomology.PerfectCanonicalTruncation.isStrictlyPerfect_truncGE`: the canonical
  truncation of a strictly perfect complex
  is strictly perfect as soon as the degree-`a` opcycles is a direct summand of a finite free
  module.
* `Stacks.Cohomology.PerfectCanonicalTruncation.isPerfectComplex_of_local_truncGE`: the
  truncation step of Tag 08CP -- a complex with no cohomology below `a` which is locally
  approximated in degrees at least `a` by a strictly perfect complex whose degree-`a` opcycles is
  a summand of a finite free module is a perfect complex.
* `Stacks.Cohomology.PerfectCanonicalTruncation.isPerfectComplex_of_local_truncGE_of_shrink`: the
  same, with the condition on the opcycles required only after shrinking.
* `Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_local_truncGE` and
  `Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_local_truncGE_of_shrink`: the
  corresponding statements for the object of `D(O_X)` the complex represents.

## Implementation notes

The source replaces `P` by the stupid truncation `σ_{≥a-1} P` and then reads off a cokernel.
Working with Mathlib's *canonical* truncation `CochainComplex.truncGE` instead removes that step
and with it the distinguished-triangle bookkeeping the source uses to identify the cone: the
term of `P.truncGE a` in degree `a` is already `coker(P^{a-1} → P^a)`, the terms above are those
of `P`, and the terms below vanish. The factorisation of the approximation through the truncation
is then Mathlib's `CochainComplex.πTruncGE`, which is a quasi-isomorphism exactly because the
target has no cohomology below `a` -- the source's `H^{a-1}(E) = 0`, and the only place the
vanishing of `E` below `a` is used.

The argument takes place at the level of complexes: near every point the truncations give a roof
of quasi-isomorphisms between a strictly perfect complex and the restriction of `K`, and such
roofs assemble into perfectness of `K`
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs`). No derived category of an open
subspace occurs, so the statements about `D(O_X)` hold for any model of that category.

The formal statements are proved over an abstract abelian category, both for tidiness and because
each then gets its own heartbeat budget.

## References

* [Stacks Project, Tag 08CP](https://stacks.math.columbia.edu/tag/08CP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace Stacks.Cohomology.PerfectCanonicalTruncation

universe u d v₁ u₁

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- **Canonical truncation turns a cohomology isomorphism above `n` into a quasi-isomorphism.**
A morphism of cochain complexes inducing an isomorphism on cohomology in every degree at least
`n` becomes a quasi-isomorphism after applying `σ^{≥n}`: below `n` both truncations have no
cohomology, and at and above `n` the cohomology is unchanged. -/
theorem quasiIso_truncGEMap {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)
    (h : ∀ i : ℤ, n ≤ i → IsIso (HomologicalComplex.homologyMap φ i)) :
    QuasiIso (CochainComplex.truncGEMap φ n) := by
  rw [CochainComplex.quasiIso_truncGEMap_iff]
  intro i hi
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact h i hi

end Abstract

variable {X : RingedSpace.{u, u}}

/-- A zero module is a direct summand of the rank-zero finite free module. -/
theorem isDirectSummandOfFiniteFree_of_isZero {M : OXMod.{u, u} X} (h : IsZero M) :
    IsDirectSummandOfFiniteFree M :=
  ⟨0, ⟨⟨0, 0, ((moduleULift.{u, u} X).map_isZero h).eq_of_src _ _⟩⟩⟩

/-- **The canonical truncation of a strictly perfect complex is strictly perfect**, as soon as
its single new term -- the degree-`a` opcycles `coker(P^{a-1} → P^a)` -- is a direct summand of a
finite free module. Every other term of `P.truncGE a` is either zero (below `a`) or a term of `P`
(above `a`), so boundedness and the summand condition are inherited. -/
theorem isStrictlyPerfect_truncGE {P : CochainComplex (OXMod.{u, u} X) ℤ}
    (hP : IsStrictlyPerfect P) (a : ℤ)
    (hop : IsDirectSummandOfFiniteFree (HomologicalComplex.opcycles P a)) :
    IsStrictlyPerfect (P.truncGE a) where
  bounded := by
    refine Set.Finite.subset (hP.bounded.union (Set.finite_singleton a)) ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_or,
      not_not] at hcon
    refine hi ?_
    rcases lt_trichotomy i a with h | rfl | h
    · exact (P.truncGE a).isZero_of_isStrictlyGE a i h
    · exact absurd rfl hcon.2
    · exact IsZero.of_iso hcon.1 (P.truncGEXIso a i h)
  directSummand := by
    intro i
    rcases lt_trichotomy i a with h | rfl | h
    · exact isDirectSummandOfFiniteFree_of_isZero
        ((P.truncGE a).isZero_of_isStrictlyGE a i h)
    · exact isDirectSummandOfFiniteFree_of_iso (P.truncGEXIsoOpcycles i) hop
    · exact isDirectSummandOfFiniteFree_of_iso (P.truncGEXIso a i h) (hP.directSummand i)

/-- **The truncation step of Tag 08CP, for complexes.** Let `K` be a complex of `O_X`-modules
with no cohomology in degrees below `a`. Suppose that near every point of `X` there is a strictly
perfect complex `P` and a map `P ⟶ K|_U` which is an isomorphism on cohomology in every degree at
least `a`, and that the degree-`a` opcycles of `P` is a direct summand of a finite free module.
Then `K` is a perfect complex.

Over `U` the canonical truncations give a roof of quasi-isomorphisms
`P.truncGE a ⟶ (K|_U).truncGE a ⟵ K|_U`: the first map is a quasi-isomorphism by
`Stacks.Cohomology.PerfectCanonicalTruncation.quasiIso_truncGEMap`, and the second because
restriction is exact, so `K|_U` inherits the vanishing of the cohomology of `K` below `a`. The
complex `P.truncGE a` is strictly perfect by
`Stacks.Cohomology.PerfectCanonicalTruncation.isStrictlyPerfect_truncGE`, and the local roofs
assemble by `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs`. -/
theorem isPerfectComplex_of_local_truncGE (K : CochainComplex (OXMod.{u, u} X) ℤ) (a : ℤ)
    (hK : ∀ i : ℤ, i < a → IsZero (K.homology i))
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        IsDirectSummandOfFiniteFree (HomologicalComplex.opcycles P a) ∧
        ∃ α : P ⟶ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U,
          ∀ j : ℤ, a ≤ j → IsIso (HomologicalComplex.homologyMap α j)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfectComplex K := by
  refine AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs fun x => ?_
  obtain ⟨U, hxU, P, hP, hop, α, hα⟩ := h x
  exact ⟨U, hxU, P.truncGE a, isStrictlyPerfect_truncGE hP a hop,
    CochainComplex.quasiIsoRoof_iff.2 ⟨_, CochainComplex.truncGEMap α a,
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U).πTruncGE a,
      quasiIso_truncGEMap α a hα, (CochainComplex.quasiIso_πTruncGE_iff _ a).2
        ((CochainComplex.isGE_iff _ a).2 fun i hi =>
          (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
            (isZero_homology_restrictComplex K i (hK i hi)))⟩⟩

/-- **The truncation step of Tag 08CP for complexes, with its module-theoretic input
localised.** This is the form Tag 08CP needs: the condition on the degree-`a` opcycles is only
required to hold *after shrinking*, which is how it comes out of flatness (the source appeals to
Modules, Lemma 08BL, whose conclusion is local).

Over the open subspace `X|_U` the data restricts to smaller opens `V`: `P|_V` is strictly
perfect and `α|_V` is still an isomorphism on cohomology in degrees at least `a`, because
restriction is exact. So `K|_U` is a perfect complex by
`Stacks.Cohomology.PerfectCanonicalTruncation.isPerfectComplex_of_local_truncGE` on `X|_U`, and
these assemble by
`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict`. -/
theorem isPerfectComplex_of_local_truncGE_of_shrink (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (a : ℤ) (hK : ∀ i : ℤ, i < a → IsZero (K.homology i))
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        (∃ α : P ⟶ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U,
          ∀ j : ℤ, a ≤ j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        ∀ y : (X.restrict U.isOpenEmbedding).carrier,
          ∃ V : Opens (X.restrict U.isOpenEmbedding).carrier, y ∈ V ∧
            IsDirectSummandOfFiniteFree
              (HomologicalComplex.opcycles
                (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P V) a)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfectComplex K := by
  refine AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict
    fun x => ?_
  obtain ⟨U, hxU, P, hP, ⟨α, hα⟩, hshrink⟩ := h x
  refine ⟨U, hxU, isPerfectComplex_of_local_truncGE (X := X.restrict U.isOpenEmbedding)
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U) a
    (fun i hi => isZero_homology_restrictComplex K i (hK i hi)) fun y => ?_⟩
  obtain ⟨V, hyV, hop⟩ := hshrink y
  let R := AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u}
    (X.restrict U.isOpenEmbedding) V
  exact ⟨V, hyV, _,
    AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_restrictComplex
      (X.restrict U.isOpenEmbedding) V hP, hop,
    (R.mapHomologicalComplex (ComplexShape.up ℤ)).map α, fun j hj =>
      Stacks.PseudoCoherence.DerivedCharacterization.isIso_homologyMap_mapHomologicalComplex R α j
        (hα j hj)⟩

/-- **The truncation step of Tag 08CP.** Under the hypotheses of
`Stacks.Cohomology.PerfectCanonicalTruncation.isPerfectComplex_of_local_truncGE`, `K` represents
a perfect object of `D(O_X)`, in any model of that category. -/
theorem isPerfect_of_local_truncGE [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (a : ℤ)
    (hK : ∀ i : ℤ, i < a → IsZero (K.homology i))
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        IsDirectSummandOfFiniteFree (HomologicalComplex.opcycles P a) ∧
        ∃ α : P ⟶ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U,
          ∀ j : ℤ, a ≤ j → IsIso (HomologicalComplex.homologyMap α j)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (DerivedCategory.Q.obj K) :=
  ⟨K, isPerfectComplex_of_local_truncGE K a hK h, ⟨Iso.refl _⟩⟩

/-- **The truncation step of Tag 08CP, with its module-theoretic input localised.** Under the
hypotheses of
`Stacks.Cohomology.PerfectCanonicalTruncation.isPerfectComplex_of_local_truncGE_of_shrink`, `K`
represents a perfect object of `D(O_X)`, in any model of that category. -/
theorem isPerfect_of_local_truncGE_of_shrink [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (a : ℤ)
    (hK : ∀ i : ℤ, i < a → IsZero (K.homology i))
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        (∃ α : P ⟶ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U,
          ∀ j : ℤ, a ≤ j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        ∀ y : (X.restrict U.isOpenEmbedding).carrier,
          ∃ V : Opens (X.restrict U.isOpenEmbedding).carrier, y ∈ V ∧
            IsDirectSummandOfFiniteFree
              (HomologicalComplex.opcycles
                (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P V) a)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (DerivedCategory.Q.obj K) :=
  ⟨K, isPerfectComplex_of_local_truncGE_of_shrink K a hK h, ⟨Iso.refl _⟩⟩

/-- **Tag 08CP, stated for a derived object, with its module-theoretic input localised.** Given a
representative `K` of `E`, a local strictly perfect approximation of `K` in degrees at least `a`
whose degree-`a` opcycles is -- after shrinking -- a direct summand of a finite free module, and
the vanishing of the cohomology of `E` below `a`, the object `E` is perfect.

Both remaining hypotheses are consequences of Tor amplitude in `[a, b]`: the vanishing below `a`
comes from tensoring with the structure sheaf, and the opcycles condition from the flatness of
`coker(P^{a-1} → P^a)` together with Modules, Lemma 08BL. The degree condition is written
`a - 1 < j` so that the data produced by
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom K (a - 1)` can
be fed in unchanged. -/
theorem isPerfect_of_local_approximation_of_opcycles [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) (a : ℤ)
    (hE : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E))
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        (∃ α : P ⟶ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U,
          ∀ j : ℤ, a - 1 < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        ∀ y : (X.restrict U.isOpenEmbedding).carrier,
          ∃ V : Opens (X.restrict U.isOpenEmbedding).carrier, y ∈ V ∧
            IsDirectSummandOfFiniteFree
              (HomologicalComplex.opcycles
                (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P V) a)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect E := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso e ?_
  refine isPerfect_of_local_truncGE_of_shrink K a (fun i hi => ?_) ?_
  · refine IsZero.of_iso (hE i hi) (Iso.trans ?_
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso e))
    exact ((DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) i).app K).symm
  · intro x
    obtain ⟨U, hxU, P, hP, ⟨α, hα⟩, hshrink⟩ := h x
    exact ⟨U, hxU, P, hP, ⟨α, fun j hj => hα j (by omega)⟩, hshrink⟩

/-- **The degree-`a` opcycles of a strictly perfect complex whose differential into degree `a`
vanishes is a direct summand of a finite free module**, because the canonical map from the
degree-`a` term is then an isomorphism. -/
theorem isDirectSummandOfFiniteFree_opcycles_of_d_eq_zero {Y : RingedSpace.{u, u}}
    {Q : CochainComplex (OXMod.{u, u} Y) ℤ} (hQ : IsStrictlyPerfect Q) (a : ℤ)
    (h : Q.d (a - 1) a = 0) :
    IsDirectSummandOfFiniteFree (HomologicalComplex.opcycles Q a) :=
  isDirectSummandOfFiniteFree_of_iso
    (Q.pOpcyclesIso (a - 1) a (by simp) h).symm (hQ.directSummand a)

/-- **A strictly perfect complex vanishing below `a` is perfect.** This is a corollary of the
truncation step and, more to the point, a machine-checked witness that the hypotheses of
`Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_local_truncGE_of_shrink` are jointly
  satisfiable and not vacuous: the
complex is its own local approximation with `α` the identity, and its degree-`a` opcycles is the
degree-`a` term because the incoming differential leaves a zero object. -/
theorem isPerfect_of_isStrictlyPerfect_of_isZero_X [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (P : CochainComplex (OXMod.{u, u} X) ℤ) (hP : IsStrictlyPerfect P) (a : ℤ)
    (hlow : ∀ i : ℤ, i < a → IsZero (P.X i)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (DerivedCategory.Q.obj P) := by
  have hGE : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff P a).2 (fun i hi => hlow i hi)
  refine isPerfect_of_local_truncGE_of_shrink P a (fun i hi => P.isZero_of_isGE a i hi)
    fun x => ⟨⊤, trivial, AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P ⊤,
      AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_restrictComplex X ⊤ hP,
      ⟨𝟙 _, fun j _ => by rw [HomologicalComplex.homologyMap_id]; infer_instance⟩,
      fun y => ⟨⊤, trivial, ?_⟩⟩
  refine isDirectSummandOfFiniteFree_opcycles_of_d_eq_zero
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_restrictComplex _ ⊤
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_restrictComplex X ⊤ hP)) a ?_
  exact IsZero.eq_of_src
    ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u} _ ⊤).map_isZero
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u} X ⊤).map_isZero (hlow (a -
        1) (by omega)))) _ _

end Stacks.Cohomology.PerfectCanonicalTruncation

end
