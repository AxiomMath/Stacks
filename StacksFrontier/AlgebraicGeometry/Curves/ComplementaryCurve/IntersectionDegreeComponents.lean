module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionNodes
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionStalks
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.AttachingPointStalk
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusUnion
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDeltaBranchesDescent
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmptySupport

/-!
# The degree of the intersection with the complementary curve is the sum over the components

Let `k` be a field, let `X` be a one-dimensional `k`-scheme, locally of finite type and with at
worst nodal singularities, let `C ⊆ X` be a closed subscheme cut out by an ideal sheaf `I`, and
let `X'` be the scheme-theoretic closure of `X \ C`, cut out by
`AlgebraicGeometry.complementaryCurveIdeal I`.  Writing `C = ⋃ Λ` for the decomposition of `C`
into its irreducible components, the degree of the intersection decomposes over them:

`deg (C ∩ X') = ∑_Λ deg (Λ ∩ X')`.

Here `deg` is `h⁰`, the dimension over `k` of the ring of global functions, which is the degree
of a finite scheme; it is the quantity `AlgebraicGeometry.genus_union` calls the degree of an
intersection, and this file matches that convention throughout.

## Why the degrees add with no correction term

The intersections `Λ ∩ X'` are *pairwise disjoint*: a point lying on two distinct components of
`C` and on `X'` would lie on a third irreducible component of `X` — the one inside `X'` and not
inside `C` — and so `X` would have at least three branches there, while a node has exactly two.
That is `Stacks.Curves.irreducibleComponentsThrough_eq_pair_of_hasAtWorstNodalSingularities`:
at a point lying on two distinct irreducible components of a one-dimensional nodal curve those
two are *all* the components through it.  A smooth point is excluded because its local ring is a
domain and so has a single minimal prime, and at a node the count of components through the point
is the count of minimal primes of the local ring, which is two by [Stacks, Tag 0C4D].

Disjointness is recorded as the ideal-sheaf identity
`vanishingIdeal Λ₁ ⊔ vanishingIdeal Λ₂ ⊔ complementaryCurveIdeal I = ⊤`
(`Stacks.Curves.sup_sup_complementaryCurveIdeal_eq_top`): the order on ideal sheaves is the order
on ideals, so a supremum cuts out an intersection and `⊤` cuts out the empty subscheme.

## What each hypothesis is for

*Nodality and `dim X = 1`* are used only for the disjointness above.

*No reducedness of `C`.* The sum is over a `Finset Λ` of irreducible components of `X` contained
in the support of `I`, and the main additivity statement
`Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_finsetInf_eq_sum`
is about the scheme-theoretic union of *those*, that is about `Λ.inf` of their vanishing ideals,
and assumes nothing about `I` beyond `Λ` sitting inside its support.  Reducedness of `C`, with
equidimensionality of `X` and of `C`, enters exactly once, in
`Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_eq_sum`, and
only to identify `I` itself with that union — which is
`Stacks.Curves.eq_union_irreducibleComponents` — so that the left-hand side reads
`deg (C ∩ X')`.  Without it the statement would be false for a reason that has nothing to do
with nodes: on `X = ℙ¹` the fat point `C = 2p` has `X' = X`, so `C ∩ X' = C` has degree two
while the one component of `C` is the reduced point `p`, of degree one.

*Properness* is required of `C ∩ X'` alone, in the shape
`IsProper ((I ⊔ complementaryCurveIdeal I).subschemeι ≫ f)`.  It is used only for finite
dimensionality of the cohomology that occurs ([Stacks, Tag 02O6]), through
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf`, and the
pieces `Λ ∩ X'` inherit it along `≤` by
`AlgebraicGeometry.isProper_subschemeι_comp_of_le`.  No properness of `X`, and nothing about its
connectedness.

*Finiteness of the family* is not hypothesised on `X`: the components summed over are given as a
`Finset`, which is how such a decomposition is supplied in
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/GenusDualGraph.lean` as well.  On a Noetherian
space one exists, by `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`.

## Which subscheme structure the components carry

A component `Λ` enters as the *reduced* closed subscheme
`Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Λ)`, not as
`AlgebraicGeometry.Scheme.irreducibleComponentIdeal`.  The two differ, and the choice is forced
by both sides of the identity.  Mathlib's `irreducibleComponentIdeal` is designed so that the
component retains the ambient multiplicities — for irreducible `X` it gives back `X` — and
consequently the infimum of the component ideals of a scheme is its nilradical, so their
scheme-theoretic union is the *reduction* and not the scheme.  With the reduced structure the
infimum is instead the vanishing ideal of the union of the components, which for a reduced `C` is
`I` on the nose; that is the identification
`Stacks.Curves.eq_union_irreducibleComponents` and the only reason `C` is assumed reduced.  It is
also the structure that makes the two sides comparable: `C` being reduced, the closed subscheme
of `C` supported on one of its components *is* the reduced one, and
`Stacks.Curves.isDiscrete_and_residueField_intersectionWithComplementaryCurve` identifies
`C ∩ X'` itself as a disjoint union of spectra of finite separable extensions of `k`
([Stacks, Tag 0E38], part (2)(a)).

## The additivity behind it

The cohomological half is the degree-zero part of the sequence of [Stacks, Tag 0C4J] proved in
`StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/ClosedUnionExactSequence.lean`,

`0 ⟶ 𝒪_{Z₁ ∪ Z₂} ⟶ 𝒪_{Z₁} ⊞ 𝒪_{Z₂} ⟶ 𝒪_{Z₁ ∩ Z₂} ⟶ 0`,

for two *disjoint* closed subschemes: there the third term is a zero object, so the first map is
an isomorphism on global sections and `deg (Z₁ ∪ Z₂) = deg Z₁ + deg Z₂`
(`AlgebraicGeometry.finrank_structureSheafCohomology_zero_inf_eq_add_of_sup_eq_top`).  This is
not a consequence of `AlgebraicGeometry.genus_union`: that identity carries the genus of the
union, which for a disjoint union is itself the quantity being computed, and the inequality
`AlgebraicGeometry.finrank_structureSheafCohomology_zero_add_le_union` extracted from it points
the wrong way.  What the vanishing of the third term adds is the surjectivity.

The lattice half is that `⊔ J` distributes over `⊓` on *comaximal* ideal sheaves,
`AlgebraicGeometry.Scheme.IdealSheafData.sup_inf_right_of_sup_sup_eq_top`, which is what turns
`C ∩ X'` into the disjoint union of the `Λ ∩ X'` as schemes and not merely as sets.  The ideal
lattice is not distributive, and this is the familiar comaximal case: `(A ⊓ B) ⊔ J` and
`(A ⊔ J) ⊓ (B ⊔ J)` agree once `A ⊔ B ⊔ J = ⊤`, because then the right-hand side is the product
`(A ⊔ J) * (B ⊔ J)`, all of whose terms lie in `A * B ⊔ J ≤ (A ⊓ B) ⊔ J`.

## Main results

* `Ideal.sup_inf_right_of_sup_sup_eq_top` and
  `AlgebraicGeometry.Scheme.IdealSheafData.sup_inf_right_of_sup_sup_eq_top`: comaximal
  distributivity, for ideals and for ideal sheaves.
* `AlgebraicGeometry.Scheme.IdealSheafData.inf_sup_eq_top` and
  `AlgebraicGeometry.Scheme.IdealSheafData.finsetInf_sup_eq_top`: an ideal sheaf comaximal with
  each member of a finite family is comaximal with the family's infimum.
* `AlgebraicGeometry.Scheme.IdealSheafData.finsetInf_sup_of_pairwise`: for a family that is
  pairwise comaximal after `⊔ J`, taking `⊔ J` commutes with the finite infimum.
* `AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_of_shortExact_of_isZero`: the global
  sections of the first two terms of a short exact sequence whose third term has no global
  sections have the same dimension.
* `AlgebraicGeometry.finrank_structureSheafCohomology_zero_inf_eq_add_of_sup_eq_top` and
  `AlgebraicGeometry.finrank_structureSheafCohomology_zero_finsetInf_eq_sum`: **the degree of a
  disjoint union of closed subschemes is the sum of their degrees**, for two pieces and for a
  finite family.
* `Stacks.Curves.irreducibleComponentsThrough_eq_pair_of_hasAtWorstNodalSingularities`: **two
  distinct irreducible components through a point of a one-dimensional nodal curve are all of
  them**; a node has only two branches.
* `Stacks.Curves.sup_sup_complementaryCurveIdeal_eq_top`: consequently two distinct components
  inside a closed subscheme and the closure of its complement have empty common intersection.
* In `Stacks.Curves`,
  `finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_finsetInf_eq_sum` and
  `finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_eq_sum`:
  **`deg (C ∩ X') = ∑_Λ deg (Λ ∩ X')`**, first for the union of a finite family of components of
  `X` inside `C` and then, for `C` reduced and equidimensional of dimension one, for `C` itself.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData
open Stacks.AlgebraicGeometry.CurveEulerBridge

universe u

/-! ### Comaximal distributivity -/

/-- **Comaximal distributivity for ideals.**  The lattice of ideals is not distributive, but
`(A ⊓ B) ⊔ J = (A ⊔ J) ⊓ (B ⊔ J)` holds as soon as `A ⊔ B ⊔ J = ⊤`: then `A ⊔ J` and `B ⊔ J` are
coprime, so their infimum is their product, and every term of that product lies in
`A * B ⊔ J ≤ (A ⊓ B) ⊔ J`. -/
theorem Ideal.sup_inf_right_of_sup_sup_eq_top {R : Type*} [CommRing R] {A B J : Ideal R}
    (h : A ⊔ B ⊔ J = ⊤) : A ⊓ B ⊔ J = (A ⊔ J) ⊓ (B ⊔ J) := by
  refine le_antisymm (le_inf (sup_le_sup_right inf_le_left _)
    (sup_le_sup_right inf_le_right _)) ?_
  have hco : A ⊔ J ⊔ (B ⊔ J) = ⊤ := by rwa [← sup_sup_distrib_right]
  rw [Ideal.inf_eq_mul_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hco), Ideal.mul_le]
  intro r hr s hs
  obtain ⟨a, ha, j, hj, rfl⟩ := Submodule.mem_sup.mp hr
  obtain ⟨b, hb, l, hl, rfl⟩ := Submodule.mem_sup.mp hs
  have key : (a + j) * (b + l) = a * b + (a * l + j * (b + l)) := by ring
  rw [key]
  exact Submodule.add_mem_sup
    (Ideal.mem_inf.mpr ⟨Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb⟩)
    (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_right _ _ hj))

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **Comaximal distributivity for ideal sheaves.**  Read on closed subschemes: if the
intersection of the union of `Z₁` and `Z₂` with `W` is empty, then it is the disjoint union of
`Z₁ ∩ W` and `Z₂ ∩ W`.  Both lattice operations are computed on the defining ideals, so this is
`Ideal.sup_inf_right_of_sup_sup_eq_top` on each affine open. -/
theorem sup_inf_right_of_sup_sup_eq_top {A B J : X.IdealSheafData} (h : A ⊔ B ⊔ J = ⊤) :
    A ⊓ B ⊔ J = (A ⊔ J) ⊓ (B ⊔ J) := by
  ext U : 2
  have hU : A.ideal U ⊔ B.ideal U ⊔ J.ideal U = ⊤ := by
    simpa using congrArg (fun K : X.IdealSheafData => K.ideal U) h
  exact Ideal.sup_inf_right_of_sup_sup_eq_top hU

/-- **An ideal sheaf comaximal with two ideal sheaves is comaximal with their infimum.**  On
closed subschemes: a closed subscheme meeting neither of two others meets their union nowhere. -/
theorem inf_sup_eq_top {A B J : X.IdealSheafData} (hA : A ⊔ J = ⊤) (hB : B ⊔ J = ⊤) :
    A ⊓ B ⊔ J = ⊤ := by
  have htop : A ⊔ B ⊔ J = ⊤ :=
    top_le_iff.mp (hA.ge.trans (sup_le_sup_right (le_sup_left : A ≤ A ⊔ B) J))
  rw [sup_inf_right_of_sup_sup_eq_top htop, hA, hB, top_inf_eq]

/-- **An ideal sheaf comaximal with each member of a finite family is comaximal with the
family's infimum.** -/
theorem finsetInf_sup_eq_top {ι : Type*} (P : ι → X.IdealSheafData) (J : X.IdealSheafData)
    (s : Finset ι) (h : ∀ i ∈ s, P i ⊔ J = ⊤) : s.inf P ⊔ J = ⊤ := by
  classical
  revert h
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert a t ha ih =>
      intro h
      rw [Finset.inf_insert]
      exact inf_sup_eq_top (h a (Finset.mem_insert_self a t))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **For a pairwise comaximal family, `⊔ J` commutes with a finite infimum.**  Read on closed
subschemes: if the pieces `Z i ∩ W` are pairwise disjoint, then `(⋃ i ∈ s, Z i) ∩ W` is their
union as a scheme, not merely as a set.  Comaximal distributivity supplies the inductive step,
and the comaximality it needs there — of `Z a ∩ W` with the union of the earlier pieces — is
`AlgebraicGeometry.Scheme.IdealSheafData.finsetInf_sup_eq_top`. -/
theorem finsetInf_sup_of_pairwise {ι : Type*} (P : ι → X.IdealSheafData) (J : X.IdealSheafData)
    (s : Finset ι) (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i ⊔ P j ⊔ J = ⊤) :
    s.inf P ⊔ J = s.inf fun i => P i ⊔ J := by
  classical
  revert h
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert a t ha ih =>
      intro h
      have hih := ih fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hstep : ∀ j ∈ t, P j ⊔ J ⊔ (P a ⊔ J) = ⊤ := by
        intro j hj
        have hne : j ≠ a := fun e => ha (e ▸ hj)
        have hh := h j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self a t) hne
        rwa [← sup_sup_distrib_right]
      have htop : P a ⊔ t.inf P ⊔ J = ⊤ := by
        rw [sup_sup_distrib_right, hih, sup_comm]
        exact finsetInf_sup_eq_top (fun i => P i ⊔ J) (P a ⊔ J) t hstep
      rw [Finset.inf_insert, sup_inf_right_of_sup_sup_eq_top htop, hih, Finset.inf_insert]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### The degree of a disjoint union of closed subschemes -/

/-- **The structure sheaf of an empty closed subscheme is a zero object.**  Its sections over an
open set of the ambient scheme are the sections of the structure sheaf of the empty scheme over
the preimage, which are subsingletons, so the identity is the zero map. -/
theorem isZero_closedSubschemeStructureSheaf_of_isEmpty {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsEmpty I.subscheme] : IsZero (closedSubschemeStructureSheaf I) := by
  refine (IsZero.iff_id_eq_zero _).2 (Scheme.Modules.hom_ext _ _ fun U => ?_)
  have : Subsingleton Γ(closedSubschemeStructureSheaf I, U) :=
    inferInstanceAs (Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U))
  ext x
  exact Subsingleton.elim _ _

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **An empty closed subscheme has degree zero**, and no higher cohomology either: its structure
sheaf is a zero object. -/
theorem finrank_structureSheafCohomology_eq_zero_of_isEmpty (I : X.IdealSheafData)
    [IsEmpty I.subscheme] (n : ℕ) :
    Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) n) = 0 := by
  rw [← finrank_cohomologyOverField_closedSubschemeStructureSheaf k f I n]
  have := ModuleCat.subsingleton_of_isZero (isZero_cohomologyOverField_of_isZero k f
    (isZero_closedSubschemeStructureSheaf_of_isEmpty I) n)
  exact Module.finrank_zero_of_subsingleton

/-- **The global sections of the first two terms of a short exact sequence whose third term has
none have the same dimension.**  For `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` with `H⁰(X, 𝒞) = 0`,
`h⁰(𝒜) = h⁰(ℬ)`.

Only the left-exact end of the long exact sequence is used, so there is no finiteness and no
properness hypothesis: `H⁰(X, 𝒜) ⟶ H⁰(X, ℬ)` is injective with image the kernel of
`H⁰(X, ℬ) ⟶ H⁰(X, 𝒞)`, which is everything.  This is the surjectivity that
`AlgebraicGeometry.finrank_cohomologyOverField_zero_le_of_shortExact` stops short of. -/
theorem finrank_cohomologyOverField_zero_eq_of_shortExact_of_isZero {A B C : X.Modules}
    (u : A ⟶ B) (v : B ⟶ C) (w : u ≫ v = 0) (hSE : (ShortComplex.mk u v w).ShortExact)
    (hC : IsZero (cohomologyOverField k f C 0)) :
    Module.finrank k (cohomologyOverField k f A 0) =
      Module.finrank k (cohomologyOverField k f B 0) := by
  obtain ⟨d, hinj, hab, hbc, hca⟩ :
      ∃ d : ∀ n : ℕ, cohomologyOverField k f C n ⟶ cohomologyOverField k f A (n + 1),
        Function.Injective (cohomologyOverFieldMap k f u 0) ∧
          (∀ n, Function.Exact (cohomologyOverFieldMap k f u n)
            (cohomologyOverFieldMap k f v n)) ∧
          (∀ n, Function.Exact (cohomologyOverFieldMap k f v n) (d n)) ∧
          ∀ n, Function.Exact (d n) (cohomologyOverFieldMap k f u (n + 1)) :=
    exists_cohomologyOverField_longExactSequence k f hSE
  have hsub : Subsingleton (cohomologyOverField k f C 0) := ModuleCat.subsingleton_of_isZero hC
  have hsurj : Function.Surjective (cohomologyOverFieldMap k f u 0) := fun b =>
    (hab 0 b).mp (Subsingleton.elim _ _)
  exact (LinearEquiv.ofBijective (cohomologyOverFieldMap k f u 0).hom
    ⟨hinj, hsurj⟩).finrank_eq

/-- **The degree of a disjoint union of two closed subschemes is the sum of their degrees.**  For
ideal sheaves with `I ⊔ J = ⊤`, so that the two closed subschemes `Z₁`, `Z₂` they cut out do not
meet,

`deg (Z₁ ∪ Z₂) = deg Z₁ + deg Z₂`,

where `deg` is `h⁰`, the dimension over `k` of the ring of global functions.

The sequence of [Stacks, Tag 0C4J] has `𝒪_{Z₁ ∩ Z₂} = 0` as its third term, so the global
sections of `𝒪_{Z₁ ∪ Z₂}` are those of `𝒪_{Z₁} ⊞ 𝒪_{Z₂}`.  Properness is required of the union
only, the pieces inheriting it by
`AlgebraicGeometry.isProper_subschemeι_comp_of_le`, and is used only for finite dimensionality:
`Module.finrank` is not additive on a product of infinite-dimensional spaces. -/
theorem finrank_structureSheafCohomology_zero_inf_eq_add_of_sup_eq_top (I J : X.IdealSheafData)
    (hIJ : I ⊔ J = ⊤) (hp : IsProper ((I ⊓ J).subschemeι ≫ f)) :
    Module.finrank k (structureSheafCohomology ((I ⊓ J).subschemeι ≫ f) 0) =
      Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0) +
        Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0) := by
  have := hp
  have : IsProper (I.subschemeι ≫ f) :=
    isProper_subschemeι_comp_of_le k f (inf_le_left : I ⊓ J ≤ I)
  have : IsProper (J.subschemeι ≫ f) :=
    isProper_subschemeι_comp_of_le k f (inf_le_right : I ⊓ J ≤ J)
  have : IsEmpty (I ⊔ J).subscheme := by rw [hIJ]; infer_instance
  have hfinI : FiniteDimensional k
      (cohomologyOverField k f (closedSubschemeStructureSheaf I) 0) :=
    finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f I 0
  have hfinJ : FiniteDimensional k
      (cohomologyOverField k f (closedSubschemeStructureSheaf J) 0) :=
    finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f J 0
  obtain ⟨hw, hSE⟩ := unionIntersection_shortExact I J
  have key := finrank_cohomologyOverField_zero_eq_of_shortExact_of_isZero k f
    (unionToBiprod I J) (biprodToIntersection I J) hw hSE
    (isZero_cohomologyOverField_of_isZero k f
      (isZero_closedSubschemeStructureSheaf_of_isEmpty (I ⊔ J)) 0)
  rw [finrank_cohomologyOverField_biprod k f _ _ 0 hfinI hfinJ] at key
  simpa only [finrank_cohomologyOverField_closedSubschemeStructureSheaf] using key

/-- **The degree of a disjoint union of a finite family of closed subschemes is the sum of their
degrees.**  For a pairwise comaximal family `P : ι → X.IdealSheafData`, so that the closed
subschemes it cuts out are pairwise disjoint, the union of the pieces indexed by a finite set `s`
is cut out by `s.inf P` and

`deg (⋃ i ∈ s, Z i) = ∑ i ∈ s, deg (Z i)`.

Properness is required of the union only; each partial union inherits it along `≤`. -/
theorem finrank_structureSheafCohomology_zero_finsetInf_eq_sum {ι : Type*}
    (P : ι → X.IdealSheafData) (s : Finset ι)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i ⊔ P j = ⊤)
    (hp : IsProper ((s.inf P).subschemeι ≫ f)) :
    Module.finrank k (structureSheafCohomology ((s.inf P).subschemeι ≫ f) 0) =
      ∑ i ∈ s, Module.finrank k (structureSheafCohomology ((P i).subschemeι ≫ f) 0) := by
  classical
  revert hdisj hp
  induction s using Finset.induction with
  | empty =>
      intro _ _
      rw [Finset.inf_empty, Finset.sum_empty]
      exact finrank_structureSheafCohomology_eq_zero_of_isEmpty k f ⊤ 0
  | insert a t ha ih =>
      intro hdisj hp
      rw [Finset.inf_insert] at hp
      have := hp
      have hcom : P a ⊔ t.inf P = ⊤ := by
        rw [sup_comm]
        refine Scheme.IdealSheafData.finsetInf_sup_eq_top P (P a) t fun i hi => ?_
        have hne : i ≠ a := fun e => ha (e ▸ hi)
        exact hdisj i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a t) hne
      rw [Finset.inf_insert, Finset.sum_insert ha,
        finrank_structureSheafCohomology_zero_inf_eq_add_of_sup_eq_top k f (P a) (t.inf P)
          hcom hp]
      congr 1
      exact ih
        (fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij)
        (isProper_subschemeι_comp_of_le k f (inf_le_right : P a ⊓ t.inf P ≤ t.inf P))

end AlgebraicGeometry

namespace Stacks.Curves

/-! ### A node has only two branches -/

/-- **Two distinct irreducible components through a point of a one-dimensional nodal curve are
all the components through it.**  Such a point is closed, because two distinct components of a
one-dimensional curve meet only in closed points, so the dichotomy of [Stacks, Tag 0C47] applies
to it.  It is not a smooth point: there the local ring is a domain and a single component passes
through.  So it is a node, where the number of geometric branches is two ([Stacks, Tag 0C4D]);
the number of components through the point is the number of minimal primes of the local ring,
which the two given components bound below by two and the branch count bounds above by two. -/
theorem irreducibleComponentsThrough_eq_pair_of_hasAtWorstNodalSingularities
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    {x : X} {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) (hCD : C ≠ D) (hxC : x ∈ C) (hxD : x ∈ D) :
    {Z ∈ irreducibleComponents X | x ∈ Z} = {C, D} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hxClosed :=
    closed_of_mem_distinct_irreducibleComponents (k := k) hX_dimension hC hD hCD hxC hxD
  have hnode : IsNode k X x := by
    rcases hX_nodal x hxClosed with hsm | hnode
    · exact absurd (irreducibleComponents_eq_of_stalkDomain
        (stalk_isDomain_of_smoothAt k X x hsm) hC hD hxC hxD) hCD
    · exact hnode
  obtain ⟨-, -, hbr⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hX_dimension x hnode
  refine irreducibleComponentsThrough_eq_pair hC hD hCD hxC hxD ?_
  rw [encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk X x]
  exact encard_minimalPrimes_stalk_eq_two X x hC hD hCD hxC hxD hbr

/-- **Two distinct irreducible components inside a closed subscheme of a nodal curve do not meet
the closure of the complement of that subscheme.**  A common point would lie on a third
irreducible component of `X`, namely one witnessing membership in the closure of the complement
and therefore not contained in the subscheme, while
`Stacks.Curves.irreducibleComponentsThrough_eq_pair_of_hasAtWorstNodalSingularities` says the two
given components are all of them.

The conclusion is stated as an identity of ideal sheaves: the order on ideal sheaves being the
order on ideals, a supremum cuts out a scheme-theoretic intersection and `⊤` cuts out the empty
subscheme. -/
theorem sup_sup_complementaryCurveIdeal_eq_top
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) (hCD : C ≠ D)
    (hCI : C ⊆ (I.support : Set X)) (hDI : D ⊆ (I.support : Set X)) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure C) ⊔
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure D) ⊔
          complementaryCurveIdeal I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine SetLike.coe_injective ?_
  simp only [Scheme.IdealSheafData.support_sup, Closeds.coe_inf, Closeds.coe_bot,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    (isClosed_of_mem_irreducibleComponents C hC).closure_eq,
    (isClosed_of_mem_irreducibleComponents D hD).closure_eq]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hxC, hxD⟩, hxJ⟩
  obtain ⟨E, hE, hEI, hxE, -⟩ :=
    exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal hX_nodal I hxJ
  have hpair := irreducibleComponentsThrough_eq_pair_of_hasAtWorstNodalSingularities
    hX_dimension hX_nodal hC hD hCD hxC hxD
  have hmem : (E : Set X) ∈ ({C, D} : Set (Set X)) := hpair ▸ ⟨hE, hxE⟩
  rcases hmem with h | h
  · exact hEI (h ▸ hCI)
  · exact hEI (h ▸ hDI)

/-! ### The degree of the intersection decomposes over the components -/

/-- **The degree of the intersection of a union of irreducible components with the closure of the
complement is the sum of the degrees of the pieces.**  Let `X` be a one-dimensional `k`-scheme,
locally of finite type and with at worst nodal singularities, let `I` cut out a closed subscheme
`C`, and let `Λ` be a finite set of irreducible components of `X` contained in the support of
`I`.  Write `Y` for the scheme-theoretic union of the members of `Λ`, cut out by the infimum of
their vanishing ideals, and `X'` for the scheme-theoretic closure of `X \ C`.  Then

`deg (Y ∩ X') = ∑_{Λ} deg (Λ ∩ X')`.

Nothing is assumed about `I` beyond the members of `Λ` lying in its support — in particular no
reducedness — and the `Λ ∩ X'` are pairwise disjoint by
`Stacks.Curves.sup_sup_complementaryCurveIdeal_eq_top`, which is where a node having only two
branches is used.  Properness is required of `Y ∩ X'` only. -/
theorem finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_finsetInf_eq_sum
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) (Λ : Finset (Set X))
    (hΛ : ∀ Z ∈ Λ, Z ∈ irreducibleComponents X ∧ Z ⊆ (I.support : Set X))
    (hp : IsProper ((((Λ.inf fun Z =>
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z))) ⊔
      complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k)))) :
    Module.finrank k (structureSheafCohomology
        ((((Λ.inf fun Z => Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z))) ⊔
          complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k))) 0) =
      ∑ Z ∈ Λ, Module.finrank k (structureSheafCohomology
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z) ⊔
          complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k))) 0) := by
  have hpair : ∀ Z ∈ Λ, ∀ W ∈ Λ, Z ≠ W →
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z) ⊔
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure W) ⊔
          complementaryCurveIdeal I = ⊤ := fun Z hZ W hW hZW =>
    sup_sup_complementaryCurveIdeal_eq_top hX_dimension hX_nodal I (hΛ Z hZ).1 (hΛ W hW).1 hZW
      (hΛ Z hZ).2 (hΛ W hW).2
  have hdistr := Scheme.IdealSheafData.finsetInf_sup_of_pairwise
    (fun Z : Set X => Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z))
    (complementaryCurveIdeal I) Λ hpair
  rw [hdistr] at hp ⊢
  refine finrank_structureSheafCohomology_zero_finsetInf_eq_sum k (X ↘ Spec (.of k)) _ Λ
    (fun Z hZ W hW hZW => ?_) hp
  rw [← sup_sup_distrib_right]
  exact hpair Z hZ W hW hZW

/-- **The degree of the intersection with the complementary curve decomposes over the components,
because a node has only two branches.**  Let `k` be a field and `X` a one-dimensional
equidimensional `k`-scheme, locally of finite type and with at worst nodal singularities.  Let
`C ⊆ X` be a reduced closed subscheme, equidimensional of dimension one, cut out by `I`, and let
`X'` be the scheme-theoretic closure of `X \ C`, cut out by
`AlgebraicGeometry.complementaryCurveIdeal I`.  Let `Λ` enumerate the irreducible components of
`C`, which under these hypotheses are the irreducible components of `X` contained in `C`.  Then

`deg (C ∩ X') = ∑_{Λ} deg (Λ ∩ X')`,

`deg` being `h⁰`, the dimension over `k` of the ring of global functions, which is the degree of
a finite scheme and the quantity `AlgebraicGeometry.genus_union` calls the degree of an
intersection.

The content is that no point of `X` lies on two distinct components of `C` and on `X'`, which
would make it a point of `X` with at least three branches; that is
`Stacks.Curves.sup_sup_complementaryCurveIdeal_eq_top`, and the degrees then add with no
correction term.  Reducedness of `C` and the two equidimensionality hypotheses are used only to
identify `C` with the union of the ambient components it contains
(`Stacks.Curves.eq_union_irreducibleComponents`); the additivity itself needs none of them, and
is
`Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_finsetInf_eq_sum`.
Properness is required of `C ∩ X'` only, and only for finite dimensionality. -/
theorem finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_eq_sum
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    (Λ : Finset (Set X))
    (hΛ : ∀ Z : Set X, Z ∈ Λ ↔ Z ∈ irreducibleComponents X ∧ Z ⊆ (I.support : Set X))
    (hp : IsProper ((I ⊔ complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k)))) :
    Module.finrank k (structureSheafCohomology
        ((I ⊔ complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k))) 0) =
      ∑ Z ∈ Λ, Module.finrank k (structureSheafCohomology
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z) ⊔
          complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k))) 0) := by
  have hunion := eq_union_irreducibleComponents hX_equidimensional hX_dimension hX_nodal I
    hY_equidimensional hY_dimension
  rw [Scheme.IdealSheafData.vanishingIdeal_iSup] at hunion
  have hI : I = Λ.inf fun Z : Set X =>
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z) := by
    rw [hunion, Finset.inf_eq_iInf, iInf_subtype]
    simp only [hΛ]
  have hB := finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_finsetInf_eq_sum
    hX_dimension hX_nodal I Λ (fun Z hZ => (hΛ Z).mp hZ) (by rw [← hI]; exact hp)
  rw [← hI] at hB
  exact hB

end Stacks.Curves

end
