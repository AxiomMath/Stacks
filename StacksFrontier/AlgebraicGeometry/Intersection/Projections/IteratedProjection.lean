module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjectionLocalIsomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A general centre which is simultaneously good for finiteness, étaleness and local isomorphism

Let `V` be a vector space of dimension `m + 2` over an algebraically closed field, let
`X ⊆ 𝐏(V)` be a closed subvariety of dimension `m` and let `Z ⊊ X` be a closed subvariety. For
a general closed point `p` of `𝐏(V)` the projection `r_p` away from `p` is defined on `X` and the
resulting morphism `r_p|_X : X ⟶ 𝐏(W_p)` is at the same time

* finite,
* étale at each of a finite collection of nonsingular closed points of `X`, and
* an isomorphism of `Z` onto its image over an open neighbourhood of `r_p(z)` for each of a
  finite collection of points `z` of `Z` which are nonsingular on `X`.

Because the three conditions each hold over a nonempty Zariski open set of centres and `𝐏(V)`
is irreducible, a single centre can be chosen for all of them at once; and because the domain of
definition of `r_p` is an open subscheme, the factorization of the inclusion `X ⊆ 𝐏(V)` through
it is unique, so the three conditions are conditions on one and the same morphism `r_p|_X`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_good_projection`:
  a nonempty Zariski open set of centres each of which is good for finiteness, for étaleness at
  the chosen points of `X` and for the local isomorphism of `r_p|_Z` at the chosen points of `Z`,
  all for the same factorization `r_p|_X`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.nonempty_inter_iInter_of_finite`: in an irreducible
  space a nonempty open subset meets the intersection of a finite family of nonempty open
  subsets, which is how a single centre is chosen for finitely many generic conditions at once.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isFinite_projection_of_disjoint`: the
  projection away from a linear subspace of any dimension is defined on a closed subscheme
  disjoint from that subspace and is finite there. For a centre of dimension `c - 1` this is the
  finiteness of a composite of `c` point projections, expressed through the single submodule of
  corank `c` cutting out the centre.

## Implementation notes

The dimension hypothesis is written with `V` of dimension `m + 2`: then `𝐏(V)` has dimension
`m + 1` and the hypothesis that `X` has dimension `m` is `dim X + 1 = m + 1`, the form consumed
by part (2) of Tag 0B1Q. The local isomorphism of `r_p|_Z` is Tag 0H8A,
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_projection_restrict`,
which needs only `Z ≠ X ≠ 𝐏(V)`.

The étale points and the points at which `r_p|_Z` is a local isomorphism are carried as two
independent finite families, which is how the source uses them: the first family is the chosen
closed point of `Z` together with the chosen closed points of each `T_i ∩ Z`, and the second is
the latter alone.

The two families of points, and the point at which the local isomorphism is wanted, are required
to be nonsingular *on `X`*, not on `Z`; this is what the local analysis of the projection
needs.

A chain of point projections `𝐏(V_N) ⇢ 𝐏(V_{N-1}) ⇢ ⋯ ⇢ 𝐏(V_n)` is the projection away from the
projective subspace of dimension `N - n - 1` spanned by its centres, which is the linear subspace
cut out by a submodule of `V_N` of corank `N - n`. Finiteness of the restriction of such a
composite to a closed subscheme disjoint from that subspace is therefore available in one step,
without reference to the chain, and is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isFinite_projection_of_disjoint`.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Tag 0B1Q](https://stacks.math.columbia.edu/tag/0B1Q)
* [Stacks Project, Tag 0H8A](https://stacks.math.columbia.edu/tag/0H8A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- In an irreducible space a nonempty open subset still meets the intersection of a finite
family of nonempty open subsets indexed by a `Finset`. -/
@[ega "0 2.1.1" "partial"]
private theorem nonempty_inter_biInter {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    {ι : Type*} (s : ι → Set T) (hopen : ∀ i, IsOpen (s i)) (hne : ∀ i, (s i).Nonempty)
    (t : Finset ι) :
    ∀ U : Set T, IsOpen U → U.Nonempty → (U ∩ ⋂ i ∈ t, s i).Nonempty := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro U _ hUne
    simpa using hUne
  | @insert a t _ ih =>
    intro U hU hUne
    have hUa : (U ∩ s a).Nonempty := by
      have h := (IrreducibleSpace.isIrreducible_univ T).2 U (s a) hU (hopen a)
        (by simpa using hUne) (by simpa using hne a)
      simpa using h
    obtain ⟨y, ⟨hyU, hya⟩, hyt⟩ := ih (U ∩ s a) (hU.inter (hopen a)) hUa
    refine ⟨y, hyU, ?_⟩
    rw [Finset.set_biInter_insert]
    exact ⟨hya, hyt⟩

/-- In an irreducible space a nonempty open subset still meets the intersection of a finite
family of nonempty open subsets. -/
@[ega "0 2.1.1" "partial"]
private theorem nonempty_inter_iInter {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    {ι : Type*} [Finite ι] (s : ι → Set T) (hopen : ∀ i, IsOpen (s i))
    (hne : ∀ i, (s i).Nonempty) (U : Set T) (hU : IsOpen U) (hUne : U.Nonempty) :
    (U ∩ ⋂ i, s i).Nonempty := by
  classical
  obtain ⟨_⟩ := nonempty_fintype ι
  simpa using nonempty_inter_biInter s hopen hne Finset.univ U hU hUne

/-- **In an irreducible space a nonempty open subset meets the intersection of a finite family
of nonempty open subsets.** This is how a single centre of projection is chosen for finitely
many generic conditions at once. -/
@[ega "0 2.1.1" "partial"]
public alias nonempty_inter_iInter_of_finite := nonempty_inter_iInter

section

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- **A nonempty open set of centres which are good for finiteness, for étaleness at finitely many
nonsingular closed points and for the local isomorphism of the projection on a smaller closed
subvariety.** Let `V` have dimension `m + 2`, let `X ⊆ 𝐏(V)` be a closed subvariety of dimension `m`
other than `𝐏(V)`, let `Z ⊊ X` be an irreducible closed subscheme, let `a t` be finitely many
nonsingular points of `X` and let `b s` be finitely many points of `Z` which are nonsingular
on `X`. Then there is a nonempty Zariski open `U ⊆ 𝐏(V)` such that for every closed point `p ∈ U`
the projection `r_p` is defined on `X` and the resulting morphism `r_p|_X : X ⟶ 𝐏(W_p)` is

* finite,
* étale at every `a t`, and
* such that `r_p|_Z` is a closed immersion, hence an isomorphism of `Z` onto its image, over an
  open neighbourhood of `r_p(b s)` for every `s`.

All three assertions are about the one morphism `r_p|_X = j ≫ r_p`, the factorization `j` of the
inclusion of `X` through the domain of definition of `r_p` being unique because that domain is
an open subscheme; and `r_p|_Z` is the composite of the inclusion `Z ⊆ X` with it. -/
public theorem exists_isOpen_forall_closedPoint_good_projection {m : ℕ}
    (hV : Module.finrank k V = m + 2) {X Z : Scheme.{u}}
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (iZ : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iZ] [IrreducibleSpace Z]
    (e : Z ⟶ X) (he : e ≫ iX = iZ) (hZX : ¬ IsIso e) (hXP : ¬ IsIso iX)
    (hdimX : topologicalKrullDim X + 1 = ((m + 1 : ℕ) : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X)
    (hareg : ∀ t, a t ∈ regularLocus X)
    {β : Type*} [Finite β] (b : β → Z)
    (hbreg : ∀ s, e (b s) ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iX ∧
          IsFinite (j ≫ projection k V (pointSubmodule k V p)) ∧
          (∀ t, EtaleAt (j ≫ projection k V (pointSubmodule k V p)) (a t)) ∧
          ∀ s, ∃ N : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
            ((e ≫ j) ≫ projection k V (pointSubmodule k V p)) (b s) ∈ N ∧
            IsClosedImmersion (((e ≫ j) ≫ projection k V (pointSubmodule k V p)) ∣_ N) := by
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by rw [hV]; omega)
  obtain ⟨U₀, hU₀ne, hU₀⟩ := exists_isOpen_isFinite_projection_restrict iX hXP
  choose UA hUAne hUA using fun t : α =>
    exists_isOpen_etaleAt_projection_restrict (m + 1) (by rw [hV]) iX hdimX (a t) (hareg t)
  choose UB hUBne hUB using fun s : β =>
    exists_isOpen_forall_closedPoint_projection_restrict iZ iX e he hZX hXP (b s) (hbreg s)
  have hAopen := U₀.isOpen.inter (isOpen_iInter_of_finite fun t => (UA t).isOpen)
  have hAne := nonempty_inter_iInter _ (fun t => (UA t).isOpen) hUAne _ U₀.isOpen hU₀ne
  refine ⟨⟨_, hAopen.inter (isOpen_iInter_of_finite fun s => (UB s).isOpen)⟩,
    nonempty_inter_iInter _ (fun s => (UB s).isOpen) hUBne _ hAopen hAne, ?_⟩
  rintro p ⟨⟨hp₀, hpA⟩, hpB⟩ hpc
  obtain ⟨j, hj, hfin⟩ := hU₀ p hp₀ hpc
  refine ⟨j, hj, hfin, fun t => ?_, fun s => ?_⟩
  · obtain ⟨j', hj', het⟩ := hUA t p (Set.mem_iInter.mp hpA t) hpc
    have hjj : j' = j := (cancel_mono _).mp (by rw [hj', hj])
    rw [← hjj]
    exact het
  · obtain ⟨jz, hjz, N, hNmem, hNci⟩ := hUB s p (Set.mem_iInter.mp hpB s) hpc
    have hez : e ≫ j = jz :=
      (cancel_mono _).mp (by rw [Category.assoc, hj, he, hjz])
    rw [hez]
    exact ⟨N, hNmem, hNci⟩

end

/-- **A linear projection whose centre misses a closed subscheme is defined on it and finite
there.** Let `i : X ⟶ 𝐏(V)` be a closed immersion and let `W ≤ V` be a submodule whose linear
subspace `linearSubspace k V W` — the centre of the projection `r_W` — is disjoint from `X`.
Then the inclusion of `X` factors uniquely through the domain of definition of `r_W` and the
resulting morphism `r_W|_X : X ⟶ 𝐏(W)` is finite.

For `W` of corank one, cut out by a closed point `p`, this is the projection away from `p`. For
`W` of corank `c` the centre is a projective subspace of dimension `c - 1`, and `r_W` is the
composite of the `c` point projections away from the points of a basis of that centre; so this
is the finiteness of such a composite, expressed through the single submodule `W` rather than
through the chain. -/
public theorem exists_isFinite_projection_of_disjoint [FiniteDimensional k V] [Nontrivial V]
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    (W : Submodule k V)
    (hdisj : Disjoint (Set.range i.base) (linearSubspace k V W)) :
    ∃ j : X ⟶ (projectionDomain k V W).toScheme,
      j ≫ (projectionDomain k V W).ι = i ∧ IsFinite (j ≫ projection k V W) := by
  have hsub : Set.range i.base ⊆ Set.range (projectionDomain k V W).ι.base := by
    rw [Scheme.Opens.range_ι, coe_mapDomain_subtype]
    exact Set.subset_compl_iff_disjoint_right.mpr hdisj
  exact ⟨IsOpenImmersion.lift _ i hsub, IsOpenImmersion.lift_fac _ _ _,
    isFinite_projection_of_isClosedImmersion i _ _ (IsOpenImmersion.lift_fac _ _ _)⟩

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
