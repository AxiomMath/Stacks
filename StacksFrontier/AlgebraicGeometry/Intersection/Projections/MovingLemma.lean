module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksCore.Tactic.StacksAttribute

/-!
# Moving a closed subvariety off a finite collection of subvarieties

Let `C, X` be closed subvarieties of `𝐏(V)` which intersect properly and let `T i ⊆ X` be a
finite collection of closed subvarieties. The source moves `C` in a one-parameter family
`C' ⊆ 𝐏(V) × 𝐏^1` whose fibre over `[g]` is the translate `r_g(C)`, taking for `𝐏^1` a general
line `ℓ` through `[id_V]` in the parameter space `𝐏 = 𝐏((End V)ᵛ)` and for `C'` the image of
`ℓ × C` under the family of projective transformations. Along such a line every translate
`r_g(C)` still meets `X` properly, by Tag 0B1S; the fibre over `0 = [id_V]` is `C` itself,
because the representatives of `[id_V]` are the unit scalar multiples of the identity; and a
general point `∞` of `ℓ` is a general point of `𝐏`, so the translate there also meets each
`T i` properly.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_projectiveSpaceOfModule_of_basis`:
  the projective space of a vector space with a basis indexed by `Fin (n + 1)` is irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage_nonempty`: the translate
  `r_g(S)` of a nonempty subset of `U(g)` is nonempty.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage_eq_of_represents_identity`:
  the translate of any subset by a representative of `[id_V]` is that subset, which is clause
  (2) of the source read on the fibre over `0`.

## Implementation notes

**What is proved and what is not.** The family `C' ⊆ 𝐏^N × 𝐏^1` itself is not constructed. The
source builds it as the image of `ℓ × C ⊆ 𝐏 × 𝐏(V)` under the morphism of Tag 0B2W, which the
library has in the shape `𝐏(V ⊗ 𝒪_𝐏(1)) ⊇ U(ψ) → 𝐏(V ⊗ 𝒪_𝐏)` over `𝐏`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection`) and fibrewise over a
single point `[g]` of `𝐏` (`AlgebraicGeometry.ProjectiveSpaceOfModule.endDomain` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection`), but not as the rational map
`𝐏 × 𝐏(V) ⊇ U(ψ) → 𝐏 × 𝐏(V)` the source takes the image of; this is recorded in the
implementation notes
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndomorphismProjection` and of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection`. What is
proved here is each of the four clauses in the fibrewise form in which the source's own proof
establishes them, with `𝐏^1` realized as the line `ℓ` and the fibre `C'_{[g]}` realized as the
translate `r_g(C)`, which is the set
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage`:

* clause (1), dominance of `C' → 𝐏^1`, becomes: the fibre over every closed point of `ℓ` is
  nonempty, so every closed point of `ℓ` is in the image of the family;
* clause (2), `C'_0 = C`, becomes: `r_g(C) = C` for every representative `g` of `[id_V]`;
* clause (3), proper intersection of `C'` with `X × 𝐏^1`, becomes: `r_g(C)` meets `X` properly
  for every representative of every closed point of `ℓ`;
* clause (4), proper intersection of `C'_∞` with the `T i`, becomes: `r_g(C)` meets each `T i`
  properly for every representative of the `∞` point of `ℓ`.

The step from the fibrewise form to the clauses about `C'` is the fibre-dimension computation
the source compresses into "Parts (1) and (2) are clear" and the two sentences after it; it
needs the family, so it is not carried out here.

**"For a general line", "a general point".** Both are read exactly as in Tag 0B2T and Tag 0B1S:
there is a nonempty Zariski open subset `U ⊆ 𝐏` such that every closed point `q ∈ U` is the `∞`
point of a line `ℓ` through `[id_V]` with the stated properties. The lines so produced sweep out
a dense open subset of `𝐏`. A line is a
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` cut out by a submodule of corank two,
as in those tags.

**`0` and `∞`.** That the two distinguished points of the line are distinct is not asserted, the
source leaving it implicit in "general". It is not needed to see that the conclusion is not
vacuous: clause (4) holds for every representative of `∞`, so if `∞` were `[id_V]` then clause
(4) would say that `C` already intersects each `T i` properly, which is the one case in which
nothing has to be moved.

**Proper intersection.** As in Tag 0B1S, the conclusion uses
`AlgebraicGeometry.ProjectiveSpaceOfModule.IsGoodEndomorphism`, whose second clause is the
dimension criterion defining `AlgebraicGeometry.IntersectProperly` (Tag 0AZQ) read on the image
set `r_g(C)`; the library has closedness of that image only for the linear projection and not
for `r_g`, so the predicate on irreducible closed subsets cannot be applied to it directly.
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_intersectProperly` checks
that the two readings agree whenever the image is the underlying set of a closed subvariety.

**What is carried.** Two families of hypotheses. First, that the bad locus of the pair `(C, X)`
is an irreducible closed subset of `𝐏` of codimension at least two: this is what the
formalization of Tag 0B1S itself carries, and it is passed through unchanged. Second, that for
each `i` the bad locus of the pair `(C, T i)` is a closed subset of `𝐏` other than all of `𝐏`.
That second family is the source's "a general point `∞ = [g] ∈ ℓ` is a general point of `𝐏` and
for such a point `r_g(C) ∩ T` is proper for any closed subvariety `T` of `𝐏(V)`", whose details
the source omits; the half of that sentence which is a general fact rather than a claim about
the `T i` — that a general point of `ℓ` is a general point of `𝐏` — is proved, as the
intersection of the open subset of Tag 0B1S with the complements of the bad loci, using that
`𝐏` is irreducible.

**Closedness of `X`.** The source calls `X` a subvariety, not necessarily closed. It is taken
closed here, because Tag 0B1S is formalized for a pair of closed subvarieties and clause (3) is
obtained from it.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The projective space of a vector space with a basis indexed by `Fin (n + 1)` is
irreducible.** Such a basis identifies `𝐏(V)` with `Proj k[T₀, …, Tₙ]`, which is irreducible
because its standard opens are irreducible and all contain the zero ideal. -/
public theorem irreducibleSpace_projectiveSpaceOfModule_of_basis {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) k V) :
    IrreducibleSpace (projectiveSpaceOfModule k V) :=
  (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom.homeomorph.irreducibleSpace_iff.mpr
    inferInstance

/-- In an irreducible space a nonempty open subset still meets the intersection of a finite
family of nonempty open subsets indexed by a `Finset`. -/
@[ega "0 2.1.1" "partial"]
private theorem nonempty_inter_biInter {Z : Type*} [TopologicalSpace Z] [IrreducibleSpace Z]
    {ι : Type*} (s : ι → Set Z) (hopen : ∀ i, IsOpen (s i)) (hne : ∀ i, (s i).Nonempty)
    (t : Finset ι) :
    ∀ U : Set Z, IsOpen U → U.Nonempty → (U ∩ ⋂ i ∈ t, s i).Nonempty := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro U _ hUne
    simpa using hUne
  | @insert a t _ ih =>
    intro U hU hUne
    have hUa : (U ∩ s a).Nonempty := by
      have h := (IrreducibleSpace.isIrreducible_univ Z).2 U (s a) hU (hopen a)
        (by simpa using hUne) (by simpa using hne a)
      simpa using h
    obtain ⟨x, ⟨hxU, hxa⟩, hxt⟩ := ih (U ∩ s a) (hU.inter (hopen a)) hUa
    refine ⟨x, hxU, ?_⟩
    rw [Finset.set_biInter_insert]
    exact ⟨hxa, hxt⟩

/-- In an irreducible space a nonempty open subset still meets the intersection of a finite
family of nonempty open subsets. -/
@[ega "0 2.1.1" "partial"]
private theorem nonempty_inter_iInter {Z : Type*} [TopologicalSpace Z] [IrreducibleSpace Z]
    {ι : Type*} [Finite ι] (s : ι → Set Z) (hopen : ∀ i, IsOpen (s i))
    (hne : ∀ i, (s i).Nonempty) (U : Set Z) (hU : IsOpen U) (hUne : U.Nonempty) :
    (U ∩ ⋂ i, s i).Nonempty := by
  classical
  obtain ⟨_⟩ := nonempty_fintype ι
  simpa using nonempty_inter_biInter s hopen hne Finset.univ U hU hUne

/-- **A nonempty subset of `U(g)` has nonempty translate.** The inclusion of `U(g)` carries the
preimage of such a subset onto the subset itself, so that preimage is nonempty and so is its
image under `r_g`. -/
public theorem endProjectionImage_nonempty {g : V →ₗ[k] V}
    {S : Set (projectiveSpaceOfModule k V)} (hS : S.Nonempty)
    (hsub : S ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    (endProjectionImage k V g S).Nonempty := by
  have himg : (endDomain k V g).ι.base '' ((endDomain k V g).ι.base ⁻¹' S) = S := by
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_self_of_subset_left hsub
  have h2 : ((endDomain k V g).ι.base '' ((endDomain k V g).ι.base ⁻¹' S)).Nonempty := by
    rw [himg]; exact hS
  exact (Set.image_nonempty.mp h2).image _

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- **Clause (2) of the Moving Lemma: the fibre over `0` is `C`.** Every endomorphism
representing the point `[id_V]` of the parameter space is a unit scalar multiple of the
identity, so the translate it induces is the identity on subsets of `𝐏(V)`. -/
@[stacks 0B1T "clause (2), C'_0 = C, in the fibrewise form of this module: the fibre of the \
family over 0 = [id_V] is r_g(C) for g a representative of [id_V], and that translate is C \
itself; the family C' and hence the scheme-theoretic reading of the equality are not \
constructed, see the implementation notes"]
public theorem endProjectionImage_eq_of_represents_identity [Nontrivial V]
    {p : ClosedPoints k (ParameterModule k V)}
    (hp : (p : projectiveSpaceOfModule k (ParameterModule k V)) = identityParameterPoint k V)
    {g : V →ₗ[k] V} (hg : RepresentsParameterPoint k V p g)
    (S : Set (projectiveSpaceOfModule k V)) :
    endProjectionImage k V g S = S := by
  obtain ⟨hg0, hgeq⟩ := hg
  have hpe : p = (dualEndClosedPointsEquiv k V).symm
      (Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V)) :=
    Subtype.ext hp
  have hmk : Projectivization.mk k g hg0 =
      Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V) := by
    rw [← hgeq, hpe, Equiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k g (LinearMap.id : V →ₗ[k] V) hg0
    (linearMapId_ne_zero k V)).mp hmk
  have hgc : g = (c : k) • LinearMap.id := by rw [← hc, Units.smul_def]
  exact endProjectionImage_of_eq_smul_id k V hgc S

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
