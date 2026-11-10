module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ChainProjection
public import
  StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersectionBound
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.IteratedProjection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.CompositionAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.IsoInvariance
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.LocalIsomorphism
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.PreimageOfImage
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.Topology.Dimension.UnionDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chain of projections of Stacks 0B0E

Let `X ⊆ 𝐏(V)` be a closed subvariety of dimension `n` of the projective space of a vector space
of dimension `N + 1` over an algebraically closed field, and let `a : α → X` be a finite family
of nonsingular closed points of `X`. The proof of Stacks 0B0E needs the composite projection

`π = r_{n+1} ∘ ⋯ ∘ r_N : X ⟶ 𝐏^n`

away from a general linear subspace of dimension `N - n - 1`, which is finite and étale at every
`a t`. Tag 0B1Q delivers one step of this, away from a single point, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_comp_eq_projection_map_subtype` presents the
composite of two steps as a projection of the smaller projective space. This module runs the
induction along that chain.

## The two invariants

Only the *last* step of the chain lands étaleness of the projection into `𝐏(V_n)`. Part (2) of
Tag 0B1Q, which is where that étaleness comes from, needs `dim 𝐏(V) = dim X + 1`, and that holds
only at the last stage; the earlier stages have `dim X < dim 𝐏(V_j) - 1`, where the available
input is part (1) of Tag 0B1Q —
`exists_isOpen_forall_closedPoint_isClosedImmersion_projection_restrict` of
`StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection` —
giving a *closed immersion over an open neighbourhood* of the image point and no more. So the
induction carries a weaker invariant, and the final step — where part (2) of Tag 0B1Q applies
because `dim X_{n + 1} + 1 = dim 𝐏(V_{n + 1})` — converts it into étaleness over `𝐏(V_n)`.

## Main results

All of them live in the namespace `AlgebraicGeometry.ProjectiveSpaceOfModule`.

* `exists_closedPoint_forall_mem_isFinite_projection`: one centre good for finiteness and for
  finitely many prescribed generic conditions, which is the part of every stage that does not
  depend on which condition is imposed.
* `exists_closedPoint_isFinite_isClosedImmersion_projection_restrict`: one non-final stage of the
  chain, as Tags 0B1P and 0B1Q(1) deliver it.
* `exists_closedPoint_isFinite_etaleAt_toImage_projection`: the same stage with the closed
  immersion over a neighbourhood recorded both as étaleness of `X ⟶ r_p(X)` at the chosen points
  and as a separating open around each of them — the two forms the chain carries.
* `exists_closedPoint_isFinite_etaleAt_projection`: the final stage, Tags 0B1P, 0B1Q(2) and
  0B1R at one common centre.
* `inter_preimage_image_eq_union_of_step`, `errorTerm_first` and `errorTerm_next`: how the error
  term of condition (4) of the source propagates along the chain.
* `inter_preimage_image_comp_subset`: how the separating opens of two consecutive stages
  compose.
* `exists_submodule_isFinite_surjective_etaleAt_image`: the induction, producing for each corank
  `s` with `1 ≤ s` and `n + s + 1 ≤ N` a submodule `W ≤ V` of corank `s` missing `X`, the finite
  projection `r_W|_X`, the closed subvariety `r_W(X) ⊆ 𝐏(W)` onto which `X` maps finitely,
  surjectively and étale at the chosen points, a separating open around each chosen point, and
  the accumulated error term.
* `exists_submodule_finrank_eq_isFinite_etaleAt_projection`: **conditions (1), (2), (3) and (4)
  of the proof of Stacks 0B0E** — a submodule `W ≤ V` of dimension `n + 1` missing `X` for which
  `π = r_W|_X : X ⟶ 𝐏(W)` is finite, étale at every chosen point, carries `Z` as the whole of
  `π^{-1}(π(Z))` near each chosen closed point of `Z`, and decomposes
  `T i ∩ π^{-1}(π(Z)) = (T i ∩ Z) ∪ F_i` with `dim F_i ≤ d + d' - n`.

Condition (3) of the source is the statement that `π|_Z : Z ⟶ π(Z)` is an isomorphism over a
neighbourhood of `π(x)` for the chosen closed points `x` of `Z`; what is produced here is the
consequence the source draws from it, that `Z` is the whole of `π^{-1}(π(Z))` on a neighbourhood
of `x`. Tag 0H8A supplies the condition itself at the last stage of the chain, and
`AlgebraicGeometry.exists_isOpen_inter_preimage_closure_range_subset` turns it into that
consequence.

## Implementation notes

**The invariant is étaleness onto the image, not a closed immersion over an open.** The
closed-immersion clause of part (1) of Tag 0B1Q is about an open subset of `𝐏(W_j)`, and those
opens do not compose from one stage to the next: shrinking one of them to a common open with the
next would need the image of a closed subset under the restricted morphism. Étaleness of
`X ⟶ X_j` at the chosen points carries exactly the same information — a local isomorphism onto
the image — and *does* compose, by `AlgebraicGeometry.etaleAt_comp`. So the invariant carries the
intermediate subvariety `X_j ⊆ 𝐏(W_j)` together with the finite surjection `X ⟶ X_j` and its
étaleness at the chosen points, and each stage extends it by one composition.

**The chain also carries a separating open around each chosen point.** At a non-final stage
`X_j ⟶ X_{j + 1}` is not merely étale at the chosen points but an *isomorphism* over an open, by
`AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_toImage`, so there is an open `O ⊆ X_j`
around each chosen point with `O ∩ u^{-1}(u(S)) ⊆ S` for *every* subset `S`, where `u` is the
morphism onto the image. That clause composes along the chain —
`inter_preimage_image_comp_subset` — and quantifying it over all subsets is what makes it
compose, since composing it at `S` uses the next stage's clause at the different subset `u(S)`.
It is what the strictness clause of Stacks 0B0E consumes: at the chosen closed point of `Z` no
component of `π^{-1}(π(Z))` other than `Z` passes through. Nothing about `Z` is carried along the
chain for it; only the last stage, where the projection is étale rather than injective, needs
`Z` itself.

**The dimension of the intermediate subvariety** is read off that finite surjection:
`AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective` gives `dim X_j = dim X`,
which is what both the non-final condition `dim X_j + 1 < dim 𝐏(W_j)` and the final condition
`dim X_j + 1 = dim 𝐏(W_j)` are about. An upper bound on `dim X_j` alone would carry the non-final
stages but not the last one, which is why the surjection is carried rather than only the
dimension bound.

**The step is indexed by a submodule of `W`.** At a stage with submodule `W ≤ V` the next
submodule is `P.map W.subtype` for `P ≤ W` the hyperplane of the chosen point of `𝐏(W)`; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ChainProjection` for why this indexing is
used rather than a submodule of `V` below `W`.

**The invariant is stated over the image schemes.** Part (1) of Tag 0B1Q applies to a *closed
immersion* into `𝐏(W)`, and at an intermediate stage `X` itself does not embed in `𝐏(W)` — its
scheme-theoretic image does. `AlgebraicGeometry.Scheme.Hom.isVariety_image` makes that image a
variety, and
`AlgebraicGeometry.Scheme.Hom.etaleAt_toImage_of_isClosedImmersion_morphismRestrict` is what
turns the closed-immersion invariant at a stage into a local isomorphism of `X` onto the image
there, which is how the chosen points travel from one stage to the next.

**The error term of condition (4) is carried as a closed subset of `X`.** Tag 0B1R gives, at
each stage and for each `i`, a decomposition of `T_{i, j} ∩ r_p^{-1}(r_p(Z_j))` inside `𝐏(W_j)`
with an error term there; what the induction carries is its inverse image in `X`, accumulated
over the stages, so that the clause is always a statement about subsets of `X` and no images of
`T i` or of `Z` have to be carried along. Those images are recomputed at each stage from
`isClosed_image_and_topologicalKrullDim_image_le`, which also bounds their dimensions by `d'` and
`d` — that bound is what makes Tag 0B1R's `dim E + dim 𝐏(W_j) ≤ dim T_{i, j} + dim Z_j + 1`
into the uniform `dim F + (n + 1) ≤ d + d' + 1`, the dimension of every projective space the
chain projects from being at least `n + 1`. The hypothesis `Y ∪ Z ≠ 𝐏(W_j)` that Tag 0B1R needs
also comes from those bounds, through `union_ne_univ_of_topologicalKrullDim_le`.

**Regularity of the chosen points runs forwards.** The final step needs `a t` to lie in the
regular locus of the scheme being projected, which at stage `j` is the image `X_j`. That comes
from the local isomorphism *already established at stage `j`* through
`AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etaleAt`, an iff; it does not come from
étaleness at the next stage, which would be circular.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1Q](https://stacks.math.columbia.edu/tag/0B1Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.AlgebraicGeometry.ProjTwistChain

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The vertex grows by the chosen point -/

/-- **A point of the domain of `r_W` lies on the vertex of the next stage exactly when `r_W`
carries it onto the centre chosen in `𝐏(W)`.** For `P ≤ W ≤ V`, a point `z` of the domain of
definition of the projection away from `W` lies on the linear subspace of `𝐏(V)` cut out by the
image of `P` in `V` if and only if `r_W z` lies on the linear subspace of `𝐏(W)` cut out by `P`.

Both sides say `P ≤ W_z` read in the right place: the degree-one forms on `W` vanishing at
`r_W z` are `W ⊓ W_z` read inside `W`, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule_projection`, and `P.map W.subtype ≤ W_z`
is `P ≤ Submodule.comap W.subtype W_z` by the map–comap adjunction. -/
public theorem mem_linearSubspace_map_subtype_iff (W : Submodule k V) (P : Submodule k ↥W)
    (z : (projectionDomain k V W).toScheme) :
    (z.val : projectiveSpaceOfModule k V) ∈ linearSubspace k V (P.map W.subtype) ↔
      projection k V W z ∈ linearSubspace k ↥W P := by
  rw [mem_linearSubspace_iff, mem_linearSubspace_iff, pointSubmodule_projection,
    Submodule.map_le_iff_le_comap]

/-- **The chosen centre being outside the image keeps the subvariety off the next vertex.** Let
`X ⊆ 𝐏(V)` lift, through `j`, into the domain of definition of the projection `r_W` (as it does
when `X` is disjoint from the linear subspace cut out by `W`), and let `p` be a closed point of
`𝐏(W)` outside the image of `X` under `r_W`. Then `X` is disjoint from the linear subspace cut
out by the image in `V` of the hyperplane of `p`, which is the vertex of the projection at the
next stage of the chain.

This is what keeps the chain going: by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isFinite_projection_of_disjoint` the
disjointness supplies both the lift of `X` into the domain of definition of the next projection
and the finiteness of that projection, so neither has to be carried along separately. -/
public theorem disjoint_linearSubspace_map_subtype_pointSubmodule [IsAlgClosed k]
    [Module.Finite k V] (W : Submodule k V) {X : Scheme.{u}}
    (iX : X ⟶ projectiveSpaceOfModule k V)
    (j : X ⟶ (projectionDomain k V W).toScheme)
    (hj : j ≫ (projectionDomain k V W).ι = iX)
    (p : projectiveSpaceOfModule k ↥W)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k ↥W)))
    (hpnot : p ∉ Set.range (j ≫ projection k V W).base) :
    Disjoint (Set.range iX.base)
      (linearSubspace k V ((pointSubmodule k ↥W p).map W.subtype)) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, rfl⟩ hmem
  have hval : ((j.base y).val : projectiveSpaceOfModule k V) = iX.base y := by
    rw [← hj, Scheme.Hom.comp_base]
    rfl
  have hiff := mem_linearSubspace_map_subtype_iff k V W (pointSubmodule k ↥W p) (j.base y)
  rw [hval] at hiff
  have hproj : projection k V W (j.base y) ∈ linearSubspace k ↥W (pointSubmodule k ↥W p) :=
    hiff.mp hmem
  rw [linearSubspace_pointSubmodule k ↥W p hp] at hproj
  refine hpnot ⟨y, ?_⟩
  change projection k V W (j.base y) = p
  exact hproj

/-! ### How the error term of condition (4) propagates along the chain -/

/-- **One step of condition (4) of the proof of Stacks 0B0E, as set theory.** Let `f : A → B` and
`g : B → C`, let `T` and `Z` be subsets of `A`, and suppose the decomposition of Tag 0B1R holds
for the images of `T` and `Z` under `f`, with error term `E`. Then

`T ∩ (g ∘ f)^{-1}((g ∘ f)(Z)) = (T ∩ f^{-1}(f(Z))) ∪ (T ∩ f^{-1}(E))`.

With `f = π_j` the projection accumulated so far and `g = r_{p}` the next one, this is the
source's "`T_i ∩ π^{-1}(π(Z))` is the union of `T_i ∩ Z` and the inverse images of the
`E_{i, j}`", one stage at a time: the new error term is the old one together with the inverse
image of the new `E`. -/
private theorem inter_preimage_image_comp_eq {A B C : Type*} (f : A → B) (g : B → C)
    (T Z : Set A) {E : Set B}
    (h : f '' T ∩ g ⁻¹' (g '' (f '' Z)) = (f '' T ∩ f '' Z) ∪ E) :
    T ∩ (g ∘ f) ⁻¹' ((g ∘ f) '' Z) = (T ∩ f ⁻¹' (f '' Z)) ∪ (T ∩ f ⁻¹' E) := by
  have hEsub : E ⊆ g ⁻¹' (g '' (f '' Z)) := by
    intro b hb
    exact (h.ge (Or.inr hb)).2
  rw [Set.image_comp]
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · have hmem : f x ∈ (f '' T ∩ f '' Z) ∪ E :=
      h.le ⟨⟨x, hx.1, rfl⟩, by simpa using hx.2⟩
    rcases hmem with hmem | hmem
    · exact Or.inl ⟨hx.1, hmem.2⟩
    · exact Or.inr ⟨hx.1, hmem⟩
  · rintro x (⟨hxT, hxZ⟩ | ⟨hxT, hxE⟩)
    · exact ⟨hxT, Set.mem_image_of_mem g hxZ⟩
    · exact ⟨hxT, hEsub hxE⟩

/-- **The decomposition of Tag 0B1R pulled back to the domain of definition of the
projection.** Tag 0B1R decomposes `A ∩ r_p^{-1}(r_p(Z))` inside the ambient projective space,
while the step of the chain needs it inside the domain of definition of `r_p`, where the
projection is a morphism. The inclusion of that domain is injective, so the decomposition
transports by taking preimages. -/
private theorem inter_preimage_image_of_image_eq {B' B C : Type*} (incl : B' → B)
    (hinj : Function.Injective incl) (g : B' → C) (A' Z' : Set B') {E : Set B}
    (h : incl '' A' ∩ incl '' (g ⁻¹' (g '' Z')) = (incl '' A' ∩ incl '' Z') ∪ E) :
    A' ∩ g ⁻¹' (g '' Z') = (A' ∩ Z') ∪ incl ⁻¹' E := by
  have h' := congrArg (fun S => incl ⁻¹' S) h
  simpa [Set.preimage_image_eq _ hinj] using h'

/-- The cone swept out by the projection away from a closed point through the image of a subset
of the domain of definition is the image of the cone formed inside that domain. -/
private theorem projectionCone_image_eq (p : projectiveSpaceOfModule k V)
    (Z' : Set (projectionDomain k V (pointSubmodule k V p)).toScheme) :
    projectionCone k V p ((projectionDomain k V (pointSubmodule k V p)).ι.base '' Z') =
      (projectionDomain k V (pointSubmodule k V p)).ι.base ''
        ((projection k V (pointSubmodule k V p)).base ⁻¹'
          ((projection k V (pointSubmodule k V p)).base '' Z')) := by
  rw [projectionCone, Set.preimage_image_eq _
    (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.injective]

/-! ### A common centre for finiteness and for finitely many generic conditions -/

/-- **One centre which is good for finiteness and for finitely many prescribed conditions.** Let
`X ⊊ 𝐏(V)` be a closed subscheme and let `U t` be finitely many nonempty Zariski opens of `𝐏(V)`.
Then there is a closed point `p` lying in every `U t`, outside `X`, for which the projection
`r_p` is defined on `X` and `r_p|_X` is finite.

This is the part of each stage of the chain of Stacks 0B0E that does not depend on *which*
generic condition is being imposed: Tag 0B1P supplies the open of centres for which `r_p|_X` is
finite, the finitely many nonempty opens all meet because `𝐏(V)` is irreducible, and their
intersection contains a closed point because `𝐏(V)` is a Jacobson space. That `p` lies outside
`X` is not read off the open of Tag 0B1P — which is opaque in its statement — but from the lift
`j` itself: `X` lands in the domain of definition of `r_p`, which is the complement of the linear
subspace cut out by the hyperplane of `p`, and that is `{p}`. -/
private theorem exists_closedPoint_forall_mem_isFinite_projection [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] {X : Scheme.{u}}
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX] (hXP : ¬ IsIso iX)
    {α : Type*} [Finite α] (U : α → (projectiveSpaceOfModule k V).Opens)
    (hUne : ∀ t, (U t : Set (projectiveSpaceOfModule k V)).Nonempty) :
    ∃ p : projectiveSpaceOfModule k V,
      IsClosed ({p} : Set (projectiveSpaceOfModule k V)) ∧
      (∀ t, p ∈ U t) ∧ p ∉ Set.range iX.base ∧
      ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
        j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iX ∧
        IsFinite (j ≫ projection k V (pointSubmodule k V p)) := by
  classical
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  obtain ⟨U₀, hU₀ne, hU₀⟩ := exists_isOpen_isFinite_projection_restrict iX hXP
  have hopen : IsOpen ((U₀ : Set (projectiveSpaceOfModule k V)) ∩
      ⋂ t, (U t : Set (projectiveSpaceOfModule k V))) :=
    U₀.isOpen.inter (isOpen_iInter_of_finite fun t => (U t).isOpen)
  have hne := nonempty_inter_iInter_of_finite
    (fun t => (U t : Set (projectiveSpaceOfModule k V)))
    (fun t => (U t).isOpen) hUne _ U₀.isOpen hU₀ne
  obtain ⟨p, ⟨hp₀, hpA⟩, hpcl⟩ := nonempty_inter_closedPoints hne hopen.isLocallyClosed
  have hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)) := mem_closedPoints_iff.mp hpcl
  obtain ⟨j, hj, hfin⟩ := hU₀ p hp₀ hpc
  refine ⟨p, hpc, fun t => Set.mem_iInter.mp hpA t, ?_, j, hj, hfin⟩
  rintro ⟨y, hy⟩
  have hdom : p ∈ (linearSubspace k V (pointSubmodule k V p))ᶜ := by
    rw [← coe_mapDomain_subtype k V (pointSubmodule k V p), ← Scheme.Opens.range_ι]
    refine ⟨j.base y, ?_⟩
    change (j ≫ (projectionDomain k V (pointSubmodule k V p)).ι).base y = p
    rw [hj]
    exact hy
  exact hdom (by rw [linearSubspace_pointSubmodule k V p hpc]; rfl)

/-! ### One non-final stage of the chain -/

/-- **One non-final stage of the chain of projections.** Let `X ⊆ 𝐏(V)` be a closed subvariety,
not the whole of `𝐏(V)`, of a projective space of dimension `m` with `dim X < m - 1`, and let
`a : α → X` be a finite family of nonsingular points. Then there is a closed point `p` of `𝐏(V)`
outside `X` for which the projection `r_p` is defined on `X`, is finite, and is a closed
immersion over an open neighbourhood of `r_p (a t)` for every `t`.

This is Tag 0B1P and part (1) of Tag 0B1Q at one common centre: the finitely many nonempty
Zariski opens of admissible centres which they produce all meet, `𝐏(V)` being irreducible, and
their intersection contains a closed point because `𝐏(V)` is a Jacobson space. That `p` lies
outside `X` is not read off the open of Tag 0B1P — which is opaque in its statement — but from
the lift `j` itself: `X` lands in the domain of definition of `r_p`, which is the complement of
the linear subspace cut out by the hyperplane of `p`, and that is `{p}`.

The hypothesis `dim X + 1 < m` is what makes this stage non-final; at the last stage it fails
and `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_good_projection`
takes over, landing étaleness instead of a closed immersion over a neighbourhood. -/
public theorem exists_closedPoint_isFinite_isClosedImmersion_projection_restrict [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] {m : ℕ} (hV : Module.finrank k V = m + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)] (hXP : ¬ IsIso iX)
    (hdim : topologicalKrullDim X + 1 < (m : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X) :
    ∃ p : projectiveSpaceOfModule k V,
      IsClosed ({p} : Set (projectiveSpaceOfModule k V)) ∧
      p ∉ Set.range iX.base ∧
      ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
        j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iX ∧
        IsFinite (j ≫ projection k V (pointSubmodule k V p)) ∧
        ∀ t, ∃ R : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
          (j ≫ projection k V (pointSubmodule k V p)).base (a t) ∈ R ∧
          IsClosedImmersion ((j ≫ projection k V (pointSubmodule k V p)) ∣_ R) := by
  classical
  choose UA hUAne hUA using fun t : α =>
    exists_isOpen_forall_closedPoint_isClosedImmersion_projection_restrict m hV iX hdim
      (a t) (hareg t)
  obtain ⟨p, hpc, hpU, hpnot, j, hj, hfin⟩ :=
    exists_closedPoint_forall_mem_isFinite_projection k V iX hXP UA hUAne
  refine ⟨p, hpc, hpnot, j, hj, hfin, fun t => ?_⟩
  obtain ⟨j', hj', R, hRmem, hRci⟩ := hUA t p (hpU t) hpc
  have hjj : j' = j := (cancel_mono _).mp (by rw [hj', hj])
  rw [← hjj]
  exact ⟨R, hRmem, hRci⟩

/-! ### The final stage of the chain -/

/-- **The final stage of the chain of projections.** Let `X ⊆ 𝐏(V)` be a closed subvariety, not
the whole of `𝐏(V)`, of a projective space of dimension `m` with `dim X = m - 1`, and let
`a : α → X` be a finite family of nonsingular points. Then there is a closed point `p` of `𝐏(V)`
outside `X` for which the projection `r_p` is defined on `X`, is finite, and is étale at every
`a t`.

This is Tag 0B1P and part (2) of Tag 0B1Q at one common centre, the common centre being supplied
by `exists_closedPoint_forall_mem_isFinite_projection` exactly as for a non-final stage. The
hypothesis `dim X + 1 = m` is the one under which part (2) applies, and it is what makes this
stage the last one: the projection lands in a projective space of dimension `dim X`, so no
further projection is defined on the image. -/
public theorem exists_closedPoint_isFinite_etaleAt_projection [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] {m : ℕ} (hV : Module.finrank k V = m + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)] (hXP : ¬ IsIso iX)
    (hdim : topologicalKrullDim X + 1 = (m : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    (Zs : Set (projectiveSpaceOfModule k V)) (hZs : IsClosed Zs)
    {ι : Type*} [Finite ι] (Ts : ι → Set (projectiveSpaceOfModule k V))
    (hTs : ∀ i, IsClosed (Ts i)) (hTZ : ∀ i, Ts i ∪ Zs ≠ Set.univ)
    (ZS : Set X) (hZScl : IsClosed ZS) (hZSirr : IsIrreducible ZS) (hZSne : ZS ≠ Set.univ)
    {β : Type*} [Finite β] (b : β → X) (hbZ : ∀ s, b s ∈ ZS)
    (_hbcl : ∀ s, IsClosed ({b s} : Set X)) (hbreg : ∀ s, b s ∈ regularLocus X) :
    ∃ p : projectiveSpaceOfModule k V,
      IsClosed ({p} : Set (projectiveSpaceOfModule k V)) ∧
      p ∉ Set.range iX.base ∧
      (∀ i, ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Ts i ∧
        topologicalKrullDim ↑E + (m : WithBot ℕ∞) ≤
          topologicalKrullDim ↑(Ts i) + topologicalKrullDim ↑Zs + 1 ∧
        Ts i ∩ projectionCone k V p Zs = (Ts i ∩ Zs) ∪ E) ∧
      ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
        j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iX ∧
        IsFinite (j ≫ projection k V (pointSubmodule k V p)) ∧
        (∀ t, EtaleAt (j ≫ projection k V (pointSubmodule k V p)) (a t)) ∧
        ∀ s, ∃ O : Set X, IsOpen O ∧ b s ∈ O ∧
          O ∩ (j ≫ projection k V (pointSubmodule k V p)).base ⁻¹'
            closure ((j ≫ projection k V (pointSubmodule k V p)).base '' ZS) ⊆ ZS := by
  classical
  -- the reduced closed subscheme on `ZS`, and the points of it over the `b s`
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨ZS, hZScl⟩ : Closeds X) with hI
  set eZ : I.subscheme ⟶ X := I.subschemeι with heZ
  have hrange : Set.range eZ.base = ZS := range_vanishingIdeal_subschemeι ZS hZScl
  have : IrreducibleSpace I.subscheme :=
    irreducibleSpace_vanishingIdeal_subscheme ZS hZScl hZSirr
  have : IsReduced I.subscheme := by
    rw [hI]
    exact inferInstanceAs
      (IsReduced (Scheme.IdealSheafData.vanishingIdeal (⟨ZS, hZScl⟩ : Closeds X)).subscheme)
  have hpt : ∀ s, ∃ z : I.subscheme, eZ.base z = b s := by
    intro s
    change b s ∈ Set.range eZ.base
    rw [hrange]
    exact hbZ s
  choose z hz using hpt
  -- the three families of generic conditions on the centre
  choose UA hUAne hUA using fun t : α ⊕ β =>
    exists_isOpen_etaleAt_projection_restrict m hV iX hdim (Sum.elim a b t) (by
      rcases t with t | s
      · exact hareg t
      · exact hbreg s)
  choose UB hUBopen hUBne hUB using fun i : ι =>
    exists_isOpen_inter_projectionCone_eq_of_isClosed k V hV (hTs i) hZs (hTZ i)
  have hZiso : ¬ IsIso eZ := by
    intro hiso
    refine hZSne ?_
    rw [← hrange]
    refine Set.eq_univ_iff_forall.mpr fun y => ⟨(CategoryTheory.inv eZ) y, ?_⟩
    have h : (CategoryTheory.inv eZ ≫ eZ) y = y := by simp
    rwa [Scheme.Hom.comp_apply] at h
  choose UC hUCne hUC using fun s : β =>
    exists_isOpen_forall_closedPoint_projection_restrict (eZ ≫ iX) iX eZ rfl hZiso hXP
      (z s) (by rw [hz s]; exact hbreg s)
  have hUne : ∀ x : (α ⊕ β) ⊕ ι ⊕ β,
      ((Sum.elim UA (Sum.elim
          (fun i => (⟨UB i, hUBopen i⟩ : (projectiveSpaceOfModule k V).Opens)) UC) x :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)).Nonempty := by
    rintro (t | i | s)
    · exact hUAne t
    · exact hUBne i
    · exact hUCne s
  obtain ⟨p, hpc, hpU, hpnot, j, hj, hfin⟩ :=
    exists_closedPoint_forall_mem_isFinite_projection k V iX hXP _ hUne
  have := hfin
  have hetale : ∀ t : α ⊕ β,
      EtaleAt (j ≫ projection k V (pointSubmodule k V p)) (Sum.elim a b t) := by
    intro t
    obtain ⟨j', hj', het⟩ := hUA t p (hpU (Sum.inl t)) hpc
    have hjj : j' = j := (cancel_mono _).mp (by rw [hj', hj])
    rw [← hjj]
    exact het
  refine ⟨p, hpc, hpnot, fun i => hUB i p (hpU (Sum.inr (Sum.inl i))) hpc, j, hj, hfin,
    fun t => hetale (Sum.inl t), fun s => ?_⟩
  obtain ⟨jz, hjz, N, hNmem, hNci⟩ := hUC s p (hpU (Sum.inr (Sum.inr s))) hpc
  have hez : eZ ≫ j = jz :=
    (cancel_mono (projectionDomain k V (pointSubmodule k V p)).ι).mp (by
      rw [Category.assoc, hj, hjz])
  have hci : IsClosedImmersion
      ((eZ ≫ (j ≫ projection k V (pointSubmodule k V p))) ∣_ N) := by
    rw [← Category.assoc, hez]
    exact hNci
  have hNmem' : (j ≫ projection k V (pointSubmodule k V p)).base (b s) ∈ N := by
    rw [← hz s]
    have h : ((eZ ≫ j) ≫ projection k V (pointSubmodule k V p)).base (z s) =
        (j ≫ projection k V (pointSubmodule k V p)).base (eZ.base (z s)) := rfl
    rw [← h, hez]
    exact hNmem
  obtain ⟨O, hOopen, hOmem, hOsub⟩ :=
    exists_isOpen_inter_preimage_closure_range_subset
      (j ≫ projection k V (pointSubmodule k V p)) eZ (hz s) (hetale (Sum.inr s)) N hNmem' hci
  refine ⟨O, hOopen, hOmem, ?_⟩
  have hr : ∀ {A B C : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C),
      Set.range (u ≫ v).base = v.base '' Set.range u.base := by
    intro A B C u v
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rwa [hr, hrange] at hOsub

/-! ### The stage, in the shape the chain carries -/

/-- A morphism whose source and target have different natural dimensions is not an isomorphism. -/
private theorem not_isIso_of_topologicalKrullDim_ne {A B : Scheme.{u}} {a b : ℕ} (f : A ⟶ B)
    (hA : topologicalKrullDim A = (a : WithBot ℕ∞)) (hB : topologicalKrullDim B = (b : WithBot ℕ∞))
    (h : a ≠ b) : ¬ IsIso f := by
  intro hiso
  rw [IsHomeomorph.topologicalKrullDim_eq _ f.homeomorph.isHomeomorph, hB] at hA
  exact h (by exact_mod_cast hA.symm)

/-- The morphism of a finite morphism onto its scheme-theoretic image is finite and surjective:
finite by cancelling the separated closed immersion of the image out of the finite morphism, and
surjective because it is dominant with closed image. -/
private theorem isFinite_and_surjective_toImage {A B : Scheme.{u}} (f : A ⟶ B) [IsFinite f] :
    IsFinite f.toImage ∧ Surjective f.toImage := by
  have : IsFinite (f.toImage ≫ f.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsFinite f.toImage := IsFinite.of_comp f.toImage f.imageι
  exact ⟨inferInstance, surjective_of_isDominant_of_isClosed_range _
    f.toImage.isClosedMap.isClosed_range⟩

/-- `p + 1 < q` for natural numbers, read in `WithBot ℕ∞`. -/
private theorem natCast_add_one_lt {p q : ℕ} (h : p + 1 < q) :
    (p : WithBot ℕ∞) + 1 < (q : WithBot ℕ∞) := by
  have h' : ((p + 1 : ℕ) : WithBot ℕ∞) < ((q : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
  simpa using h'

/-- **One stage of the chain of projections, landing a local isomorphism onto the image.** In the
situation of the previous theorem,
`exists_closedPoint_isFinite_isClosedImmersion_projection_restrict`, the closed immersion over a
neighbourhood of `r_p (a t)` is recorded as étaleness of `X ⟶ r_p(X)` at `a t`.

This is the form in which the chain carries the invariant: the closed-immersion clause is about
an open of `𝐏(W_p)` and cannot be composed from one stage to the next, whereas étaleness of the
morphism onto the image composes by
`AlgebraicGeometry.etaleAt_comp` and, being an *iff* through
`AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etaleAt`, also carries the nonsingularity of
the chosen points forwards onto the image. -/
public theorem exists_closedPoint_isFinite_etaleAt_toImage_projection [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] {m : ℕ} (hV : Module.finrank k V = m + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)] (hXP : ¬ IsIso iX)
    (hdim : topologicalKrullDim X + 1 < (m : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    (Zs : Set (projectiveSpaceOfModule k V)) (hZs : IsClosed Zs)
    {ι : Type*} [Finite ι] (Ts : ι → Set (projectiveSpaceOfModule k V))
    (hTs : ∀ i, IsClosed (Ts i)) (hTZ : ∀ i, Ts i ∪ Zs ≠ Set.univ) :
    ∃ p : projectiveSpaceOfModule k V,
      IsClosed ({p} : Set (projectiveSpaceOfModule k V)) ∧
      p ∉ Set.range iX.base ∧
      (∀ i, ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Ts i ∧
        topologicalKrullDim ↑E + (m : WithBot ℕ∞) ≤
          topologicalKrullDim ↑(Ts i) + topologicalKrullDim ↑Zs + 1 ∧
        Ts i ∩ projectionCone k V p Zs = (Ts i ∩ Zs) ∪ E) ∧
      ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
        j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iX ∧
        IsFinite (j ≫ projection k V (pointSubmodule k V p)) ∧
        (∀ t, EtaleAt (j ≫ projection k V (pointSubmodule k V p)).toImage (a t)) ∧
        ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧ ∀ S : Set X,
          O ∩ (j ≫ projection k V (pointSubmodule k V p)).toImage.base ⁻¹'
            ((j ≫ projection k V (pointSubmodule k V p)).toImage.base '' S) ⊆ S := by
  classical
  choose UA hUAne hUA using fun t : α =>
    exists_isOpen_forall_closedPoint_isClosedImmersion_projection_restrict m hV iX hdim
      (a t) (hareg t)
  choose UB hUBopen hUBne hUB using fun i : ι =>
    exists_isOpen_inter_projectionCone_eq_of_isClosed k V hV (hTs i) hZs (hTZ i)
  have hUne : ∀ x : α ⊕ ι,
      ((Sum.elim UA (fun i => (⟨UB i, hUBopen i⟩ : (projectiveSpaceOfModule k V).Opens)) x :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)).Nonempty := by
    rintro (t | i)
    · exact hUAne t
    · exact hUBne i
  obtain ⟨p, hpc, hpU, hpnot, j, hj, hfin⟩ :=
    exists_closedPoint_forall_mem_isFinite_projection k V iX hXP _ hUne
  have : IsIntegral X := inferInstance
  have := hfin
  have hstage : ∀ t, ∃ R : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
      (j ≫ projection k V (pointSubmodule k V p)).base (a t) ∈ R ∧
      IsClosedImmersion ((j ≫ projection k V (pointSubmodule k V p)) ∣_ R) := by
    intro t
    obtain ⟨j', hj', R, hRmem, hRci⟩ := hUA t p (hpU (Sum.inl t)) hpc
    have hjj : j' = j := (cancel_mono _).mp (by rw [hj', hj])
    rw [hjj] at hRmem hRci
    exact ⟨R, hRmem, hRci⟩
  refine ⟨p, hpc, hpnot, fun i => hUB i p (hpU (Sum.inr i)) hpc, j, hj, hfin, fun t => ?_,
    fun t => ?_⟩
  · obtain ⟨R, hRmem, hRci⟩ := hstage t
    exact Scheme.Hom.etaleAt_toImage_of_isClosedImmersion_morphismRestrict _ R hRci hRmem
  · obtain ⟨R, hRmem, hRci⟩ := hstage t
    exact Scheme.Hom.exists_isOpen_forall_inter_preimage_image_subset_toImage _ R hRci hRmem

/-! ### Dimensions of images, and proper closed subsets -/

/-- A morphism which is an isomorphism has injective underlying map. -/
private theorem injective_base_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] :
    Function.Injective ⇑f.base := f.homeomorph.injective

/-- **The image of a closed subset under a finite morphism of schemes of finite type over a field
is closed and has at most the dimension of the subset.** Closedness is universal closedness of a
finite morphism; the dimension bound is
`AlgebraicGeometry.topologicalKrullDim_closure_image_le` with the closure dropped. -/
@[ega "IV 5.4.2" "partial, special case"]
public theorem isClosed_image_and_topologicalKrullDim_image_le {A B : Scheme.{u}} (f : A ⟶ B)
    [IsFinite f] (sA : A ⟶ Spec (.of k)) (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA]
    [LocallyOfFiniteType sB] [QuasiCompact sA] (hf : f ≫ sB = sA) {S : Set A} (hS : IsClosed S) :
    IsClosed (f.base '' S) ∧
      topologicalKrullDim ↥(f.base '' S) ≤ topologicalKrullDim ↥S := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  have hcl : IsClosed (f.base '' S) := f.isClosedMap _ hS
  refine ⟨hcl, ?_⟩
  have h := topologicalKrullDim_closure_image_le k f sA sB hf hS
  rwa [hcl.closure_eq] at h

/-- A subset of dimension strictly below that of the ambient space is not the whole space. -/
private theorem ne_univ_of_topologicalKrullDim_le {T : Type*} [TopologicalSpace T] {A : Set T}
    {c : WithBot ℕ∞} (hAc : topologicalKrullDim ↥A ≤ c) (hc : c < topologicalKrullDim T) :
    A ≠ Set.univ := by
  intro h
  rw [h, topologicalKrullDim_univ] at hAc
  exact absurd hAc (not_le.mpr hc)

/-- Two closed subsets of dimension strictly below that of the ambient space do not cover it.
This is the hypothesis `Y ∪ Z ≠ 𝐏(V)` of Tag 0B1R, which holds at every stage of the chain of
Stacks 0B0E because `d` and `d'` are less than `dim X`, itself less than the dimension of every
projective space the chain passes through. -/
private theorem union_ne_univ_of_topologicalKrullDim_le {T : Type*} [TopologicalSpace T]
    [QuasiSober T] {A B : Set T} (hA : IsClosed A) (hB : IsClosed B) {c c' M : ℕ}
    (hAc : topologicalKrullDim ↥A ≤ (c : WithBot ℕ∞)) (hBc : topologicalKrullDim ↥B ≤ c')
    (hM : topologicalKrullDim T = (M : WithBot ℕ∞)) (hc : c < M) (hc' : c' < M) :
    A ∪ B ≠ Set.univ := by
  intro h
  have hle := topologicalKrullDim_union_le hA hB
  rw [h, topologicalKrullDim_univ, hM] at hle
  exact absurd (hle.trans (max_le_max hAc hBc))
    (not_le.mpr (max_lt (by exact_mod_cast hc) (by exact_mod_cast hc')))

/-- **The error term of condition (4) after one more projection.** Given the decomposition at the
projection `πs = incl ∘ f₀` accumulated so far, with error term `F`, and the decomposition of
Tag 0B1R for the images of `T` and `Z` under `πs`, with error term `E`, the decomposition at the
projection `πs' = e ∘ g ∘ f₀` holds with error term `F ∪ (T ∩ πs^{-1}(E))`.

Everything is set theory: `incl` is the inclusion of the domain of definition of the next
projection, injective because it is an open immersion, `g` is that projection, and `e` is the
identification of its target with the projective space of a submodule of `V`. -/
private theorem preimage_image_comp_injective {XX M W : Type*} (u : XX → M) (v : M → W)
    (hv : Function.Injective v) (Z : Set XX) :
    (v ∘ u) ⁻¹' ((v ∘ u) '' Z) = u ⁻¹' (u '' Z) := by
  rw [Set.image_comp, Set.preimage_comp, Set.preimage_image_eq _ hv]

private theorem inter_preimage_image_eq_union_of_step {XX BB DD CC CC' : Type*}
    (f₀ : XX → DD) {incl : DD → BB} (hincl : Function.Injective incl)
    (g : DD → CC) {e : CC → CC'} (he : Function.Injective e)
    {πs : XX → BB} (hπs : πs = incl ∘ f₀)
    {πs' : XX → CC'} (hπs' : πs' = e ∘ (g ∘ f₀))
    (T Z F : Set XX) (hinv : T ∩ πs ⁻¹' (πs '' Z) = (T ∩ Z) ∪ F) {E : Set BB}
    (hdec : πs '' T ∩ incl '' (g ⁻¹' (g '' (f₀ '' Z))) = (πs '' T ∩ πs '' Z) ∪ E) :
    T ∩ πs' ⁻¹' (πs' '' Z) = (T ∩ Z) ∪ (F ∪ (T ∩ πs ⁻¹' E)) := by
  subst hπs
  subst hπs'
  rw [Set.image_comp incl f₀ T, Set.image_comp incl f₀ Z] at hdec
  have h1 := inter_preimage_image_of_image_eq incl hincl g (f₀ '' T) (f₀ '' Z) hdec
  have h2 := inter_preimage_image_comp_eq f₀ g T Z h1
  have hinv' : T ∩ f₀ ⁻¹' (f₀ '' Z) = (T ∩ Z) ∪ F := by
    rwa [preimage_image_comp_injective f₀ incl hincl Z] at hinv
  rw [preimage_image_comp_injective (g ∘ f₀) e he Z, h2, hinv', Set.preimage_comp,
    Set.union_assoc]

/-- The part of the error term of condition (4) that comes from the stage just passed: the inverse
image of `E` in `T` meets the dimension bound `dim F + (n + 1) ≤ d + d' + 1`. -/
private lemma topologicalKrullDim_inter_preimage_add_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] {T : Set X} {E : Set Y} (hE : IsClosed E) {x y : WithBot ℕ∞}
    {n M d d' : ℕ} (hM : n + 1 ≤ M)
    (he : topologicalKrullDim ↥E + (M : WithBot ℕ∞) ≤ x + y + 1) (hx : x ≤ d') (hy : y ≤ d) :
    topologicalKrullDim ↥(T ∩ f.base ⁻¹' E) + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
      ((d + d' + 1 : ℕ) : WithBot ℕ∞) :=
  calc _ ≤ topologicalKrullDim ↥E + (M : WithBot ℕ∞) :=
        add_le_add ((topologicalKrullDim_le_of_subset Set.inter_subset_right).trans
          (topologicalKrullDim_preimage_le_of_isIntegralHom f hE)) (by exact_mod_cast hM)
    _ ≤ x + y + 1 := he
    _ ≤ (d' : WithBot ℕ∞) + (d : WithBot ℕ∞) + 1 := add_le_add (add_le_add hx hy) le_rfl
    _ = ((d + d' + 1 : ℕ) : WithBot ℕ∞) := by push_cast; ring

/-- **Condition (4) at the first projection taken**, where the projection accumulated so far is
the closed immersion of `X` itself, so that the error term starts from nothing and is the inverse
image of the one Tag 0B1R produces. -/
private theorem errorTerm_first {X : Scheme.{u}}
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX] {p : projectiveSpaceOfModule k V}
    {j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme}
    (hj : j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iX)
    {T : Set X} (hT : IsClosed T) (Z : Set X) {E : Set (projectiveSpaceOfModule k V)}
    (hE : IsClosed E) {x y : WithBot ℕ∞} {n M d d' : ℕ} (hM : n + 1 ≤ M)
    (he : topologicalKrullDim ↥E + (M : WithBot ℕ∞) ≤ x + y + 1) (hx : x ≤ d') (hy : y ≤ d)
    (hEeq : iX.base '' T ∩ projectionCone k V p (iX.base '' Z) =
      (iX.base '' T ∩ iX.base '' Z) ∪ E) :
    ∃ F : Set X, IsClosed F ∧
      topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + d' + 1 : ℕ) : WithBot ℕ∞) ∧
      T ∩ ((j ≫ projection k V (pointSubmodule k V p)).base ⁻¹'
        ((j ≫ projection k V (pointSubmodule k V p)).base '' Z)) = (T ∩ Z) ∪ F := by
  have hfac : ⇑iX.base = ⇑(projectionDomain k V (pointSubmodule k V p)).ι.base ∘ ⇑j.base := by
    rw [← hj]; rfl
  have hπ1 : ⇑(j ≫ projection k V (pointSubmodule k V p)).base =
      id ∘ (⇑(projection k V (pointSubmodule k V p)).base ∘ ⇑j.base) := rfl
  have hcone : projectionCone k V p (⇑iX.base '' Z) =
      ⇑(projectionDomain k V (pointSubmodule k V p)).ι.base ''
        (⇑(projection k V (pointSubmodule k V p)).base ⁻¹'
          (⇑(projection k V (pointSubmodule k V p)).base '' (⇑j.base '' Z))) := by
    rw [← projectionCone_image_eq k V p (⇑j.base '' Z), ← Set.image_comp, ← hfac]
  have hstep := inter_preimage_image_eq_union_of_step (⇑j.base)
    (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.injective
    (⇑(projection k V (pointSubmodule k V p)).base) Function.injective_id hfac hπ1 T Z ∅
    (by rw [Set.preimage_image_eq _ iX.isClosedEmbedding.injective, Set.union_empty])
    (by rw [← hcone]; exact hEeq)
  exact ⟨T ∩ iX.base ⁻¹' E, hT.inter (hE.preimage iX.continuous),
    topologicalKrullDim_inter_preimage_add_le iX hE hM he hx hy, by rw [hstep, Set.empty_union]⟩

/-- **Condition (4) after one more projection in the chain.** The error term grows by the inverse
image of the one Tag 0B1R produces, and keeps the dimension bound. -/
private theorem errorTerm_next {X Y : Scheme.{u}} (W : Submodule k V)
    (p : projectiveSpaceOfModule k ↥W) (W' : Submodule k V)
    {j : X ⟶ (projectionDomain k V W).toScheme} {iY : Y ⟶ projectiveSpaceOfModule k ↥W}
    {q : X ⟶ Y} (hqiY : q ≫ iY = j ≫ projection k V W)
    {jY : Y ⟶ (projectionDomain k ↥W (pointSubmodule k ↥W p)).toScheme}
    (hjY : jY ≫ (projectionDomain k ↥W (pointSubmodule k ↥W p)).ι = iY)
    {j' : X ⟶ (projectionDomain k V W').toScheme}
    (e : projectiveSpaceOfModule k ↥(pointSubmodule k ↥W p) ⟶ projectiveSpaceOfModule k ↥W')
    [IsIso e]
    (hcomp : j' ≫ projection k V W' =
      ((q ≫ jY) ≫ projection k ↥W (pointSubmodule k ↥W p)) ≫ e)
    [IsIntegralHom (j ≫ projection k V W)] {T : Set X} (hT : IsClosed T) (Z : Set X) {F : Set X}
    (hF : IsClosed F) {n d d' : ℕ}
    (hFdim : topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + d' + 1 : ℕ) : WithBot ℕ∞))
    (hFeq : T ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
      (T ∩ Z) ∪ F)
    {E : Set (projectiveSpaceOfModule k ↥W)} (hE : IsClosed E) {x y : WithBot ℕ∞} {M : ℕ}
    (hM : n + 1 ≤ M) (he : topologicalKrullDim ↥E + (M : WithBot ℕ∞) ≤ x + y + 1)
    (hx : x ≤ d') (hy : y ≤ d)
    (hEeq : (j ≫ projection k V W).base '' T ∩
        projectionCone k ↥W p ((j ≫ projection k V W).base '' Z) =
      ((j ≫ projection k V W).base '' T ∩ (j ≫ projection k V W).base '' Z) ∪ E) :
    ∃ F' : Set X, IsClosed F' ∧
      topologicalKrullDim ↥F' + ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + d' + 1 : ℕ) : WithBot ℕ∞) ∧
      T ∩ ((j' ≫ projection k V W').base ⁻¹' ((j' ≫ projection k V W').base '' Z)) =
        (T ∩ Z) ∪ F' := by
  have hfac0 : (q ≫ jY) ≫ (projectionDomain k ↥W (pointSubmodule k ↥W p)).ι =
      j ≫ projection k V W := by
    rw [Category.assoc, hjY, hqiY]
  have hfac : ⇑(j ≫ projection k V W).base =
      ⇑(projectionDomain k ↥W (pointSubmodule k ↥W p)).ι.base ∘ ⇑(q ≫ jY).base := by
    rw [← hfac0]; rfl
  have hπ2 : ⇑(j' ≫ projection k V W').base =
      ⇑e.base ∘ (⇑(projection k ↥W (pointSubmodule k ↥W p)).base ∘ ⇑(q ≫ jY).base) := by
    rw [hcomp]; rfl
  have hcone : projectionCone k ↥W p (⇑(j ≫ projection k V W).base '' Z) =
      ⇑(projectionDomain k ↥W (pointSubmodule k ↥W p)).ι.base ''
        (⇑(projection k ↥W (pointSubmodule k ↥W p)).base ⁻¹'
          (⇑(projection k ↥W (pointSubmodule k ↥W p)).base '' (⇑(q ≫ jY).base '' Z))) := by
    rw [← projectionCone_image_eq k ↥W p (⇑(q ≫ jY).base '' Z), ← Set.image_comp, ← hfac]
  have hG :=
    topologicalKrullDim_inter_preimage_add_le (T := T) (j ≫ projection k V W) hE hM he hx hy
  have hGcl := hT.inter (hE.preimage (j ≫ projection k V W).continuous)
  refine ⟨F ∪ (T ∩ (j ≫ projection k V W).base ⁻¹' E), hF.union hGcl, ?_,
    inter_preimage_image_eq_union_of_step (⇑(q ≫ jY).base)
      (projectionDomain k ↥W (pointSubmodule k ↥W p)).ι.isOpenEmbedding.injective
      (⇑(projection k ↥W (pointSubmodule k ↥W p)).base) (injective_base_of_isIso e) hfac hπ2
      T Z F hFeq (by rw [← hcone]; exact hEeq)⟩
  refine (add_le_add (topologicalKrullDim_union_le hF hGcl) le_rfl).trans ?_
  rw [← max_add_add_right]
  exact max_le hFdim hG

/-- **The separating opens of two consecutive stages compose.** If `u` separates every subset of
its source from its image on `V₁` and `v` does the same on `V₂`, then `v ∘ u` does so on
`V₁ ∩ u^{-1}(V₂)`.

This is why the clause is quantified over all subsets: composing it at `S` uses it for `v` at
the different subset `u(S)`. -/
private theorem inter_preimage_image_comp_subset {A B C : Type*} (u : A → B) (v : B → C)
    {V₁ : Set A} {V₂ : Set B} (h₁ : ∀ S : Set A, V₁ ∩ u ⁻¹' (u '' S) ⊆ S)
    (h₂ : ∀ S : Set B, V₂ ∩ v ⁻¹' (v '' S) ⊆ S) (S : Set A) :
    (V₁ ∩ u ⁻¹' V₂) ∩ (v ∘ u) ⁻¹' ((v ∘ u) '' S) ⊆ S := by
  rintro y ⟨⟨hy1, hy2⟩, hy3⟩
  rw [Set.image_comp, Set.preimage_comp] at hy3
  exact h₁ S ⟨hy1, h₂ (u '' S) ⟨hy2, hy3⟩⟩

/-- **The next stage of the chain lifts `X` into the domain of the next projection.** At a
closed point `p` of `𝐏(W)` off the image `Y` of `X`, with `jY` lifting `Y` into the domain of
`r_p`, the submodule `P.map W.subtype` of `p` still misses `X`, `X` lifts finitely into the domain
of its projection, and that projection is `q ≫ jY ≫ r_p` up to the identification of the targets. -/
private theorem exists_lift_projection_map_subtype [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (W : Submodule k V) {X Y : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V)
    [IsClosedImmersion iX]
    {j : X ⟶ (projectionDomain k V W).toScheme} (hj : j ≫ (projectionDomain k V W).ι = iX)
    {iY : Y ⟶ projectiveSpaceOfModule k ↥W} {q : X ⟶ Y} (hqiY : q ≫ iY = j ≫ projection k V W)
    (p : projectiveSpaceOfModule k ↥W) (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k ↥W)))
    (hpnot : p ∉ Set.range iY.base)
    {jY : Y ⟶ (projectionDomain k ↥W (pointSubmodule k ↥W p)).toScheme}
    (hjY : jY ≫ (projectionDomain k ↥W (pointSubmodule k ↥W p)).ι = iY) :
    Disjoint (Set.range iX.base)
        (linearSubspace k V ((pointSubmodule k ↥W p).map W.subtype)) ∧
      ∃ j' : X ⟶ (projectionDomain k V ((pointSubmodule k ↥W p).map W.subtype)).toScheme,
        j' ≫ (projectionDomain k V ((pointSubmodule k ↥W p).map W.subtype)).ι = iX ∧
        IsFinite (j' ≫ projection k V ((pointSubmodule k ↥W p).map W.subtype)) ∧
        j' ≫ projection k V ((pointSubmodule k ↥W p).map W.subtype) =
          ((q ≫ jY) ≫ projection k ↥W (pointSubmodule k ↥W p)) ≫
            (mapOfLinearEquiv (mapSubtypeEquiv k V W (pointSubmodule k ↥W p))).inv := by
  have hpnot' : p ∉ Set.range (j ≫ projection k V W).base := by
    rintro ⟨x, hx⟩
    refine hpnot ⟨q.base x, ?_⟩
    rw [← hx, ← hqiY]
    rfl
  have hdisj' := disjoint_linearSubspace_map_subtype_pointSubmodule k V W iX j hj p hpc hpnot'
  obtain ⟨j', hj', hfin'⟩ := exists_isFinite_projection_of_disjoint iX _ hdisj'
  obtain ⟨jP, hjP, hjPeq⟩ := exists_comp_eq_projection_map_subtype k V W (pointSubmodule k ↥W p)
    j j' (by rw [hj', hj])
  have hjPq : jP = q ≫ jY := by
    refine (cancel_mono (projectionDomain k ↥W (pointSubmodule k ↥W p)).ι).mp ?_
    rw [hjP, Category.assoc, hjY, hqiY]
  refine ⟨hdisj', j', hj', hfin', ?_⟩
  rw [hjPeq, hjPq]
  simp only [Category.assoc]

/-! ### The chain induction -/

/-- **The first stage of the chain, with a dimension bound `d' i` for each `T i`.** The
projection away from a general closed point of `𝐏(V)`, with the closed subvariety `X` replaced by
its image, and the error term of condition (4) of the proof of Stacks 0B0E started from the
decomposition Tag 0B1R supplies at that centre, bounded separately for each `i`. -/
private theorem exists_first_submodule_family [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V]
    {N n : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) (hsN : n + 2 ≤ N)
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d : ℕ} (hd : d < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    {d' : ι → ℕ} (hd' : ∀ i, d' i < n)
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' i : WithBot ℕ∞)) :
    ∃ W : Submodule k V, Module.finrank k ↥W + 1 = N + 1 ∧
      Disjoint (Set.range iX.base) (linearSubspace k V W) ∧
      ∃ j : X ⟶ (projectionDomain k V W).toScheme,
        j ≫ (projectionDomain k V W).ι = iX ∧
        (∀ i, ∃ F : Set X, IsClosed F ∧
          topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
            ((d + d' i + 1 : ℕ) : WithBot ℕ∞) ∧
          T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
            (T i ∩ Z) ∪ F) ∧
        ∃ (Y : Scheme.{u}) (iY : Y ⟶ projectiveSpaceOfModule k ↥W) (q : X ⟶ Y),
          IsClosedImmersion iY ∧
          IsVariety k (iY ≫ projectiveSpaceOfModuleToSpec k ↥W) ∧
          IsFinite q ∧ Surjective q ∧ q ≫ iY = j ≫ projection k V W ∧
          (∀ t, EtaleAt q (a t)) ∧
          ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
            ∀ S : Set X, O ∩ q.base ⁻¹' (q.base '' S) ⊆ S := by
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k V) = (N : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have hXP : ¬ IsIso iX := not_isIso_of_topologicalKrullDim_ne iX hdim hdimP (by omega)
  have hdimlt : topologicalKrullDim X + 1 < (N : WithBot ℕ∞) := by
    rw [hdim]
    exact natCast_add_one_lt (by omega)
  have : IsIntegral X := inferInstance
  have himg : ∀ {S : Set X}, IsClosed S → IsClosed (iX.base '' S) ∧
      topologicalKrullDim ↥(iX.base '' S) ≤ topologicalKrullDim ↥S := fun {S} hS =>
    isClosed_image_and_topologicalKrullDim_image_le k iX
      (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) rfl hS
  have hTZ : ∀ i, iX.base '' (T i) ∪ iX.base '' Z ≠ Set.univ := by
    intro i
    exact union_ne_univ_of_topologicalKrullDim_le (himg (hTcl i)).1 (himg hZcl).1
      ((himg (hTcl i)).2.trans (hTd i)) ((himg hZcl).2.trans hZd) hdimP
      (by have := hd' i; omega) (by omega)
  obtain ⟨p, hpc, hpnot, hE, j, hj, hfin, het, hsep⟩ :=
    exists_closedPoint_isFinite_etaleAt_toImage_projection k V hV iX hXP hdimlt a hareg
      (iX.base '' Z) (himg hZcl).1 (fun i => iX.base '' (T i)) (fun i => (himg (hTcl i)).1) hTZ
  have := hfin
  have hWrank : Module.finrank k ↥(pointSubmodule k V p) = N := by
    have := finrank_pointSubmodule_add_one k V p hpc
    omega
  have : Nontrivial ↥(pointSubmodule k V p) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hWrank]; omega)
  obtain ⟨hqfin, hqsurj⟩ :=
    isFinite_and_surjective_toImage (j ≫ projection k V (pointSubmodule k V p))
  refine ⟨pointSubmodule k V p, by omega, ?_, j, hj, fun i => ?_,
    (j ≫ projection k V (pointSubmodule k V p)).image,
    (j ≫ projection k V (pointSubmodule k V p)).imageι,
    (j ≫ projection k V (pointSubmodule k V p)).toImage,
    inferInstance, IsVariety.mk, hqfin, hqsurj, Scheme.Hom.toImage_imageι _, het, hsep⟩
  · rw [linearSubspace_pointSubmodule k V p hpc]
    exact Set.disjoint_singleton_right.mpr hpnot
  · obtain ⟨E, hEcl, hEsub, hEdim, hEeq⟩ := hE i
    exact errorTerm_first k V iX hj (hTcl i) Z hEcl (by omega) hEdim
      ((himg (hTcl i)).2.trans (hTd i)) ((himg hZcl).2.trans hZd) hEeq

/-- **The first stage of the chain.** The projection away from a general closed point of `𝐏(V)`,
with the closed subvariety `X` replaced by its image, and the error term of condition (4) of the
proof of Stacks 0B0E started from the decomposition Tag 0B1R supplies at that centre. -/
private theorem exists_first_submodule [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    {N n : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) (hsN : n + 2 ≤ N)
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d d' : ℕ} (hd : d < n) (hd' : d' < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' : WithBot ℕ∞)) :
    ∃ W : Submodule k V, Module.finrank k ↥W + 1 = N + 1 ∧
      Disjoint (Set.range iX.base) (linearSubspace k V W) ∧
      ∃ j : X ⟶ (projectionDomain k V W).toScheme,
        j ≫ (projectionDomain k V W).ι = iX ∧
        (∀ i, ∃ F : Set X, IsClosed F ∧
          topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
            ((d + d' + 1 : ℕ) : WithBot ℕ∞) ∧
          T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
            (T i ∩ Z) ∪ F) ∧
        ∃ (Y : Scheme.{u}) (iY : Y ⟶ projectiveSpaceOfModule k ↥W) (q : X ⟶ Y),
          IsClosedImmersion iY ∧
          IsVariety k (iY ≫ projectiveSpaceOfModuleToSpec k ↥W) ∧
          IsFinite q ∧ Surjective q ∧ q ≫ iY = j ≫ projection k V W ∧
          (∀ t, EtaleAt q (a t)) ∧
          ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
            ∀ S : Set X, O ∩ q.base ⁻¹' (q.base '' S) ⊆ S :=
  exists_first_submodule_family k V hV iX hdim hsN a hareg hd Z hZcl hZd T hTcl (fun _ => hd') hTd

/-- **One step of the chain induction, with a dimension bound `d' i` for each `T i`.** Given the
invariant at a submodule `W` of corank `s`,
with `X` mapping finitely and surjectively onto a closed subvariety `Y ⊆ 𝐏(W)` étale at the
chosen points and the error term of condition (4) accumulated so far, the invariant at a
submodule of corank `s + 1`.

The chosen centre is a closed point `p` of `𝐏(W)` off `Y`, the next submodule is the image in
`V` of the hyperplane of `p`, and the next subvariety is the image of `Y` under the projection of
`𝐏(W)` away from `p`, read in `𝐏` of that image through
`AlgebraicGeometry.ProjectiveSpaceOfModule.mapOfLinearEquiv`. The error term grows by the inverse
image of the one Tag 0B1R produces in `𝐏(W)` for the images of `T i` and `Z` there. -/
private theorem exists_next_submodule_family [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V]
    {N n s : ℕ} {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d : ℕ} (hd : d < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    {d' : ι → ℕ} (hd' : ∀ i, d' i < n)
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' i : WithBot ℕ∞))
    (W : Submodule k V) (hWrank : Module.finrank k ↥W + s = N + 1) (hsN : n + s + 2 ≤ N)
    (j : X ⟶ (projectionDomain k V W).toScheme) (hj : j ≫ (projectionDomain k V W).ι = iX)
    (hF : ∀ i, ∃ F : Set X, IsClosed F ∧
      topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + d' i + 1 : ℕ) : WithBot ℕ∞) ∧
      T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
        (T i ∩ Z) ∪ F)
    {Y : Scheme.{u}} (iY : Y ⟶ projectiveSpaceOfModule k ↥W) [IsClosedImmersion iY]
    [IsVariety k (iY ≫ projectiveSpaceOfModuleToSpec k ↥W)]
    (q : X ⟶ Y) [IsFinite q] [Surjective q] (hqiY : q ≫ iY = j ≫ projection k V W)
    (hq : ∀ t, EtaleAt q (a t))
    (hqsep : ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
      ∀ S : Set X, O ∩ q.base ⁻¹' (q.base '' S) ⊆ S) :
    ∃ W' : Submodule k V, Module.finrank k ↥W' + (s + 1) = N + 1 ∧
      Disjoint (Set.range iX.base) (linearSubspace k V W') ∧
      ∃ j' : X ⟶ (projectionDomain k V W').toScheme,
        j' ≫ (projectionDomain k V W').ι = iX ∧
        (∀ i, ∃ F : Set X, IsClosed F ∧
          topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
            ((d + d' i + 1 : ℕ) : WithBot ℕ∞) ∧
          T i ∩ ((j' ≫ projection k V W').base ⁻¹' ((j' ≫ projection k V W').base '' Z)) =
            (T i ∩ Z) ∪ F) ∧
        ∃ (Y' : Scheme.{u}) (iY' : Y' ⟶ projectiveSpaceOfModule k ↥W') (q' : X ⟶ Y'),
          IsClosedImmersion iY' ∧
          IsVariety k (iY' ≫ projectiveSpaceOfModuleToSpec k ↥W') ∧
          IsFinite q' ∧ Surjective q' ∧ q' ≫ iY' = j' ≫ projection k V W' ∧
          (∀ t, EtaleAt q' (a t)) ∧
          ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
            ∀ S : Set X, O ∩ q'.base ⁻¹' (q'.base '' S) ⊆ S := by
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank k ↥W = m + 1 := ⟨N - s, by omega⟩
  have : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := k) (by rw [hm]; omega)
  have : IsIntegral Y := inferInstance
  have hfinπ : IsFinite (j ≫ projection k V W) := by rw [← hqiY]; infer_instance
  have hYdim : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_eq_of_isIntegralHom_of_surjective q, hdim]
  have hPWdim : topologicalKrullDim (projectiveSpaceOfModule k ↥W) = (m : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hm
  have hnm : n + 1 < m := by omega
  have hYP : ¬ IsIso iY := not_isIso_of_topologicalKrullDim_ne iY hYdim hPWdim (by omega)
  have hYlt : topologicalKrullDim Y + 1 < (m : WithBot ℕ∞) := by
    rw [hYdim]
    exact natCast_add_one_lt hnm
  have hbreg : ∀ t, q.base (a t) ∈ regularLocus Y := fun t =>
    (isRegularLocalRing_stalk_iff_of_etaleAt q (hq t)).mp (hareg t)
  have himg : ∀ {S : Set X}, IsClosed S →
      IsClosed ((j ≫ projection k V W).base '' S) ∧
      topologicalKrullDim ↥((j ≫ projection k V W).base '' S) ≤ topologicalKrullDim ↥S :=
    fun {S} hS =>
      isClosed_image_and_topologicalKrullDim_image_le k (j ≫ projection k V W)
        (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k ↥W)
        (by rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]) hS
  have hTZ : ∀ i, (j ≫ projection k V W).base '' (T i) ∪ (j ≫ projection k V W).base '' Z ≠
      Set.univ := by
    intro i
    exact union_ne_univ_of_topologicalKrullDim_le (himg (hTcl i)).1 (himg hZcl).1
      ((himg (hTcl i)).2.trans (hTd i)) ((himg hZcl).2.trans hZd) hPWdim
      (by have := hd' i; omega) (by omega)
  obtain ⟨p, hpc, hpnot, hE, jY, hjY, hfinY, hetY, hsepY⟩ :=
    exists_closedPoint_isFinite_etaleAt_toImage_projection k ↥W hm iY hYP hYlt
      (fun t => q.base (a t)) hbreg ((j ≫ projection k V W).base '' Z) (himg hZcl).1
      (fun i => (j ≫ projection k V W).base '' (T i)) (fun i => (himg (hTcl i)).1) hTZ
  have := hfinY
  obtain ⟨hdisj', j', hj', -, hcomp⟩ :=
    exists_lift_projection_map_subtype k V W iX hj hqiY p hpc hpnot hjY
  have hW'rank : Module.finrank k ↥((pointSubmodule k ↥W p).map W.subtype) = m := by
    rw [Submodule.finrank_map_subtype_eq]
    have := finrank_pointSubmodule_add_one k ↥W p hpc
    omega
  have : Nontrivial ↥((pointSubmodule k ↥W p).map W.subtype) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hW'rank]; omega)
  obtain ⟨hqfin, hqsurj⟩ :=
    isFinite_and_surjective_toImage (jY ≫ projection k ↥W (pointSubmodule k ↥W p))
  have := hqfin
  have := hqsurj
  refine ⟨(pointSubmodule k ↥W p).map W.subtype, by omega, hdisj', j', hj', fun i => ?_,
    (jY ≫ projection k ↥W (pointSubmodule k ↥W p)).image,
    (jY ≫ projection k ↥W (pointSubmodule k ↥W p)).imageι ≫
      (mapOfLinearEquiv (mapSubtypeEquiv k V W (pointSubmodule k ↥W p))).inv,
    q ≫ (jY ≫ projection k ↥W (pointSubmodule k ↥W p)).toImage,
    inferInstance, IsVariety.mk, inferInstance, inferInstance, ?_,
    fun t => etaleAt_comp q _ (hq t) (hetY t), fun t => ?_⟩
  · obtain ⟨F, hFcl, hFdim, hFeq⟩ := hF i
    obtain ⟨E, hEcl, hEsub, hEdim, hEeq⟩ := hE i
    exact errorTerm_next k V W p ((pointSubmodule k ↥W p).map W.subtype) hqiY hjY _ hcomp
      (hTcl i) Z hFcl hFdim hFeq hEcl (by omega) hEdim ((himg (hTcl i)).2.trans (hTd i))
      ((himg hZcl).2.trans hZd) hEeq
  · rw [hcomp]
    simp only [Category.assoc, Scheme.Hom.toImage_imageι_assoc]
  · obtain ⟨O, hOopen, hOmem, hO⟩ := hqsep t
    obtain ⟨O', hO'open, hO'mem, hO'⟩ := hsepY t
    refine ⟨O ∩ q.base ⁻¹' O', hOopen.inter (hO'open.preimage q.continuous),
      ⟨hOmem, hO'mem⟩, fun S => ?_⟩
    have hbase : ⇑(q ≫ (jY ≫ projection k ↥W (pointSubmodule k ↥W p)).toImage).base =
        ⇑(jY ≫ projection k ↥W (pointSubmodule k ↥W p)).toImage.base ∘ ⇑q.base := rfl
    rw [hbase]
    exact inter_preimage_image_comp_subset _ _ hO hO' S

/-- **One step of the chain induction.** Given the invariant at a submodule `W` of corank `s`,
with `X` mapping finitely and surjectively onto a closed subvariety `Y ⊆ 𝐏(W)` étale at the
chosen points and the error term of condition (4) accumulated so far, the invariant at a
submodule of corank `s + 1`.

The chosen centre is a closed point `p` of `𝐏(W)` off `Y`, the next submodule is the image in
`V` of the hyperplane of `p`, and the next subvariety is the image of `Y` under the projection of
`𝐏(W)` away from `p`, read in `𝐏` of that image through
`AlgebraicGeometry.ProjectiveSpaceOfModule.mapOfLinearEquiv`. The error term grows by the inverse
image of the one Tag 0B1R produces in `𝐏(W)` for the images of `T i` and `Z` there. -/
private theorem exists_next_submodule [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    {N n s : ℕ} {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d d' : ℕ} (hd : d < n) (hd' : d' < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' : WithBot ℕ∞))
    (W : Submodule k V) (hWrank : Module.finrank k ↥W + s = N + 1) (hsN : n + s + 2 ≤ N)
    (j : X ⟶ (projectionDomain k V W).toScheme) (hj : j ≫ (projectionDomain k V W).ι = iX)
    (hF : ∀ i, ∃ F : Set X, IsClosed F ∧
      topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + d' + 1 : ℕ) : WithBot ℕ∞) ∧
      T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
        (T i ∩ Z) ∪ F)
    {Y : Scheme.{u}} (iY : Y ⟶ projectiveSpaceOfModule k ↥W) [IsClosedImmersion iY]
    [IsVariety k (iY ≫ projectiveSpaceOfModuleToSpec k ↥W)]
    (q : X ⟶ Y) [IsFinite q] [Surjective q] (hqiY : q ≫ iY = j ≫ projection k V W)
    (hq : ∀ t, EtaleAt q (a t))
    (hqsep : ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
      ∀ S : Set X, O ∩ q.base ⁻¹' (q.base '' S) ⊆ S) :
    ∃ W' : Submodule k V, Module.finrank k ↥W' + (s + 1) = N + 1 ∧
      Disjoint (Set.range iX.base) (linearSubspace k V W') ∧
      ∃ j' : X ⟶ (projectionDomain k V W').toScheme,
        j' ≫ (projectionDomain k V W').ι = iX ∧
        (∀ i, ∃ F : Set X, IsClosed F ∧
          topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
            ((d + d' + 1 : ℕ) : WithBot ℕ∞) ∧
          T i ∩ ((j' ≫ projection k V W').base ⁻¹' ((j' ≫ projection k V W').base '' Z)) =
            (T i ∩ Z) ∪ F) ∧
        ∃ (Y' : Scheme.{u}) (iY' : Y' ⟶ projectiveSpaceOfModule k ↥W') (q' : X ⟶ Y'),
          IsClosedImmersion iY' ∧
          IsVariety k (iY' ≫ projectiveSpaceOfModuleToSpec k ↥W') ∧
          IsFinite q' ∧ Surjective q' ∧ q' ≫ iY' = j' ≫ projection k V W' ∧
          (∀ t, EtaleAt q' (a t)) ∧
          ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
            ∀ S : Set X, O ∩ q'.base ⁻¹' (q'.base '' S) ⊆ S :=
  exists_next_submodule_family k V iX hdim a hareg hd Z hZcl hZd T hTcl (fun _ => hd') hTd W hWrank
    hsN j hj hF iY q hqiY hq hqsep

/-- **The chain of projections of Stacks 0B0E, run through its non-final stages.** Let
`X ⊆ 𝐏(V)` be a closed subvariety of dimension `n` of the projective space of a vector space of
dimension `N + 1` over an algebraically closed field, let `a : α → X` be finitely many
nonsingular points of `X`, let `Z ⊆ X` be closed of dimension at most `d < n` and let
`T i ⊆ X` be finitely many closed subsets of dimension at most `d' i < n`, the bound
depending on `i`. For every `s` with `1 ≤ s` and `n + s + 1 ≤ N` there is a submodule `W ≤ V`
of corank `s` whose linear subspace misses `X`, so that the projection `r_W` is defined on `X`,
together with

* the closed subvariety `Y = r_W(X)` of `𝐏(W)` onto which `X` maps finitely, surjectively, and
  étale at every `a t` — conditions (1) and (2) of the source, accumulated;
* for every `i` a closed `F ⊆ X` with `dim F ≤ d + d' i - n` and
  `T i ∩ π^{-1}(π(Z)) = (T i ∩ Z) ∪ F` for `π = r_W|_X` — condition (4) of the source,
  accumulated.

Étaleness of `X ⟶ r_W(X)` at the chosen points is the local isomorphism of part (1) of Tag 0B1Q
accumulated along the chain; it is what the last stage of the chain, where part (2) of Tag 0B1Q
applies, consumes, and it carries the nonsingularity of the chosen points from each stage to the
next through `AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etaleAt`. The error term `F` is
the union of the inverse images of the error terms Tag 0B1R produces at the stages passed so far;
the bound `dim F + (n + 1) ≤ d + d' i + 1` is uniform in the stage because every projection of the
chain is taken from a projective space of dimension at least `n + 1`, the last one included, and
that is the worst case. The induction starts at `s = 1`: for `s = 0` the submodule would be `V`
itself, and `r_V` being an isomorphism is neither proved nor needed — the case `N = n + 1` takes
no projection at all. -/
public theorem exists_submodule_isFinite_surjective_etaleAt_image_family [IsAlgClosed k]
    [FiniteDimensional k V] {N n : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d : ℕ} (hd : d < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    {d' : ι → ℕ} (hd' : ∀ i, d' i < n)
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' i : WithBot ℕ∞))
    (s : ℕ) (hs : 1 ≤ s) :
    n + s + 1 ≤ N →
      ∃ W : Submodule k V, Module.finrank k ↥W + s = N + 1 ∧
        Disjoint (Set.range iX.base) (linearSubspace k V W) ∧
        ∃ j : X ⟶ (projectionDomain k V W).toScheme,
          j ≫ (projectionDomain k V W).ι = iX ∧
          (∀ i, ∃ F : Set X, IsClosed F ∧
            topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
              ((d + d' i + 1 : ℕ) : WithBot ℕ∞) ∧
            T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
              (T i ∩ Z) ∪ F) ∧
          ∃ (Y : Scheme.{u}) (iY : Y ⟶ projectiveSpaceOfModule k ↥W) (q : X ⟶ Y),
            IsClosedImmersion iY ∧
            IsVariety k (iY ≫ projectiveSpaceOfModuleToSpec k ↥W) ∧
            IsFinite q ∧ Surjective q ∧ q ≫ iY = j ≫ projection k V W ∧
            (∀ t, EtaleAt q (a t)) ∧
            ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
              ∀ S : Set X, O ∩ q.base ⁻¹' (q.base '' S) ⊆ S := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by rw [hV]; omega)
  induction s, hs using Nat.le_induction with
  | base =>
    exact fun hsN => exists_first_submodule_family k V hV iX hdim (by omega) a hareg hd Z hZcl hZd
      T hTcl hd' hTd
  | succ s hs ih =>
    intro hsN
    obtain ⟨W, hWrank, -, j, hj, hFinv, Y, iY, q, hciY, hvY, hfq, hsq, hqiY, hqet, hqsep⟩ :=
      ih (by omega)
    have := hciY
    have := hvY
    have := hfq
    have := hsq
    exact exists_next_submodule_family k V iX hdim a hareg hd Z hZcl hZd T hTcl hd' hTd W hWrank
      (by omega) j hj hFinv iY q hqiY hqet hqsep

/-- **The chain of projections of Stacks 0B0E, run through its non-final stages.** Let
`X ⊆ 𝐏(V)` be a closed subvariety of dimension `n` of the projective space of a vector space of
dimension `N + 1` over an algebraically closed field, let `a : α → X` be finitely many
nonsingular points of `X`, let `Z ⊆ X` be closed of dimension at most `d < n` and let
`T i ⊆ X` be finitely many closed subsets of dimension at most `d' < n`. For every `s` with
`1 ≤ s` and `n + s + 1 ≤ N` there is a submodule `W ≤ V` of corank `s` whose linear subspace
misses `X`, so that the projection `r_W` is defined on `X`, together with

* the closed subvariety `Y = r_W(X)` of `𝐏(W)` onto which `X` maps finitely, surjectively, and
  étale at every `a t` — conditions (1) and (2) of the source, accumulated;
* for every `i` a closed `F ⊆ X` with `dim F ≤ d + d' - n` and
  `T i ∩ π^{-1}(π(Z)) = (T i ∩ Z) ∪ F` for `π = r_W|_X` — condition (4) of the source,
  accumulated.

Étaleness of `X ⟶ r_W(X)` at the chosen points is the local isomorphism of part (1) of Tag 0B1Q
accumulated along the chain; it is what the last stage of the chain, where part (2) of Tag 0B1Q
applies, consumes, and it carries the nonsingularity of the chosen points from each stage to the
next through `AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etaleAt`. The error term `F` is
the union of the inverse images of the error terms Tag 0B1R produces at the stages passed so far;
the bound `dim F + (n + 1) ≤ d + d' + 1` is uniform in the stage because every projection of the
chain is taken from a projective space of dimension at least `n + 1`, the last one included, and
that is the worst case. The induction starts at `s = 1`: for `s = 0` the submodule would be `V`
itself, and `r_V` being an isomorphism is neither proved nor needed — the case `N = n + 1` takes
no projection at all. -/
public theorem exists_submodule_isFinite_surjective_etaleAt_image [IsAlgClosed k]
    [FiniteDimensional k V] {N n : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d d' : ℕ} (hd : d < n) (hd' : d' < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' : WithBot ℕ∞))
    (s : ℕ) (hs : 1 ≤ s) :
    n + s + 1 ≤ N →
      ∃ W : Submodule k V, Module.finrank k ↥W + s = N + 1 ∧
        Disjoint (Set.range iX.base) (linearSubspace k V W) ∧
        ∃ j : X ⟶ (projectionDomain k V W).toScheme,
          j ≫ (projectionDomain k V W).ι = iX ∧
          (∀ i, ∃ F : Set X, IsClosed F ∧
            topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
              ((d + d' + 1 : ℕ) : WithBot ℕ∞) ∧
            T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
              (T i ∩ Z) ∪ F) ∧
          ∃ (Y : Scheme.{u}) (iY : Y ⟶ projectiveSpaceOfModule k ↥W) (q : X ⟶ Y),
            IsClosedImmersion iY ∧
            IsVariety k (iY ≫ projectiveSpaceOfModuleToSpec k ↥W) ∧
            IsFinite q ∧ Surjective q ∧ q ≫ iY = j ≫ projection k V W ∧
            (∀ t, EtaleAt q (a t)) ∧
            ∀ t, ∃ O : Set X, IsOpen O ∧ a t ∈ O ∧
              ∀ S : Set X, O ∩ q.base ⁻¹' (q.base '' S) ⊆ S :=
  exists_submodule_isFinite_surjective_etaleAt_image_family k V hV iX hdim a hareg hd Z hZcl hZd
    T hTcl (fun _ => hd') hTd s hs
/-! ### The composite projection -/

/-- **Conditions (1), (2), (3) and (4) of the proof of Stacks 0B0E.** Let `X ⊆ 𝐏(V)` be a closed
subvariety of dimension `n` of the projective space of a vector space of dimension `N + 1` over
an algebraically closed field, with `n < N`; let `a : α → X` be finitely many nonsingular points
of `X`, let `Z ⊆ X` be an irreducible closed subset of dimension at most `d < n`, let
`T i ⊆ X` be finitely many closed subsets of dimension at most `d' i < n`, the bound
depending on `i`, and let `b : β → X` be finitely many nonsingular closed points of `Z`. Then
there is a submodule `W ≤ V` of dimension `n + 1` whose linear subspace — a projective subspace
of dimension `N - n - 1` — misses `X`, so that the projection `r_W` away from it is defined on
`X`, and for `π = r_W|_X : X ⟶ 𝐏(W)`

1. `π` is finite,
2. `π` is étale at every `a t` and at every `b s`,
3. every `b s` has an open neighbourhood `O` in `X` with `O ∩ π^{-1}(π(Z)) ⊆ Z`,
4. for every `i` there is a closed `F ⊆ X` with `dim F ≤ d + d' i - n` and
   `T i ∩ π^{-1}(π(Z)) = (T i ∩ Z) ∪ F`.

This is the composite `π = (r_{n + 1} ∘ ⋯ ∘ r_N)|_X` of the source, presented through the single
submodule `W` rather than through the chain. Clause 3 is condition (3) of the source in the form
its only consumer uses: the source says that `π|_Z` is an isomorphism onto its image over a
neighbourhood of `π (b s)`, and concludes from it that `Z` is the whole of `π^{-1}(π(Z))` near
`b s`, so that no other component of `π^{-1}(π(Z))` passes through `b s`.

For `N = n + 1` the submodule `W` is the hyperplane of a single general closed point and the
final-stage lemma applies to `X` itself; for `N > n + 1` the chain is run down to corank
`N - n - 1` by `exists_submodule_isFinite_surjective_etaleAt_image` and the last projection is
taken on the image `X_{n + 1} ⊆ 𝐏(W_{n + 1})` there, where
`dim X_{n + 1} + 1 = dim 𝐏(W_{n + 1})` and so part (2) of Tag 0B1Q applies. Étaleness travels
back to `X` by `etaleAt_comp` along the étale `X ⟶ X_{n + 1}` the chain carries, and across the
identification `𝐏(P) ≅ 𝐏(P.map W.subtype)` by `etaleAt_comp_isIso_iff`; clause 3 travels back
along the separating opens the chain carries, by `inter_preimage_image_comp_subset`. -/
public theorem exists_submodule_finrank_eq_isFinite_etaleAt_projection_family [IsAlgClosed k]
    [FiniteDimensional k V] {N n : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) (hnN : n < N)
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d : ℕ} (hd : d < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZirr : IsIrreducible Z)
    (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    {d' : ι → ℕ} (hd' : ∀ i, d' i < n)
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' i : WithBot ℕ∞))
    {β : Type*} [Finite β] (b : β → X) (hbZ : ∀ s, b s ∈ Z)
    (hbcl : ∀ s, IsClosed ({b s} : Set X)) (hbreg : ∀ s, b s ∈ regularLocus X) :
    ∃ W : Submodule k V, Module.finrank k ↥W = n + 1 ∧
      Disjoint (Set.range iX.base) (linearSubspace k V W) ∧
      ∃ j : X ⟶ (projectionDomain k V W).toScheme,
        j ≫ (projectionDomain k V W).ι = iX ∧
        IsFinite (j ≫ projection k V W) ∧
        (∀ t, EtaleAt (j ≫ projection k V W) (a t)) ∧
        (∀ s, EtaleAt (j ≫ projection k V W) (b s)) ∧
        (∀ s, ∃ O : Set X, IsOpen O ∧ b s ∈ O ∧
          O ∩ ((j ≫ projection k V W).base ⁻¹'
            ((j ≫ projection k V W).base '' Z)) ⊆ Z) ∧
        ∀ i, ∃ F : Set X, IsClosed F ∧
          topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
            ((d + d' i + 1 : ℕ) : WithBot ℕ∞) ∧
          T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
            (T i ∩ Z) ∪ F := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by rw [hV]; omega)
  have : IsIntegral X := inferInstance
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k V) = (N : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have habreg : ∀ t : α ⊕ β, Sum.elim a b t ∈ regularLocus X := by
    rintro (t | s)
    · exact hareg t
    · exact hbreg s
  have hZne : Z ≠ Set.univ :=
    ne_univ_of_topologicalKrullDim_le hZd (by rw [hdim]; exact_mod_cast hd)
  rcases eq_or_lt_of_le (show n + 1 ≤ N from hnN) with heq | hlt
  · have hXP : ¬ IsIso iX := not_isIso_of_topologicalKrullDim_ne iX hdim hdimP (by omega)
    have hdim' : topologicalKrullDim X + 1 = (N : WithBot ℕ∞) := by
      rw [hdim, ← heq]
      push_cast
      ring
    have himg : ∀ {S : Set X}, IsClosed S → IsClosed (iX.base '' S) ∧
        topologicalKrullDim ↥(iX.base '' S) ≤ topologicalKrullDim ↥S := fun {S} hS =>
      isClosed_image_and_topologicalKrullDim_image_le k iX
        (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) rfl hS
    have hTZ : ∀ i, iX.base '' (T i) ∪ iX.base '' Z ≠ Set.univ := by
      intro i
      exact union_ne_univ_of_topologicalKrullDim_le (himg (hTcl i)).1 (himg hZcl).1
        ((himg (hTcl i)).2.trans (hTd i)) ((himg hZcl).2.trans hZd) hdimP
        (by have := hd' i; omega) (by omega)
    obtain ⟨p, hpc, hpnot, hE, j, hj, hfin, het, hsepZ⟩ :=
      exists_closedPoint_isFinite_etaleAt_projection k V hV iX hXP hdim' (Sum.elim a b) habreg
        (iX.base '' Z) (himg hZcl).1 (fun i => iX.base '' (T i)) (fun i => (himg (hTcl i)).1) hTZ
        Z hZcl hZirr hZne b hbZ hbcl hbreg
    refine ⟨pointSubmodule k V p, ?_, ?_, j, hj, hfin, fun t => het (Sum.inl t),
      fun s => het (Sum.inr s), fun s => ?_, fun i => ?_⟩
    · have := finrank_pointSubmodule_add_one k V p hpc
      omega
    · rw [linearSubspace_pointSubmodule k V p hpc]
      exact Set.disjoint_singleton_right.mpr hpnot
    · obtain ⟨O, hOopen, hOmem, hOsub⟩ := hsepZ s
      exact ⟨O, hOopen, hOmem, fun y hy => hOsub ⟨hy.1, subset_closure hy.2⟩⟩
    · obtain ⟨E, hEcl, hEsub, hEdim, hEeq⟩ := hE i
      exact errorTerm_first k V iX hj (hTcl i) Z hEcl (by omega) hEdim
        ((himg (hTcl i)).2.trans (hTd i)) ((himg hZcl).2.trans hZd) hEeq
  · obtain ⟨W, hWrank, -, j, hj, hFinv, Y, iY, q, hciY, hvY, hfq, hsq, hqiY, hqet, hqsep⟩ :=
      exists_submodule_isFinite_surjective_etaleAt_image_family k V hV iX hdim (Sum.elim a b)
        habreg hd Z hZcl hZd T hTcl hd' hTd (N - n - 1) (by omega) (by omega)
    have := hciY
    have := hvY
    have := hfq
    have := hsq
    have : IsIntegral Y := inferInstance
    have hfinπ : IsFinite (j ≫ projection k V W) := by rw [← hqiY]; infer_instance
    have hm : Module.finrank k ↥W = (n + 1) + 1 := by omega
    have : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := k) (by rw [hm]; omega)
    have hYdim : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
      rw [← topologicalKrullDim_eq_of_isIntegralHom_of_surjective q, hdim]
    have hPWdim : topologicalKrullDim (projectiveSpaceOfModule k ↥W) =
        ((n + 1 : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hm
    have hYP : ¬ IsIso iY := not_isIso_of_topologicalKrullDim_ne iY hYdim hPWdim (by omega)
    have hYeq : topologicalKrullDim Y + 1 = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hYdim]
      push_cast
      ring
    have hYreg : ∀ t : α ⊕ β, q.base (Sum.elim a b t) ∈ regularLocus Y := fun t =>
      (isRegularLocalRing_stalk_iff_of_etaleAt q (hqet t)).mp (habreg t)
    have himg : ∀ {S : Set X}, IsClosed S →
        IsClosed ((j ≫ projection k V W).base '' S) ∧
        topologicalKrullDim ↥((j ≫ projection k V W).base '' S) ≤ topologicalKrullDim ↥S :=
      fun {S} hS =>
        isClosed_image_and_topologicalKrullDim_image_le k (j ≫ projection k V W)
          (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k ↥W)
          (by rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]) hS
    have hqimg : ∀ {S : Set X}, IsClosed S → IsClosed (q.base '' S) ∧
        topologicalKrullDim ↥(q.base '' S) ≤ topologicalKrullDim ↥S := fun {S} hS =>
      isClosed_image_and_topologicalKrullDim_image_le k q
        (iX ≫ projectiveSpaceOfModuleToSpec k V) (iY ≫ projectiveSpaceOfModuleToSpec k ↥W)
        (by rw [← Category.assoc, hqiY, Category.assoc, projection_comp_toSpec,
          ← Category.assoc, hj]) hS
    have hTZ : ∀ i, (j ≫ projection k V W).base '' (T i) ∪ (j ≫ projection k V W).base '' Z ≠
        Set.univ := by
      intro i
      exact union_ne_univ_of_topologicalKrullDim_le (himg (hTcl i)).1 (himg hZcl).1
        ((himg (hTcl i)).2.trans (hTd i)) ((himg hZcl).2.trans hZd) hPWdim
        (by have := hd' i; omega) (by omega)
    -- the image of `Z` in `Y`, and the chosen points carried onto it
    have hZYirr : IsIrreducible (q.base '' Z) :=
      hZirr.image _ (Scheme.Hom.continuous q).continuousOn
    have hZYne : q.base '' Z ≠ Set.univ :=
      ne_univ_of_topologicalKrullDim_le ((hqimg hZcl).2.trans hZd)
        (by rw [hYdim]; exact_mod_cast hd)
    have hbYZ : ∀ s, q.base (b s) ∈ q.base '' Z := fun s => ⟨b s, hbZ s, rfl⟩
    have hbYcl : ∀ s, IsClosed ({q.base (b s)} : Set Y) := by
      intro s
      have h := (hqimg (hbcl s)).1
      rwa [Set.image_singleton] at h
    obtain ⟨p, hpc, hpnot, hE, jY, hjY, hfinY, hetY, hsepY⟩ :=
      exists_closedPoint_isFinite_etaleAt_projection k ↥W hm iY hYP hYeq
        (fun t => q.base (Sum.elim a b t)) hYreg ((j ≫ projection k V W).base '' Z)
        (himg hZcl).1 (fun i => (j ≫ projection k V W).base '' (T i))
        (fun i => (himg (hTcl i)).1) hTZ (q.base '' Z) (hqimg hZcl).1 hZYirr hZYne
        (fun s => q.base (b s)) hbYZ hbYcl (fun s => hYreg (Sum.inr s))
    obtain ⟨hdisj', j', hj', hfin', hcomp⟩ :=
      exists_lift_projection_map_subtype k V W iX hj hqiY p hpc hpnot hjY
    have hcompet : ∀ t : α ⊕ β,
        EtaleAt (j' ≫ projection k V ((pointSubmodule k ↥W p).map W.subtype))
          (Sum.elim a b t) := by
      intro t
      rw [hcomp, etaleAt_comp_isIso_iff, Category.assoc]
      exact etaleAt_comp q _ (hqet t) (hetY t)
    have hbasecomp : ⇑(j' ≫ projection k V ((pointSubmodule k ↥W p).map W.subtype)).base =
        ⇑(mapOfLinearEquiv (mapSubtypeEquiv k V W (pointSubmodule k ↥W p))).inv.base ∘
          (⇑(jY ≫ projection k ↥W (pointSubmodule k ↥W p)).base ∘ ⇑q.base) := by
      rw [hcomp]; rfl
    refine ⟨(pointSubmodule k ↥W p).map W.subtype, ?_, hdisj', j', hj', hfin',
      fun t => hcompet (Sum.inl t), fun s => hcompet (Sum.inr s), fun s => ?_, fun i => ?_⟩
    · rw [Submodule.finrank_map_subtype_eq]
      have := finrank_pointSubmodule_add_one k ↥W p hpc
      omega
    · obtain ⟨O₁, hO₁open, hO₁mem, hO₁⟩ := hqsep (Sum.inr s)
      obtain ⟨O₂, hO₂open, hO₂mem, hO₂⟩ := hsepY s
      refine ⟨O₁ ∩ q.base ⁻¹' O₂, hO₁open.inter (hO₂open.preimage q.continuous),
        ⟨hO₁mem, hO₂mem⟩, ?_⟩
      rw [hbasecomp, preimage_image_comp_injective _ _
        (injective_base_of_isIso
          (mapOfLinearEquiv (mapSubtypeEquiv k V W (pointSubmodule k ↥W p))).inv) Z]
      rintro y ⟨⟨hy1, hy2⟩, hy3⟩
      rw [Set.image_comp, Set.preimage_comp] at hy3
      exact hO₁ Z ⟨hy1, hO₂ ⟨hy2, subset_closure hy3⟩⟩
    · obtain ⟨F, hFcl, hFdim, hFeq⟩ := hFinv i
      obtain ⟨E, hEcl, hEsub, hEdim, hEeq⟩ := hE i
      exact errorTerm_next k V W p ((pointSubmodule k ↥W p).map W.subtype) hqiY hjY _ hcomp
        (hTcl i) Z hFcl hFdim hFeq hEcl le_rfl hEdim ((himg (hTcl i)).2.trans (hTd i))
        ((himg hZcl).2.trans hZd) hEeq

/-- **Conditions (1), (2), (3) and (4) of the proof of Stacks 0B0E.** Let `X ⊆ 𝐏(V)` be a closed
subvariety of dimension `n` of the projective space of a vector space of dimension `N + 1` over
an algebraically closed field, with `n < N`; let `a : α → X` be finitely many nonsingular points
of `X`, let `Z ⊆ X` be an irreducible closed subset of dimension at most `d < n`, let
`T i ⊆ X` be finitely many closed subsets of dimension at most `d' < n`, and let `b : β → X` be
finitely many nonsingular closed points of `Z`. Then there is a submodule `W ≤ V` of dimension
`n + 1` whose linear subspace — a projective subspace of dimension `N - n - 1` — misses `X`, so
that the projection `r_W` away from it is defined on `X`, and for `π = r_W|_X : X ⟶ 𝐏(W)`

1. `π` is finite,
2. `π` is étale at every `a t` and at every `b s`,
3. every `b s` has an open neighbourhood `O` in `X` with `O ∩ π^{-1}(π(Z)) ⊆ Z`,
4. for every `i` there is a closed `F ⊆ X` with `dim F ≤ d + d' - n` and
   `T i ∩ π^{-1}(π(Z)) = (T i ∩ Z) ∪ F`.

This is the composite `π = (r_{n + 1} ∘ ⋯ ∘ r_N)|_X` of the source, presented through the single
submodule `W` rather than through the chain. Clause 3 is condition (3) of the source in the form
its only consumer uses: the source says that `π|_Z` is an isomorphism onto its image over a
neighbourhood of `π (b s)`, and concludes from it that `Z` is the whole of `π^{-1}(π(Z))` near
`b s`, so that no other component of `π^{-1}(π(Z))` passes through `b s`.

For `N = n + 1` the submodule `W` is the hyperplane of a single general closed point and the
final-stage lemma applies to `X` itself; for `N > n + 1` the chain is run down to corank
`N - n - 1` by `exists_submodule_isFinite_surjective_etaleAt_image` and the last projection is
taken on the image `X_{n + 1} ⊆ 𝐏(W_{n + 1})` there, where
`dim X_{n + 1} + 1 = dim 𝐏(W_{n + 1})` and so part (2) of Tag 0B1Q applies. Étaleness travels
back to `X` by `etaleAt_comp` along the étale `X ⟶ X_{n + 1}` the chain carries, and across the
identification `𝐏(P) ≅ 𝐏(P.map W.subtype)` by `etaleAt_comp_isIso_iff`; clause 3 travels back
along the separating opens the chain carries, by `inter_preimage_image_comp_subset`. -/
public theorem exists_submodule_finrank_eq_isFinite_etaleAt_projection [IsAlgClosed k]
    [FiniteDimensional k V] {N n : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) (hnN : n < N)
    {α : Type*} [Finite α] (a : α → X) (hareg : ∀ t, a t ∈ regularLocus X)
    {d d' : ℕ} (hd : d < n) (hd' : d' < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZirr : IsIrreducible Z)
    (hZd : topologicalKrullDim ↥Z ≤ (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' : WithBot ℕ∞))
    {β : Type*} [Finite β] (b : β → X) (hbZ : ∀ s, b s ∈ Z)
    (hbcl : ∀ s, IsClosed ({b s} : Set X)) (hbreg : ∀ s, b s ∈ regularLocus X) :
    ∃ W : Submodule k V, Module.finrank k ↥W = n + 1 ∧
      Disjoint (Set.range iX.base) (linearSubspace k V W) ∧
      ∃ j : X ⟶ (projectionDomain k V W).toScheme,
        j ≫ (projectionDomain k V W).ι = iX ∧
        IsFinite (j ≫ projection k V W) ∧
        (∀ t, EtaleAt (j ≫ projection k V W) (a t)) ∧
        (∀ s, EtaleAt (j ≫ projection k V W) (b s)) ∧
        (∀ s, ∃ O : Set X, IsOpen O ∧ b s ∈ O ∧
          O ∩ ((j ≫ projection k V W).base ⁻¹'
            ((j ≫ projection k V W).base '' Z)) ⊆ Z) ∧
        ∀ i, ∃ F : Set X, IsClosed F ∧
          topologicalKrullDim ↥F + ((n + 1 : ℕ) : WithBot ℕ∞) ≤
            ((d + d' + 1 : ℕ) : WithBot ℕ∞) ∧
          T i ∩ ((j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z)) =
            (T i ∩ Z) ∪ F :=
  exists_submodule_finrank_eq_isFinite_etaleAt_projection_family k V hV iX hdim hnN a hareg hd Z
    hZcl hZirr hZd T hTcl (fun _ => hd') hTd b hbZ hbcl hbreg
end AlgebraicGeometry.ProjectiveSpaceOfModule

end
