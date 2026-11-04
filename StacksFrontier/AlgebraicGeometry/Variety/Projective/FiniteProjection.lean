module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projection from a point is finite on a closed subscheme

Let `V` be a finite-dimensional vector space over an algebraically closed field `k` and let
`X ⊆ 𝐏(V)` be a closed subscheme other than `𝐏(V)` itself. For a closed point `p` of `𝐏(V)`
outside `X` the projection `r_p : 𝐏(V) ∖ {p} → 𝐏(W_p)` away from `p` is defined on all of `X`,
and the resulting morphism `r_p|_X : X → 𝐏(W_p)` is finite.

The reason is that `r_p` is an *affine* morphism — the preimage of the standard open `D₊(g)` of
`𝐏(W_p)` is the standard open `D₊(g)` of `𝐏(V)` — while `r_p|_X` is proper, `X` being proper
over `k` and `𝐏(W_p)` separated over `k`. An affine proper morphism is finite.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistChain.isAffineHom_mapHom`: the morphism of projective
  spectra induced by a graded ring homomorphism is affine on its domain of definition.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isAffineHom_projection`: a linear projection of
  projective spaces is an affine morphism.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isReduced_projectiveSpaceOfModule`: the projective
  space of a nonzero finite-dimensional vector space is reduced.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isFinite_projection_of_isClosedImmersion`: the
  restriction of a linear projection to a closed subscheme lying in its domain of definition is
  a finite morphism.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_isFinite_projection_restrict`: the
  assertion of Tag 0B1P, that the projections away from the closed points of a nonempty open
  subset of `𝐏(V)` all restrict to finite morphisms on `X`.

## Implementation notes

The source's hypothesis is that `X` is a closed subscheme of `𝐏(V)` different from `𝐏(V)`; here
`X` is a scheme together with a closed immersion `i : X ⟶ 𝐏(V)`, and `X ≠ 𝐏(V)` is `¬ IsIso i`.
That hypothesis is used only to produce a point outside `X`: since `𝐏(V)` is reduced, a
surjective closed immersion into it is an isomorphism, so the complement of the image of `i` is
a nonempty open, and it is the open `U = 𝐏(V) ∖ X` of the source's proof. Reducedness is
obtained by transporting integrality of `ℙⁿ_k` along the isomorphism attached to a basis.

The projection away from `p` is `AlgebraicGeometry.ProjectiveSpaceOfModule.projection` for the
hyperplane `W_p = AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule k V p` of degree-one
forms vanishing at `p`; it is defined on
`AlgebraicGeometry.ProjectiveSpaceOfModule.projectionDomain`, which for a closed point is the
complement of `{p}`. The restriction `r_p|_X` is therefore not a composite of `i` with a
morphism of `𝐏(V)`, but the composite of the factorization of `i` through that open with the
projection. The factorization exists because the image of `i` misses `p`, and it is unique
because the inclusion of an open is a monomorphism, so naming it in the statement is no choice:
`isFinite_projection_of_isClosedImmersion` is stated for every factorization, and the finiteness
asserted of the one produced here is finiteness of `r_p|_X`.

The source deduces finiteness from the fibres of `r_p` being affine lines, hence the fibres of
`r_p|_X` proper and affine, hence finite. The route taken here replaces the fibrewise argument
by the affineness of `r_p` itself, which is what the fibre computation amounts to, and then
appeals to the equivalence between finiteness and the conjunction of affineness and properness:
an affine universally closed morphism is integral, and an integral morphism locally of finite
type is finite.

## References

* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01WN](https://stacks.math.columbia.edu/tag/01WN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.ProjTwistChain

universe u w w'

section AffineHom

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The morphism induced by a graded ring homomorphism is affine.** Every point of `Proj 𝒜`
lies in a standard open `D₊(f)` with `f` homogeneous of positive degree, and the inverse image
of `D₊(f)` under `mapHom 𝒜 ℬ ψ` is the standard open `D₊(ψ f)` of `Proj ℬ`, which is contained
in the domain of definition `U(ψ)` and is affine there. -/
@[ega "II 2.8.3"]
public instance isAffineHom_mapHom (ψ : 𝒜 →+*ᵍ ℬ) : IsAffineHom (mapHom 𝒜 ℬ ψ) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
  obtain ⟨d, f, hd, hf, hfx⟩ := exists_homogeneous_pos_notMem 𝒜 x
  refine ⟨AlgebraicGeometry.Proj.basicOpen 𝒜 f, hfx,
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 f hf hd, ?_⟩
  rw [mapHom_preimage_basicOpen 𝒜 ℬ ψ f d hf hd]
  refine (AlgebraicGeometry.Proj.isAffineOpen_basicOpen ℬ (ψ f) (ψ.map_mem hf)
    hd).preimage_of_isOpenImmersion (mapDomain 𝒜 ℬ ψ).ι ?_
  rw [Scheme.Opens.opensRange_ι]
  exact basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf

end AffineHom

end Stacks.AlgebraicGeometry.ProjTwistChain

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

open Stacks.AlgebraicGeometry.ProjTwistChain

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **A linear projection of projective spaces is an affine morphism.** -/
public instance isAffineHom_projection (W : Submodule k V) :
    IsAffineHom (projection k V W) :=
  isAffineHom_mapHom _ _ _

/-- **The projective space of a nonzero finite-dimensional vector space is reduced**, being
isomorphic to projective `n`-space over the ground field, which is integral. -/
public theorem isReduced_projectiveSpaceOfModule [FiniteDimensional k V] [Nontrivial V] :
    IsReduced (projectiveSpaceOfModule k V) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  exact isReduced_of_isOpenImmersion
    (projectiveSpaceOfModuleIsoProjMvPolynomial (Module.finBasisOfFinrankEq k V hn)).hom

variable {k V}

/-- **A linear projection is finite on a closed subscheme contained in its domain.**

Let `i : X ⟶ 𝐏(V)` be a closed immersion and let `j` be a factorization of `i` through the
domain of definition of the projection `r_W` away from the linear subspace cut out by a
submodule `W` of `V`. Then `r_W|_X = j ≫ r_W` is a finite morphism `X ⟶ 𝐏(W)`.

It is affine because `j` is a closed immersion and `r_W` is affine, and it is proper because
composing it with the structure morphism of `𝐏(W)` gives the structure morphism of `X`, which
is proper, while `𝐏(W)` is separated over the ground field. An affine proper morphism is
finite. -/
public theorem isFinite_projection_of_isClosedImmersion [FiniteDimensional k V]
    [Nontrivial V] {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V)
    [IsClosedImmersion i] (W : Submodule k V)
    (j : X ⟶ (projectionDomain k V W).toScheme)
    (hj : j ≫ (projectionDomain k V W).ι = i) :
    IsFinite (j ≫ projection k V W) := by
  have hji : IsClosedImmersion (j ≫ (projectionDomain k V W).ι) := by
    rw [hj]; infer_instance
  have hjclosed : IsClosedImmersion j := IsClosedImmersion.of_comp j (projectionDomain k V W).ι
  have hproper : IsProper ((j ≫ projection k V W) ≫
      projectiveSpaceOfModuleToSpec k ↥W) := by
    rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]
    infer_instance
  have hproper' : IsProper (j ≫ projection k V W) :=
    IsProper.of_comp _ (projectiveSpaceOfModuleToSpec k ↥W)
  have hint : IsIntegralHom (j ≫ projection k V W) :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨hint, inferInstance⟩

/-- **Stacks Project, Tag 0B1P.** Let `V` be a vector space of dimension `n + 1` over an
algebraically closed field and let `X ⊆ 𝐏(V)` be a closed subscheme with `X ≠ 𝐏(V)`. Then there
is a nonempty Zariski open `U ⊆ 𝐏(V)` such that for every closed point `p ∈ U` the projection
`r_p` away from `p` is defined on `X` and the restriction `r_p|_X : X ⟶ 𝐏(W_p)` is a finite
morphism.

The open is the complement of `X`, which is nonempty because a surjective closed immersion into
the reduced scheme `𝐏(V)` would be an isomorphism. -/
@[stacks 0B1P]
public theorem exists_isOpen_isFinite_projection_restrict [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V)
    [IsClosedImmersion i] (hX : ¬ IsIso i) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
            IsFinite (j ≫ projection k V (pointSubmodule k V p)) := by
  have hclosed : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hred : IsReduced (projectiveSpaceOfModule k V) := isReduced_projectiveSpaceOfModule k V
  have hne : (Set.range i.base)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro hsurj
    have : Surjective i := ⟨Set.range_eq_univ.mp hsurj⟩
    exact hX (isIso_of_isClosedImmersion_of_surjective i)
  refine ⟨⟨(Set.range i.base)ᶜ, hclosed.isOpen_compl⟩, hne, fun p hp hpclosed => ?_⟩
  have hsub : Set.range i.base ⊆
      Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := by
    rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V p hpclosed]
    exact Set.subset_compl_singleton_iff.mpr hp
  refine ⟨IsOpenImmersion.lift (projectionDomain k V (pointSubmodule k V p)).ι i hsub,
    IsOpenImmersion.lift_fac _ _ _, ?_⟩
  exact isFinite_projection_of_isClosedImmersion i _ _ (IsOpenImmersion.lift_fac _ _ _)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
