module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Global
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.DegreePositiveSection
public import StacksFrontier.AlgebraicGeometry.AmpleSigma.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
import StacksCore.Tactic.StacksAttribute

/-!
# Ampleness and the degrees on the one-dimensional components, both directions

[Stacks, Tag 0B5Y] says: let `k` be a field, let `X` be a proper scheme over `k` of dimension at
most one, let `𝓛` be an invertible `𝒪_X`-module and let `C₁, …, C_t ⊆ X` be the irreducible
components of dimension one. Then

1. `𝓛` is ample

if and only if

2. `deg(𝓛|_{C_i}) > 0` for every `i`.

The implication (1) ⟹ (2) is `./ComponentPositivity.lean`, where it is proved with no hypothesis
beyond the tag's own. This file assembles the biconditional. Its implication (2) ⟹ (1) follows
the source: the one-dimensional components `C₁, …, C_t` and the zero-dimensional ones
`x₁, …, x_r` together make a finite family of closed immersions covering `X`, so

`g : C₁ ⨿ … ⨿ C_t ⨿ x₁ ⨿ … ⨿ x_r ⟶ X`

is finite and surjective; `𝓛` is ample exactly when `g^*𝓛` is, by [Stacks, Tag 0B5V]; on a
zero-dimensional member `g^*𝓛` is an invertible module on an affine scheme, hence ample; and on a
one-dimensional member it is ample by the converse direction of [Stacks, Tag 0B5X], which is
`AlgebraicGeometry.isAmple_of_invertibleCurveDegree_pos_of_isCurve` of
`./DegreePositiveSection.lean`. Every step carries no hypothesis beyond the tag's own, so the
biconditional does not either.

## Main definitions

The elided prefix throughout is `AlgebraicGeometry`.

* `genericComponent` and `genericComponentι`: the irreducible component through a generic point,
  with its reduced induced closed subscheme structure, and its closed immersion into `X`. This is
  the tag's family, indexed over *all* the generic points rather than only the one-dimensional
  ones, because the family that covers `X` must contain the isolated closed points as well.

## Main results

* `isAmple_of_forall_isAmple_pullback_of_iUnion_range_eq_univ`: **ampleness descends along a
  finite family of closed immersions whose images cover `X`.** Unconditional. This is where
  [Stacks, Tag 0B5V] is used, in the direction `g^*𝓛` ample ⟹ `𝓛` ample, which
  `Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback` proves with no hypothesis
  beyond the tag's own; the other input is ampleness on the disjoint union itself,
  `AlgebraicGeometry.isAmple_sigma_of_forall_isAmple_pullback_sigmaι` of
  `../AmpleSigma/Basic.lean`.
* `isAmple_pullback_genericComponent_of_topologicalKrullDim_le_zero`: on a zero-dimensional
  component the restriction of any invertible module is ample. Unconditional.
* `isAmple_pullback_reducedComponent_of_invertibleCurveDegree_pos`: on a one-dimensional
  component, positivity of the degree makes the restriction ample. Unconditional.
* `isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos`: **[Stacks, Tag 0B5Y]**, both
  directions, at the tag's own hypotheses and indexing, with no hypothesis beyond the tag's own.

## Implementation notes

**The components are indexed by their generic points, not by `irreducibleComponents X`.** The
one-dimensional components already carry the index
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X`, a subset of the generic points,
and `Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent` is built from the closure of the
generic point. Indexing the covering family the same way makes
`AlgebraicGeometry.genericComponent X ξ` and
`Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ⟨ξ.1, _⟩` the *same term*, so the
one-dimensional members of the family need no transport; indexing by `irreducibleComponents X`
would need an equality of schemes.

**The dimension of a component is read off `X`.** A closed immersion cannot raise the dimension
(`StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion`), and
`Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_le_zero_or_eq_one` turns `≤ 1` on
`X` into the dichotomy "`≤ 0` or `= 1`" on the component, which is the split the source makes
between its `x_j` and its `C_i`.

**Three invertibility spellings and two ampleness predicates meet here.** The degree theory is
stated over `AlgebraicGeometry.SheafOfModules.IsInvertible` and
`AlgebraicGeometry.Scheme.Modules.IsAmple`, while [Stacks, Tag 0B5V] is stated over
`Stacks.Ample.IsInvertibleModule` and `Stacks.Ample.IsAmple`;
`Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple` crosses the predicates with no hypothesis,
the invertibility classes agree by `inferInstance`, and
`RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom` and
`AlgebraicGeometry.Scheme.Modules.pullback g` are the same functor by `rfl`. Invertibility of a
pullback is not an instance in this development, so it is passed positionally wherever a
statement mentions it.

## References

* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01PU](https://stacks.math.columbia.edu/tag/01PU)
* [Stacks Project, Tag 0CYI](https://stacks.math.columbia.edu/tag/0CYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ComponentDegrees
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry

/-! ### Descent of ampleness along a finite closed cover -/

/-- **Ampleness descends along a finite family of closed immersions whose images cover `X`.** Let
`X` be proper over a field `k`, let `𝓛` be an invertible `𝒪_X`-module, and let `i j : C j ⟶ X`,
`j` ranging over a finite type, be closed immersions whose images cover `X`. If every restriction
`𝓛|_{C j}` is ample then `𝓛` is ample.

The morphism `g = ∐_j C j ⟶ X` induced by the family is finite ([Stacks, Tag 0CYI],
`AlgebraicGeometry.isFinite_sigmaDesc`, since a closed immersion is finite) and surjective
(`AlgebraicGeometry.Surjective.sigmaDesc_of_union_range_eq_univ`), so the converse direction of
[Stacks, Tag 0B5V] — `Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback`, which
carries no hypothesis beyond that tag's own — reduces ampleness of `𝓛` to ampleness of `g^*𝓛`.
The restriction of `g^*𝓛` to the `j`th summand is `𝓛|_{C j}` by
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `CategoryTheory.Limits.Sigma.ι_desc`, so
`AlgebraicGeometry.isAmple_sigma_of_forall_isAmple_pullback_sigmaι` finishes. -/
public theorem isAmple_of_forall_isAmple_pullback_of_iUnion_range_eq_univ
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {ι : Type u} [Finite ι] {C : ι → Scheme.{u}}
    (i : ∀ j, C j ⟶ X) [∀ j, IsClosedImmersion (i j)] (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hcover : (⋃ j, Set.range (i j).base) = Set.univ)
    (hample : ∀ j, @Scheme.Modules.IsAmple (C j) ((Scheme.Modules.pullback (i j)).obj L)
      (SheafOfModules.isInvertible_pullback (i j) L)) :
    Scheme.Modules.IsAmple X L := by
  have _ : Surjective (Sigma.desc i) := Surjective.sigmaDesc_of_union_range_eq_univ hcover
  have hiso (j : ι) : (Scheme.Modules.pullback (Sigma.ι C j)).obj
        ((Scheme.Modules.pullback (Sigma.desc i)).obj L)
      ≅ (Scheme.Modules.pullback (i j)).obj L :=
    (Scheme.Modules.pullbackComp (Sigma.ι C j) (Sigma.desc i)).app L ≪≫
      (Scheme.Modules.pullbackCongr (Sigma.ι_desc i j)).app L
  refine (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mpr
    (Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback (Sigma.desc i) L k f ?_)
  refine (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple (∐ C)
    ((Scheme.Modules.pullback (Sigma.desc i)).obj L)).mp ?_
  refine isAmple_sigma_of_forall_isAmple_pullback_sigmaι C _
    (SheafOfModules.isInvertible_pullback (Sigma.desc i) L) fun j => ?_
  exact @Scheme.Modules.isAmple_of_iso (C j) ((Scheme.Modules.pullback (i j)).obj L)
    ((Scheme.Modules.pullback (Sigma.ι C j)).obj ((Scheme.Modules.pullback (Sigma.desc i)).obj L))
    (SheafOfModules.isInvertible_pullback (i j) L)
    (SheafOfModules.isInvertible_pullback (Sigma.ι C j) _)
    (hiso j).symm (hample j)

/-! ### The irreducible components as a covering family -/

/-- **The irreducible component through a generic point, with its reduced induced closed
subscheme structure.** For a generic point of a one-dimensional component this is the same term as
`Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent`, whose index set
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne` is the subset of generic points whose
component has dimension one. -/
public abbrev genericComponent (X : Scheme.{u}) (ξ : genericPoints (X : Type u)) : Scheme.{u} :=
  (vanishingIdeal ⟨closure ({ξ.1} : Set X), isClosed_closure⟩).subscheme

/-- The closed immersion of the irreducible component through a generic point. -/
public abbrev genericComponentι (X : Scheme.{u}) (ξ : genericPoints (X : Type u)) :
    genericComponent X ξ ⟶ X :=
  (vanishingIdeal ⟨closure ({ξ.1} : Set X), isClosed_closure⟩).subschemeι

/-- **The image of a component is the component.** The range of the closed immersion cut out by
the vanishing ideal sheaf of a closed set is that closed set. -/
public theorem range_genericComponentι (X : Scheme.{u}) (ξ : genericPoints (X : Type u)) :
    Set.range (genericComponentι X ξ).base = closure ({ξ.1} : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- **The irreducible components cover `X`.** Every point lies in its own irreducible component,
and that component is the closure of a generic point. This is the covering hypothesis that
`AlgebraicGeometry.isAmple_of_forall_isAmple_pullback_of_iUnion_range_eq_univ` asks for. -/
public theorem iUnion_range_genericComponentι (X : Scheme.{u}) :
    (⋃ ξ : genericPoints (X : Type u), Set.range (genericComponentι X ξ).base) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
  refine ⟨genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [range_genericComponentι]
  exact (genericPoints.isGenericPoint_ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).ge mem_irreducibleComponent

/-- **A component with its reduced induced structure is integral.** It is reduced by construction
and irreducible because an irreducible component is. -/
public theorem isIntegral_genericComponent (X : Scheme.{u}) (ξ : genericPoints (X : Type u)) :
    IsIntegral (genericComponent X ξ) :=
  StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    ⟨closure ({ξ.1} : Set X), isClosed_closure⟩ (genericPoints.component ξ).2.1

/-- **The dimension of a component is the dimension of the closed set it sits on.** The closed
immersion is an embedding onto that set, and the topological Krull dimension is a homeomorphism
invariant. -/
public theorem topologicalKrullDim_genericComponent (X : Scheme.{u})
    (ξ : genericPoints (X : Type u)) :
    topologicalKrullDim (genericComponent X ξ) = topologicalKrullDim (closure ({ξ.1} : Set X)) :=
  ((IsPreimmersion.isEmbedding (genericComponentι X ξ)).toHomeomorph.isHomeomorph
      ).topologicalKrullDim_eq.trans
    (IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.setCongr (range_genericComponentι X ξ)).isHomeomorph)

/-! ### Ampleness on a zero-dimensional component -/

/-- **On a zero-dimensional irreducible component the restriction of any invertible module is
ample.** The component is integral, so irreducible and nonempty; of dimension zero it is a single
point (`StacksTag09NX.subsingleton_of_topologicalKrullDim_le_zero`), hence affine
(`StacksTag09NX.isAffine_of_subsingleton`); and an invertible module on a quasi-compact affine
scheme is ample ([Stacks, Tag 0B5P] on its affine hypothesis,
`AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible`).

These are the isolated closed points `x₁, …, x_r` of the proof of [Stacks, Tag 0B5Y], and this is
why the tag's degree condition ranges over the one-dimensional components only. **No
hypothesis.** -/
public theorem isAmple_pullback_genericComponent_of_topologicalKrullDim_le_zero
    (X : Scheme.{u}) [CompactSpace X] (ξ : genericPoints (X : Type u))
    (h0 : topologicalKrullDim (genericComponent X ξ) ≤ 0) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    @Scheme.Modules.IsAmple (genericComponent X ξ)
      ((Scheme.Modules.pullback (genericComponentι X ξ)).obj L)
      (SheafOfModules.isInvertible_pullback (genericComponentι X ξ) L) := by
  have : IsIntegral (genericComponent X ξ) := isIntegral_genericComponent X ξ
  have : CompactSpace (genericComponent X ξ) :=
    StacksTag09NX.compactSpace_of_isClosedImmersion (genericComponentι X ξ)
  have : Subsingleton (genericComponent X ξ) :=
    StacksTag09NX.subsingleton_of_topologicalKrullDim_le_zero _ h0
  have : IsAffine (genericComponent X ξ) := StacksTag09NX.isAffine_of_subsingleton _
  exact @Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _
    ((Scheme.Modules.pullback (genericComponentι X ξ)).obj L)
    (SheafOfModules.isInvertible_pullback (genericComponentι X ξ) L)

/-! ### Ampleness on a one-dimensional component -/

/-- **On a one-dimensional irreducible component, positivity of the degree makes the restriction
of an invertible module ample.** The component with its reduced induced structure is a proper
curve over `k`, so this is the converse direction of [Stacks, Tag 0B5X] read at the component:
`AlgebraicGeometry.isAmple_of_invertibleCurveDegree_pos_of_isCurve` of
`./DegreePositiveSection.lean`, which carries no hypothesis.

That the component is a proper curve over `k` is
`Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp` together with
`Stacks.AlgebraicGeometry.ComponentDegrees.isProper_reducedComponentι_comp`, both proved with no
hypothesis. **No hypothesis beyond the tag's own.** -/
public theorem isAmple_pullback_reducedComponent_of_invertibleCurveDegree_pos (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (ζ : genericPointsOne X)
    (hpos : 0 < @invertibleCurveDegree k _ (reducedComponent X ζ) (reducedComponentι X ζ ≫ f)
      (isProper_reducedComponentι_comp k f ζ)
      (topologicalKrullDim_reducedComponent_le X hdim ζ)
      ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj L)
      (SheafOfModules.isInvertible_pullback (reducedComponentι X ζ) L)) :
    @Scheme.Modules.IsAmple (reducedComponent X ζ)
      ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj L)
      (SheafOfModules.isInvertible_pullback (reducedComponentι X ζ) L) :=
  @isAmple_of_invertibleCurveDegree_pos_of_isCurve k _ (reducedComponent X ζ)
    (reducedComponentι X ζ ≫ f) (isCurve_reducedComponentι_comp k f ζ)
    (isProper_reducedComponentι_comp k f ζ)
    (topologicalKrullDim_reducedComponent_le X hdim ζ)
    ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj L)
    (SheafOfModules.isInvertible_pullback (reducedComponentι X ζ) L) hpos

/-! ### [Stacks, Tag 0B5Y] -/

/-- **[Stacks, Tag 0B5Y], both directions.** Let `k` be a field, let `X` be a scheme proper of
dimension at most one over `k` and let `𝓛` be an invertible `𝒪_X`-module. Then `𝓛` is ample if
and only if the degree of the restriction of `𝓛` to every one-dimensional irreducible component
of `X`, taken with its reduced induced closed subscheme structure, is positive.

The components of dimension one are the tag's `C₁, …, C_t`: they are indexed by their generic
points, `Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X`, the reduced induced
subscheme is `Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent`, and that it is a
proper curve over `k` is proved with no hypothesis.

The implication (1) ⟹ (2) is
`AlgebraicGeometry.invertibleCurveDegree_reducedComponent_pos_of_isAmple` of
`./ComponentPositivity.lean`, which has no hypothesis beyond the tag's own.

For the implication (2) ⟹ (1) the covering family of the source is formed: all the irreducible
components, which are finitely many because a scheme proper over a field is Noetherian. Each has
dimension zero or one. On a zero-dimensional one the restriction of `𝓛` is ample outright, and on
a one-dimensional one positivity of the degree makes it ample by the converse direction of
[Stacks, Tag 0B5X]; ampleness then descends to `X` along the finite surjection from the disjoint
union, by [Stacks, Tag 0B5V] together with
`AlgebraicGeometry.isAmple_sigma_of_forall_isAmple_pullback_sigmaι`.

**No hypothesis beyond the tag's own.** -/
@[stacks 0B5Y "both directions, at the tag's own indexing by the one-dimensional irreducible \
  components with their reduced induced closed subscheme structure"]
public theorem isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    Scheme.Modules.IsAmple X L ↔
      ∀ ζ : genericPointsOne X,
        0 < @invertibleCurveDegree k _ (reducedComponent X ζ) (reducedComponentι X ζ ≫ f)
          (isProper_reducedComponentι_comp k f ζ)
          (topologicalKrullDim_reducedComponent_le X hdim ζ)
          ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj L)
          (SheafOfModules.isInvertible_pullback (reducedComponentι X ζ) L) := by
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : Finite (genericPoints (X : Type u)) :=
    (genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  refine ⟨fun hL ζ => invertibleCurveDegree_reducedComponent_pos_of_isAmple k f hdim L hL ζ,
    fun hdeg => ?_⟩
  refine isAmple_of_forall_isAmple_pullback_of_iUnion_range_eq_univ k f
    (genericComponentι X) L (iUnion_range_genericComponentι X) fun ξ => ?_
  rcases topologicalKrullDim_le_zero_or_eq_one (genericComponentι X ξ) hdim with h0 | h1
  · exact isAmple_pullback_genericComponent_of_topologicalKrullDim_le_zero X ξ h0 L
  · have hmem : ξ.1 ∈ genericPointsOne X :=
      mem_genericPointsOne_iff.mpr ⟨ξ.2, (topologicalKrullDim_genericComponent X ξ) ▸ h1⟩
    exact isAmple_pullback_reducedComponent_of_invertibleCurveDegree_pos k f hdim L
      ⟨ξ.1, hmem⟩ (hdeg ⟨ξ.1, hmem⟩)

end AlgebraicGeometry

end
