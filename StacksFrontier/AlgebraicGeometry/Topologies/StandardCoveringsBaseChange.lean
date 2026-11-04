module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.StandardForm.Affine
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoverings

/-!
# Standard coverings are stable under base change

A standard `τ`-covering `{Tᵢ ⟶ V}` of an affine scheme `V`, in the sense of
`AlgebraicGeometry.IsStandardCovering`, stays a standard `τ`-covering after base change along an
arbitrary morphism `w : V' ⟶ V` of affine schemes: the family of first projections
`{V' ×_V Tᵢ ⟶ V'}` is again a standard `τ`-covering, for each of the five topologies.

## Main results

* `AlgebraicGeometry.IsStandardCovering.pullback_fst` is the statement uniform in the topology.
* `AlgebraicGeometry.IsStandardCovering.fppf_pullback_fst`,
  `AlgebraicGeometry.IsStandardCovering.syntomic_pullback_fst`,
  `AlgebraicGeometry.IsStandardCovering.smooth_pullback_fst`,
  `AlgebraicGeometry.IsStandardCovering.etale_pullback_fst` and
  `AlgebraicGeometry.IsStandardCovering.zariski_pullback_fst` are the five topologies read off
  one at a time.

## Implementation notes

The four clauses of `AlgebraicGeometry.IsStandardCovering` are discharged separately, and only
the last of them looks at the topology. Finiteness of the index type is unchanged. Affineness of
the new sources is Mathlib's instance for a fibre product with an affine factor and an affine
morphism. Joint surjectivity is `AlgebraicGeometry.iUnion_range_pullback_fst_eq_univ`: the range
of a first projection is the preimage of the range of the second morphism, so the ranges of the
base-changed family are the preimages of the original ranges and taking preimages commutes with
unions.

For the last clause, flatness, local finite presentation, quasi-compactness,
quasi-separatedness, étaleness and being an open immersion are all stable under base change in
Mathlib, and `AlgebraicGeometry.FinitePresentation` is the conjunction of three of those;
standard smoothness and standard syntomicity of a morphism of affine schemes are stable under
base change by `AlgebraicGeometry.isStandardSmooth_pullback_fst` and
`AlgebraicGeometry.isStandardSyntomic_pullback_fst`. The Zariski clause asks for more than a
property of the morphism — a member must be identified with a basic open of the target together
with its immersion — and that identification is transported in
`AlgebraicGeometry.exists_basicOpen_arrow_pullback_fst`: the base change of a basic open
immersion is an open immersion whose range is the preimage of the basic open, which is the basic
open of the pulled-back section, so the two open immersions are identified by
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`.

## References

* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- A jointly surjective family stays jointly surjective after base change: the range of a first
projection out of a fibre product is the preimage of the range of the morphism it is pulled back
along, and preimages commute with unions. -/
public lemma iUnion_range_pullback_fst_eq_univ {T V : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} (f : ∀ i, U i ⟶ T) (w : V ⟶ T)
    (h : (⋃ i, Set.range (f i)) = Set.univ) :
    (⋃ i, Set.range (pullback.fst w (f i))) = Set.univ := by
  simp only [Scheme.Pullback.range_fst]
  rw [← Set.preimage_iUnion, h, Set.preimage_univ]

/-- The base change of a basic open immersion is a basic open immersion: if `g : X ⟶ T` is the
immersion of a basic open `T.basicOpen a` read through an isomorphism, then the first projection
`V ×_T X ⟶ V` is the immersion of the basic open of `V` cut out by the pullback of `a`, again
read through an isomorphism. -/
public lemma exists_basicOpen_arrow_pullback_fst {T V X : Scheme.{u}} (a : Γ(T, ⊤))
    (e : X ≅ (T.basicOpen a).toScheme) (g : X ⟶ T) (hg : g = e.hom ≫ (T.basicOpen a).ι)
    (w : V ⟶ T) :
    ∃ b : Γ(V, ⊤), ∃ e' : pullback w g ≅ (V.basicOpen b).toScheme,
      pullback.fst w g = e'.hom ≫ (V.basicOpen b).ι := by
  have hgopen : IsOpenImmersion g := by
    rw [hg]; infer_instance
  have hfstopen : IsOpenImmersion (pullback.fst w g) :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) w g hgopen
  have hgr : Set.range g = (T.basicOpen a : Set T) := by
    rw [hg, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι]
  have hrange : Set.range (pullback.fst w g) =
      Set.range ((V.basicOpen (w.appTop a)).ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, hgr,
      ← Scheme.preimage_basicOpen_top w a]
    rfl
  exact ⟨w.appTop a, IsOpenImmersion.isoOfRangeEq _ _ hrange,
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange).symm⟩

/-- **Base change of a standard covering.** A standard `τ`-covering of an affine scheme stays a
standard `τ`-covering after base change along an arbitrary morphism of affine schemes, for each
of the five topologies. -/
public theorem IsStandardCovering.pullback_fst {τ : CoveringTopology} {T : Scheme.{u}} [IsAffine T]
    {I : Type v} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering τ U f)
    {V : Scheme.{u}} [IsAffine V] (w : V ⟶ T) :
    IsStandardCovering τ (fun i => pullback w (f i)) (fun i => pullback.fst w (f i)) := by
  have haffine : ∀ i, IsAffine (pullback w (f i)) := by
    intro i
    have := h.affine_source i
    have : IsAffineHom (f i) := isAffineHom_of_isAffine (f i)
    infer_instance
  refine ⟨h.finite_index, haffine,
    iUnion_range_pullback_fst_eq_univ f w h.jointly_surjective, ?_⟩
  intro i
  have hsrc := h.affine_source i
  have htgt := haffine i
  have hi := h.standard i
  have sq : IsPullback (pullback.snd w (f i)) (pullback.fst w (f i)) (f i) w :=
    (IsPullback.of_hasPullback w (f i)).flip
  cases τ with
  | fppf =>
    exact ⟨Flat.isStableUnderBaseChange.of_isPullback sq hi.1,
      locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback sq hi.2.1,
      quasiCompact_isStableUnderBaseChange.of_isPullback sq hi.2.2.1,
      quasiSeparated_isStableUnderBaseChange.of_isPullback sq hi.2.2.2⟩
  | syntomic => exact isStandardSyntomic_pullback_fst (f i) w hi
  | smooth => exact isStandardSmooth_pullback_fst (f i) w hi
  | etale => exact Etale.etale_isStableUnderBaseChange.of_isPullback sq hi
  | zariski =>
    obtain ⟨a, e, he⟩ := hi
    exact exists_basicOpen_arrow_pullback_fst a e (f i) he w

/-- Base change of a standard fppf covering. -/
public theorem IsStandardCovering.fppf_pullback_fst {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering .fppf U f)
    {V : Scheme.{u}} [IsAffine V] (w : V ⟶ T) :
    IsStandardCovering .fppf (fun i => pullback w (f i)) (fun i => pullback.fst w (f i)) :=
  h.pullback_fst w

/-- Base change of a standard syntomic covering. -/
public theorem IsStandardCovering.syntomic_pullback_fst {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering .syntomic U f)
    {V : Scheme.{u}} [IsAffine V] (w : V ⟶ T) :
    IsStandardCovering .syntomic (fun i => pullback w (f i)) (fun i => pullback.fst w (f i)) :=
  h.pullback_fst w

/-- Base change of a standard smooth covering. -/
public theorem IsStandardCovering.smooth_pullback_fst {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering .smooth U f)
    {V : Scheme.{u}} [IsAffine V] (w : V ⟶ T) :
    IsStandardCovering .smooth (fun i => pullback w (f i)) (fun i => pullback.fst w (f i)) :=
  h.pullback_fst w

/-- Base change of a standard étale covering. -/
public theorem IsStandardCovering.etale_pullback_fst {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering .etale U f)
    {V : Scheme.{u}} [IsAffine V] (w : V ⟶ T) :
    IsStandardCovering .etale (fun i => pullback w (f i)) (fun i => pullback.fst w (f i)) :=
  h.pullback_fst w

/-- Base change of a standard Zariski covering. -/
public theorem IsStandardCovering.zariski_pullback_fst {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering .zariski U f)
    {V : Scheme.{u}} [IsAffine V] (w : V ⟶ T) :
    IsStandardCovering .zariski (fun i => pullback w (f i)) (fun i => pullback.fst w (f i)) :=
  h.pullback_fst w

end AlgebraicGeometry
