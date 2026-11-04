module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ClauseTwoFibre
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionClassifyingRange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionFibreDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionProper

/-!
# The fibre of `π : T ⟶ 𝐏` over a closed class is `F(g) = X ∩ r_g⁻¹(Y)`

Let `X, Y` be closed subsets of `𝐏(V)` and let `T` be the incidence correspondence
`{(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` over `X × Y`. For a closed point `[g]` of the
parameter space whose domain of definition contains `X`, this file identifies the fibre of the
projection `π : T ⟶ 𝐏` over `[g]` with
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionFibre`, the subset
`F(g) = X ∩ r_g⁻¹(Y)` of `𝐏(V)`:

`dim (π⁻¹([g])) = dim F(g)`.

Together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le`
this is what turns a jump of the fibre dimension of `π` into the failure of clause (2) of Tag
0B1S, and conversely.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endPairSection`: the graph `x ↦ (x, r_g(x))` of
  `r_g`, as a morphism `U(g) ⟶ 𝐏(V) ×_k 𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endTripleSection`: the morphism
  `x ↦ (x, r_g(x), [g])` from `U(g)` to the triple product, for a *closed* class `[g]`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.eq_of_isClosed_singleton_of_tpProj_eq`: a closed
  point of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` is determined by its three projections. Over an algebraically
  closed field a closed point of a scheme of finite type is a `k`-point, and a `k`-point of a
  fibre product is its two components.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosedImmersion_endTripleSectionLift`: the
  morphism `x ↦ (x, r_g(x), [g])` is a closed immersion into the open subscheme of the triple
  product on which the first projection lands in `U(g)`. It is a section of the first
  projection there, and that projection is separated.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.image_endTripleSection_eq`: **its image is exactly
  the slice of the correspondence over `[g]`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_transitionVarietyToPar_eq`:
  **the fibre of `π` over `[g]` has the dimension of `F(g)`.**

## Implementation notes

**Why a scheme-theoretic graph is needed.** The slice of the correspondence over `[g]` is cut
out by the `2 × 2` minors of `(f ∘ g, f')`, and *not* by the set-theoretic condition
`r_g(x) = y`: for `g` the identity the latter holds at the generic point of `𝐏(V) ×_k 𝐏(V)`,
which is not on the diagonal. So the slice is compared with the graph of `r_g` as a closed
subscheme, and the comparison of the two *closed* subsets is checked at closed points, where the
minors can be evaluated
(`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`)
and where a point of the triple product is determined by its projections. The ambient space in
which the check is run is the open subscheme on which the first projection lands in `U(g)`,
which contains the slice because `X ⊆ U(g)`; it is a Jacobson space, being of finite type over
the ground field.

The route through
`AlgebraicGeometry.ProjectiveSpaceOfModule.parFibreSection` — identifying the fibre of the
projection to the parameter space with `𝐏(V) ×_k 𝐏(V)` and then cutting it down — is not taken:
it would still leave the graph of `r_g` to be identified inside that product, which is the whole
of the work, and it needs the injectivity of the first projection on that fibre as a separate
step.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-- **A topological embedding does not change the dimension of a subset.** The restriction of an
embedding to a subset is a continuous bijection onto the image which is again inducing, hence a
homeomorphism. -/
private theorem topologicalKrullDim_image_of_isEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {e : α → β} (he : Topology.IsEmbedding e) (S : Set α) :
    topologicalKrullDim ↥(e '' S) = topologicalKrullDim ↥S := by
  set r : ↥S → ↥(e '' S) := fun s => ⟨e s.1, ⟨s.1, s.2, rfl⟩⟩ with hr
  have hcont : Continuous r :=
    ((he.continuous.comp continuous_subtype_val)).subtype_mk _
  have hcomp : (Subtype.val : ↥(e '' S) → β) ∘ r = e ∘ (Subtype.val : ↥S → α) := rfl
  have hind : Topology.IsInducing r := by
    refine Topology.IsInducing.of_comp hcont continuous_subtype_val ?_
    rw [hcomp]
    exact he.isInducing.comp Topology.IsInducing.subtypeVal
  have hinj : Function.Injective r := fun a b h =>
    Subtype.ext (he.injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective r := by
    rintro ⟨b, x, hxS, rfl⟩
    exact ⟨⟨x, hxS⟩, rfl⟩
  exact (IsHomeomorph.topologicalKrullDim_eq r
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, hinj⟩, hsurj⟩)).symm

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [IsAlgClosed k]
  [FiniteDimensional k V] [Nontrivial V] [Nontrivial (ParameterModule k V)]

/-! ### Closed points of the triple product are determined by their three projections -/

/-- **A closed point of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` is determined by its three projections.** Over an
algebraically closed field the closed points of a scheme locally of finite type are its
`k`-points (`AlgebraicGeometry.pointEquivClosedPoint`), and a `k`-point of a fibre product is
its two components. -/
public theorem eq_of_isClosed_singleton_of_tpProj_eq {t t' : transitionProd k V}
    (ht : IsClosed ({t} : Set (transitionProd k V)))
    (ht' : IsClosed ({t'} : Set (transitionProd k V)))
    (hsrc : (tpSource k V).base t = (tpSource k V).base t')
    (htgt : (tpTarget k V).base t = (tpTarget k V).base t')
    (hpar : (tpPar k V).base t = (tpPar k V).base t') : t = t' := by
  set gZ := transitionProdToSpec k V with hgZ
  set a := IsLocalRing.closedPoint k with ha
  set p := pointOfClosedPoint gZ t ht with hpdef
  set p' := pointOfClosedPoint gZ t' ht' with hp'def
  have hp : p ≫ gZ = 𝟙 _ := pointOfClosedPoint_comp gZ t ht
  have hp' : p' ≫ gZ = 𝟙 _ := pointOfClosedPoint_comp gZ t' ht'
  have hpt : p.base a = t := pointOfClosedPoint_apply gZ t ht a
  have hpt' : p'.base a = t' := pointOfClosedPoint_apply gZ t' ht' a
  -- the three components are `k`-points of the three factors
  have hkey : ∀ (W : Type u) [AddCommGroup W] [Module k W]
      [FiniteDimensional k W] [Nontrivial W]
      (pr : transitionProd k V ⟶ projectiveSpaceOfModule k W)
      (_ : pr ≫ projectiveSpaceOfModuleToSpec k W = gZ),
      pr.base t = pr.base t' → p ≫ pr = p' ≫ pr := by
    intro W _ _ _ _ pr hpr heq
    have h1 : (p ≫ pr) ≫ projectiveSpaceOfModuleToSpec k W = 𝟙 _ := by
      rw [Category.assoc, hpr, hp]
    have h2 : (p' ≫ pr) ≫ projectiveSpaceOfModuleToSpec k W = 𝟙 _ := by
      rw [Category.assoc, hpr, hp']
    have hval : ((pointEquivClosedPoint (projectiveSpaceOfModuleToSpec k W))
          ⟨p ≫ pr, h1⟩ : closedPoints (projectiveSpaceOfModule k W)) =
        ((pointEquivClosedPoint (projectiveSpaceOfModuleToSpec k W))
          ⟨p' ≫ pr, h2⟩ : closedPoints (projectiveSpaceOfModule k W)) := by
      refine Subtype.ext ?_
      change (p ≫ pr).base a = (p' ≫ pr).base a
      change pr.base (p.base a) = pr.base (p'.base a)
      rw [hpt, hpt', heq]
    exact congrArg Subtype.val
      ((pointEquivClosedPoint (projectiveSpaceOfModuleToSpec k W)).injective hval)
  have hS := hkey V (tpSource k V) (tpSource_comp_toSpec k V) hsrc
  have hT := hkey V (tpTarget k V) (tpTarget_comp_toSpec k V) htgt
  have hP := hkey (ParameterModule k V) (tpPar k V) (tpPar_comp_toSpec k V) hpar
  have hFst : p ≫ tpFst k V = p' ≫ tpFst k V := by
    refine pullback.hom_ext ?_ ?_
    · change (p ≫ tpFst k V) ≫ pullback.fst _ _ = (p' ≫ tpFst k V) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, ← tpSource, hS]
    · change (p ≫ tpFst k V) ≫ pullback.snd _ _ = (p' ≫ tpFst k V) ≫ pullback.snd _ _
      rw [Category.assoc, Category.assoc, ← tpTarget, hT]
  have hpp : p = p' := pullback.hom_ext hFst hP
  rw [← hpt, ← hpt', hpp]

/-! ### The graph of `r_g` and the slice over a closed class -/

variable {k V}

/-- **The graph of `r_g`:** the morphism `x ↦ (x, r_g(x))` from the domain of definition `U(g)`
to `𝐏(V) ×_k 𝐏(V)`. Both components are morphisms over the ground field, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_comp_toSpec`. -/
public def endPairSection (g : V →ₗ[k] V) :
    (endDomain k V g).toScheme ⟶ prodTwo k V :=
  pullback.lift (endDomain k V g).ι (endProjection k V g)
    (endProjection_comp_toSpec k V g).symm

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] [Nontrivial (ParameterModule k V)] in
/-- The first component of the graph `endPairSection g` is the inclusion of `U(g)`. -/
@[reassoc]
public theorem endPairSection_comp_fst (g : V →ₗ[k] V) :
    endPairSection g ≫ pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) = (endDomain k V g).ι :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] [Nontrivial (ParameterModule k V)] in
/-- The second component of the graph `endPairSection g` is `r_g`. -/
@[reassoc]
public theorem endPairSection_comp_snd (g : V →ₗ[k] V) :
    endPairSection g ≫ pullback.snd (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) = endProjection k V g :=
  pullback.lift_snd _ _ _

variable (k V) in
/-- **The triple `x ↦ (x, r_g(x), [g])`**, for a closed point `q` of the parameter space: the
morphism from `U(g)` to `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` whose first two components are the graph of `r_g`
and whose last is constant at `q`. -/
public def endTripleSection (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    (endDomain k V g).toScheme ⟶ transitionProd k V :=
  pullback.lift (endPairSection g)
    ((endDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V ≫
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq)
    (by
      rw [prodTwoToSpec, ← Category.assoc, endPairSection_comp_fst, Category.assoc,
        Category.assoc, pointOfClosedPoint_comp, Category.comp_id])

omit [Nontrivial V] in
/-- The first two components of the triple section form the graph of `r_g`. -/
@[reassoc]
public theorem endTripleSection_comp_tpFst (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    endTripleSection k V g hq ≫ tpFst k V = endPairSection g :=
  pullback.lift_fst _ _ _

omit [Nontrivial V] in
/-- The last component of the triple section is constant at the closed point `q`. -/
@[reassoc]
public theorem endTripleSection_comp_tpPar (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    endTripleSection k V g hq ≫ tpPar k V =
      (endDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V ≫
        pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq :=
  pullback.lift_snd _ _ _

omit [Nontrivial V] in
/-- The first projection of the triple section is the inclusion of `U(g)`. -/
@[reassoc]
public theorem endTripleSection_comp_tpSource (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    endTripleSection k V g hq ≫ tpSource k V = (endDomain k V g).ι := by
  rw [tpSource, ← Category.assoc, endTripleSection_comp_tpFst, endPairSection_comp_fst]

omit [Nontrivial V] in
/-- The second projection of the triple section is `r_g`. -/
@[reassoc]
public theorem endTripleSection_comp_tpTarget (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    endTripleSection k V g hq ≫ tpTarget k V = endProjection k V g := by
  rw [tpTarget, ← Category.assoc, endTripleSection_comp_tpFst, endPairSection_comp_snd]

/-- Pointwise form of a commuting triangle of schemes: `g (f y) = h y` when `f ≫ g = h`. -/
private theorem base_apply_eq_of_comp_eq {A B C : Scheme} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C}
    (e : f ≫ g = h) (y : A) : g.base (f.base y) = h.base y := by
  rw [← e]
  rfl

omit [Nontrivial V] in
/-- Pointwise form of `endTripleSection_comp_tpSource`: the first projection of the triple at
`y` is `y` itself, read in `𝐏(V)`. -/
public theorem tpSource_endTripleSection (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (y : (endDomain k V g).toScheme) :
    (tpSource k V).base ((endTripleSection k V g hq).base y) =
      (endDomain k V g).ι.base y := by
  exact base_apply_eq_of_comp_eq (endTripleSection_comp_tpSource g hq) y

omit [Nontrivial V] in
/-- Pointwise form of `endTripleSection_comp_tpTarget`: the second projection of the triple at `y`
is `r_g(y)`. -/
public theorem tpTarget_endTripleSection (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (y : (endDomain k V g).toScheme) :
    (tpTarget k V).base ((endTripleSection k V g hq).base y) = endProjection k V g y := by
  exact base_apply_eq_of_comp_eq (endTripleSection_comp_tpTarget g hq) y

omit [Nontrivial V] in
/-- The triple section lands over `q`: the parameter of the triple at every point of `U(g)` is `q`.
-/
public theorem tpPar_endTripleSection (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (y : (endDomain k V g).toScheme) :
    (tpPar k V).base ((endTripleSection k V g hq).base y) = q := by
  rw [base_apply_eq_of_comp_eq (endTripleSection_comp_tpPar g hq) y]
  exact pointOfClosedPoint_apply (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq _

omit [Nontrivial V] in
/-- **The triple section is a topological embedding**, its composite with the first projection
being the inclusion of the open subscheme `U(g)`. -/
public theorem isEmbedding_endTripleSection (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    Topology.IsEmbedding (endTripleSection k V g hq).base := by
  refine Topology.IsEmbedding.of_comp (endTripleSection k V g hq).base.hom.continuous
    (tpSource k V).base.hom.continuous ?_
  have hfun : (tpSource k V).base ∘ (endTripleSection k V g hq).base =
      (endDomain k V g).ι.base := funext fun y => tpSource_endTripleSection g hq y
  rw [show ((tpSource k V).base : transitionProd k V → projectiveSpaceOfModule k V) ∘
    ((endTripleSection k V g hq).base : (endDomain k V g).toScheme → transitionProd k V) =
    (endDomain k V g).ι.base from hfun]
  exact (endDomain k V g).ι.isOpenEmbedding.isEmbedding

omit [Nontrivial V] in
/-- **The triple section lands over `U(g)`.** -/
public theorem range_endTripleSection_subset (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    Set.range (endTripleSection k V g hq).base ⊆
      ((tpSource k V ⁻¹ᵁ endDomain k V g : (transitionProd k V).Opens) :
        Set (transitionProd k V)) := by
  rintro _ ⟨y, rfl⟩
  change (tpSource k V).base ((endTripleSection k V g hq).base y) ∈ endDomain k V g
  rw [tpSource_endTripleSection g hq y]
  exact y.2

/-- The triple section, read as a morphism into the open subscheme of the triple product on
which the first projection lands in `U(g)`. -/
public def endTripleSectionLift (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    (endDomain k V g).toScheme ⟶
      (tpSource k V ⁻¹ᵁ endDomain k V g : (transitionProd k V).Opens).toScheme :=
  IsOpenImmersion.lift (tpSource k V ⁻¹ᵁ endDomain k V g : (transitionProd k V).Opens).ι
    (endTripleSection k V g hq)
    (by
      rw [Scheme.Opens.range_ι]
      exact range_endTripleSection_subset g hq)

omit [Nontrivial V] in
/-- The lift of the triple section, followed by the inclusion of the open subscheme, is the triple
section. -/
@[reassoc]
public theorem endTripleSectionLift_comp_ι (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    endTripleSectionLift g hq ≫
        (tpSource k V ⁻¹ᵁ endDomain k V g : (transitionProd k V).Opens).ι =
      endTripleSection k V g hq :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The triple section is a closed immersion into that open subscheme.** It is a section of
the restriction of the first projection, which is separated: the first projection is the proper
projection of the triple product to `𝐏(V) ×_k 𝐏(V)` followed by a base change of the separated
structure morphism of `𝐏(V)`. -/
public instance isClosedImmersion_endTripleSectionLift (g : V →ₗ[k] V)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    IsClosedImmersion (endTripleSectionLift g hq) := by
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have hsepV : IsSeparated (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have : IsSeparated (tpSource k V) := by
    have : IsProper (tpFst k V) := isProper_tpFst k V
    have : IsSeparated (tpFst k V) := inferInstance
    rw [tpSource]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have : IsSeparated (tpSource k V ∣_ endDomain k V g) := inferInstance
  have hsec : endTripleSectionLift g hq ≫ (tpSource k V ∣_ endDomain k V g) = 𝟙 _ := by
    rw [← cancel_mono (endDomain k V g).ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, endTripleSectionLift_comp_ι, endTripleSection_comp_tpSource,
      Category.id_comp]
  have : IsClosedImmersion
      (endTripleSectionLift g hq ≫ (tpSource k V ∣_ endDomain k V g)) := by
    rw [hsec]
    infer_instance
  exact IsClosedImmersion.of_comp (endTripleSectionLift g hq)
    (tpSource k V ∣_ endDomain k V g)

/-! ### The slice of the correspondence over a closed class -/

variable (k V) in
/-- **The slice of the correspondence over `X × Y` above a point `q` of the parameter space**,
read inside the triple product: the triples of the correspondence whose class is `q`. -/
public def transitionSlice (X Y : Set (projectiveSpaceOfModule k V))
    (q : projectiveSpaceOfModule k (ParameterModule k V)) : Set (transitionProd k V) :=
  transitionLocusOver k V X Y ∩ (tpPar k V).base ⁻¹' {q}

omit [Nontrivial (ParameterModule k V)] in
/-- The slice of the correspondence over a closed point `q` of the parameter space is closed. -/
public theorem isClosed_transitionSlice {X Y : Set (projectiveSpaceOfModule k V)}
    (hXc : IsClosed X) (hYc : IsClosed Y)
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    IsClosed (transitionSlice k V X Y q) :=
  (isClosed_transitionLocusOver k V X Y hXc hYc).inter
    (hq.preimage (tpPar k V).base.hom.continuous)

/-- **The triple at a point of `F(g)` lies on the slice over `[g]`.** The two projection
conditions are the definition of `F(g) = X ∩ r_g⁻¹(Y)`; that the triple lies on the transition
locus is checked at the closed points of `F(g)`, where the minors of `(f ∘ g, f')` are evaluated
by
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`
with `f' = f ∘ g`, and is transported to the whole of `F(g)` by
`Set.subset_of_isClosed_of_closedPoints_subset`. -/
public theorem endTripleSection_mem_transitionSlice
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    {g : V →ₗ[k] V} (hg : g ≠ 0)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (hqrep : q = linearFunctionalPoint k (ParameterModule k V)
      (Module.Dual.eval k (V →ₗ[k] V) g) (eval_ne_zero k V hg))
    {y : (endDomain k V g).toScheme}
    (hy : (endDomain k V g).ι.base y ∈ endProjectionFibre k V g X Y) :
    (endTripleSection k V g hq).base y ∈ transitionSlice k V X Y q := by
  have : JacobsonSpace (endDomain k V g).toScheme :=
    LocallyOfFiniteType.jacobsonSpace ((endDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V)
  have hFc : IsClosed (endProjectionFibre k V g X Y) :=
    isClosed_endProjectionFibre k V g hXc hYc hdom
  have hsub : (endDomain k V g).ι.base ⁻¹' endProjectionFibre k V g X Y ⊆
      (endTripleSection k V g hq).base ⁻¹' transitionLocus k V := by
    refine Set.subset_of_isClosed_of_closedPoints_subset
      (hFc.preimage (endDomain k V g).ι.base.hom.continuous)
      ((isClosed_transitionLocus k V).preimage
        (endTripleSection k V g hq).base.hom.continuous) (fun w hw hwc => ?_)
    have hwimg : IsClosed ({(endDomain k V g).ι.base w} : Set (projectiveSpaceOfModule k V)) :=
      isClosed_singleton_image_of_isClosed_singleton (endDomain k V g).ι
        ((endDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) rfl w hwc
    obtain ⟨f, hf, hfw⟩ := exists_eq_linearFunctionalPoint k V _ hwimg
    have hfdom : linearFunctionalPoint k V f hf ∈ endDomain k V g := by
      rw [← hfw]; exact w.2
    have hfg : f ∘ₗ g ≠ 0 := fun h =>
      (notMem_endDomain_linearFunctionalPoint_iff k V f hf g).mpr h hfdom
    have hsrc : (tpSource k V).base ((endTripleSection k V g hq).base w) =
        linearFunctionalPoint k V f hf := by
      rw [tpSource_endTripleSection, hfw]
    have htgt : (tpTarget k V).base ((endTripleSection k V g hq).base w) =
        linearFunctionalPoint k V (f ∘ₗ g) hfg := by
      rw [tpTarget_endTripleSection]
      exact endProjection_eq_linearFunctionalPoint k V g w f hf hfg hfw
    have hpar : (tpPar k V).base ((endTripleSection k V g hq).base w) =
        linearFunctionalPoint k (ParameterModule k V) (Module.Dual.eval k (V →ₗ[k] V) g)
          (eval_ne_zero k V hg) := by
      rw [tpPar_endTripleSection, hqrep]
    exact (mem_transitionLocus_iff_of_linearFunctionalPoint k V _ f hf hsrc (f ∘ₗ g) hfg htgt
      _ (eval_ne_zero k V hg) hpar g (fun _ => rfl)).mpr
      (Submodule.mem_span_singleton_self _)
  refine ⟨⟨⟨hsub hy, ?_⟩, ?_⟩, ?_⟩
  · rw [Set.mem_preimage, tpSource_endTripleSection]
    exact endProjectionFibre_subset k V g X Y hy
  · rw [Set.mem_preimage, tpTarget_endTripleSection]
    obtain ⟨z, hz, hzeq⟩ := hy.2
    have hzy : z = y := (endDomain k V g).ι.isOpenEmbedding.injective hzeq
    rw [← hzy]
    exact hz
  · rw [Set.mem_preimage, tpPar_endTripleSection]
    rfl

/-- **Every point of the slice over `[g]` is in the image of the triple section.** Both are
closed subsets of the open subscheme of the triple product on which the first projection lands
in `U(g)` — the slice because `X ⊆ U(g)`, the image because the triple section is a closed
immersion there — so the containment is checked at the closed points of that open subscheme,
where the minors identify the second projection as `r_g` of the first and where a point of the
triple product is determined by its three projections. -/
public theorem transitionSlice_subset_range_endTripleSection
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    {g : V →ₗ[k] V} (hg : g ≠ 0)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (hqrep : q = linearFunctionalPoint k (ParameterModule k V)
      (Module.Dual.eval k (V →ₗ[k] V) g) (eval_ne_zero k V hg)) :
    transitionSlice k V X Y q ⊆ Set.range (endTripleSection k V g hq).base := by
  set W : (transitionProd k V).Opens := tpSource k V ⁻¹ᵁ endDomain k V g with hWdef
  have : JacobsonSpace W.toScheme :=
    LocallyOfFiniteType.jacobsonSpace (W.ι ≫ transitionProdToSpec k V)
  have hAc : IsClosed (transitionSlice k V X Y q) := isClosed_transitionSlice hXc hYc hq
  have hAW : transitionSlice k V X Y q ⊆ (W : Set (transitionProd k V)) := fun t ht =>
    hdom ht.1.1.2
  have hstep : W.ι.base ⁻¹' transitionSlice k V X Y q ⊆
      Set.range (endTripleSectionLift g hq).base := by
    refine Set.subset_of_isClosed_of_closedPoints_subset
      (hAc.preimage W.ι.base.hom.continuous)
      (IsClosedImmersion.isClosedEmbedding (endTripleSectionLift g hq)).isClosed_range
      (fun w hw hwc => ?_)
    have htA : W.ι.base w ∈ transitionSlice k V X Y q := hw
    -- the point is closed in the whole triple product
    have htc : IsClosed ({W.ι.base w} : Set (transitionProd k V)) := by
      rw [← closure_eq_iff_isClosed]
      refine Set.Subset.antisymm (fun s hs => ?_) subset_closure
      have hsA : s ∈ transitionSlice k V X Y q :=
        hAc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr htA) hs
      obtain ⟨w', hw'⟩ : s ∈ Set.range W.ι.base := by
        rw [Scheme.Opens.range_ι]; exact hAW hsA
      have hw'cl : w' ∈ closure ({w} : Set W.toScheme) := by
        rw [W.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
          Set.image_singleton, Set.mem_preimage, hw']
        exact hs
      rw [hwc.closure_eq, Set.mem_singleton_iff] at hw'cl
      rw [← hw', hw'cl]
      rfl
    -- its three projections are closed points, hence cut out by functionals
    have hsrcc : IsClosed ({(tpSource k V).base (W.ι.base w)} :
        Set (projectiveSpaceOfModule k V)) :=
      isClosed_singleton_image_of_isClosed_singleton (tpSource k V) (transitionProdToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) (tpSource_comp_toSpec k V) _ htc
    have htgtc : IsClosed ({(tpTarget k V).base (W.ι.base w)} :
        Set (projectiveSpaceOfModule k V)) :=
      isClosed_singleton_image_of_isClosed_singleton (tpTarget k V) (transitionProdToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) (tpTarget_comp_toSpec k V) _ htc
    obtain ⟨f, hf, hfsrc⟩ := exists_eq_linearFunctionalPoint k V _ hsrcc
    obtain ⟨f', hf', hftgt⟩ := exists_eq_linearFunctionalPoint k V _ htgtc
    have hpar : (tpPar k V).base (W.ι.base w) =
        linearFunctionalPoint k (ParameterModule k V) (Module.Dual.eval k (V →ₗ[k] V) g)
          (eval_ne_zero k V hg) := by
      rw [Set.mem_singleton_iff.mp htA.2, hqrep]
    have hspan : f ∘ₗ g ∈ Submodule.span k {f'} :=
      (mem_transitionLocus_iff_of_linearFunctionalPoint k V _ f hf hfsrc f' hf' hftgt
        _ (eval_ne_zero k V hg) hpar g (fun _ => rfl)).mp htA.1.1.1
    -- the point of `U(g)` above the first projection
    obtain ⟨y, hyeq⟩ : ∃ y : (endDomain k V g).toScheme,
        (endDomain k V g).ι.base y = (tpSource k V).base (W.ι.base w) := by
      have hmem : (tpSource k V).base (W.ι.base w) ∈
          Set.range (endDomain k V g).ι.base := by
        rw [Scheme.Opens.range_ι]
        exact hdom htA.1.1.2
      exact hmem
    have hfg : f ∘ₗ g ≠ 0 := by
      refine fun h => (notMem_endDomain_linearFunctionalPoint_iff k V f hf g).mpr h ?_
      rw [← hfsrc, ← hyeq]
      exact y.2
    have hproj : endProjection k V g y = linearFunctionalPoint k V f' hf' :=
      (endProjection_eq_linearFunctionalPoint_iff k V g y hf hf' hfg
        (hyeq.trans hfsrc)).mpr hspan
    have hyc : IsClosed ({y} : Set (endDomain k V g).toScheme) := by
      have hpre : ({y} : Set (endDomain k V g).toScheme) =
          (endDomain k V g).ι.base ⁻¹' {(endDomain k V g).ι.base y} := by
        refine Set.ext fun z => ?_
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h => by rw [h], fun h => (endDomain k V g).ι.isOpenEmbedding.injective h⟩
      rw [hpre]
      refine IsClosed.preimage (endDomain k V g).ι.base.hom.continuous ?_
      rw [hyeq]
      exact hsrcc
    have hσc : IsClosed ({(endTripleSection k V g hq).base y} : Set (transitionProd k V)) := by
      refine isClosed_singleton_image_of_isClosed_singleton (endTripleSection k V g hq)
        ((endDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V)
        (transitionProdToSpec k V) ?_ y hyc
      rw [← tpSource_comp_toSpec, ← Category.assoc, endTripleSection_comp_tpSource]
    have heq : W.ι.base w = (endTripleSection k V g hq).base y :=
      eq_of_isClosed_singleton_of_tpProj_eq k V htc hσc
        (by rw [tpSource_endTripleSection, hyeq])
        (by rw [tpTarget_endTripleSection, hproj, ← hftgt])
        (by rw [tpPar_endTripleSection, Set.mem_singleton_iff.mp htA.2])
    refine ⟨y, ?_⟩
    refine W.ι.isOpenEmbedding.injective ?_
    rw [heq]
    exact base_apply_eq_of_comp_eq (endTripleSectionLift_comp_ι g hq) y
  intro t ht
  obtain ⟨w, hwt⟩ : t ∈ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hAW ht
  obtain ⟨y, hy⟩ := hstep (by rw [Set.mem_preimage, hwt]; exact ht)
  refine ⟨y, ?_⟩
  rw [← base_apply_eq_of_comp_eq (endTripleSectionLift_comp_ι g hq) y, hy, hwt]

/-- **The image of the triple section is exactly the slice of the correspondence over `[g]`.** -/
public theorem image_endTripleSection_eq
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    {g : V →ₗ[k] V} (hg : g ≠ 0)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (hqrep : q = linearFunctionalPoint k (ParameterModule k V)
      (Module.Dual.eval k (V →ₗ[k] V) g) (eval_ne_zero k V hg)) :
    (endTripleSection k V g hq).base ''
        ((endDomain k V g).ι.base ⁻¹' endProjectionFibre k V g X Y) =
      transitionSlice k V X Y q := by
  refine Set.Subset.antisymm ?_ fun t ht => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact endTripleSection_mem_transitionSlice hXc hYc hg hdom hq hqrep hy
  · obtain ⟨y, rfl⟩ :=
      transitionSlice_subset_range_endTripleSection hXc hYc hg hdom hq hqrep ht
    refine ⟨y, ⟨?_, ⟨y, ?_, rfl⟩⟩, rfl⟩
    · have h := ht.1.1.2
      rw [Set.mem_preimage, tpSource_endTripleSection] at h
      exact h
    · have h := ht.1.2
      rw [Set.mem_preimage, tpTarget_endTripleSection] at h
      exact h

/-- **The fibre of `π : T ⟶ 𝐏` over a closed class `[g]` has the dimension of
`F(g) = X ∩ r_g⁻¹(Y)`.** The fibre is homeomorphic to the set-theoretic preimage, which the
closed immersion of the correspondence carries onto the slice of
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionLocusOver` over `[g]`; that slice is the
image of `F(g)` under the triple section `x ↦ (x, r_g(x), [g])`, an embedding.

This is the identification clause (2) of Tag 0B1S needs: together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le`
it says that the class `[g]` is bad exactly when the fibre of `π` over it has dimension greater
than `dim X + dim Y - dim 𝐏(V)`. -/
public theorem topologicalKrullDim_fiber_transitionVarietyToPar_eq
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    {g : V →ₗ[k] V} (hg : g ≠ 0)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (hqrep : q = linearFunctionalPoint k (ParameterModule k V)
      (Module.Dual.eval k (V →ₗ[k] V) g) (eval_ne_zero k V hg)) :
    topologicalKrullDim ((transitionVarietyToPar k V
        (prodOfClosedToProdTwo k V X Y hXc hYc)).fiber q) =
      topologicalKrullDim ↥(endProjectionFibre k V g X Y) := by
  have : IsClosedImmersion (transitionVarietyToSubscheme k V
      (prodOfClosedToProdTwo k V X Y hXc hYc)) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst (transitionProj k V)
      (prodOfClosedToProdTwo k V X Y hXc hYc)))
  set π := transitionVarietyToPar k V (prodOfClosedToProdTwo k V X Y hXc hYc) with hπ
  set i := transitionVarietyι k V X Y hXc hYc with hi
  have himg : i.base '' (π.base ⁻¹' {q}) = transitionSlice k V X Y q := by
    rw [transitionSlice, ← range_transitionVarietyι k V X Y hXc hYc]
    refine Set.ext fun t => ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, rfl⟩, hz⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      exact ⟨z, hz, rfl⟩
  have hFsub : endProjectionFibre k V g X Y ⊆ Set.range (endDomain k V g).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact (endProjectionFibre_subset k V g X Y).trans hdom
  calc topologicalKrullDim (π.fiber q)
      = topologicalKrullDim ↥(π.base ⁻¹' {q}) :=
        IsHomeomorph.topologicalKrullDim_eq _ (π.fiberHomeo q).isHomeomorph
    _ = topologicalKrullDim ↥(i.base '' (π.base ⁻¹' {q})) :=
        (topologicalKrullDim_image_of_isEmbedding
          i.isClosedEmbedding.isEmbedding (π.base ⁻¹' {q})).symm
    _ = topologicalKrullDim ↥(transitionSlice k V X Y q) := by rw [himg]
    _ = topologicalKrullDim ↥((endDomain k V g).ι.base ⁻¹'
          endProjectionFibre k V g X Y) := by
        rw [← image_endTripleSection_eq hXc hYc hg hdom hq hqrep]
        exact topologicalKrullDim_image_of_isEmbedding (isEmbedding_endTripleSection g hq) _
    _ = topologicalKrullDim ↥(endProjectionFibre k V g X Y) := by
        rw [← topologicalKrullDim_image_of_isEmbedding
          (endDomain k V g).ι.isOpenEmbedding.isEmbedding
          ((endDomain k V g).ι.base ⁻¹' endProjectionFibre k V g X Y),
          Set.image_preimage_eq_of_subset hFsub]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
