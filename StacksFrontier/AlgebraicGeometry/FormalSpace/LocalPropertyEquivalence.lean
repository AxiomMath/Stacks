module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability

/-!
# The equivalence of the three local conditions on a morphism of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S` and let `P` be a local property of continuous homomorphisms of
topological rings of a class `C`. **Stacks 0ANG** says that the following are equivalent:

1. for every commutative diagram with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   morphism of `C` with property `P`;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM such that each `Uᵢ ⟶ Vⱼ` corresponds to a morphism
   of `C` with property `P`;
3. there are a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` where `Vᵢ` is an affine formal algebraic space, `Vᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Uᵢ ⟶ Vᵢ` corresponds to a morphism of `C` with property `P`.

The three conditions are
`AlgebraicGeometry.FormalSpace.HasPropertyOnEveryAffineEtaleDiagram`,
`AlgebraicGeometry.FormalSpace.HasPropertyAfterTargetCover` and
`AlgebraicGeometry.FormalSpace.HasPropertyAfterSourceCover`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ColimitOfThickeningsIsFormalAlgebraicSpace`: **Stacks 0AIU**,
  in the shape in which Stacks 0AJH and Stacks 0AJI consume it.

## Main results

* `isFormalAlgebraicSpace_pullback_of_representable_of_isAffineFormal` and
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart`: **Stacks 0AJ3** for the
  fibre products this proof forms, with no instance of the set-theoretic condition of
  **Stacks 0AIS** assumed.
* `AlgebraicGeometry.FormalSpace.hasEtaleRefinementOfSourceCover`:
  the covering refinement constructed in the proof of **Stacks 0ANG**, previously the
  hypothesis `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover`.
* `hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_colimitOfThickenings`:
  **Stacks 0ANG**, the implication from condition (1) to condition (2), standing on Stacks 0AIU
  alone. Against
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal`,
  the two instances of the set-theoretic condition of **Stacks 0AIS** that that result assumes
  as `hset` and `hstageset` are here proved rather than assumed.
* `AlgebraicGeometry.FormalSpace.hasProperty_tfae`: the equivalence of the three conditions, at
  the source's hypotheses on `f` and on `P` but with two further inputs, `hchart` and `hcolim`.
  It is not registered. **Stacks 0ANG** itself, with neither input, is
  `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed` in
  `StacksFrontier/AlgebraicGeometry/FormalSpace/LocalPropertyCountablyIndexed.lean`: there `hcolim`
  is replaced by the étale case of Stacks 0AJH, which is all the fibre products of the argument
  need (`StacksFrontier/AlgebraicGeometry/FormalSpace/RepresentableEtaleSource.lean`), and `hchart`
  by the class-generic implication (3) ⟹ (1) of
  `StacksFrontier/AlgebraicGeometry/FormalSpace/LocalPropertySourceCover.lean`, which rests on the
  essential surjectivity of Stacks 0AN8,
  `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`. The section "What is still
  assumed" below records the two inputs of `hasProperty_tfae`.

## Implementation notes

The implication (1) ⟹ (2) is
`AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`, whose
hypothesis that the fibre products of condition (2) be formal algebraic spaces is discharged by
this library's **Stacks 0AJ3**,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable`, through
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart`, which supplies the two
instances of the set-theoretic condition of Stacks 0AIS that Stacks 0AJ3 asks for; the
implication (2) ⟹ (3) is
`AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_afterTargetCover`, which holds for
any class and property; the implication (3) ⟹ (1) is
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover`, whose
geometric input `HasEtaleRefinementOfSourceCover` is proved here.

That refinement is the heart of the source's proof, and it is built here along a route slightly
shorter than the source's. Given a covering `{Uᵢ ⟶ X}` with factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` and a
diagram `U₀ ⟶ V₀` over `f` as in condition (1), form

* `Qᵢ = Vᵢ ×_Y V₀`, a formal algebraic space because `Vᵢ ⟶ Y` is representable by algebraic
  spaces, so that `Qᵢ` lies representably over the *affine* formal algebraic space `V₀` and
  Stacks 0AJH applies; choose a covering `{Zᵢⱼ ⟶ Qᵢ}`;
* `Nᵢ = Uᵢ ×_X U₀`, a formal algebraic space for the same reason, together with the morphism
  `gᵢ : Nᵢ ⟶ Qᵢ` induced by `Uᵢ ⟶ Vᵢ` and `U₀ ⟶ V₀`, which exist over `Y` because the two
  morphisms `Nᵢ ⟶ X` agree; choose a covering `{Mᵢₗ ⟶ Nᵢ}`;
* `Tᵢⱼₗ = Zᵢⱼ ×_{Qᵢ} Mᵢₗ`, again a formal algebraic space, and choose a covering
  `{Wᵢⱼₗₖ ⟶ Tᵢⱼₗ}`.

Taking the fibre product over `Qᵢ = Vᵢ ×_Y V₀` rather than over `Vᵢ`, as the source does, is
what makes *both* squares of the conclusion commute at once: the two composites
`Wᵢⱼₗₖ ⟶ Vᵢ` and the two composites `Wᵢⱼₗₖ ⟶ V₀` agree by the defining property of `Tᵢⱼₗ`
together with `gᵢ ≫ pr₁ = pr₁ ≫ (Uᵢ ⟶ Vᵢ)` and `gᵢ ≫ pr₂ = pr₂ ≫ (U₀ ⟶ V₀)`.

Covering `Nᵢ` before forming the third fibre product, rather than taking `Zᵢⱼ ×_{Qᵢ} Nᵢ`
directly, is what keeps the set-theoretic condition of Stacks 0AIS out of the hypotheses: every
fibre product formed above then has *two affine formal legs*, which is what
`satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts` asks for, over a
base whose relative products of representables are representable — the representability
assertion of **Stacks 0AIP**, carried for an arbitrary formal algebraic space by
`AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`.

The family `{Wᵢⱼₗₖ ⟶ U₀}` is jointly surjective because each of its four stages is, the outer
ones by base change; the stages are composed by
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_sigma_comp`. A finite subfamily still
covers because the reduction of the affine formal algebraic space `U₀` is quasi-compact, which
is the sharp form of the implication (1) ⟹ (2) of **Stacks 0AJ9**,
`AlgebraicGeometry.FormalSpace.exists_finite_subcover_of_isAffineFormalAlgebraicSpace`: the
subfamily it returns is a subfamily of the covering supplied, so the factorizations
`Wᵢⱼₗₖ ⟶ Zᵢⱼ ⟶ V₀` attached to the covering survive the shrinking.

## The two inputs of `hasProperty_tfae`

`AlgebraicGeometry.FormalSpace.hasProperty_tfae` states the equivalence at the source's
hypotheses on `f` and `P` and two further inputs. Both are now discharged in
`AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed`, which is the
registered form of **Stacks 0ANG**:

* `hcolim`, of the shape
  `AlgebraicGeometry.FormalSpace.ColimitOfThickeningsIsFormalAlgebraicSpace` (Stacks 0AIU), is
  used here only for fibre products one of whose legs is representable étale. For those the
  étale case of Stacks 0AJH, `AlgebraicGeometry.FormalSpace.representableEtaleOverAffineIsFormal`,
  suffices; see `StacksFrontier/AlgebraicGeometry/FormalSpace/RepresentableEtaleSource.lean`.
* `hchart`, the translation of the three axioms of `TopologicalRing.PropertyIsLocal` into the
  geometric axioms `ChartPropertyAscendsAlongAffineEtale` and
  `ChartPropertyDescendsAlongFiniteAffineEtaleCover`, is replaced by the class-generic
  implication (3) ⟹ (1) of
  `StacksFrontier/AlgebraicGeometry/FormalSpace/LocalPropertySourceCover.lean`, which works with
  charts of the class rather than with all affine formal algebraic spaces. It uses the invariance
  of `P` under isomorphism of source and target, which is part of the hypothesis of
  Situation 0CBA, and the essential surjectivity of Stacks 0AN8,
  `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 0AIU as a proposition -/

/-- **Stacks 0AIU**, corrected, in the shape in which Stacks 0AJH and Stacks 0AJI consume it: a sheaf
isomorphic to the colimit of a directed system of algebraic spaces whose transition morphisms
are representable thickenings is a formal algebraic space, provided it satisfies the
set-theoretic condition of Stacks 0AIS. -/
abbrev ColimitOfThickeningsIsFormalAlgebraicSpace : Prop :=
  ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS),
    (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
    (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
    ∀ Z : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS Z →
      Nonempty (Z ≅ colimit E) → IsFormalAlgebraicSpace B S hS Z

/-! ### Representable étale morphisms and base change -/

/-! ### Stacks 0AJ3 for the fibre products the proof of Stacks 0ANG forms -/

/-- **Stacks 0AJ3** for a fibre product of two *affine* formal algebraic spaces over a formal
algebraic space, one of whose legs is representable by algebraic spaces: no instance of the
set-theoretic condition of Stacks 0AIS has to be assumed.

The projection to the source of the other leg is a base change of the representable leg, so the
fibre product lies over an *affine* formal algebraic space representably and Stacks 0AJH
applies. Its set-theoretic condition is
`satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts`, whose hypothesis
that the base have representable relative products is the representability assertion of
**Stacks 0AIP**, carried here for an arbitrary formal algebraic space by
`AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`. -/
theorem isFormalAlgebraicSpace_pullback_of_representable_of_isAffineFormal
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS)
    {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hv : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS v.hom) :
    IsFormalAlgebraicSpace B S hS (pullback v f) := by
  have hsnd : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.snd v f).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
      (pullback.fst v f).hom (pullback.snd v f).hom v.hom f.hom
      ((IsPullback.of_hasPullback v f).map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hv
  exact isFormalAlgebraicSpace_of_representable_over_affineFormal B S hS (pullback.snd v f) hX
    hsnd (satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS v f
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hV)
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hX)
      hV.1 hX.1) hcolim

/-- **Stacks 0AJ3** for the fibre product of a morphism of formal algebraic spaces with an
affine formal chart of its target — the fibre product `V ×_Y X` of condition (2) of
**Stacks 0ANG** — with no instance of the set-theoretic condition of Stacks 0AIS assumed.

Both instances that Stacks 0AJ3 asks for are supplied by
`satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts`, whose three
hypotheses of representable relative products are the representability assertion of
**Stacks 0AIP** for an arbitrary formal algebraic space,
`AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`: the
first instance is the condition on `V ×_Y X` itself, and the second is the condition on
`W ×_X (V ×_Y X)` for a chart `W` of `X`, which is the fibre product `W ×_Y V` over `Y` and so
is reached through the comparison isomorphism of the two pasted cartesian squares. -/
theorem isFormalAlgebraicSpace_pullback_chart
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS)
    {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (V : FppfSheaf B S hS) (v : V ⟶ Y) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hv : IsRepresentableEtale B S hS v) :
    IsFormalAlgebraicSpace B S hS (pullback v f) := by
  have hYrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY
  have hVrep := hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hV
  refine isFormalAlgebraicSpace_pullback_of_representable B S hS v f hX hv.1
    (satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS v f hYrep
      hVrep (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX) hV.1 hX.1)
    (fun W w hW _ ↦ ?_) hcolim
  refine satisfiesSetTheoreticCondition_of_iso B S hS
    ((IsPullback.of_hasPullback w (pullback.snd v f)).paste_vert
      (IsPullback.of_hasPullback v f).flip).isoPullback.symm ?_
  exact satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS (w ≫ f)
    v hYrep (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hW) hVrep
    hW.1 hV.1

/-! ### The covering refinement in the proof of Stacks 0ANG -/

/-- The refinement of a covering constructed in the proof of **Stacks 0ANG**, before the finite
subfamily is extracted.

Given a covering `{Uᵢ ⟶ X}` of the source with factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` through
representable étale charts of the target, and a commutative square `U₀ ⟶ V₀` over `f` with
`U₀`, `V₀` affine and representable étale over `X`, `Y`, the charts of the fibre products
`Zᵢⱼ ×_{Vᵢ ×_Y V₀} (Uᵢ ×_X U₀)`, for `{Zᵢⱼ ⟶ Vᵢ ×_Y V₀}` a covering, form a covering of `U₀`
refining `{Uᵢ ⟶ X}` and mapping to the charts `Zᵢⱼ` of `V₀`. -/
theorem exists_affineEtaleCover_refining_sourceCover
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hXformal : IsFormalAlgebraicSpace B S hS X) (hYformal : IsFormalAlgebraicSpace B S hS Y)
    {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
    (t : ∀ i, U i ⟶ V i) (hUcover : IsAffineEtaleCover B S hS U u)
    (hVaffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (V i))
    (hVetale : ∀ i, IsRepresentableEtale B S hS (v i))
    (hVsquare : ∀ i, u i ≫ f = t i ≫ v i)
    (U₀ V₀ : FppfSheaf B S hS) (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    (hV₀ : IsAffineFormalAlgebraicSpace B S hS V₀)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsquare : a ≫ f = τ ≫ b) :
    ∃ (σ : Type (u + 1)) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ ∀ s, p s ≫ τ = m s ≫ c s := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hUaffine, hUetale, hUsurj⟩ := hUcover
  -- `Qᵢ = Vᵢ ×_Y V₀` and `Nᵢ = Uᵢ ×_X U₀` are formal algebraic spaces
  have hQ : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (v i) b) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_representable_of_isAffineFormal B S hS hcolim (v i) b
      hYformal (hVaffine i) hV₀ (hVetale i).1
  have hN : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (u i) a) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_representable_of_isAffineFormal B S hS hcolim (u i) a
      hXformal (hUaffine i) hU₀ (hUetale i).1
  -- the morphism `gᵢ : Nᵢ ⟶ Qᵢ` induced by `Uᵢ ⟶ Vᵢ` and `U₀ ⟶ V₀`
  obtain ⟨g, hgfst, hgsnd⟩ : ∃ g : ∀ i, pullback (u i) a ⟶ pullback (v i) b,
      (∀ i, g i ≫ pullback.fst (v i) b = pullback.fst (u i) a ≫ t i) ∧
        ∀ i, g i ≫ pullback.snd (v i) b = pullback.snd (u i) a ≫ τ := by
    refine ⟨fun i ↦ pullback.lift (pullback.fst (u i) a ≫ t i) (pullback.snd (u i) a ≫ τ) ?_,
      fun i ↦ pullback.lift_fst _ _ _, fun i ↦ pullback.lift_snd _ _ _⟩
    rw [Category.assoc, Category.assoc, ← hVsquare i, ← hsquare, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  -- coverings `{Zᵢⱼ ⟶ Qᵢ}` of the fibre products `Qᵢ` and `{Mᵢₗ ⟶ Nᵢ}` of the `Nᵢ`
  choose J Z z hZaffine hZetale hZsurj using fun i ↦ (hQ i).2
  choose L M ml hMaffine hMetale hMsurj using fun i ↦ (hN i).2
  -- `Tᵢⱼₗ = Zᵢⱼ ×_{Qᵢ} Mᵢₗ` is a formal algebraic space, both its legs being affine
  have hT : ∀ i (l : L i) (j : J i),
      IsFormalAlgebraicSpace B S hS (pullback (z i j) (ml i l ≫ g i)) := fun i l j ↦
    isFormalAlgebraicSpace_pullback_of_representable_of_isAffineFormal B S hS hcolim (z i j)
      (ml i l ≫ g i) (hQ i) (hZaffine i j) (hMaffine i l) (hZetale i j).1
  -- coverings `{Wᵢⱼₗₖ ⟶ Tᵢⱼₗ}`
  choose K W w hWaffine hWetale hWsurj using fun (i : I) (l : L i) (j : J i) ↦ (hT i l j).2
  -- the composite `Wᵢⱼₗₖ ⟶ Tᵢⱼₗ ⟶ Mᵢₗ` is representable étale
  have hWM : ∀ i l j k, IsRepresentableEtale B S hS
      ((w i l j k ≫ pullback.snd (z i j) (ml i l ≫ g i)) ≫ ml i l) := fun i l j k ↦
    IsRepresentableEtale.comp B S hS (IsRepresentableEtale.comp B S hS (hWetale i l j k)
      (isRepresentableEtale_pullback_snd B S hS (z i j) (ml i l ≫ g i) (hZetale i j)))
      (hMetale i l)
  -- the composite family `{Wᵢⱼₗₖ ⟶ U₀}` is an affine étale covering of `U₀`
  have hcover : IsAffineEtaleCover B S hS
      (fun s : (i : I) × ((l : L i) × ((j : J i) × K i l j)) ↦
        W s.1 s.2.1 s.2.2.1 s.2.2.2)
      (fun s ↦ ((w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
          pullback.snd (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1)) ≫ ml s.1 s.2.1) ≫
        pullback.snd (u s.1) a) := by
    refine ⟨fun s ↦ hWaffine s.1 s.2.1 s.2.2.1 s.2.2.2, fun s ↦ IsRepresentableEtale.comp B S hS
      (hWM s.1 s.2.1 s.2.2.1 s.2.2.2)
      (isRepresentableEtale_pullback_snd B S hS (u s.1) a (hUetale s.1)), ?_⟩
    refine Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (fun i ↦ pullback.snd (u i) a)
      (fun i (p : (l : L i) × ((j : J i) × K i l j)) ↦
        (w i p.1 p.2.1 p.2.2 ≫ pullback.snd (z i p.2.1) (ml i p.1 ≫ g i)) ≫ ml i p.1)
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd a u hUsurj) fun i ↦ ?_
    refine Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (ml i)
      (fun l (p : (j : J i) × K i l j) ↦
        w i l p.1 p.2 ≫ pullback.snd (z i p.1) (ml i l ≫ g i)) (hMsurj i) fun l ↦ ?_
    exact Sheaf.isLocallySurjective_sigmaDesc_sigma_comp
      (fun j ↦ pullback.snd (z i j) (ml i l ≫ g i)) (w i l)
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (ml i l ≫ g i) (z i) (hZsurj i))
      (hWsurj i l)
  refine ⟨(i : I) × ((l : L i) × ((j : J i) × K i l j)), fun s ↦ s.1,
    fun s ↦ W s.1 s.2.1 s.2.2.1 s.2.2.2, fun s ↦ Z s.1 s.2.2.1,
    fun s ↦ ((w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
        pullback.snd (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1)) ≫ ml s.1 s.2.1) ≫
      pullback.snd (u s.1) a,
    fun s ↦ ((w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
        pullback.snd (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1)) ≫ ml s.1 s.2.1) ≫
      pullback.fst (u s.1) a,
    fun s ↦ w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
      pullback.fst (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1),
    fun s ↦ z s.1 s.2.2.1 ≫ pullback.fst (v s.1) b,
    fun s ↦ z s.1 s.2.2.1 ≫ pullback.snd (v s.1) b, hcover,
    fun s ↦ hZaffine s.1 s.2.2.1, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩
  · exact IsRepresentableEtale.comp B S hS (hWM s.1 s.2.1 s.2.2.1 s.2.2.2)
      (isRepresentableEtale_pullback_fst B S hS (u s.1) a ha)
  · exact IsRepresentableEtale.comp B S hS (hZetale s.1 s.2.2.1)
      (isRepresentableEtale_pullback_fst B S hS (v s.1) b hb)
  · exact IsRepresentableEtale.comp B S hS (hZetale s.1 s.2.2.1)
      (isRepresentableEtale_pullback_snd B S hS (v s.1) b (hVetale s.1))
  · simp only [Category.assoc, ← hgfst s.1, pullback.condition_assoc]
  · simp only [Category.assoc, ← hgsnd s.1, pullback.condition_assoc]

/-- The refinement of a covering constructed in the proof of **Stacks 0ANG**, previously the
hypothesis `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover`: the covering of
`U₀` produced by
`AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_refining_sourceCover`, cut down to a
finite subfamily which still covers `U₀` by
`AlgebraicGeometry.FormalSpace.exists_finite_subcover_of_isAffineFormalAlgebraicSpace`, the
implication (1) ⟹ (2) of **Stacks 0AJ9** for an affine formal algebraic space. The subfamily
returned there is a subfamily of the covering supplied, so the whole datum attached to it —
the charts `Zᵢⱼ` of `V₀` and the two commuting squares — is carried along by reindexing. -/
theorem hasEtaleRefinementOfSourceCover
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hXformal : IsFormalAlgebraicSpace B S hS X) (hYformal : IsFormalAlgebraicSpace B S hS Y) :
    HasEtaleRefinementOfSourceCover B S hS f := by
  intro I U V u v t hUcover hVaffine hVetale hVsquare U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨σ', k, W, Z, p, q, m, r, c, hWcover, hZaff, hq, hr, hc, hsq₁, hsq₂⟩ :=
    exists_affineEtaleCover_refining_sourceCover B S hS hcolim f hXformal hYformal U V u v t
      hUcover hVaffine hVetale hVsquare U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨σ, hσ, κ, hsub⟩ :=
    exists_finite_subcover_of_isAffineFormalAlgebraicSpace B S hS U₀ W p hU₀ hWcover
  exact ⟨σ, hσ, fun s ↦ k (κ s), fun s ↦ W (κ s), fun s ↦ Z (κ s), fun s ↦ p (κ s),
    fun s ↦ q (κ s), fun s ↦ m (κ s), fun s ↦ r (κ s), fun s ↦ c (κ s), hsub,
    fun s ↦ hZaff (κ s), fun s ↦ hq (κ s), fun s ↦ hr (κ s), fun s ↦ hc (κ s),
    fun s ↦ hsq₁ (κ s), fun s ↦ hsq₂ (κ s)⟩

/-! ### Stacks 0ANG -/

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Stacks 0ANG, condition (1) implies condition (2)**, with no instance of the set-theoretic
condition of **Stacks 0AIS** assumed, so that the only standing input is **Stacks 0AIU**.

The hypothesis `hpb` of
`AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram` — that the
fibre products `V ×_Y X` of condition (2) are formal algebraic spaces, which is **Stacks 0AJ3** —
is discharged by `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart`. Against
`AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal`,
which takes Stacks 0AJ3 from
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable` and so inherits
its two instances of the set-theoretic condition of Stacks 0AIS as the hypotheses `hset` and
`hstageset`, those two instances are here *proved*, by
`satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts`: every fibre
product in question has two affine formal legs over a formal algebraic space, and the
representable relative products that lemma asks of the three corners are the representability
assertion of **Stacks 0AIP**,
`AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`. -/
theorem hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_colimitOfThickenings
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f) :
    HasPropertyAfterTargetCover B S hS C P f :=
  hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS C P f hY
    (isFormalAlgebraicSpace_pullback_chart B S hS hcolim hX hY) hf

/-- The equivalence asserted by **Stacks 0ANG**, at the source's hypotheses and two further
inputs, `hchart` and `hcolim`, so that it is not registered; the unconditional statement is
`AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed`. See the section
"What is still assumed" of this file's module documentation for the two inputs.

Let `f : X ⟶ Y` be a morphism of locally countably indexed formal algebraic spaces over `S` and
let `P` be a local property of morphisms of `WAdm^count`, that is
`TopologicalRing.PropertyIsLocal P C`. The following are equivalent:

1. for every commutative diagram with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   morphism of `C` with property `P`;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM such that each `Uᵢ ⟶ Vⱼ` corresponds to a morphism
   of `C` with property `P`;
3. there are a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` where `Vᵢ` is an affine formal algebraic space, `Vᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Uᵢ ⟶ Vᵢ` corresponds to a morphism of `C` with property
   `P`.

The cycle runs `(1) ⟹ (2) ⟹ (3) ⟹ (1)`, as in the source. The first step takes the fibre
products of condition (2) from this library's Stacks 0AJ3,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable`, so that
Stacks 0AJ3 is not assumed; the second holds for any class and property; and the third refines
the covering of condition (3) against a diagram as in condition (1) by
`AlgebraicGeometry.FormalSpace.hasEtaleRefinementOfSourceCover`, so that the refinement is not
assumed either, and then applies the two locality axioms on `P` that `hchart` extracts from
`hP`. -/
theorem hasProperty_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hP : TopologicalRing.PropertyIsLocal P C)
    (hchart : TopologicalRing.PropertyIsLocal P C →
      ChartPropertyAscendsAlongAffineEtale B S hS C P ∧
        ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS C P)
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS C P f,
        HasPropertyAfterTargetCover B S hS C P f,
        HasPropertyAfterSourceCover B S hS C P f ] := by
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_colimitOfThickenings B S hS C P
      hcolim f hX.1 hY.1 h
  tfae_have 2 → 3 := fun h ↦
    hasPropertyAfterSourceCover_of_afterTargetCover B S hS C P f h
  tfae_have 3 → 1 := fun h ↦
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover B S hS C P f
      (hchart hP).1 (hchart hP).2
      (hasEtaleRefinementOfSourceCover B S hS hcolim f hX.1 hY.1) h
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
