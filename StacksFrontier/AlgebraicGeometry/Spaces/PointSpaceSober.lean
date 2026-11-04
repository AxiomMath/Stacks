module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FibrePointsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.Topology.Sober.Defs

/-!
# The point space of a decent algebraic space is Kolmogorov, and when it is sober

Stacks 03K3 says that the point space of a decent algebraic space over a scheme `S` is
Kolmogorov, and Stacks 03K6 says that it is sober. This file proves Stacks 03K3 outright, and
reduces Stacks 03K6 to the one named input of its source proof which this repository does not
have: Tag 086U, Rydh's theorem that a decent algebraic space has a dense open subspace which is
a scheme. The source's other input, Tag 03KF for decency, *is* available — Tag 03KF for
property `(γ)`, proved as
`AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable` and specialized to closed
subspaces as `AlgebraicGeometry.Space.isDecentSpace_of_isClosedSubspace` — and is supplied here
rather than assumed.

Kolmogorov is `T0Space` and sober is `T0Space` together with `QuasiSober`, by
`StacksFrontier/Topology/Sober/Defs.lean`; so what Stacks 03K3 contributes to Stacks 03K6 is
exactly the first sentence of the source's proof, "we have seen in Lemma 03K3 that `|X|` is
Kolmogorov", and what remains is the existence of generic points.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.eq_of_specializes_of_specializes_points_of_isDecentSpace`: the
  specialization order on the point space of a decent algebraic space is antisymmetric.
* `AlgebraicGeometry.Space.quasiSober_points_of_exists_scheme_in_closed`: the point space of a
  presheaf is quasi-sober as soon as every irreducible closed set of points contains a nonempty
  relatively open piece which is, topologically, the point space of a scheme.
* `AlgebraicGeometry.Space.exists_scheme_in_closed_of_decentCore` derives that hypothesis from
  Tag 03KF for the closed subspaces of `X` together with the geometric core of Tag 086U, so the
  hypothesis is not stronger than those two inputs.
* `AlgebraicGeometry.Space.stacksSober_points_of_isDecentSpace_of_exists_scheme_in_closed` and
  `AlgebraicGeometry.Space.stacksSober_points_of_isDecentSpace_of_decentCore`: the conclusion of
  Stacks 03K6 for a decent algebraic space over `S`, from the topological hypothesis and from
  the geometric core of Tag 086U alone respectively.

## Implementation notes

**Stacks 03K3.** The proof is the source's. Let `x₁ ⤳ x₂` and `x₂ ⤳ x₁` in `|X|`. Choose an
étale scheme chart `a : h_U ⟶ X` through `x₂` (Tag 04N5,
`AlgebraicGeometry.Space.exists_etale_chart_at_point`) with `u` above `x₂`. Lifting the first
specialization along the chart gives `u₁ ⤳ u` above `x₁`, and lifting the second along the same
chart at `u₁` gives `u₂ ⤳ u₁` above `x₂`; both lifts are Stacks 03IL,
`AlgebraicGeometry.Space.exists_specialization_lift_of_isDecentSpace`. Then `u₂ ⤳ u` is a
specialization between two points of `U` above the single point `x₂`, so `u₂ = u` by
Stacks 03K5, `AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_isDecentSpace`.
That leaves `u ⤳ u₁` and `u₁ ⤳ u` inside the scheme `U`, which is `T₀`, so `u = u₁` and
therefore `x₁ = x₂`. The source chooses one chart whose image contains *both* points and lifts
both specializations into it; one chart through `x₂` suffices, because the first lift produces
the point above `x₁` in that same chart.

Only the two tags 03IL and 03K5 are used, both in their bare unconditional form for a
decent space, and the source's own appeal to Tag 03IL twice is reproduced exactly. Decency
cannot be dropped: the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DimensionZeroOverFieldSpecialization.lean` exhibit
`𝔸¹_k/ℤ`, an algebraic space whose point space carries the indiscrete topology on an infinite
set and so is not `T₀`. That file carries `T0Space (points B S hS X)` as an explicit hypothesis
in `AlgebraicGeometry.Space.discreteTopology_points_of_topologicalKrullDim_eq_zero`; Stacks 03K3
discharges it whenever `X` is decent.

**Why Stacks 03K6 is not proved here, and what it is reduced to.** The source deduces soberness
from Stacks 03K3 as follows: an irreducible closed `T ⊆ |X|` carries a closed subspace `Z ⊆ X`
with `|Z| = T` (Tag 03IQ, proved as
`AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace'`), `Z` is again decent because
`Z ⟶ X` is representable (Tag 03KF), and Tag 086U then provides a dense open subspace
`Z' ⊆ Z` which is a scheme, so `|Z'| ⊆ T` is a nonempty open piece of `T` homeomorphic to the
point space of a scheme; its generic point is a generic point of `T`.

Tag 086U is **not available in this repository**. It is reduced, in
`StacksFrontier/AlgebraicGeometry/Spaces/DenseOpenSchemeLocus.lean`, to a geometric core which
`StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocusEquivalence.lean` shows to be
*equivalent* to the theorem itself, so the gap recorded against it is the whole theorem and not
a lemma inside it. It is therefore the single hypothesis of
`AlgebraicGeometry.Space.stacksSober_points_of_isDecentSpace_of_decentCore`, as `hcore`, which
is verbatim the hypothesis of
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_decentCore`.

The other two tags the source's step consumes are both available and are therefore proved here
rather than assumed. Tag 03IQ is proved inside
`AlgebraicGeometry.Space.exists_scheme_in_closed_of_decentCore`. Tag 03KF holds for property
`(γ)` — `AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable`, specialized to
closed subspaces as `AlgebraicGeometry.Space.isDecentSpace_of_isClosedSubspace` — which is the
only instance of 03KF the proof uses, so it is supplied out of the decency of `X` in
`AlgebraicGeometry.Space.stacksSober_points_of_isDecentSpace_of_decentCore`. Only 086U is owed.
`AlgebraicGeometry.Space.exists_scheme_in_closed_of_decentCore` keeps `h03KF` as a hypothesis
because it does not assume `X` decent and so cannot derive it. **Nothing in this file carries
`@[stacks 03K6]`**: the tag is not proved, only reduced.

**Why the topological hypothesis is not a restatement of the conclusion.**
`AlgebraicGeometry.Space.quasiSober_points_of_exists_scheme_in_closed` consumes the two tags
only through the geometric statement that every nonempty closed set of points has a nonempty
relatively open piece which is topologically the point space of a scheme, and
`AlgebraicGeometry.Space.exists_scheme_in_closed_of_decentCore` proves that statement from them,
so no strength has been added. In the other direction the hypothesis is genuinely restrictive:
it fails for `𝔸¹_k/ℤ`, whose point space is indiscrete on an infinite set, because its only
irreducible closed set is the whole of `|X|`, its only nonempty relatively open piece is `|X|`
itself, and an indiscrete space on more than one point is not `T₀`, hence is not the point space
of a scheme. The hypothesis also asks for the least the argument needs: `e` is required only to
be topologically inducing, not injective, although the composite `|Z'| → |Z| → |X|` produced by
`exists_scheme_in_closed_of_decentCore` is an embedding.

**The remaining argument.** Given the hypothesis, `|V|` is an irreducible space, because every
open set of `|V|` is the `e`-preimage of an open set of points of `X` and `T` is
preirreducible; `|V|` is a scheme, hence quasi-sober, so it has a generic point `ν`; and
`e ν` is a generic point of `T`, because `e` is continuous — so the range of `e` lies in the
closure of `e ν` — while the range of `e`, being a nonempty relatively open piece of the
irreducible set `T`, is dense in `T`.

**One inlined monotonicity step.** The discharge needs that a closed immersion and an open
immersion of algebraic spaces are immersions, in order to apply
`AlgebraicGeometry.Space.isInducing_pointsMap_of_isImmersion`. The first is
`AlgebraicGeometry.Space.isImmersion_of_isClosedImmersion`, in
`StacksFrontier/AlgebraicGeometry/Spaces/SeparatedVariants.lean`. The library has no form of the
second, which is therefore proved inline from
`CategoryTheory.MorphismProperty.relative_monotone`, declaring no new name.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The specialization order on the point space of a decent algebraic space is
antisymmetric.** If `x` and `x'` are points of `|X|` each of which is a specialization of the
other, they are equal.

This is the content of Stacks 03K3;
`AlgebraicGeometry.Space.t0Space_points_of_hasFiniteChartFibers`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/Points.lean`) is the same statement in the form of
Definition 004X, from a weaker hypothesis. The two specializations are lifted into
one étale scheme chart through `x'` by Stacks 03IL, the resulting specialization inside a single
fibre is collapsed by Stacks 03K5, and what is left is an antisymmetric pair in the point space
of a scheme, which is `T₀`. -/
theorem eq_of_specializes_of_specializes_points_of_isDecentSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) {x x' : points B S hS X}
    (h : x ⤳ x') (h' : x' ⤳ x) : x = x' := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x'
  obtain ⟨u₁, hu₁sp, hu₁⟩ := exists_specialization_lift_of_isDecentSpace B S hS X hX hXdec
    x' x h U a ha (p.class B S hS (yoneda.obj U)) hp
  obtain ⟨u₂, hu₂sp, hu₂⟩ := exists_specialization_lift_of_isDecentSpace B S hS X hX hXdec
    x x' h' U a ha u₁ hu₁
  have hequiv : ∀ c d : points B S hS (yoneda.obj U),
      c ⤳ d ↔ pointsEquivScheme B S hS U c ⤳ pointsEquivScheme B S hS U d := fun c d =>
    ((schemePointsHomeomorph B S hS U).isEmbedding.isInducing.specializes_iff
      (x := c) (y := d)).symm
  have hsymm : ∀ c : points B S hS (yoneda.obj U),
      (pointsEquivScheme B S hS U).symm (pointsEquivScheme B S hS U c) = c :=
    fun c => (pointsEquivScheme B S hS U).symm_apply_apply c
  -- `u₂` and the chosen point both lie above `x'`, and `u₂` specializes to it: Stacks 03K5.
  have heq : pointsEquivScheme B S hS U (p.class B S hS (yoneda.obj U)) =
      pointsEquivScheme B S hS U u₂ :=
    eq_of_specializes_of_pointsMap_eq_of_isDecentSpace B S hS hX hXdec U a
      (isEtale_of_presheaf_etale B S hS ha) _ _
      (by rw [hsymm, hsymm, hp, hu₂]) ((hequiv _ _).mp (hu₂sp.trans hu₁sp))
  have hu₂eq : u₂ = p.class B S hS (yoneda.obj U) :=
    (pointsEquivScheme B S hS U).injective heq.symm
  -- The chosen point and `u₁` now specialize to each other inside the chart, which is `T₀`.
  have hins := ((hequiv _ _).mp hu₁sp).antisymm ((hequiv _ _).mp (hu₂eq ▸ hu₂sp))
  have hu₁eq : u₁ = p.class B S hS (yoneda.obj U) :=
    (pointsEquivScheme B S hS U).injective hins.eq
  rw [← hu₁, hu₁eq, hp]

/-- **The existence of generic points in the point space, from a scheme inside every closed
set.** Let `X` be a presheaf on the big fppf site of `S` and assume that every irreducible
closed set `T` of points of `X` has a nonempty relatively open piece `O ∩ T` which is,
topologically, the point space of an object of the site: there is a topologically inducing map
`e` from the underlying scheme of some `V` onto `O ∩ T`. Then the point space of `X` is
quasi-sober.

This is the second half of the proof of Stacks 03K6, and the hypothesis is what the source's
appeal to Tags 03IQ, 03KF and 086U supplies there; of the three only 03IQ is available in this
repository, and `AlgebraicGeometry.Space.exists_scheme_in_closed_of_decentCore` proves the
hypothesis from the other two. The scheme `|V|` is irreducible
because `T` is, so it has a generic point, and the image of that point is a generic point of `T`
because the range of `e` is dense in `T`. -/
theorem quasiSober_points_of_exists_scheme_in_closed
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : ∀ T : Set (points B S hS X), IsIrreducible T → IsClosed T →
      ∃ (V : BigFppfOver B S hS) (O : Set (points B S hS X))
        (e : (BigFppfOver.toScheme B S hS).obj V → points B S hS X),
        Topology.IsInducing e ∧ IsOpen O ∧ Set.range e = O ∩ T ∧ (Set.range e).Nonempty) :
    QuasiSober (points B S hS X) := by
  rw [← local_quasiSober_iff]
  intro T hTirr hTclosed
  obtain ⟨V, O, e, hind, hO, hrange, hne⟩ := h T hTirr hTclosed
  obtain ⟨ξ₀, hξ₀⟩ := hne
  have hVne : Nonempty ((BigFppfOver.toScheme B S hS).obj V) := by
    obtain ⟨w, -⟩ := hξ₀
    exact ⟨w⟩
  have hOT : (T ∩ O).Nonempty := by
    rw [hrange] at hξ₀
    exact ⟨ξ₀, hξ₀.2, hξ₀.1⟩
  -- A nonempty relatively open piece of an irreducible set is dense in it.
  have hdense : T ⊆ closure (O ∩ T) := by
    intro t ht
    rw [mem_closure_iff]
    intro N hN htN
    obtain ⟨c, hcT, hcN, hcO⟩ := hTirr.isPreirreducible N O hN hO ⟨t, ht, htN⟩ hOT
    exact ⟨c, hcN, hcO, hcT⟩
  have hmem : ∀ w, e w ∈ O ∩ T := fun w => hrange ▸ Set.mem_range_self w
  -- `|V|` is irreducible: its opens are the `e`-preimages of opens of `|X|`.
  have hVirr : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj V) := by
    rw [irreducibleSpace_def]
    refine ⟨Set.univ_nonempty, fun u v hu hv hune hvne => ?_⟩
    obtain ⟨Ou, hOu, hueq⟩ := hind.isOpen_iff.mp hu
    obtain ⟨Ov, hOv, hveq⟩ := hind.isOpen_iff.mp hv
    obtain ⟨a, -, hau⟩ := hune
    obtain ⟨b, -, hbv⟩ := hvne
    have hea : e a ∈ T ∩ (Ou ∩ O) := ⟨(hmem a).2, by rwa [← hueq] at hau, (hmem a).1⟩
    have heb : e b ∈ T ∩ (Ov ∩ O) := ⟨(hmem b).2, by rwa [← hveq] at hbv, (hmem b).1⟩
    obtain ⟨c, hcT, ⟨hcOu, hcO⟩, hcOv, -⟩ :=
      hTirr.isPreirreducible (Ou ∩ O) (Ov ∩ O) (hOu.inter hO) (hOv.inter hO) ⟨e a, hea⟩
        ⟨e b, heb⟩
    obtain ⟨w, hw⟩ : c ∈ Set.range e := by rw [hrange]; exact ⟨hcO, hcT⟩
    refine ⟨w, Set.mem_univ w, ?_, ?_⟩
    · rw [← hueq, Set.mem_preimage, hw]; exact hcOu
    · rw [← hveq, Set.mem_preimage, hw]; exact hcOv
  have hgenmem := hmem (genericPoint ((BigFppfOver.toScheme B S hS).obj V))
  refine ⟨e (genericPoint ((BigFppfOver.toScheme B S hS).obj V)), hgenmem.2,
    subset_antisymm ?_ ?_⟩
  · have hsub : O ∩ T ⊆ closure {e (genericPoint ((BigFppfOver.toScheme B S hS).obj V))} := by
      rw [← hrange]
      rintro - ⟨w, rfl⟩
      exact ((genericPoint_specializes w).map hind.continuous).mem_closure
    exact hdense.trans (closure_minimal hsub isClosed_closure)
  · exact hTclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgenmem.2)

/-- **A scheme inside every closed set of points, from Tag 03KF and the geometric core of
Tag 086U.** Assume that every closed subspace of `X` is decent — Tag 03KF for property `(γ)`,
which holds for `X` decent — and assume the geometric core of Tag 086U, that every nonempty
decent algebraic space over `S` has a nonempty representable open subspace. Then every nonempty
closed set `T` of points of `X` has a nonempty relatively open piece which is, topologically,
the point space of an object of the site. Nonempty is all that is asked of `T` here, which is
weaker than the irreducibility that
`AlgebraicGeometry.Space.quasiSober_points_of_exists_scheme_in_closed` asks for.

This is the first half of the proof of Stacks 03K6, and it is what makes the hypothesis of
`AlgebraicGeometry.Space.quasiSober_points_of_exists_scheme_in_closed` no stronger than those
two tags. The closed subspace on `T` is the reduced one of Tag 03IQ, whose point set is `T`;
the open subspace of it produced by the core is representable, so its point space is
homeomorphic to the point space of an object of the site by Tag 03BX; both inclusions are
inducing on points by Tag 0ABJ; and the open range upstairs becomes a relatively open piece of
`T` downstairs. -/
theorem exists_scheme_in_closed_of_decentCore
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h03KF : ∀ Z : Subfunctor X, IsClosedSubspace B S hS Z →
      IsDecentSpace B S hS Z.toFunctor)
    (hcore : ∀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y →
      IsDecentSpace B S hS Y → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    (T : Set (points B S hS X)) (hT : IsClosed T) (hTne : T.Nonempty) :
    ∃ (V : BigFppfOver B S hS) (O : Set (points B S hS X))
      (e : (BigFppfOver.toScheme B S hS).obj V → points B S hS X),
      Topology.IsInducing e ∧ IsOpen O ∧ Set.range e = O ∩ T ∧ (Set.range e).Nonempty := by
  have hZcl : IsClosedSubspace B S hS (reducedClosedSubspace B S hS X hX T hT) :=
    isClosedSubspace_reducedClosedSubspace' B S hS hX T hT
  have hZrange : Set.range (pointsMap B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
      (reducedClosedSubspace B S hS X hX T hT).ι) = T :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT
  have hZne : Nonempty (points B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor) := by
    obtain ⟨t, ht⟩ := hTne
    rw [← hZrange] at ht
    obtain ⟨z, -⟩ := ht
    exact ⟨z⟩
  obtain ⟨H, hHopen, hHrep, hHne⟩ := hcore _ hZcl.1 (h03KF _ hZcl) hZne
  have hZind := isInducing_pointsMap_of_isImmersion B S hS hX
    (reducedClosedSubspace B S hS X hX T hT).ι
    (isImmersion_of_isClosedImmersion B S hS hZcl.2)
  have hHind := isInducing_pointsMap_of_isImmersion B S hS hZcl.1 H.ι
    (MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage _
      (fun _ _ f hf => by
        have : AlgebraicGeometry.IsOpenImmersion f := hf
        infer_instance)) _ hHopen.2)
  have hHopenrange : IsOpen (Set.range (pointsMap B S hS H.toFunctor H.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS H.ι hHopen.2
  obtain ⟨O, hO, hOeq⟩ := hZind.image_eq_isOpen_inter_range hHopenrange
  let eH : points B S hS (yoneda.obj H.toFunctor.reprX) ≃ₜ points B S hS H.toFunctor :=
    { toEquiv := pointsEquivOfIso B S hS H.toFunctor.reprW
      continuous_toFun := continuous_pointsMap B S hS H.toFunctor.reprW.hom
      continuous_invFun := continuous_pointsMap B S hS H.toFunctor.reprW.inv }
  refine ⟨H.toFunctor.reprX, O,
    pointsMap B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
        (reducedClosedSubspace B S hS X hX T hT).ι ∘
      pointsMap B S hS H.toFunctor H.ι ∘ eH ∘
        (schemePointsHomeomorph B S hS H.toFunctor.reprX).symm,
    hZind.comp (hHind.comp (eH.isInducing.comp
      (schemePointsHomeomorph B S hS H.toFunctor.reprX).symm.isInducing)), hO, ?_⟩
  rw [Set.range_comp, Set.range_comp, Set.range_comp,
    Set.range_eq_univ.mpr (schemePointsHomeomorph B S hS H.toFunctor.reprX).symm.surjective,
    Set.image_univ, Set.range_eq_univ.mpr eH.surjective, Set.image_univ]
  exact ⟨by rw [hOeq, hZrange], hHne.image _⟩

/-- **The conclusion of Stacks 03K6 for a decent algebraic space, from the topological
hypothesis.** The point space of a decent algebraic space over a scheme `S` is sober — every
irreducible closed set has a unique generic point — as soon as every irreducible closed set of
points has a nonempty relatively open piece which is, topologically, the point space of an
object of the site.

Soberness is `T0Space` together with `QuasiSober`, by `stacksSober_iff_t0_and_quasiSober`: the
first factor is Stacks 03K3, out of
`AlgebraicGeometry.Space.eq_of_specializes_of_specializes_points_of_isDecentSpace` above, and the
second is `AlgebraicGeometry.Space.quasiSober_points_of_exists_scheme_in_closed`. The
hypothesis is supplied by Tags 03KF and 086U through
`AlgebraicGeometry.Space.exists_scheme_in_closed_of_decentCore`; of those two, Tag 03KF for
property `(γ)` is available as
`AlgebraicGeometry.Space.isDecentSpace_of_isClosedSubspace` and Tag 086U is not, so this
declaration does not carry `@[stacks 03K6]`. -/
theorem stacksSober_points_of_isDecentSpace_of_exists_scheme_in_closed
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (h : ∀ T : Set (points B S hS X), IsIrreducible T → IsClosed T →
      ∃ (V : BigFppfOver B S hS) (O : Set (points B S hS X))
        (e : (BigFppfOver.toScheme B S hS).obj V → points B S hS X),
        Topology.IsInducing e ∧ IsOpen O ∧ Set.range e = O ∩ T ∧ (Set.range e).Nonempty) :
    StacksSober (points B S hS X) :=
  stacksSober_iff_t0_and_quasiSober.mpr
    ⟨(t0Space_iff_inseparable _).mpr fun _ _ hins =>
        eq_of_specializes_of_specializes_points_of_isDecentSpace B S hS hX hXdec
          hins.specializes hins.specializes',
      quasiSober_points_of_exists_scheme_in_closed B S hS h⟩

/-- **Stacks 03K6 modulo the geometric core of Tag 086U.** The point space of a decent
algebraic space over a scheme `S` is sober, granting that every nonempty decent algebraic space
over `S` has a nonempty representable open subspace (the geometric core of Tag 086U, which
`StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocusEquivalence.lean` shows to be
equivalent to Tag 086U itself).

This is the source's proof of Stacks 03K6 with its one remaining unavailable input carried as a
named hypothesis and everything else proved. The source's other input, Tag 03KF for the closed
subspaces of `X`, is supplied here by
`AlgebraicGeometry.Space.isDecentSpace_of_isClosedSubspace`, Tag 03KF for property `(γ)`, out of
the decency of `X`. Discharging `hcore` discharges the tag, with no further work on this file;
until then this declaration does not carry `@[stacks 03K6]`. -/
theorem stacksSober_points_of_isDecentSpace_of_decentCore
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (hcore : ∀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y →
      IsDecentSpace B S hS Y → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    StacksSober (points B S hS X) :=
  stacksSober_points_of_isDecentSpace_of_exists_scheme_in_closed B S hS hX hXdec
    (fun T hTirr hTcl =>
      exists_scheme_in_closed_of_decentCore B S hS hX
        (fun _ hZ => isDecentSpace_of_isClosedSubspace B S hS hXdec hZ)
        hcore T hTcl hTirr.nonempty)

end AlgebraicGeometry.Space

end
