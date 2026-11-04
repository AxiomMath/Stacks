module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentMultiplicityBranchIndexing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceTopTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# The étale charts of a space and of its top subfunctor

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceTopTransport` transports the
integral closed subspaces, the δ-dimension and the multiplicity of Stacks 0EE9 between `X` and
`(⊤ : Subfunctor X).toFunctor`, and so defines the multiplicity `m_{X', X}` of an integral
closed subspace of `X` in `X` itself as the multiplicity of the closed subspace `⊤ ⊆ X` at the
corresponding subspace of the top subfunctor. What that file does *not* do is transport the
étale charts, and a consumer that reads the multiplicity as a length on a chart —
`AlgebraicGeometry.Space.spaceMultiplicity_eq_length_localizationAtPrime` does exactly that —
needs the charts on the side of `X`, not on the side of its top subfunctor. This file supplies
the transport and that reading.

The inclusion `(⊤ : Subfunctor X).ι` is an isomorphism, so it is étale, and postcomposition
with its inverse carries an étale chart of `X` to one of `(⊤ : Subfunctor X).toFunctor`
(`AlgebraicGeometry.Space.smallEtalePostcomp`, Stacks 03LP). Postcomposition does not touch the
chart's scheme: the chart is a morphism out of a scheme and only the morphism is changed, so
`chartScheme` of the transported chart is the *same* scheme and a point of one chart is a point
of the other. The only thing that moves is the point of the space a chart point determines, and
it moves exactly along `|(⊤ : Subfunctor X).ι|`.

## Main results

* `AlgebraicGeometry.Space.topSubfunctorChart`: an étale chart of `X` read as one of
  `(⊤ : Subfunctor X).toFunctor`, with the same scheme
  (`AlgebraicGeometry.Space.chartScheme_topSubfunctorChart`).
* `AlgebraicGeometry.Space.chartSchemeToPoints_topSubfunctorChart` and
  `AlgebraicGeometry.Space.pointsMap_ι_chartSchemeToPoints_topSubfunctorChart`: the point of
  `|⊤|` a chart point determines maps along `|(⊤ : Subfunctor X).ι|` to the point of `|X|` it
  determines on the original chart.
* `Space.IntegralClosedSubspace.pointsMap_ι_ambientGenericPoint_topSubfunctorEquiv_symm`:
  the generic point of the subspace of `⊤` corresponding to `X'` maps to the generic point of
  `X'`.
* `AlgebraicGeometry.Space.multiplicityInAmbient_eq_length_localizationAtPrime`: **the
  multiplicity `m_{X', X}` as a length at a branch on a chart of `X`**, which is what Stacks
  0EQA's coefficient has to be computed from.

## Implementation notes

`AlgebraicGeometry.Space.smallEtalePostcomp` is stated for morphisms of the category
`AlgebraicGeometry.AlgebraicSpaces` of bundled algebraic spaces, so the inverse of the inclusion
is packaged with `CategoryTheory.ObjectProperty.homMk`; `(⊤ : Subfunctor X).toFunctor` is an
algebraic space by `AlgebraicGeometry.Space.isClosedSubspace_top_subfunctor`.

`AlgebraicGeometry.Space.multiplicityInAmbient_eq_length_localizationAtPrime` states its
`Algebra`, `IsHenselization` and localization instances at the spelling
`(chartScheme W).presheaf.stalk u` of the chart local ring, for the chart `W` of `X` the
consumer has. Those are the instances
`AlgebraicGeometry.Space.spaceMultiplicity_eq_length_localizationAtPrime` asks for at the
spelling `(chartScheme (topSubfunctorChart … W)).presheaf.stalk u`; the two schemes are the same
but only definitionally, so the instances are passed across by `exact` at default transparency
rather than found by instance search. The multiplicity of `⊤ ⊆ X` is identified with the
multiplicity of Stacks 0EE9 on the algebraic space `(⊤ : Subfunctor X).toFunctor` itself by
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_spaceMultiplicity`.

No tag is claimed: the source does not distinguish `X` from its top subfunctor, so there is no
numbered result here.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### An étale chart of `X` read as an étale chart of its top subfunctor -/

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The inverse of the inclusion of the top subfunctor is étale, being an isomorphism. -/
theorem isEtale_inv_ι_top : IsEtale B S hS (inv (⊤ : Subfunctor X).ι) :=
  isEtale_of_isIso B S hS _

include hX in
/-- The inclusion of the top subfunctor, as a morphism of bundled algebraic spaces from `X` to
`(⊤ : Subfunctor X).toFunctor` — that is, its inverse, which is the direction charts of `X` are
pushed along. -/
def topSubfunctorInvHom :
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨(⊤ : Subfunctor X).toFunctor, (isClosedSubspace_top_subfunctor B S hS hX).1⟩ :=
  ObjectProperty.homMk (inv (⊤ : Subfunctor X).ι)

include hX in
/-- **An étale chart of `X`, read as an étale chart of `(⊤ : Subfunctor X).toFunctor`**: the
postcomposition of its structure morphism with the inverse of the inclusion of the top
subfunctor, which is étale because that inverse is an isomorphism. -/
def topSubfunctorChart (W : SmallEtale B S hS X) :
    SmallEtale B S hS (⊤ : Subfunctor X).toFunctor :=
  (smallEtalePostcomp B S hS (topSubfunctorInvHom B S hS hX)
    (isEtale_inv_ι_top B S hS)).obj W

/-- **The transport does not change the chart's scheme.** Postcomposition changes only the
structure morphism of a chart, so the scheme of the transported chart is the very same
scheme. -/
theorem chartScheme_topSubfunctorChart (W : SmallEtale B S hS X) :
    chartScheme (topSubfunctorChart B S hS hX W) = chartScheme W :=
  rfl

/-- **The point of `|⊤|` determined by a chart point.** A point of the scheme of a chart `W` of
`X` determines a point of `|(⊤ : Subfunctor X).toFunctor|` through the transported chart, and it
is the image along `|(⊤ : Subfunctor X).ι|⁻¹` of the point of `|X|` it determines through `W`.

This is `AlgebraicGeometry.Space.pointsMap_chartSchemeToPoints`: postcomposition leaves the
underlying object of the site and the structure morphism's source untouched, so the point the
transported chart determines is given by the same formula. -/
theorem chartSchemeToPoints_topSubfunctorChart (W : SmallEtale B S hS X) (x : chartScheme W) :
    chartSchemeToPoints B S hS (⊤ : Subfunctor X).toFunctor
        (topSubfunctorChart B S hS hX W) x =
      pointsMap B S hS X (inv (⊤ : Subfunctor X).ι) (chartSchemeToPoints B S hS X W x) :=
  (pointsMap_chartSchemeToPoints B S hS X (inv (⊤ : Subfunctor X).ι) W x).symm

/-- **The point of `|⊤|` determined by a chart point lies over the point of `|X|` determined by
it**, the two being matched by the inclusion of the top subfunctor. This is the previous
statement with the isomorphism cancelled. -/
theorem pointsMap_ι_chartSchemeToPoints_topSubfunctorChart (W : SmallEtale B S hS X)
    (x : chartScheme W) :
    pointsMap B S hS (⊤ : Subfunctor X).toFunctor (⊤ : Subfunctor X).ι
        (chartSchemeToPoints B S hS (⊤ : Subfunctor X).toFunctor
          (topSubfunctorChart B S hS hX W) x) =
      chartSchemeToPoints B S hS X W x := by
  rw [chartSchemeToPoints_topSubfunctorChart, ← Function.comp_apply
      (f := pointsMap B S hS (⊤ : Subfunctor X).toFunctor (⊤ : Subfunctor X).ι),
    ← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id, id]

/-! ### The generic point of a transported integral closed subspace -/

variable (hXdec : IsDecentSpace B S hS X)

include hX hXdec in
/-- **The generic point of the integral closed subspace of `⊤` corresponding to `X'` lies over
the generic point of `X'`.** The correspondence is taking the image along the inclusion of the
top subfunctor, so this is
`AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint_pushforward`. -/
theorem IntegralClosedSubspace.pointsMap_ι_ambientGenericPoint_topSubfunctorEquiv_symm
    (X' : IntegralClosedSubspace B S hS X) :
    pointsMap B S hS (⊤ : Subfunctor X).toFunctor (⊤ : Subfunctor X).ι
        (IntegralClosedSubspace.ambientGenericPoint B S hS
          ((IntegralClosedSubspace.topSubfunctorEquiv B S hS hX hXdec).symm X')) =
      IntegralClosedSubspace.ambientGenericPoint B S hS X' := by
  rw [← IntegralClosedSubspace.ambientGenericPoint_pushforward B S hS hX
    (isClosedSubspace_top_subfunctor B S hS hX).1 hXdec
    (isClosedSubspace_top_subfunctor B S hS hX).2]
  exact congrArg (IntegralClosedSubspace.ambientGenericPoint B S hS)
    ((IntegralClosedSubspace.topSubfunctorEquiv B S hS hX hXdec).apply_symm_apply X')

end Chart

/-! ### The multiplicity in the ambient space as a length at a branch on a chart of `X` -/

section Multiplicity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (W : SmallEtale D.site D.base D.base_mem X) (u : chartScheme W)

include hX hXdec in
/-- **The multiplicity `m_{X', X}` of Stacks 0EE9 is a length at a branch, read on a chart of
`X` itself.** Let `W` be an étale scheme chart of `X`, `u` a point of the chart, `Bh` a
henselization or a strict henselization of `𝒪_{W, u}` and `q` a minimal prime of `Bh` lying over
the prime `p` of `𝒪_{W, u}` — a branch of `X` at the image of `u`. Let `X' ⊆ X` be an integral
closed subspace whose generic point is the point of `|X|` cut out by `p`. Then

  `m_{X', X} = length_{(Bh)_q}((Bh)_q)`.

This is `AlgebraicGeometry.Space.spaceMultiplicity_eq_length_localizationAtPrime` at the
algebraic space `(⊤ : Subfunctor X).toFunctor`, whose chart is
`AlgebraicGeometry.Space.topSubfunctorChart` of `W` — the same scheme, so the same local ring
and the same branch — and whose integral closed subspace is the one corresponding to `X'`; the
multiplicity of the closed subspace `⊤ ⊆ X` is that multiplicity by
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_spaceMultiplicity`. The two
generic-point conditions match because
`|(⊤ : Subfunctor X).ι|` is injective and carries each side to the other
(`AlgebraicGeometry.Space.pointsMap_ι_chartSchemeToPoints_topSubfunctorChart` and
`IntegralClosedSubspace.pointsMap_ι_ambientGenericPoint_topSubfunctorEquiv_symm`). -/
theorem multiplicityInAmbient_eq_length_localizationAtPrime
    {Bh : Type w} [CommRing Bh] [IsLocalRing Bh]
    [Algebra ↥((chartScheme W).presheaf.stalk u) Bh]
    (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥((chartScheme W).presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥((chartScheme W).presheaf.stalk u) L Bh]
    (p : PrimeSpectrum ↥((chartScheme W).presheaf.stalk u)) (q : Ideal Bh) [q.IsPrime]
    [q.LiesOver p.asIdeal] (hq : q ∈ minimalPrimes Bh)
    (X' : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hX' : IntegralClosedSubspace.ambientGenericPoint D.site D.base D.base_mem X' =
      chartSchemeToPoints D.site D.base D.base_mem X W ((chartScheme W).fromSpecStalk u p)) :
    multiplicityInAmbient D hX hXdec X' =
      ((Module.length (Localization.AtPrime q) (Localization.AtPrime q)).toNat : ℤ) := by
  have hover : p.asIdeal = q.under ↥((chartScheme W).presheaf.stalk u) := Ideal.LiesOver.over
  let : IsLocalRing
      ↥((chartScheme (topSubfunctorChart D.site D.base D.base_mem hX W)).presheaf.stalk u) :=
    inferInstanceAs (IsLocalRing ↥((chartScheme W).presheaf.stalk u))
  let : Algebra ↥((chartScheme (topSubfunctorChart D.site D.base D.base_mem hX W)).presheaf.stalk
      u) Bh := inferInstanceAs (Algebra ↥((chartScheme W).presheaf.stalk u) Bh)
  let : Algebra (IsLocalRing.ResidueField
      ↥((chartScheme (topSubfunctorChart D.site D.base D.base_mem hX W)).presheaf.stalk u)) L :=
    inferInstanceAs (Algebra
      (IsLocalRing.ResidueField ↥((chartScheme W).presheaf.stalk u)) L)
  let : IsLocalRing.IsHenselization
      ↥((chartScheme (topSubfunctorChart D.site D.base D.base_mem hX W)).presheaf.stalk u) L Bh :=
    inferInstanceAs (IsLocalRing.IsHenselization ↥((chartScheme W).presheaf.stalk u) L Bh)
  let : Ideal.LiesOver q (show Ideal ↥((chartScheme
      (topSubfunctorChart D.site D.base D.base_mem hX W)).presheaf.stalk u) from p.asIdeal) :=
    ⟨hover⟩
  rw [multiplicityInAmbient, closedSubspaceMultiplicity_eq_spaceMultiplicity]
  refine spaceMultiplicity_eq_length_localizationAtPrime D (⊤ : Subfunctor X).toFunctor
    (isClosedSubspace_top_subfunctor D.site D.base D.base_mem hX).1
    (topSubfunctorChart D.site D.base D.base_mem hX W) u L p q hq
    ((IntegralClosedSubspace.topSubfunctorEquiv D.site D.base D.base_mem hX hXdec).symm X') ?_
  refine pointsMap_injective_of_mono D.site D.base D.base_mem (⊤ : Subfunctor X).ι ?_
  rw [IntegralClosedSubspace.pointsMap_ι_ambientGenericPoint_topSubfunctorEquiv_symm
    D.site D.base D.base_mem hX hXdec]
  exact hX'.trans (pointsMap_ι_chartSchemeToPoints_topSubfunctorChart D.site D.base D.base_mem
    hX W ((chartScheme W).fromSpecStalk u p)).symm

end Multiplicity

end AlgebraicGeometry.Space

end
