module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Finite presentation for algebraic spaces: permanence properties and local criteria

Three ways in which local finite presentation of a morphism of algebraic spaces over a scheme
`S` (Stacks 03XP, part (1)) is produced from weaker data: it holds for every open immersion; it
is equivalent to local finite type over a locally Noetherian target; and it holds for the
relative diagonal of a morphism locally of finite type. The last two also give the global form,
finite presentation (Stacks 03XP, part (3)), since that is local finite presentation together
with quasi-compactness and quasi-separatedness.

A morphism of finite presentation also transports the finiteness conditions on a space
backwards: its source is quasi-compact and quasi-separated as soon as its target is, and
Noetherian as soon as its target is.

Local finite presentation is then characterised in nine equivalent ways: it can be tested at
every point of the source, after base change to every scheme or to every affine scheme or to
one surjective étale chart of the target, on the composite with one surjective étale chart of
the source, on every — or on one surjective — commuting square of étale charts, and over a
pair of Zariski coverings of target and source.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.qcqs_of_isFinitePresentation`: **Stacks 06G5**. Its
  quasi-separatedness half is
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isFinitePresentation`, proved here;
  its quasi-compactness half is
  `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation`, proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/ApproximationSteps.lean`.
* `AlgebraicGeometry.Space.isNoetherian_of_isFinitePresentation`: **Stacks 04ZL**.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isOpenImmersion`: **Stacks 06CN**.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType` and
  `AlgebraicGeometry.Space.isFinitePresentation_of_isFiniteType` are the two parts of
  **Stacks 06G4**.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_pullbackDiagonal` and
  `AlgebraicGeometry.Space.isFinitePresentation_pullbackDiagonal` are the two assertions of
  **Stacks 084P**.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_tfae`: **Stacks 0410**, the nine
  criteria, with the equivalence of its first two conditions also stated separately as
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_iff_forall_isFinitePresentationAt`.

## Implementation notes

Stacks 06G4 part (1) is proved on one surjective étale chart square rather than on all of them:
local finite presentation of morphisms of schemes is étale local on the source and target by
Stacks 04R3, so conditions (1) and (2) of Stacks 03MJ agree for it
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`), and a single square is
produced by lifting an atlas of the final target through Stacks 02X1.

For 06G4 the atlas of the target is the one witnessing its local Noetherianity, so the scheme
it is indexed by is locally Noetherian and Mathlib's instance making a morphism locally of
finite type with locally Noetherian target locally of finite presentation applies to the
lifted square directly. Taking that atlas is what avoids the every-chart form of Stacks 03E8,
which would need local Noetherianity of schemes to be local for the étale precoverage; see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/NoetherianSpaces.lean`. Local
Noetherianity of the target is the étale-local scheme property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of Stacks 03E6 at
`AlgebraicGeometry.IsLocallyNoetherian`, as in that file.

Stacks 06CN is stated without any algebraicity hypothesis. An open immersion in the sense of
Stacks 02YU, part (1) is representable and relatively étale, so in a commuting square of étale
charts the composite of the chart of the source with the immersion is again an étale chart of
the target, and Stacks 03EC identifies the morphism of the site as an étale morphism of
schemes; étale morphisms of schemes are locally of finite presentation. No descent along an
atlas, and hence no algebraic space, enters.

Stacks 084P is Stacks 05WT applied to the factorisation of the identity of the source through
its relative diagonal: the identity is locally of finite presentation because it is étale
(Stacks 0468), and the second projection of the fibre square is locally of finite type by base
change, Stacks 03XH. The finite-presentation assertion adds quasi-compactness of the diagonal,
which *is* quasi-separatedness of the morphism, and quasi-separatedness of the diagonal, which
comes from its separatedness: the relative diagonal is separated after every represented base
change by Stacks 03HK, part (4), that reading agrees with Stacks 03HL, part (1) because the
diagonal is representable by Stacks 03HK, part (1), and a separated morphism is quasi-separated
by Stacks 03KK.

Both conclusions of Stacks 06G5 are read off one conjunct of finite presentation each, so the
lemma carries no argument of its own. Quasi-compactness is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ApproximationSteps.lean`, where quasi-compactness of a
morphism is introduced: it is the quasi-compactness of the source of the base change of `f`
along the identity of `Y`. Quasi-separatedness is Stacks 04ZH, part (2) at the
quasi-separatedness conjunct, and it is proved here because that part needs the relative
diagonal of `f` to be representable, which the algebraicity hypothesis on the source supplies.
Throughout, a quasi-separated algebraic space is one which is quasi-separated in the absolute
sense of Stacks 03BS, part (3) — quasi-separated over the terminal scheme — which is the
reading under which Stacks 04ZH, part (2) is stated and the one Noetherianity of a space uses.

Stacks 04ZL is assembled from the three components of Noetherianity of an algebraic space
(Stacks 03EA): quasi-compactness and quasi-separatedness of the source are the two conclusions
of Stacks 06G5 at the quasi-compact and quasi-separated target, and local Noetherianity of the
source is Stacks 04ZK, the morphism being locally of finite type by Stacks 0464. The deduction
lives here rather than with Noetherianity in
`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianSpaces.lean` because two of its three inputs
do.

Stacks 0410 needs no argument of its own: the nine criteria hold for any property of scheme
morphisms which is étale local on the source and target, stable under composition and base
change, and implied by étaleness, and that is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae`. Local finite presentation satisfies all
four, the first by Stacks 04R3 and the other three by Mathlib, so 0410 is the instance of that
theorem at it. Only the pointwise condition has to be rephrased: Stacks 03XP, part (2) records
the point of the open subspace lying over the given point as a membership in the range of the
map on points, where the general statement keeps it as an existential.

## References

* [Stacks Project, Tag 0410](https://stacks.math.columbia.edu/tag/0410)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
* [Stacks Project, Tag 06CN](https://stacks.math.columbia.edu/tag/06CN)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
* [Stacks Project, Tag 06G5](https://stacks.math.columbia.edu/tag/06G5)
* [Stacks Project, Tag 084P](https://stacks.math.columbia.edu/tag/084P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Quasi-compact and quasi-separated source -/

/-- **Stacks 06G5, quasi-separatedness.** If `f : X ⟶ Y` is of finite presentation and `Y` is
a quasi-separated algebraic space, then `X` is quasi-separated.

Finite presentation includes quasi-separatedness of `f` (Stacks 03XP, part (3)), and Stacks
04ZH, part (2) passes quasi-separatedness from the target of a quasi-separated morphism to its
source. The algebraicity of `X` is what makes the relative diagonal of `f` representable, which
is what that part needs. -/
theorem isAbsolutelyQuasiSeparated_of_isFinitePresentation (hZ : B.Contains (⊤_ Scheme.{u}))
    {f : X ⟶ Y} (hX : IsAlgebraicSpace B S hS X)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hf : IsFinitePresentation B S hS f) : IsAbsolutelyQuasiSeparated B S hS hZ X :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hYqs hf.2.2

/-- **Stacks 06G5.** If `Y` is a quasi-compact and quasi-separated algebraic space over `S`
and `X` is of finite presentation over `Y`, then `X` is quasi-compact and quasi-separated.

The two conclusions are independent of each other and each comes from one conjunct of finite
presentation (Stacks 03XP, part (3)): quasi-compactness of `X` from quasi-compactness of `f`,
and quasi-separatedness of `X` from quasi-separatedness of `f`. As everywhere in this
development, a quasi-compact and quasi-separated algebraic space is one which is quasi-compact
in the sense of Stacks 03E3 and quasi-separated in the absolute sense of Stacks 03BS, part
(3), that is, quasi-separated over the terminal scheme. -/
@[stacks 06G5]
theorem qcqs_of_isFinitePresentation (hZ : B.Contains (⊤_ Scheme.{u})) {f : X ⟶ Y}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hf : IsFinitePresentation B S hS f) :
    IsQuasiCompactSpace B S hS X ∧ IsAbsolutelyQuasiSeparated B S hS hZ X :=
  ⟨isQuasiCompactSpace_of_isFinitePresentation B S hS f hY hYqc hf,
    isAbsolutelyQuasiSeparated_of_isFinitePresentation B S hS hZ hX hYqs hf⟩

/-! ### Noetherian source -/

/-- **Stacks 04ZL.** A morphism of algebraic spaces over `S` of finite presentation whose
target is Noetherian has Noetherian source.

Noetherianity of an algebraic space (Stacks 03EA) is quasi-compactness, quasi-separatedness
and local Noetherianity. The first two of the three are exactly Stacks 06G5 applied to the
quasi-compact and quasi-separated target, and local Noetherianity of the source comes from
Stacks 04ZK, the morphism being locally of finite type by Stacks 0464. -/
@[stacks 04ZL]
theorem isNoetherian_of_isFinitePresentation (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsFinitePresentation B S hS f) (hYnoeth : IsNoetherian B S hS hZ Y) :
    IsNoetherian B S hS hZ X :=
  have hqcqs := qcqs_of_isFinitePresentation B S hS hZ hX hY hYnoeth.1 hYnoeth.2.1 hf
  ⟨hqcqs.1, hqcqs.2,
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hX hY f
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1) hYnoeth.2.2⟩

/-! ### Open immersions -/

/-- **Stacks 06CN.** An open immersion of algebraic spaces over `S` is locally of finite
presentation.

An open immersion is relatively étale, so in a commuting square of étale charts the composite
of the chart of the source with the immersion is an étale chart of the target and Stacks 03EC
makes the morphism of the site étale; an étale morphism of schemes is locally of finite
presentation. Neither the source nor the target has to be an algebraic space. -/
@[stacks 06CN]
theorem isLocallyOfFinitePresentation_of_isOpenImmersion {f : X ⟶ Y}
    (hf : IsOpenImmersion B S hS f) : IsLocallyOfFinitePresentation B S hS f := by
  have := isMultiplicative_presheaf_etale B S hS
  intro U V a b h ha hb hsq
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) :=
    etale_of_etale_charts B S hS (a ≫ f) b
      (MorphismProperty.comp_mem _ a f ha (presheaf_etale_of_isOpenImmersion B S hS hf)) hb h hsq
  infer_instance

/-! ### Locally Noetherian target -/

/-- **Stacks 06G4, part (1).** A morphism of algebraic spaces over `S` which is locally of
finite type and whose target is locally Noetherian is locally of finite presentation.

The surjective étale atlas of the target witnessing its local Noetherianity lifts, by Stacks
02X1, to a surjective étale chart of the source together with a morphism of the site making
the square commute. Local finite type of the morphism tests exactly such squares, so the
underlying scheme morphism is locally of finite type with locally Noetherian target and hence
locally of finite presentation; one surjective chart square suffices by Stacks 03MJ. -/
@[stacks 06G4 "part (1)", sga "3 VIA 2.5.4" "more general"]
theorem isLocallyOfFinitePresentation_of_isLocallyOfFiniteType
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFinitePresentation B S hS f := by
  obtain ⟨V, q, hqSurj, hqEtale, hV⟩ := hN
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hqSurj hqEtale
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hX hY f).mpr
    ⟨U, V, p, q, α, hpEtale, hqEtale, hpSurj, hcomm.symm, ?_⟩
  have := hf U V p q α hpEtale hqEtale hcomm.symm
  have := hV
  infer_instance

/-- **Stacks 06G4, part (2).** A morphism of algebraic spaces over `S` which is of finite type
and quasi-separated and whose target is locally Noetherian is of finite presentation.

Finite presentation is local finite presentation, quasi-compactness and quasi-separatedness
(Stacks 03XP, part (3)) and finite type is local finite type together with quasi-compactness
(Stacks 03XF, part (3)), so only the first conjunct has content and that is part (1). -/
@[stacks 06G4 "part (2)"]
theorem isFinitePresentation_of_isFiniteType
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hf : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    IsFinitePresentation B S hS f :=
  ⟨isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hX hY f hN hf.1, hf.2, hqs⟩

/-! ### The relative diagonal -/

/-- The second projection of the fibre square of a morphism of algebraic spaces over `S`
locally of finite type is locally of finite type, being a base change of the morphism
(Stacks 03XH). -/
private theorem isLocallyOfFiniteType_pullback_snd (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (pullback.snd f f) := by
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let fs : Xs ⟶ Ys := ObjectProperty.homMk f
  exact (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS fs fs) hf

/-- **Stacks 084P**, the local assertion. The relative diagonal of a morphism of algebraic
spaces over `S` which is locally of finite type is locally of finite presentation.

The diagonal is the first factor of a factorisation of the identity of the source through the
fibre square. The identity is locally of finite presentation because it is étale (Stacks
0468), and the second projection is locally of finite type by base change, so Stacks 05WT
applies. -/
@[stacks 084P "the local assertion",
  ega "IV 1.4.3.1" "more general",
  ega "IV 17.4.1.2" "more general"]
theorem isLocallyOfFinitePresentation_pullbackDiagonal (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFinitePresentation B S hS (pullback.diagonal f) :=
  isLocallyOfFinitePresentation_of_comp B S hS hX
    (isAlgebraicSpace_pullback B S hS f f hX hX hY) hX (pullback.diagonal f) (pullback.snd f f)
    (by simpa using isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_id B S hS X))
    (isLocallyOfFiniteType_pullback_snd B S hS f hX hY hf)

/-- **Stacks 084P**, the global assertion. The relative diagonal of a quasi-separated morphism
of algebraic spaces over `S` which is locally of finite type is of finite presentation.

Quasi-compactness of the diagonal is quasi-separatedness of the morphism (Stacks 03HL, part
(3)). Quasi-separatedness of the diagonal follows from its separatedness by Stacks 03KK, and
the diagonal is separated because it is so after every represented base change (Stacks 03HK,
part (4)) and the two readings agree for a representable morphism (Stacks 03KY), the diagonal
being representable by Stacks 03HK, part (1). -/
@[stacks 084P "the global assertion"]
theorem isFinitePresentation_pullbackDiagonal (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    IsFinitePresentation B S hS (pullback.diagonal f) :=
  ⟨isLocallyOfFinitePresentation_pullbackDiagonal B S hS f hX hY hf, hqs,
    isQuasiSeparated_of_isSeparated B S hS
      ((isSeparated_iff_presheaf B S hS (pullback.diagonal f) hX
        (isAlgebraicSpace_pullback B S hS f f hX hX hY)
        (relativelyRepresentable_pullbackDiagonal B S hS f hX)).2
        (presheaf_isSeparated_pullbackDiagonal B S hS f hX))⟩

/-! ### The nine criteria of Stacks 0410 -/

/-- **Stacks 0410.** Nine criteria for a morphism of algebraic spaces over `S` to be locally
of finite presentation: pointwise finite presentation, local finite presentation of every base
change to a scheme or to an affine scheme or to one surjective étale chart of the target, local
finite presentation of the composite with one surjective étale chart of the source, local
finite presentation of the morphism of schemes in every — or in one surjective — commuting
square of étale charts, or over a pair of Zariski coverings.

Local finite presentation of morphisms of schemes is étale local on the source and target
(Stacks 04R3), stable under composition and base change, and implied by étaleness, so this is
the instance of `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae` at that property. -/
@[stacks 0410]
theorem isLocallyOfFinitePresentation_tfae
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      IsLocallyOfFinitePresentation B S hS f,
      ∀ x : points B S hS X, IsFinitePresentationAt B S hS f x,
      ∀ (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ Y),
        IsLocallyOfFinitePresentation B S hS (pullback.fst g f),
      ∀ (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
          IsLocallyOfFinitePresentation B S hS (pullback.fst g f),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          IsLocallyOfFinitePresentation B S hS (pullback.fst g f),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          IsLocallyOfFinitePresentation B S hS (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          IsLocallyOfFinitePresentation B S hS (yoneda.map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsLocallyOfFinitePresentation B S hS (yoneda.map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsLocallyOfFinitePresentation B S hS
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] := by
  have h := holdsOnEveryEtaleChart_tfae B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget inferInstance inferInstance
    (fun _ hg => have := hg; inferInstance) hX hY f
  have key : (∀ x : points B S hS X, ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
        ∃ x' : points B S hS U.toFunctor,
          pointsMap B S hS U.toFunctor U.ι x' = x ∧
            IsLocallyOfFinitePresentation B S hS (U.ι ≫ f)) ↔
      ∀ x : points B S hS X, IsFinitePresentationAt B S hS f x :=
    forall_congr' fun _ => ⟨fun ⟨U, hU, y, hy, hq⟩ => ⟨U, hU, ⟨y, hy⟩, hq⟩,
      fun ⟨U, hU, ⟨y, hy⟩, hq⟩ => ⟨U, hU, y, hy, hq⟩⟩
  tfae_have 1 ↔ 2 := (h.out 1 2).trans key
  tfae_have 1 ↔ 3 := h.out 1 3
  tfae_have 1 ↔ 4 := h.out 1 4
  tfae_have 1 ↔ 5 := h.out 1 5
  tfae_have 1 ↔ 6 := h.out 1 6
  tfae_have 1 ↔ 7 := h.out 1 7
  tfae_have 1 ↔ 8 := h.out 1 8
  tfae_have 1 ↔ 9 := h.out 1 9
  tfae_finish

/-- **Stacks 0410**, the equivalence of conditions (1) and (2): a morphism of algebraic spaces
over `S` is locally of finite presentation exactly when it is of finite presentation at every
point of its source. -/
theorem isLocallyOfFinitePresentation_iff_forall_isFinitePresentationAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallyOfFinitePresentation B S hS f ↔
      ∀ x : points B S hS X, IsFinitePresentationAt B S hS f x :=
  (isLocallyOfFinitePresentation_tfae B S hS hX hY f).out 1 2

end AlgebraicGeometry.Space

end
