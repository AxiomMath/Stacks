module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Characterization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit

/-!
# The hypothesis-free halves of the étale-chart comparison

A property `P` of morphisms of schemes is transferred to a morphism `f` of algebraic spaces
over `S` in two ways: by asking that the morphism of schemes underlying *every* commuting
square of étale charts of `f` has `P`, which is
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, or by exhibiting *one* such square whose
chart of the source is in addition surjective, which is
`AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart`. That the two agree when `P` is étale
local on the source and target — Stacks 03MJ, in all three of its forms — is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartLocality.lean`, which this file imports and
re-exports.

What is proved here are the implications of 03MJ that hold with *no* hypothesis on `P` and no
algebraicity of the source or target, which the equivalences there do not expose separately.

## Main results

* `AlgebraicGeometry.Space.presheaf_etale_of_iso`: an isomorphism of presheaves is an étale
  chart, because every represented base change of it is an isomorphism of schemes.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_surjectiveChart`: the implication
  (2) ⇒ (1), which uses no algebraicity of the source or the target at all — only the
  representability contained in the given charts.
* `AlgebraicGeometry.Space.map_of_holdsOnEveryEtaleChart_of_representable`: for a morphism of
  representable spaces, the every-chart condition implies `P` for the induced morphism of
  schemes, with no hypothesis on `P`.

## Implementation notes

For (2) ⇒ (1): given the distinguished square `(a, b, h)` with `a` surjective and an
arbitrary square `(a', b', h')`, the two source charts are compared through the fibre product
`W` of `a'` and `a`, and the two target charts through the fibre product `Z` of `b` and `b'`.
The projections `W ⟶ U'` and `W ⟶ U` are étale because `a` and `a'` are, and `W ⟶ U'` is
surjective because `a` is; likewise for the projections of `Z`. The universal property of `Z`
produces `k : W ⟶ Z` over both `h` and `h'`. Now `P (T.map h)` gives `P (T.map k)` by the
every-étale-diagram characterization of Stacks 04R1 part (c), and `P (T.map k)` gives
`P (T.map h')` by the one-surjective-étale-diagram characterization of Stacks 04R1 part (d).
Only these two characterizations use étale locality, and they are what the hypothesis
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` is for: without some such hypothesis the
equivalence fails, exactly as recorded for the one-way implication of
`AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp`.

`map_of_holdsOnEveryEtaleChart_of_representable` instantiates the every-chart condition at the
square formed by the two Yoneda representations, which is a square of étale charts by
`presheaf_etale_of_iso`.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R1](https://stacks.math.columbia.edu/tag/04R1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The equivalence of conditions (1) and (2) -/

/-- **Stacks 03MJ, condition (2) implies condition (1).** A property of morphisms of schemes
which is étale local on the source and target and holds on one commuting square of étale
charts of a morphism of algebraic spaces over `S` whose chart of the source is surjective
holds on every such square.

Neither the source nor the target has to be an algebraic space: the only representability
used is the one contained in the given charts. -/
theorem holdsOnEveryEtaleChart_of_surjectiveChart
    (hP : IsEtaleLocalOnSourceAndTarget P) {f : F ⟶ G}
    (hchart : HoldsOnSurjectiveEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P f := by
  set T := BigFppfOver.toScheme B S hS with hT
  obtain ⟨U, V, a, b, h, ha, hb, haSurj, hab, hPab⟩ := hchart
  intro U' V' a' b' h' ha' hb' hab'
  have hw : yoneda.map (ha'.rep.fst' a) ≫ a' = yoneda.map (ha'.rep.snd a) ≫ a :=
    (ha'.rep.isPullback' a).w
  have hu₀ : Etale (T.map (ha'.rep.snd a)) :=
    ha'.property a (yoneda.map (ha'.rep.fst' a)) (ha'.rep.snd a) (ha'.rep.isPullback' a)
  have hu : Etale (T.map (ha'.rep.fst' a)) :=
    ha.property a' (yoneda.map (ha'.rep.snd a)) (ha'.rep.fst' a)
      (ha'.rep.isPullback' a).flip
  have huSurj : Surjective (T.map (ha'.rep.fst' a)) :=
    haSurj.property a' (yoneda.map (ha'.rep.snd a)) (ha'.rep.fst' a)
      (ha'.rep.isPullback' a).flip
  have hv₀ : Etale (T.map (hb.rep.snd b')) :=
    hb.property b' (yoneda.map (hb.rep.fst' b')) (hb.rep.snd b') (hb.rep.isPullback' b')
  have hv : Etale (T.map (hb.rep.fst' b')) :=
    hb'.property b (yoneda.map (hb.rep.snd b')) (hb.rep.fst' b')
      (hb.rep.isPullback' b').flip
  have hcompat : yoneda.map (ha'.rep.snd a ≫ h) ≫ b =
      yoneda.map (ha'.rep.fst' a ≫ h') ≫ b' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hab, hab', ← Category.assoc, ← Category.assoc, hw]
  have hk : hb.rep.lift' (ha'.rep.snd a ≫ h) (ha'.rep.fst' a ≫ h') hcompat ≫
      hb.rep.fst' b' = ha'.rep.snd a ≫ h := hb.rep.lift'_fst _ _ _
  have hk₀ : hb.rep.lift' (ha'.rep.snd a ≫ h) (ha'.rep.fst' a ≫ h') hcompat ≫
      hb.rep.snd b' = ha'.rep.fst' a ≫ h' := hb.rep.lift'_snd _ _ _
  have hPk : P (T.map (hb.rep.lift' (ha'.rep.snd a ≫ h)
      (ha'.rep.fst' a ≫ h') hcompat)) :=
    (IsEtaleLocalOnSourceAndTarget.iff_forall_etale_diagrams (T.map h) hP).mp hPab
      (T.map (ha'.rep.snd a)) (T.map (hb.rep.fst' b')) _ hu₀ hv
      (by simpa only [Functor.map_comp] using congrArg T.map hk)
  refine (IsEtaleLocalOnSourceAndTarget.iff_exists_surjective_etale_diagram
    (T.map h') hP).mpr ⟨_, _, T.map (ha'.rep.fst' a), T.map (hb.rep.snd b'), _, hu, hv₀,
    huSurj.surj, ?_, hPk⟩
  simpa only [Functor.map_comp] using congrArg T.map hk₀

/-! ### Comparison with a morphism of schemes -/

/-- The every-chart condition for a morphism of representable algebraic spaces over `S`
implies the property for the morphism of schemes corresponding to it under the Yoneda
representations: the two representations form a square of étale charts, and the condition is
instantiated at it. No hypothesis on `P` is needed for this implication. -/
theorem map_of_holdsOnEveryEtaleChart_of_representable
    [F.IsRepresentable] [G.IsRepresentable] (f : F ⟶ G)
    (hall : HoldsOnEveryEtaleChart B S hS P f) :
    P ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (F.reprW.hom ≫ f ≫ G.reprW.inv))) :=
  hall F.reprX G.reprX F.reprW.hom G.reprW.hom _
    (presheaf_etale_of_iso B S hS F.reprW) (presheaf_etale_of_iso B S hS G.reprW) (by simp)



end AlgebraicGeometry.Space

end
