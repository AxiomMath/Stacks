module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability

/-!
# Composition and cancellation of a local property of morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of continuous
homomorphisms between topological rings of a class `C`. **Stacks 0GBI** says that if `P` is
stable under composition in the sense of Situation 0GBH, then the equivalent conditions of
Stacks 0ANG pass from two composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of formal algebraic
spaces over `S` to the composite `g ∘ f`, and **Stacks 0GBM** says that if `P` has the
cancellation property of Situation 0GBL then they pass from `g ∘ f` and `g` to `f`. Remarks
0GBK and 0GBP are the variants for the Noetherian class; those two transfers are proved here
uniformly over all properties, but their tags are carried on the corresponding statements about
arrows of `WAdm^{Noeth}` in `StacksFrontier/Topology/Algebra/AdicTopology/LocalProperties.lean`.

Both proofs run over the same covering: an affine étale covering `{Z_k ⟶ Z}`, for each `k` an
affine étale covering `{Y_kj ⟶ Z_k ×_Z Y}`, and for each `k` and `j` an affine étale covering
`{X_kji ⟶ Y_kj ×_Y X}`. The arrows `X_kji ⟶ Y_kj` and `Y_kj ⟶ Z_k` of the class `C` carry `P`
by condition (1) of Stacks 0ANG, and the ring-level axiom turns them into `P` for the arrow
that condition (3) asks for — the composite `X_kji ⟶ Z_k` for Stacks 0GBI, the first factor
`X_kji ⟶ Y_kj` for Stacks 0GBM.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasFormalAlgebraicSpaceChartPullbacks`: the assertion of
  Stacks 0AJ3 for the fibre products of a morphism with the affine étale charts of its target.
* `AlgebraicGeometry.FormalSpace.ChartPropertyIsStableUnderComposition` and
  `AlgebraicGeometry.FormalSpace.ChartPropertyHasCancellation`: the axioms of Situations 0GBH
  and 0GBL read on morphisms of affine formal algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal`:
  **Stacks 0ANG**, condition (1) implies condition (2), with the fibre products supplied by the
  previous result instead of by hypothesis.
* `AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_chartFactorization_comp`: the covering
  of `X` with its two layers of chart factorizations constructed in the proofs of Stacks 0GBI
  and 0GBM.
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_comp` and
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp`: **Stacks 0GBI**,
  conditions (3) and (1) of Stacks 0ANG for the composite.
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_comp` and
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_comp`: **Stacks
  0GBM**, conditions (3) and (1) of Stacks 0ANG for the first factor.
* `AlgebraicGeometry.FormalSpace.transfersCompositionOnAffineEtaleDiagrams` and
  `AlgebraicGeometry.FormalSpace.transfersCancellationOnAffineEtaleDiagrams`: the Noetherian
  variants of Remarks 0GBK and 0GBP, the two transfers uniformly over every property of arrows
  of `WAdm^{Noeth}` admitting the relevant bundle.

## Implementation notes

The covering is built by the implications (1) ⟹ (2) ⟹ (3) of Stacks 0ANG applied to `g`,
which produce the covering `{Y_kj ⟶ Y}` of the intermediate space together with the
factorizations `Y_kj ⟶ Z_k ⟶ Z` and `P` on each `Y_kj ⟶ Z_k`, followed by one more layer of
coverings of the fibre products `Y_kj ×_Y X`. That those fibre products are formal algebraic
spaces is Stacks 0AJ3, so it is the hypothesis `HasFormalAlgebraicSpaceChartPullbacks`, as it
is in the implication (1) ⟹ (2) itself; it mentions neither `C` nor `P`.

The statements about a single pair of morphisms keep it. They assume formality only of the
final target `Z`, and discharging it for `f : X ⟶ Y` and `g : Y ⟶ Z` would mean assuming
formality of `X` and of `Y` too — a stronger hypothesis, not a discharge. Where a consumer does
have the source,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isRepresentableEtale` — the
étale case of Stacks 0AJ3 — discharges it with nothing assumed: a chart of the target is
representable étale, so its base change to the source is, and the étale case of Stacks 0AJI
settles the fibre product.
An earlier form of this file pointed instead at
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable`, the general
Stacks 0AJ3 of this library, which costs Stacks 0AIU and the set-theoretic condition of Stacks
0AIS; those are not needed for a chart.

The ring-level axiom enters only through morphisms of affine formal algebraic spaces, and
condition (1) of Stacks 0ANG quantifies over *presentations* of those morphisms by chart rings,
so passing from the axiom to the chart statement needs every chart to be presented by a ring of
the class `C` and every morphism between presented charts to be realized by a continuous
homomorphism — the anti-equivalence of Stacks 0AN0 together with the type of the spaces as in
Stacks 0AKY. The library carries Stacks 0AN0 only for charts already presented as formal
spectra by rings whose formal spectrum is known to be affine
(`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`), and
transporting that along the isomorphisms of condition (1) is not available, so the translated
axioms are the hypotheses `ChartPropertyIsStableUnderComposition` and
`ChartPropertyHasCancellation`. They stand in the same relation to Situations 0GBH and 0GBL as
`AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale` does to axiom (1) of
Situation 0CBA.

Passing from condition (3) back to condition (1) is the implication (3) ⟹ (1) of Stacks 0ANG,
carried as the hypothesis `AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryAffineEtaleDiagram`
exactly as in the base change transfer of Stacks 0GBG.

The predicates of `StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability` that the two
uniform transfers discharge quantify over *all* fppf sheaves, not only over the locally
Noetherian formal algebraic spaces that Stacks 0GBI and 0GBM are about, so the uniform
statements ask for the coverings of Definition 0AIM for every morphism; the single-pair
statements ask for them only where the source demands them. The fibre products of Stacks 0AJ3
are not asked for in the uniform statements: `hspace` already gives formality of every sheaf,
which is all that the discharge above needs.

## References

* [Stacks Project, Tag 0GBI](https://stacks.math.columbia.edu/tag/0GBI)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GBM](https://stacks.math.columbia.edu/tag/0GBM)
* [Stacks Project, Tag 0GBP](https://stacks.math.columbia.edu/tag/0GBP)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
* [Stacks Project, Tag 0GBH](https://stacks.math.columbia.edu/tag/0GBH)
* [Stacks Project, Tag 0GBL](https://stacks.math.columbia.edu/tag/0GBL)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJI](https://stacks.math.columbia.edu/tag/0AJI)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A family of morphisms of fppf sheaves obtained by composing a jointly locally surjective
family `(qⱼ : Gⱼ ⟶ X)` with a jointly locally surjective family over each of its sources is
again jointly locally surjective: each `Sigma.desc` is an epimorphism of sheaves of sets, and
the composite family cancels through the two of them in turn. -/
lemma isLocallySurjective_sigmaDesc_comp
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X : FppfSheaf B S hS} {J : Type (u + 1)} {G : J → FppfSheaf B S hS} (q : ∀ j, G j ⟶ X)
    {I : J → Type (u + 1)} {U : ∀ j, I j → FppfSheaf B S hS} (w : ∀ j i, U j i ⟶ G j)
    (hq : Sheaf.IsLocallySurjective (Sigma.desc q))
    (hw : ∀ j, Sheaf.IsLocallySurjective (Sigma.desc (w j))) :
    Sheaf.IsLocallySurjective (Sigma.desc fun p : Σ j, I j ↦ w p.1 p.2 ≫ q p.1) := by
  have := hq
  rw [Sheaf.isLocallySurjective_iff_epi]
  constructor
  intro Z g h hgh
  refine (cancel_epi (Sigma.desc q)).1 (Sigma.hom_ext _ _ fun j ↦ ?_)
  have := hw j
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_comp_desc]
  refine (cancel_epi (Sigma.desc (w j))).1 (Sigma.hom_ext _ _ fun i ↦ ?_)
  simpa only [← Category.assoc, Sigma.ι_comp_desc] using
    Sigma.ι (fun p : Σ j, I j ↦ U p.1 p.2) ⟨j, i⟩ ≫= hgh

/-- The assertion of **Stacks 0AJ3** for the fibre products formed in the proofs of Stacks
0ANG, 0GBI and 0GBM: the fibre product of a morphism with an affine étale chart of its target
is a formal algebraic space. -/
abbrev HasFormalAlgebraicSpaceChartPullbacks {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f)

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The composition axiom of **Situation 0GBH**, read on affine formal algebraic spaces through
the anti-equivalence of Stacks 0AN0: `P` passes from two composable morphisms of affine formal
algebraic spaces to their composite. -/
abbrev ChartPropertyIsStableUnderComposition : Prop :=
  ∀ {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : V ⟶ W),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsAffineFormalAlgebraicSpace B S hS W →
    HasPropertyOnAffineChartMap B S hS C P t → HasPropertyOnAffineChartMap B S hS C P s →
      HasPropertyOnAffineChartMap B S hS C P (t ≫ s)

/-- The cancellation property of **Situation 0GBL**, read on affine formal algebraic spaces
through the anti-equivalence of Stacks 0AN0: `P` passes from a composite of morphisms of affine
formal algebraic spaces together with its second factor to its first factor. -/
abbrev ChartPropertyHasCancellation : Prop :=
  ∀ {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : V ⟶ W),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsAffineFormalAlgebraicSpace B S hS W →
    HasPropertyOnAffineChartMap B S hS C P s →
    HasPropertyOnAffineChartMap B S hS C P (t ≫ s) →
      HasPropertyOnAffineChartMap B S hS C P t

/-- The covering constructed in the proofs of **Stacks 0GBI** and **Stacks 0GBM**: an affine
étale covering `{Uᵢ ⟶ X}` of the source of `f : X ⟶ Y`, together with factorizations
`Uᵢ ⟶ Vᵢ ⟶ Y` through affine étale charts of `Y` and `Vᵢ ⟶ Wᵢ ⟶ Z` through affine étale charts
of `Z`, with `P` on each `Vᵢ ⟶ Wᵢ`.

It is obtained from the implications (1) ⟹ (2) ⟹ (3) of Stacks 0ANG for `g`, which produce the
covering of `Y` and the factorizations of its members through charts of `Z`, followed by
coverings of the fibre products of those members with `X`. -/
theorem exists_affineEtaleCover_chartFactorization_comp
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    ∃ (I : Type (u + 1)) (U V W : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X)
      (t : ∀ i, U i ⟶ V i) (s : ∀ i, V i ⟶ W i) (v : ∀ i, V i ⟶ Y) (w : ∀ i, W i ⟶ Z),
      IsAffineEtaleCover B S hS U u ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (V i)) ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) ∧
        (∀ i, IsRepresentableEtale B S hS (v i)) ∧
        (∀ i, IsRepresentableEtale B S hS (w i)) ∧
        (∀ i, u i ≫ f = t i ≫ v i) ∧ (∀ i, v i ≫ g = s i ≫ w i) ∧
        ∀ i, HasPropertyOnAffineChartMap B S hS C P (s i) := by
  obtain ⟨J, V, v, hVcover, hfac⟩ :=
    hasPropertyAfterSourceCover_of_afterTargetCover B S hS C P g
      (hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS C P g hZ hpbg hg)
  choose W w s hWaffine hWetale hWsquare hWproperty using hfac
  choose I U m hUaffine hUetale hUsurj using fun j ↦
    (hpbf (V j) (v j) (hVcover.1 j) (hVcover.2.1 j)).2
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨Σ j, I j, fun p ↦ U p.1 p.2, fun p ↦ V p.1, fun p ↦ W p.1,
    fun p ↦ m p.1 p.2 ≫ pullback.snd (v p.1) f,
    fun p ↦ m p.1 p.2 ≫ pullback.fst (v p.1) f, fun p ↦ s p.1, fun p ↦ v p.1, fun p ↦ w p.1,
    ⟨fun p ↦ hUaffine p.1 p.2,
      fun p ↦ IsRepresentableEtale.comp B S hS (hUetale p.1 p.2)
        (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVcover.2.1 p.1)), ?_⟩,
    fun p ↦ hVcover.1 p.1, fun p ↦ hWaffine p.1, fun p ↦ hVcover.2.1 p.1,
    fun p ↦ hWetale p.1, fun p ↦ ?_, fun p ↦ hWsquare p.1, fun p ↦ hWproperty p.1⟩
  · exact Sheaf.isLocallySurjective_sigmaDesc_comp (fun j ↦ pullback.snd (v j) f) m
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVcover.2.2) hUsurj
  · rw [Category.assoc, Category.assoc, ← pullback.condition]

/-- **Stacks 0GBI**, in the form the covering of its proof produces: if `P` is stable under
composition on charts and `f : X ⟶ Y`, `g : Y ⟶ Z` satisfy condition (1) of Stacks 0ANG, then
the composite `g ∘ f` satisfies condition (3) of Stacks 0ANG.

Each member `Uᵢ ⟶ X` of the covering factors as `Uᵢ ⟶ Wᵢ ⟶ Z` through the chart `Wᵢ` of `Z`,
and `P` holds on `Uᵢ ⟶ Wᵢ` because it holds on `Uᵢ ⟶ Vᵢ` by condition (1) for `f` and on
`Vᵢ ⟶ Wᵢ` by condition (1) for `g`. -/
theorem hasPropertyAfterSourceCover_comp
    (hchart : ChartPropertyIsStableUnderComposition B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyAfterSourceCover B S hS C P (f ≫ g) := by
  obtain ⟨I, U, V, W, u, t, s, v, w, hUcover, hVaffine, hWaffine, hv, hw, hsq₁, hsq₂, hs⟩ :=
    exists_affineEtaleCover_chartFactorization_comp B S hS C P f g hZ hpbg hpbf hg
  refine ⟨I, U, u, hUcover, fun i ↦ ⟨W i, w i, t i ≫ s i, hWaffine i, hw i, ?_, ?_⟩⟩
  · rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]
  · exact hchart (t i) (s i) (hUcover.1 i) (hVaffine i) (hWaffine i)
      (hf (U i) (V i) (u i) (v i) (t i) (hUcover.1 i) (hVaffine i) (hUcover.2.1 i) (hv i)
        (hsq₁ i)) (hs i)

/-- **Stacks 0GBI.** Let `P` be a local property of arrows of the class `C` which is stable
under composition. If `f : X ⟶ Y` and `g : Y ⟶ Z` are morphisms of formal algebraic spaces over
`S` satisfying the equivalent conditions of Stacks 0ANG for `P`, then so does `g ∘ f`.

Condition (3) is what the covering of the proof gives; the passage back to condition (1) is the
implication (3) ⟹ (1) of Stacks 0ANG, carried as the hypothesis `h31`. -/
@[stacks 0GBI "condition (1) for the composite, granting the composition axiom of Situation \
0GBH read on charts through Stacks 0AN0 (hchart), the implication (3) ⟹ (1) of Stacks 0ANG \
(h31) and the fibre products of Stacks 0AJ3 (hpbf, hpbg)"]
theorem hasPropertyOnEveryAffineEtaleDiagram_comp
    (hchart : ChartPropertyIsStableUnderComposition B S hS C P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g) :=
  h31 _ (hasPropertyAfterSourceCover_comp B S hS C P hchart f g hZ hpbg hpbf hf hg)

/-- **Stacks 0GBM**, in the form the covering of its proof produces: if `P` has the
cancellation property on charts and `g ∘ f`, `g` satisfy condition (1) of Stacks 0ANG, then
`f : X ⟶ Y` satisfies condition (3) of Stacks 0ANG.

Each member `Uᵢ ⟶ X` of the covering factors as `Uᵢ ⟶ Vᵢ ⟶ Y` through the chart `Vᵢ` of `Y`,
and `P` holds on `Uᵢ ⟶ Vᵢ` by cancellation against `Vᵢ ⟶ Wᵢ`, which has `P` by condition (1)
for `g`, and `Uᵢ ⟶ Wᵢ`, which has `P` by condition (1) for `g ∘ f`. -/
theorem hasPropertyAfterSourceCover_of_comp
    (hchart : ChartPropertyHasCancellation B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyAfterSourceCover B S hS C P f := by
  obtain ⟨I, U, V, W, u, t, s, v, w, hUcover, hVaffine, hWaffine, hv, hw, hsq₁, hsq₂, hs⟩ :=
    exists_affineEtaleCover_chartFactorization_comp B S hS C P f g hZ hpbg hpbf hg
  refine ⟨I, U, u, hUcover, fun i ↦ ⟨V i, v i, t i, hVaffine i, hv i, hsq₁ i, ?_⟩⟩
  refine hchart (t i) (s i) (hUcover.1 i) (hVaffine i) (hWaffine i) (hs i)
    (hfg (U i) (W i) (u i) (w i) (t i ≫ s i) (hUcover.1 i) (hWaffine i) (hUcover.2.1 i)
      (hw i) ?_)
  rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]

/-- **Stacks 0GBM.** Let `P` be a local property of arrows of the class `C` with the
cancellation property. If `g ∘ f` and `g : Y ⟶ Z` satisfy the equivalent conditions of Stacks
0ANG for `P`, then so does `f : X ⟶ Y`.

Condition (3) is what the covering of the proof gives; the passage back to condition (1) is the
implication (3) ⟹ (1) of Stacks 0ANG, carried as the hypothesis `h31`. -/
@[stacks 0GBM "condition (1) for the first factor, granting the cancellation axiom of \
Situation 0GBL read on charts through Stacks 0AN0 (hchart), the implication (3) ⟹ (1) of \
Stacks 0ANG (h31) and the fibre products of Stacks 0AJ3 (hpbf, hpbg)"]
theorem hasPropertyOnEveryAffineEtaleDiagram_of_comp
    (hchart : ChartPropertyHasCancellation B S hS C P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P f :=
  h31 _ (hasPropertyAfterSourceCover_of_comp B S hS C P hchart f g hZ hpbg hpbf hfg hg)

/-- **The Noetherian variant of Stacks 0GBI, uniformly over all properties:** whenever `P` is a
local property of arrows of `WAdm^{Noeth}` stable under composition, condition (1) of
Stacks 0ANG transfers from `(f, P)` and `(g, P)` to `(g ∘ f, P)`.

The three inputs of the single-pair statement are asked of every property carrying the bundle
of Remark 0GBK, which is how that bundle supplies locality, and of every pair of morphisms. -/
theorem transfersCompositionOnAffineEtaleDiagrams
    (hchart : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsStableUnderCompositionNoetherian.{u} P →
        ChartPropertyIsStableUnderComposition B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hspace : ∀ Z : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS Z)
    (hpb : ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
      HasFormalAlgebraicSpaceChartPullbacks B S hS f) :
    ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.PropertyIsStableUnderCompositionNoetherian.{u} P →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) := by
  intro P hP _X _Y Z f g hf hg
  exact hasPropertyOnEveryAffineEtaleDiagram_comp B S hS _ P (hchart P hP)
    (h31 P hP.isLocal) f g (hspace Z) (hpb g) (hpb f) hf hg

/-- If every fppf sheaf is a formal algebraic space, the fibre products of a morphism with the
affine étale charts of its target are formal algebraic spaces. -/
private theorem hasFormalAlgebraicSpaceChartPullbacks_of_forall
    (hspace : ∀ Z : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS Z)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : HasFormalAlgebraicSpaceChartPullbacks B S hS f :=
  fun _V v _hV hv ↦
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS v f (hspace _) hv

/-- **The Noetherian variant of Stacks 0GBI, uniformly over all properties:** whenever `P` is a
local property of arrows of `WAdm^{Noeth}` stable under composition, condition (1) of
Stacks 0ANG transfers from `(f, P)` and `(g, P)` to `(g ∘ f, P)`.

The three inputs of the single-pair statement are asked of every property carrying the bundle
of Remark 0GBK, which is how that bundle supplies locality, and of every pair of morphisms. -/
theorem transfersCompositionOnAffineEtaleDiagrams_of_isLocalNoetherian
    (hchart : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsStableUnderCompositionNoetherian.{u} P →
        ChartPropertyIsStableUnderComposition B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hspace : ∀ Z : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS Z) :
    ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.PropertyIsStableUnderCompositionNoetherian.{u} P →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) := by
  intro P hP _X _Y _Z f g
  exact transfersCompositionOnAffineEtaleDiagrams B S hS hchart h31 hspace
    (hasFormalAlgebraicSpaceChartPullbacks_of_forall B S hS hspace) P hP f g

/-- **The Noetherian variant of Stacks 0GBM, uniformly over all properties:** whenever `P` is a
local property of arrows of `WAdm^{Noeth}` with the cancellation property, condition (1) of
Stacks 0ANG transfers from `(g ∘ f, P)` and `(g, P)` to `(f, P)`.

Locality is asked separately here, as in the statement of Remark 0GBP, because the cancellation
property of Situation 0GBL carries no locality field for the Noetherian class. -/
theorem transfersCancellationOnAffineEtaleDiagrams
    (hchart : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
      TopologicalRing.HasNoetherianCancellationProperty.{u} P →
        ChartPropertyHasCancellation B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hspace : ∀ Z : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS Z)
    (hpb : ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
      HasFormalAlgebraicSpaceChartPullbacks B S hS f) :
    ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
      TopologicalRing.HasNoetherianCancellationProperty.{u} P →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f := by
  intro P hlocal hcancel _X _Y Z f g hfg hg
  exact hasPropertyOnEveryAffineEtaleDiagram_of_comp B S hS _ P (hchart P hlocal hcancel)
    (h31 P hlocal) f g (hspace Z) (hpb g) (hpb f) hfg hg

/-- **The Noetherian variant of Stacks 0GBM, uniformly over all properties:** whenever `P` is a
local property of arrows of `WAdm^{Noeth}` with the cancellation property, condition (1) of
Stacks 0ANG transfers from `(g ∘ f, P)` and `(g, P)` to `(f, P)`.

Locality is asked separately here, as in the statement of Remark 0GBP, because the cancellation
property of Situation 0GBL carries no locality field for the Noetherian class. -/
theorem transfersCancellationOnAffineEtaleDiagrams_of_isLocalNoetherian
    (hchart : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
      TopologicalRing.HasNoetherianCancellationProperty.{u} P →
        ChartPropertyHasCancellation B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hspace : ∀ Z : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS Z) :
    ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
      TopologicalRing.HasNoetherianCancellationProperty.{u} P →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f := by
  intro P hlocal hcancel _X _Y _Z f g
  exact transfersCancellationOnAffineEtaleDiagrams B S hS hchart h31 hspace
    (hasFormalAlgebraicSpaceChartPullbacks_of_forall B S hS hspace) P hlocal hcancel f g

end AlgebraicGeometry.FormalSpace

end
