module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The chart restriction of a module is the identity-chart restriction of its étale pullback

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `M` be an
`𝒪_X`-module on the small étale site of `X` and let `V` be an étale scheme chart of `X`.  There
are two readings of "restrict `M` to the Zariski site of the scheme of `V`":
`AlgebraicGeometry.Space.restrictToChartScheme` at the chart `V` of `X`, and the same
construction at the *identity* chart of the algebraic space `AlgebraicGeometry.Space.chartSpace`
represented by `V`, applied to the étale pullback of `M` along the structure morphism of `V`.

This file proves that the two are **the same module**, not merely isomorphic ones, and draws the
three consequences that the pullback statement of Stacks 060S needs: Zariski quasi-coherence of
a chart restriction, its compatibility with base change along a morphism of charts, and its
compatibility with base change along a commuting square of charts over a morphism of algebraic
spaces.

## Main results

* `Stacks.SheafOfModules.pushforward_ulift_pushforward_id`: a direct image along `G`, pushed
  forward along `F` after the universe of its sections is raised, is the direct image along
  `F ⋙ G`.
* `AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback_idEtaleChart`: **the chart
  restriction of `M` at `V` is the identity-chart restriction of its étale pullback to the chart
  space of `V`.**
* `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_chartBaseChange`: **base change of the
  chart restriction along a morphism of étale charts.**
* `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_modulePullback_square`: **the
  base-change identity `(f^*G)|_U ≅ ψ^*(G|_V)` of Stacks 060S** at a commuting square of charts
  over a morphism `f : X ⟶ Y` of algebraic spaces.

## Implementation notes

**Why the identification is an equality.**  `AlgebraicGeometry.Space.restrictToChartScheme` is
the Zariski sheafification of the sections of the module restricted along
`AlgebraicGeometry.Space.openChartFunctor`, with scalars extended along
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` and the sections first raised to
`max u m` by `SheafOfModules.uliftForPresentation`.  Three things hold on the nose: the index
functor of the identity chart of the chart space, composed with
`AlgebraicGeometry.Space.smallEtalePostcomp` along the structure morphism, *is* the index functor
of the chart; the structure presheaf of the chart space *is* the restriction of the structure
presheaf of `X` along that postcomposition; and therefore the two change-of-scalars maps are the
same term.  The étale pullback `AlgebraicGeometry.Space.etaleModulePullback` is itself a
`CategoryTheory.SheafOfModules.pushforward` along the postcomposition with the identity as its
structure map, so what remains is that two presheaf pushforwards collapse to one — which is
`CategoryTheory.PresheafOfModules.pushforwardComp`, an `CategoryTheory.Iso.refl` — and that
raising the universe of the sections commutes with a pushforward.

**The collapse is stated for bare data.**  Instantiating it directly at the chart exhausts the
heartbeat budget: the definitional check then runs through the whole of
`restrictToChartScheme`.  `Stacks.SheafOfModules.pushforward_ulift_pushforward_id` is about four
bare pieces of data, so the check it performs is small, and
`AlgebraicGeometry.Space.restrictToChartScheme_eq_sheafification` — the definition of the chart
restriction, read back as an equation — is what lets it be applied under the sheafification by a
single `congrArg`.  The continuity instance of the postcomposition is passed positionally for
the same reason that `AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` takes its
own: the topologies of the chart space admit two spellings and instance search is syntactic.

**What the three consequences consume.**  Quasi-coherence is Descent, Proposition 03DX for the
scheme of the chart, in the form
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, reached through
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`; the two base changes are
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`, which is
stated for identity charts of represented algebraic spaces and is exactly what the equality
above makes applicable at an arbitrary chart.  The module comparisons that cross between the
inverse image of Stacks 03LU and étale restriction are Stacks 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, together with the composition
comparison `AlgebraicGeometry.Space.modulePullbackCompIso`; quasi-coherence of an inverse image
is Stacks 03GA.

**Only the existence of an isomorphism is produced by the two base-change statements**, as in
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`: the
module there is obtained from the counit of an equivalence of categories, so no canonicity of
the comparison is available, and none is needed by the consumers, local projectivity being
invariant under isomorphism.

No declaration here carries a `stacks` tag: these are inputs to Stacks 060Q and 060S, not
assertions of a tag, and the clauses of Stacks 03DX, 03GA, 03LU and 03LW used are already
covered in the tree.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 060Q](https://stacks.math.columbia.edu/tag/060Q)
* [Stacks Project, Tag 060S](https://stacks.math.columbia.edu/tag/060S)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe w m t v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {G : D ⥤ E} [hcont : G.IsContinuous K L]
    {R : CategoryTheory.Sheaf L RingCat.{w}}
    {F : C ⥤ D} {RC : Cᵒᵖ ⥤ RingCat.{w}}

/-- **A direct image along `G`, pushed forward along `F` after the universe of its sections is
raised, is the direct image along `F ⋙ G`.**

The structure map of the inner direct image is the identity, so the composite change of scalars
is the outer one and the two pushforwards collapse by
`CategoryTheory.PresheafOfModules.pushforwardComp`; raising the universe of the sections is
objectwise, so it commutes with a pushforward.  Both steps are definitional, and stating them
for bare data is what keeps the check they perform small enough to instantiate. -/
theorem pushforward_ulift_pushforward_id
    (ρ : RC ⟶ (F ⋙ G).op ⋙ R.val) (N : _root_.SheafOfModules.{m} R) :
    (PresheafOfModules.pushforward (F := F) ρ).obj
        (_root_.SheafOfModules.uliftForPresentation.{u₂, v₂, w, m, t}
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((G.sheafPushforwardContinuous RingCat.{w} K L).obj R))).obj N)).val
      = (PresheafOfModules.pushforward (F := F ⋙ G) ρ).obj
          (_root_.SheafOfModules.uliftForPresentation.{u₃, v₃, w, m, t} N).val := rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The definition of the chart restriction, read back as an equation**: the restriction of an
`𝒪_F`-module to the scheme of an étale chart is the Zariski sheafification of its sections
restricted along `AlgebraicGeometry.Space.openChartFunctor`, with scalars extended along
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` and raised to `max u m` beforehand.

This is `rfl`, and it is here so that an equality of the presheaves being sheafified can be
transported under the sheafification by `congrArg` without the elaborator having to unfold
`AlgebraicGeometry.Space.restrictToChartScheme` inside a larger definitional check. -/
theorem restrictToChartScheme_eq_sheafification
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, m} B S hS F hF) (U : SmallEtale B S hS F) :
    restrictToChartScheme B S hS F hF M U =
      (letI : HasSheafify (Opens.grothendieckTopology (chartScheme U))
          AddCommGrpCat.{max u m} := hasSheafifyEssentiallySmallSite _ _
       letI : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
          AddCommGrpCat.{max u m} :=
         GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
       (PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)).obj
         ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj
           (_root_.SheafOfModules.uliftForPresentation M).val)) := rfl

/-- **The restriction of an `𝒪_X`-module to the scheme of an étale chart `V` is the restriction,
along the identity chart, of its étale pullback to the algebraic space represented by `V`.**

No hypothesis on the module is needed and the two sides are equal, not merely isomorphic: the
index functor of the identity chart of the chart space, composed with postcomposition along the
structure morphism of `V`, is the index functor of `V`, and the two changes of scalars are the
same term, so the statement is the collapse of two pushforwards of presheaves of modules. -/
theorem restrictToChartScheme_etaleModulePullback_idEtaleChart
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, m} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    restrictToChartScheme B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2
        ((etaleModulePullback B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).obj M)
        (idEtaleChart B S hS (chartFppfObject B S hS X V))
      = restrictToChartScheme B S hS X.1 X.2 M V := by
  have key :
      (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS
            (chartSpace B S hS X V).1
            (idEtaleChart B S hS (chartFppfObject B S hS X V)))).obj
          (_root_.SheafOfModules.uliftForPresentation
            ((etaleModulePullback B S hS (chartToSpace B S hS X V)
              (isEtale_chartToSpace B S hS X V)).obj M)).val
        = (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 V)).obj
            (_root_.SheafOfModules.uliftForPresentation M).val :=
    Stacks.SheafOfModules.pushforward_ulift_pushforward_id
      (F := openChartFunctor B S hS (chartSpace B S hS X V).1
        (idEtaleChart B S hS (chartFppfObject B S hS X V)))
      (G := smallEtalePostcomp B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V))
      (K := (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1
        (chartSpace B S hS X V).2).J)
      (L := (smallEtaleRingedSite B S hS X.1 X.2).J)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (hcont := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS
        (chartToSpace B S hS X V) (isEtale_chartToSpace B S hS X V))
      (chartSchemeRestrictionRingHom B S hS X.1 V) M
  let : HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact congrArg
    (PresheafOfModules.sheafification (𝟙 (chartScheme V).ringCatSheaf.obj)).obj key

/-- The étale pullback of a quasi-coherent `𝒪_X`-module to a chart space is quasi-coherent: it
is the inverse image of Stacks 03LU along the structure morphism of the chart, by Stacks 03LW,
and the inverse image preserves quasi-coherence by Stacks 03GA. -/
theorem isQuasicoherentOnSite_etaleModulePullback_chartToSpace
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    ((etaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).app M)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X V) M hM)

/-- The étale pullback of `M` to the chart space of `V'` is the inverse image, along the
represented morphism of chart spaces, of its étale pullback to the chart space of `V`.

Both are inverse images of Stacks 03LU — by Stacks 03LW — along the two sides of
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`, so the comparison is the composition
comparison of Stacks 03LU. -/
noncomputable def modulePullbackChartMapEtaleModulePullbackIso
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)
    {V' V : SmallEtale B S hS X.1} (g : V' ⟶ V) :
    (modulePullback B S hS (chartMap B S hS X g)).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).obj M) ≅
      (etaleModulePullback B S hS (chartToSpace B S hS X V')
        (isEtale_chartToSpace B S hS X V')).obj M :=
  (modulePullback B S hS (chartMap B S hS X g)).mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).app M).symm ≪≫
    (modulePullbackCompIso B S hS (chartMap B S hS X g)
      (chartToSpace B S hS X V)).app M ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M)
      (chartMap_comp_chartToSpace B S hS X g)) ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V')
      (isEtale_chartToSpace B S hS X V')).app M

/-- A comparison of the étale pullbacks to the chart spaces over a morphism `ψ` of charts gives the
Zariski base change of chart restrictions, by the equality of the identity-chart restrictions. -/
private theorem nonempty_restrictToChartScheme_of_iso_etaleModulePullback
    {X Y : AlgebraicSpaces B S hS} (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (ψ : (chartFppfObject B S hS X U) ⟶ (chartFppfObject B S hS Y V))
    (N : Modules.{u, u} B S hS X.1 X.2)
    (e : (modulePullback B S hS (representedSpaceMap B S hS ψ)).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).obj G) ≅
      (etaleModulePullback B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).obj N) :
    Nonempty (restrictToChartScheme B S hS X.1 X.2 N U ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ψ)).obj
        (restrictToChartScheme B S hS Y.1 Y.2 G V)) := by
  obtain ⟨e'⟩ := nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent ψ
    ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
      (isEtale_chartToSpace B S hS Y V)).obj G)
    (isQuasicoherentOnSite_etaleModulePullback_chartToSpace B S hS Y G hG V)
  rw [← restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS Y G V,
    ← restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS X N U]
  exact ⟨((restrictToChartSchemeFunctor B S hS (chartSpace B S hS X U).1
      (chartSpace B S hS X U).2
      (idEtaleChart B S hS (chartFppfObject B S hS X U))).mapIso e).symm ≪≫ e'⟩

/-- **Base change of the chart restriction along a morphism of étale charts.**  For a
quasi-coherent `𝒪_X`-module `M` and a morphism `g : V' ⟶ V` of étale charts, the Zariski
pullback of `M|_V` along the morphism of chart schemes is `M|_{V'}`.

Both chart restrictions are identity-chart restrictions of étale pullbacks to the two chart
spaces, so this is
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent` at the
morphism of the underlying objects of the big fppf site, transported along the comparison of the
two étale pullbacks. -/
theorem nonempty_restrictToChartScheme_chartBaseChange
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) {V' V : SmallEtale B S hS X.1} (g : V' ⟶ V) :
    Nonempty ((Scheme.Modules.pullback (chartSchemeMap g)).obj
        (restrictToChartScheme B S hS X.1 X.2 M V) ≅
      restrictToChartScheme B S hS X.1 X.2 M V') := by
  obtain ⟨e⟩ := nonempty_restrictToChartScheme_of_iso_etaleModulePullback B S hS M hM V' V
    ((SmallEtale.toOver B S hS X.1).map g) M
    (modulePullbackChartMapEtaleModulePullbackIso B S hS X M g)
  exact ⟨e.symm⟩

variable {B S hS} in
/-- A morphism of the big fppf category which commutes with the structure morphisms of an étale
chart of `X` and an étale chart of `Y` through `f` represents a morphism of the chart spaces over
`f`: a morphism of algebraic spaces is determined by its underlying morphism of presheaves. -/
theorem representedSpaceMap_comp_chartToSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (ψ : (chartFppfObject B S hS X U) ⟶ (chartFppfObject B S hS Y V))
    (hsq : U.1.hom ≫ f.hom = yoneda.map ψ ≫ V.1.hom) :
    representedSpaceMap B S hS ψ ≫ chartToSpace B S hS Y V =
      chartToSpace B S hS X U ≫ f :=
  ObjectProperty.hom_ext _ hsq.symm

/-- The étale pullback to the chart space of `U` of the inverse image `f^*G` is the inverse image
along `ψ` of the étale pullback of `G` to the chart space of `V`.

Both are inverse images of Stacks 03LU of `G` along the two sides of
`AlgebraicGeometry.Space.representedSpaceMap_comp_chartToSpace`, read through Stacks 03LW at the
two étale structure morphisms, so the comparison is the composition comparison of Stacks 03LU
used once on each side. -/
noncomputable def modulePullbackSquareEtaleModulePullbackIso
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (ψ : (chartFppfObject B S hS X U) ⟶ (chartFppfObject B S hS Y V))
    (hsq : U.1.hom ≫ f.hom = yoneda.map ψ ≫ V.1.hom) :
    (modulePullback B S hS (representedSpaceMap B S hS ψ)).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).obj G) ≅
      (etaleModulePullback B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).obj ((modulePullback B S hS f).obj G) :=
  (modulePullback B S hS (representedSpaceMap B S hS ψ)).mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).app G).symm ≪≫
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS ψ)
      (chartToSpace B S hS Y V)).app G ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS k).obj G)
      (representedSpaceMap_comp_chartToSpace f U V ψ hsq)) ≪≫
    ((modulePullbackCompIso B S hS (chartToSpace B S hS X U) f).app G).symm ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).app ((modulePullback B S hS f).obj G)

/-- **The base-change identity `(f^*G)|_U ≅ ψ^*(G|_V)` which the proof of Stacks 060S uses.**
For a morphism `f : X ⟶ Y` of algebraic spaces, a quasi-coherent `𝒪_Y`-module `G`, étale charts
`U` of `X` and `V` of `Y` and a morphism `ψ` of their underlying objects making the square
commute, the restriction of `f^*G` to the scheme of `U` is the Zariski pullback along `ψ` of the
restriction of `G` to the scheme of `V`.

This is `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`
at `ψ`, both chart restrictions being identity-chart restrictions of étale pullbacks, with the
two inverse images of `G` over the square compared by
`AlgebraicGeometry.Space.modulePullbackSquareEtaleModulePullbackIso`. -/
theorem nonempty_restrictToChartScheme_modulePullback_square
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (ψ : (chartFppfObject B S hS X U) ⟶ (chartFppfObject B S hS Y V))
    (hsq : U.1.hom ≫ f.hom = yoneda.map ψ ≫ V.1.hom) :
    Nonempty (restrictToChartScheme B S hS X.1 X.2 ((modulePullback B S hS f).obj G) U ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ψ)).obj
        (restrictToChartScheme B S hS Y.1 Y.2 G V)) := by
  exact nonempty_restrictToChartScheme_of_iso_etaleModulePullback B S hS G hG U V ψ _
    (modulePullbackSquareEtaleModulePullbackIso B S hS f G U V ψ hsq)

end AlgebraicGeometry.Space

end
