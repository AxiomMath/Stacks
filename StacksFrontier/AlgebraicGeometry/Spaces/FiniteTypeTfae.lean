module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Characterization
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange

/-!
# Local finite type of a morphism of algebraic spaces is étale local

Tag 040Y is a nine-way equivalence for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`. Five of the nine conditions are reached here: `f` is locally of finite type (1);
the base change of `f` to every scheme over `Y` is locally of finite type (3); the base
change of `f` to *one* surjective étale scheme over `Y` is locally of finite type (5); the
composite of `f` with *one* surjective étale chart of `X` is locally of finite type (6); the
scheme morphism induced in every commuting square of étale charts is locally of finite type
(7); and the same for *one* such square whose chart of the source is surjective (8).

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_iff_holdsOnEveryEtaleChart` is the
  equivalence of conditions (1) and (7), which is the definition unfolded.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_iff_holdsOnSurjectiveEtaleChart` is the
  equivalence of conditions (1) and (8), that is Stacks 03MJ for local finite type.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_iff_forall_pullback_fst`,
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_iff_exists_etale_atlas_pullback` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_iff_exists_surjective_etale_source_chart`
  are the equivalences of condition (1) with conditions (3), (5) and (6).
* `AlgebraicGeometry.Space.isFiniteTypeAt_of_isLocallyOfFiniteType'` of
  `StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteAtPoint`, re-exported here, is the
  implication from condition (1) to condition (2).
* `AlgebraicGeometry.Space.locallyOfFiniteType_of_etale_square` and
  `AlgebraicGeometry.Space.locallyOfFiniteType_of_surjective_etale_square` are the two
  scheme-level consequences of étale locality of local finite type on which the equivalences
  rest.

## Implementation notes

`AlgebraicGeometry.Space.IsLocallyOfFiniteType` is literally condition (7), the
every-étale-chart condition of Stacks 03MJ, so conditions (1) and (7) are the same
statement and their equivalence is `Iff.rfl`.

The equivalence of (1) and (8) is the content of Stacks 03MJ. It is not obtained from
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`, even though the witness
of `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` that it asks for is now available as
`AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_locallyOfFiniteType`: that equivalence also
asks for both the source and the target to be algebraic spaces, and (8) ⇒ (1) needs neither.
What the argument uses instead are the two square lemmas
`AlgebraicGeometry.Space.locallyOfFiniteType_of_etale_square` and
`AlgebraicGeometry.Space.locallyOfFiniteType_of_surjective_etale_square`, which are parts (c)
and (d) of Stacks 04R1 instantiated at that witness and carry no algebraicity hypothesis. So
the only algebraicity used in (8) ⇒ (1) is the representability contained in the given charts:
no hypothesis on the source or the target is needed for that direction.

Conditions (3) and (5) are compared with (8) rather than with (1) directly: the surjective
étale chart square is assembled out of a chart of the target, an atlas of the fibre product
and the universal property of the fibre product, and the fibre product is an algebraic space
by Stacks 02X2, `AlgebraicGeometry.isAlgebraicSpace_pullback`, which is why those two
equivalences carry algebraicity hypotheses on both `X` and `Y`. The forward implication
(1) ⇒ (3) is Stacks 03XH, base change of local finite type.

Condition (6) does *not* go through (8), and
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_exists_surjective_etale_source_chart`
therefore needs no algebraicity at all: an arbitrary chart square of `f` is pulled back along
the given chart `φ` of the source, which turns it into a chart square of `φ ≫ f` over the
same chart of the target, and the descent lemma removes the surjective étale morphism that
appears in front of the morphism of the site. Algebraicity of `X` and `Y` re-enters only in
the forward implication (1) ⇒ (6), which uses an atlas of `X` together with Stacks 06LT and
the composition of Stacks 03XG.

Condition (4) — the same as (3) for affine schemes over `Y` — and condition (9), the Zariski
form, are not treated. The missing step for (4) is that an algebraic space has no affine
surjective étale chart in general, only one which is a disjoint union of affines (Stacks
03FX), so (4) ⇒ (8) needs local finite type to be glued over the summands rather than read
off one chart. Condition (2) is reached only in the direction (1) ⇒ (2): the converse needs
local finite type to be glued from open subspaces covering the source.

## References

* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 06LT](https://stacks.math.columbia.edu/tag/06LT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Two consequences of étale locality of local finite type -/

/-- Local finite type passes to the morphism induced in a commuting square of étale
morphisms of schemes over a morphism which is locally of finite type.

This is part (c) of the every-étale-diagram characterization of Stacks 04R1, instantiated at
`AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_locallyOfFiniteType`. -/
theorem locallyOfFiniteType_of_etale_square {X₀ Y₀ U V : Scheme.{u}}
    {f : X₀ ⟶ Y₀} {a : U ⟶ X₀} {b : V ⟶ Y₀} {k : U ⟶ V}
    (ha : Etale a) (hb : Etale b) (hcomm : k ≫ b = a ≫ f)
    (hf : LocallyOfFiniteType f) : LocallyOfFiniteType k :=
  (IsEtaleLocalOnSourceAndTarget.iff_forall_etale_diagrams f
    isEtaleLocalOnSourceAndTarget_locallyOfFiniteType).mp hf a b k ha hb hcomm

/-- Local finite type descends from the morphism induced in a commuting square of étale
morphisms of schemes whose morphism of sources is in addition surjective.

This is part (d) of the one-surjective-étale-diagram characterization of Stacks 04R1,
instantiated at `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_locallyOfFiniteType`. -/
theorem locallyOfFiniteType_of_surjective_etale_square {X₀ Y₀ U V : Scheme.{u}}
    {f : X₀ ⟶ Y₀} {a : U ⟶ X₀} {b : V ⟶ Y₀} {k : U ⟶ V}
    (hsurj : Surjective a) (ha : Etale a) (hb : Etale b) (hcomm : k ≫ b = a ≫ f)
    (hk : LocallyOfFiniteType k) : LocallyOfFiniteType f :=
  (IsEtaleLocalOnSourceAndTarget.iff_exists_surjective_etale_diagram f
    isEtaleLocalOnSourceAndTarget_locallyOfFiniteType).mpr
      ⟨U, V, a, b, k, ha, hb, hsurj.surj, hcomm, hk⟩

/-! ### Conditions (7) and (8) -/

/-- If `O` satisfies a property of schemes, so does the projection `fst'` of the represented
pullback of `O` along a relatively representable `R`. -/
private theorem property_map_fst'_of_presheaf {P : MorphismProperty Scheme.{u}}
    {U₀ U' : BigFppfOver B S hS} {R : yoneda.obj U₀ ⟶ X} {O : yoneda.obj U' ⟶ X}
    (hR : yoneda.relativelyRepresentable R)
    (hO : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf O) :
    P ((BigFppfOver.toScheme B S hS).map (hR.fst' O)) :=
  hO.property R (yoneda.map (hR.snd O)) (hR.fst' O) (hR.isPullback' O).flip

/-- **Stacks 040Y, conditions (1) and (7).** A morphism of algebraic spaces over `S` is
locally of finite type exactly when the scheme morphism induced in every commuting square of
étale charts of it is locally of finite type. This is
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` unfolded. -/
@[stacks 040Y "conditions (1) and (7)"]
theorem isLocallyOfFiniteType_iff_holdsOnEveryEtaleChart (f : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS f ↔
      HoldsOnEveryEtaleChart B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f :=
  Iff.rfl

/-- **Stacks 040Y, condition (8) implies condition (1).** A morphism of algebraic spaces over
`S` which is locally of finite type on one commuting square of étale charts whose chart of
the source is surjective is locally of finite type.

This is the implication of Stacks 03MJ for local finite type, carried out with the two square
lemmas of this file in place of a witness of
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget`. Neither the source nor the target has to
be an algebraic space: the only representability used is the one contained in the given
charts. -/
theorem isLocallyOfFiniteType_of_holdsOnSurjectiveEtaleChart {f : X ⟶ Y}
    (h : HoldsOnSurjectiveEtaleChart B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f) :
    IsLocallyOfFiniteType B S hS f := by
  set T := BigFppfOver.toScheme B S hS with hT
  obtain ⟨U, V, a, b, k, ha, hb, haSurj, hab, hPab⟩ := h
  intro U' V' a' b' h' ha' hb' hab'
  have hw : yoneda.map (ha'.rep.fst' a) ≫ a' = yoneda.map (ha'.rep.snd a) ≫ a :=
    (ha'.rep.isPullback' a).w
  have hu₀ : Etale (T.map (ha'.rep.snd a)) := ha'.property_snd a
  have hu : Etale (T.map (ha'.rep.fst' a)) := property_map_fst'_of_presheaf B S hS ha'.rep ha
  have huSurj : Surjective (T.map (ha'.rep.fst' a)) :=
    property_map_fst'_of_presheaf B S hS ha'.rep haSurj
  have hv₀ : Etale (T.map (hb.rep.snd b')) := hb.property_snd b'
  have hv : Etale (T.map (hb.rep.fst' b')) := property_map_fst'_of_presheaf B S hS hb.rep hb'
  have hcompat : yoneda.map (ha'.rep.snd a ≫ k) ≫ b =
      yoneda.map (ha'.rep.fst' a ≫ h') ≫ b' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hab, hab', ← Category.assoc, ← Category.assoc, hw]
  have hk : hb.rep.lift' (ha'.rep.snd a ≫ k) (ha'.rep.fst' a ≫ h') hcompat ≫
      hb.rep.fst' b' = ha'.rep.snd a ≫ k := hb.rep.lift'_fst _ _ _
  have hk₀ : hb.rep.lift' (ha'.rep.snd a ≫ k) (ha'.rep.fst' a ≫ h') hcompat ≫
      hb.rep.snd b' = ha'.rep.fst' a ≫ h' := hb.rep.lift'_snd _ _ _
  have hPk : LocallyOfFiniteType (T.map (hb.rep.lift'
      (ha'.rep.snd a ≫ k) (ha'.rep.fst' a ≫ h') hcompat)) :=
    locallyOfFiniteType_of_etale_square hu₀ hv
      (by simpa only [Functor.map_comp] using congrArg T.map hk) hPab
  exact locallyOfFiniteType_of_surjective_etale_square huSurj hu hv₀
    (by simpa only [Functor.map_comp] using congrArg T.map hk₀) hPk

/-- **Stacks 040Y, condition (1) implies condition (8).** A morphism of algebraic spaces over
`S` which is locally of finite type is locally of finite type on some commuting square of
étale charts whose chart of the source is surjective.

The square is produced from an atlas of the target by
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`, and the every-chart
condition is instantiated at it. -/
theorem holdsOnSurjectiveEtaleChart_of_isLocallyOfFiniteType
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) :
    HoldsOnSurjectiveEtaleChart B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact ⟨U, V, p, b, α, hpEtale, hbEtale, hpSurj, hcomm.symm,
    hf U V p b α hpEtale hbEtale hcomm.symm⟩

/-- **Stacks 040Y, conditions (1) and (8).** A morphism of algebraic spaces over `S` is
locally of finite type exactly when it is locally of finite type on one commuting square of
étale charts whose chart of the source is surjective. -/
@[stacks 040Y "conditions (1) and (8)"]
theorem isLocallyOfFiniteType_iff_holdsOnSurjectiveEtaleChart
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS f ↔
      HoldsOnSurjectiveEtaleChart B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f :=
  ⟨holdsOnSurjectiveEtaleChart_of_isLocallyOfFiniteType B S hS hX hY,
    isLocallyOfFiniteType_of_holdsOnSurjectiveEtaleChart B S hS⟩

/-! ### Conditions (3) and (5): base changes to schemes over the target -/

/-- **Stacks 040Y, condition (1) implies condition (3).** The base change of a morphism of
algebraic spaces over `S` which is locally of finite type to any scheme over its target is
locally of finite type. This is Stacks 03XH for the cartesian square of the base change. -/
@[stacks 040Y "condition (1) implies condition (3)"]
theorem isLocallyOfFiniteType_pullback_fst
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (V : BigFppfOver B S hS)
    (g : yoneda.obj V ⟶ Y) :
    IsLocallyOfFiniteType B S hS (pullback.fst g f) :=
  IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback g f) hX hY hf

/-- **Stacks 040Y, condition (5) implies condition (8).** If the base change of
`f : X ⟶ Y` to one surjective étale scheme over `Y` is locally of finite type, then `f` is
locally of finite type on a commuting square of étale charts whose chart of the source is
surjective.

An atlas `d` of the fibre product `V ×_Y X` provides the chart square: the morphism of the
site under it is the one Yoneda-corresponding to `d ≫ pullback.fst`, its chart of the source
is `d ≫ pullback.snd`, which is surjective and étale because `pullback.snd` is a base change
of the atlas `b` of the target, and the every-chart hypothesis on the base change is
instantiated at `d` over the identity chart of `h_V`. -/
theorem holdsOnSurjectiveEtaleChart_of_exists_etale_atlas_pullback
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : ∃ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) b ∧
      IsLocallyOfFiniteType B S hS (pullback.fst b f)) :
    HoldsOnSurjectiveEtaleChart B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f := by
  obtain ⟨V, b, hbS, hbE, hlft⟩ := h
  have hmulE := isMultiplicative_presheaf_etale B S hS
  have _ := surjective_isStableUnderComposition.{u}
  have _ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hW : IsAlgebraicSpace B S hS (pullback b f) :=
    isAlgebraicSpace_pullback B S hS b f (isAlgebraicSpace_yoneda B S hS V) hX hY
  obtain ⟨U, d, hdS, hdE⟩ := hW.exists_atlas
  obtain ⟨α, hα⟩ : ∃ α : U ⟶ V, yoneda.map α = d ≫ pullback.fst b f :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hsndS := presheaf_of_isPullback B S hS (IsPullback.of_hasPullback b f) hbS
  have hsndE := presheaf_of_isPullback B S hS (IsPullback.of_hasPullback b f) hbE
  have hPα : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) :=
    hlft U V d (𝟙 (yoneda.obj V)) α hdE (hmulE.id_mem _) (by rw [hα]; simp)
  refine ⟨U, V, d ≫ pullback.snd b f, b, α,
    MorphismProperty.comp_mem _ _ _ hdE hsndE, hbE,
    MorphismProperty.comp_mem _ _ _ hdS hsndS, ?_, hPα⟩
  rw [hα, Category.assoc, Category.assoc, pullback.condition]

/-- **Stacks 040Y, conditions (1) and (5).** A morphism of algebraic spaces over `S` is
locally of finite type exactly when its base change to some surjective étale scheme over its
target is locally of finite type. -/
@[stacks 040Y "conditions (1) and (5)"]
theorem isLocallyOfFiniteType_iff_exists_etale_atlas_pullback
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) b ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) b ∧
        IsLocallyOfFiniteType B S hS (pullback.fst b f) := by
  refine ⟨fun hf ↦ ?_, fun h ↦ isLocallyOfFiniteType_of_holdsOnSurjectiveEtaleChart B S hS
    (holdsOnSurjectiveEtaleChart_of_exists_etale_atlas_pullback B S hS hX hY h)⟩
  obtain ⟨V, b, hbS, hbE⟩ := hY.exists_atlas
  exact ⟨V, b, hbS, hbE, isLocallyOfFiniteType_pullback_fst B S hS hX hY hf V b⟩

/-- **Stacks 040Y, conditions (1) and (3).** A morphism of algebraic spaces over `S` is
locally of finite type exactly when its base change to every scheme over its target is
locally of finite type. -/
@[stacks 040Y "conditions (1) and (3)"]
theorem isLocallyOfFiniteType_iff_forall_pullback_fst
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS f ↔
      ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsLocallyOfFiniteType B S hS (pullback.fst g f) := by
  refine ⟨fun hf ↦ isLocallyOfFiniteType_pullback_fst B S hS hX hY hf, fun h ↦ ?_⟩
  obtain ⟨V, b, hbS, hbE⟩ := hY.exists_atlas
  exact (isLocallyOfFiniteType_iff_exists_etale_atlas_pullback B S hS hX hY f).2
    ⟨V, b, hbS, hbE, h V b⟩

/-! ### Condition (6): one surjective étale chart of the source -/

/-- **Stacks 040Y, condition (6) implies condition (1).** If `f : X ⟶ Y` becomes locally of
finite type after precomposition with one surjective étale chart `φ` of `X`, then `f` is
locally of finite type.

Condition (8) is bypassed, and with it every algebraicity hypothesis: an arbitrary chart
square of `f` is pulled back along `φ`, which produces a chart square of `φ ≫ f` over the
*same* chart of the target whose morphism of the site is the given one precomposed with a
surjective étale morphism, and local finite type descends along the latter. The fibre product
used is the represented one supplied by relative representability of `φ`. -/
theorem isLocallyOfFiniteType_of_exists_surjective_etale_source_chart {f : X ⟶ Y}
    (h : ∃ (U₀ : BigFppfOver B S hS) (φ : yoneda.obj U₀ ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ ∧
      IsLocallyOfFiniteType B S hS (φ ≫ f)) :
    IsLocallyOfFiniteType B S hS f := by
  set T := BigFppfOver.toScheme B S hS with hT
  obtain ⟨U₀, φ, hφS, hφE, hlft⟩ := h
  intro U' V' a' b' h' ha' hb' hab'
  have hsq := hφE.rep.isPullback' a'
  have hτS : Surjective (T.map (hφE.rep.snd a')) := hφS.property_snd a'
  have hτE : Etale (T.map (hφE.rep.snd a')) := hφE.property_snd a'
  have hψE : Etale (T.map (hφE.rep.fst' a')) := property_map_fst'_of_presheaf B S hS hφE.rep ha'
  have hψchart := (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@Etale.{u} : MorphismProperty Scheme.{u}) (hφE.rep.fst' a')).2 hψE
  have hcomm : yoneda.map (hφE.rep.snd a' ≫ h') ≫ b' =
      yoneda.map (hφE.rep.fst' a') ≫ (φ ≫ f) := by
    rw [Functor.map_comp, Category.assoc, hab', ← Category.assoc, ← Category.assoc, hsq.w]
  have hcompP := hlft _ V' (yoneda.map (hφE.rep.fst' a')) b'
    (hφE.rep.snd a' ≫ h') hψchart hb' hcomm
  rw [Functor.map_comp] at hcompP
  exact locallyOfFiniteType_of_comp_surjective_etale _ _ hτS hτE hcompP

/-- **Stacks 040Y, conditions (1) and (6).** A morphism of algebraic spaces over `S` is
locally of finite type exactly when its composite with some surjective étale chart of its
source is locally of finite type.

For the forward direction an atlas of the source is étale, hence locally of finite type by
Stacks 06LT, and local finite type is stable under composition by Stacks 03XG. -/
@[stacks 040Y "conditions (1) and (6)"]
theorem isLocallyOfFiniteType_iff_exists_surjective_etale_source_chart
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS f ↔
      ∃ (U₀ : BigFppfOver B S hS) (φ : yoneda.obj U₀ ⟶ X),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) φ ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) φ ∧
        IsLocallyOfFiniteType B S hS (φ ≫ f) := by
  refine ⟨fun hf ↦ ?_, isLocallyOfFiniteType_of_exists_surjective_etale_source_chart B S hS⟩
  obtain ⟨U₀, φ, hφS, hφE⟩ := hX.exists_atlas
  exact ⟨U₀, φ, hφS, hφE, isLocallyOfFiniteType_comp' B S hS φ f hX hY
    (isLocallyOfFiniteType_of_isEtale' B S hS φ (isEtale_of_presheaf_etale B S hS hφE)) hf⟩

end AlgebraicGeometry.Space

end
