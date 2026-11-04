module

public import Mathlib.CategoryTheory.Limits.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# The chart condition for a structural morphism descends along an fppf cover

Let `S` be a scheme contained in a big fppf site `B` and let `F` be a presheaf on the big fppf
site of `S`. The every-étale-chart condition of Stacks 03MJ for the structural morphism
`F ⟶ *` of `F` — that is, `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` applied to the unique
morphism to the terminal presheaf — can be checked after base change to a single object `T₀` of
the site whose structural morphism of schemes is flat, surjective and locally of finite
presentation, i.e. after an fppf covering of the base by one scheme. The property of morphisms
of schemes being tested has to be fpqc local on the target and inherited by the first factor of
a composite; étale locality on the source and target, the standing hypothesis of Stacks 03MJ, is
*not* needed.

## Main definitions

* `AlgebraicGeometry.Space.yonedaTerminalIso`: the Yoneda presheaf of the terminal object of
  the big fppf site of `S` is the terminal presheaf.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`: for a morphism of the site,
  the every-étale-chart condition of Stacks 03MJ is equivalent to the tested property of the
  underlying morphism of schemes.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isTerminal`: the every-étale-chart
  condition for a morphism into a terminal presheaf does not depend on which terminal presheaf
  is used.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_terminal_of_fppfCover`: the every-étale-chart
  condition for the structural morphism of a presheaf descends along an fppf covering of the base
  by one scheme.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_terminal_of_fppfCover`: the same for local
  finite type.

## Implementation notes

Stacks 041S, that local finite type is fppf local on the base for morphisms of *algebraic
spaces*, quantified over all fppf coverings, is more general than the one-member,
structural-morphism, chart-level case proved here.

The hypotheses on the covering are stated for
`(BigFppfOver.toScheme B S hS).map (terminal.from T₀)`, the image under the forgetful functor of
the unique morphism of the site to its terminal object, rather than for the structural morphism
`B.inclusion.map T₀.hom` to `S`. The two agree up to the isomorphism
`AlgebraicGeometry.Space.toSchemeTerminalIso`, which identifies the underlying scheme of the
terminal object of the site with `S`; `AlgebraicGeometry.Space.toScheme_map_terminal_from` is
that comparison.

The fibre product of the base change is formed in the site, while the structural morphism is
`CategoryTheory.Limits.terminal.from` in the presheaf category; the two are compared through
`AlgebraicGeometry.Space.yonedaTerminalIso`.

No hypothesis that `F` is an algebraic space is needed: the base change happens inside the site
and the only facts used about charts are that `CategoryTheory.MorphismProperty.presheaf` is
stable under base change and that the identity of an object of the site is an étale chart of its
Yoneda presheaf.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 041S](https://stacks.math.columbia.edu/tag/041S)
* [Stacks Project, Tag 02KX](https://stacks.math.columbia.edu/tag/02KX)
* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity of an object of the big fppf site of `S` is an étale chart of its Yoneda
presheaf. -/
theorem presheaf_yoneda_map_id_etale (V : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 V)) := by
  refine (presheaf_yoneda_map_etale_iff B S hS (𝟙 V)).2 ?_
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- For a morphism `k` of the big fppf site of `S` and a property `P` of morphisms of schemes
which is étale local on the source and target, the every-étale-chart condition of Stacks 03MJ
for `yoneda.map k` is equivalent to `P` for the underlying morphism of schemes. -/
theorem holdsOnEveryEtaleChart_yoneda_map_iff {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {V U : BigFppfOver B S hS} (k : V ⟶ U) :
    HoldsOnEveryEtaleChart B S hS P (yoneda.map k) ↔
      P ((BigFppfOver.toScheme B S hS).map k) := by
  refine ⟨fun h => ?_, holdsOnEveryEtaleChart_yoneda_map B S hS hP k⟩
  exact h V U (yoneda.map (𝟙 V)) (yoneda.map (𝟙 U)) k
    (presheaf_yoneda_map_id_etale B S hS V) (presheaf_yoneda_map_id_etale B S hS U) (by simp)

/-- The Yoneda presheaf of the terminal object of the big fppf site of `S` is terminal. -/
noncomputable def isTerminal_yoneda_obj_terminal :
    IsTerminal (yoneda.obj (⊤_ (BigFppfOver B S hS))) :=
  terminalIsTerminal.isTerminalObj yoneda _

/-- The Yoneda presheaf of the terminal object of the big fppf site of `S` is the terminal
presheaf. -/
noncomputable def yonedaTerminalIso :
    yoneda.obj (⊤_ (BigFppfOver B S hS)) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (isTerminal_yoneda_obj_terminal B S hS).uniqueUpToIso terminalIsTerminal

/-- The underlying scheme of the terminal object of the big fppf site of `S` is `S`. -/
noncomputable def toSchemeTerminalIso :
    (BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS)) ≅ S :=
  (BigFppfOver.toScheme B S hS).mapIso
    (terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := B.obj hS)))

/-- The image under the forgetful functor to schemes of the unique morphism of the site to its
terminal object is the structural morphism to `S`, read through
`AlgebraicGeometry.Space.toSchemeTerminalIso`. -/
theorem toScheme_map_terminal_from (U : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (terminal.from U) ≫ (toSchemeTerminalIso B S hS).hom
      = B.inclusion.map U.hom := by
  have h : terminal.from U ≫ (terminalIsTerminal.uniqueUpToIso
      (Over.mkIdTerminal (X := B.obj hS))).hom = Over.mkIdTerminal.from U :=
    Over.mkIdTerminal.hom_ext _ _
  have h2 : (BigFppfOver.toScheme B S hS).map (terminal.from U) ≫
      (toSchemeTerminalIso B S hS).hom
      = (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from U) := by
    rw [← h, Functor.map_comp]
    rfl
  rw [h2]
  exact congrArg B.inclusion.map (Over.mkIdTerminal_from_left U)

/-- **The every-étale-chart condition for a morphism into a terminal presheaf is independent of
the terminal presheaf chosen.** -/
theorem holdsOnEveryEtaleChart_of_isTerminal {P : MorphismProperty Scheme.{u}}
    {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsTerminal G) (hG' : IsTerminal G') (f : F ⟶ G) (f' : F ⟶ G')
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P f' := by
  intro U₁ V₁ a b h ha hb _
  exact hf U₁ V₁ a (b ≫ (hG'.uniqueUpToIso hG).hom) h ha
    ((MorphismProperty.cancel_right_of_respectsIso _ b _).mpr hb) (hG.hom_ext _ _)

/-- **The every-étale-chart condition of Stacks 03MJ for the structural morphism of a presheaf
descends along an fppf covering of the base by one scheme.**

Let `P` be a property of morphisms of schemes which is fpqc local on the target and is inherited
by the first factor of a composite. Let `T₀` be an object of the big fppf site of `S` whose
morphism to the terminal object is flat, surjective and locally of finite presentation on
underlying schemes, and let `F'` be the base change of a presheaf `F` along `T₀`, presented as a
fibre product square over the terminal presheaf. If `P` holds on every étale chart of the
projection `F' ⟶ yoneda T₀`, then it holds on every étale chart of the structural morphism of
`F`. -/
theorem holdsOnEveryEtaleChart_terminal_of_fppfCover
    (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage]
    (hPcancel : ∀ {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z), P (u ≫ v) → P u)
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T₀ : BigFppfOver B S hS)
    (hflat : AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme B S hS).map (terminal.from T₀)))
    (hsurj : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (terminal.from T₀)))
    (hlfp : AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (terminal.from T₀)))
    {q : F' ⟶ F} {pr : F' ⟶ yoneda.obj T₀}
    (hsq : IsPullback q pr (terminal.from F) (terminal.from (yoneda.obj T₀)))
    (hF' : HoldsOnEveryEtaleChart B S hS P pr) :
    HoldsOnEveryEtaleChart B S hS P (terminal.from F) := by
  intro U₁ V₁ a b h ha _ _
  refine hPcancel _ ((BigFppfOver.toScheme B S hS).map (terminal.from V₁)) ?_
  rw [← Functor.map_comp, terminal.comp_from]
  have hWsite : IsPullback (pullback.fst (terminal.from U₁) (terminal.from T₀))
      (pullback.snd (terminal.from U₁) (terminal.from T₀))
      (terminal.from U₁) (terminal.from T₀) := IsPullback.of_hasPullback _ _
  have hvert : ∀ W : BigFppfOver B S hS,
      IsPullback (yoneda.map (terminal.from W)) (𝟙 (yoneda.obj W))
        (yonedaTerminalIso B S hS).hom (terminal.from (yoneda.obj W)) := fun W =>
    IsPullback.of_vert_isIso ⟨terminal.hom_ext _ _⟩
  have hstep : IsPullback
      (yoneda.map (pullback.snd (terminal.from U₁) (terminal.from T₀)))
      (yoneda.map (pullback.fst (terminal.from U₁) (terminal.from T₀)))
      (terminal.from (yoneda.obj T₀)) (terminal.from (yoneda.obj U₁)) := by
    have hpaste := (hWsite.map (yoneda (C := BigFppfOver B S hS))).flip.paste_vert (hvert U₁)
    rwa [Category.comp_id, show yoneda.map (terminal.from T₀) ≫ (yonedaTerminalIso B S hS).hom
      = terminal.from (yoneda.obj T₀) from terminal.hom_ext _ _] at hpaste
  have hbase := IsPullback.of_right'
    (show IsPullback (yoneda.map (pullback.snd (terminal.from U₁) (terminal.from T₀)))
        (yoneda.map (pullback.fst (terminal.from U₁) (terminal.from T₀)))
        (terminal.from (yoneda.obj T₀)) (a ≫ terminal.from F) from
      (show a ≫ terminal.from F = terminal.from (yoneda.obj U₁) from
        terminal.hom_ext _ _) ▸ hstep)
    hsq.flip
  have hchart := (MorphismProperty.relative_isStableUnderBaseChange
      (F := yoneda (C := BigFppfOver B S hS))
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback hbase.flip ha
  have hPsnd := hF' _ T₀ _ (yoneda.map (𝟙 T₀))
    (pullback.snd (terminal.from U₁) (terminal.from T₀)) hchart
    (presheaf_yoneda_map_id_etale B S hS T₀)
    (by rw [hsq.flip.lift_fst]; simp)
  have hSpb := hWsite.map (BigFppfOver.toScheme B S hS)
  have hcov : Presieve.singleton ((BigFppfOver.toScheme B S hS).map (terminal.from T₀))
      ∈ Scheme.fpqcPrecoverage.coverings
        ((BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS))) :=
    Scheme.fppfPrecoverage_le_fpqcPrecoverage _ (Scheme.Hom.singleton_mem_fppfPrecoverage _)
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hcov ?_
  intro V g _ hg
  cases hg
  rw [← MorphismProperty.cancel_left_of_respectsIso P hSpb.isoPullback.hom
      (pullback.snd _ _), hSpb.isoPullback_hom_snd]
  exact hPsnd

/-- **Local finite type of the structural morphism of a presheaf descends along an fppf covering
of the base by one scheme.** Let `T₀` be an object of the big fppf site of `S` whose morphism to
the terminal object is flat, surjective and locally of finite presentation on underlying schemes,
and let `F'` be the base change of a presheaf `F` along `T₀`. If the projection `F' ⟶ yoneda T₀`
is locally of finite type, then so is the structural morphism of `F`. -/
theorem isLocallyOfFiniteType_terminal_of_fppfCover
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T₀ : BigFppfOver B S hS)
    (hflat : AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme B S hS).map (terminal.from T₀)))
    (hsurj : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (terminal.from T₀)))
    (hlfp : AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (terminal.from T₀)))
    {q : F' ⟶ F} {pr : F' ⟶ yoneda.obj T₀}
    (hsq : IsPullback q pr (terminal.from F) (terminal.from (yoneda.obj T₀)))
    (hF' : IsLocallyOfFiniteType B S hS pr) :
    IsLocallyOfFiniteType B S hS (terminal.from F) :=
  holdsOnEveryEtaleChart_terminal_of_fppfCover B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (fun _ _ hc => LocallyOfFiniteType.of_comp hc) T₀ hflat hsurj hlfp hsq hF'

end AlgebraicGeometry.Space

end
