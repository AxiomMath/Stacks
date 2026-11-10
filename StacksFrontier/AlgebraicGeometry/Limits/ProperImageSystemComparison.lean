module

public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemComparison
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystem

/-!
# Tag 0CNV from a proper model: eventual properness of the given stage morphisms

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, let `X ⟶ S` and `Y ⟶ S` be quasi-separated and of finite type, and let
`f : X ⟶ Y` be a morphism over `S`. Tags 0CNQ and 0CNR describe `X` and `Y` as the limits of the
systems of scheme-theoretic images attached to good diagrams for them, and realise `f` by an
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt` of those systems on a common tail.

Tag 0CNV asserts that if `f` is proper then the stage morphisms of *any* such realisation are
eventually proper. Its Stacks proof has two halves.

* The geometric half: *some* good diagram has all of its stage morphisms proper, namely one whose
  model is proper over the model of `Y`. This is
  `AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt_isProper_of_isProper_model`
  (`StacksFrontier/AlgebraicGeometry/Limits/ProperImageSystem.lean`).
* The transfer half: by Remark 0CNS the systems attached to two good diagrams for the same scheme
  over `S` are eventually isomorphic, naturally in morphisms over `S`, so a property of the stage
  morphisms of one realisation transfers to every other at late stages.

This file performs the transfer, and thereby reduces Tag 0CNV to a single input: the existence of
a good diagram for `X` whose model is proper over a model for `Y` at the same stage.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt_of_isProper_model`:
  the conclusion of Tag 0CNV for a given morphism of image systems, given a pair of good diagrams
  related by a proper morphism of models.
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt_of_exists_model`: the
  same with the proper model as an existential hypothesis, which is the form the remaining input
  produces.

Both carry the smallness hypothesis `CategoryTheory.FinallySmall.{u} I`, inherited from the Tag
0CNS statements `AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem` and
`AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison` that the
transfer runs through.

## What is still missing for Tag 0CNV

**Tag 09ZR alone.** The hypothesis `hmodel` of `eventually_isProper_morphismAt_of_exists_model`
— a good diagram for `X` whose model is proper over a model for `Y` — is built by the Stacks
proof from Tag 09ZR (a proper morphism factors as a closed immersion into a proper morphism of
finite presentation), part (1) of Tag 01ZM (descending a morphism of finite presentation to a
finite stage) and Tag 081F (descending properness to a finite stage). The last two are available
and both descents are performed in
`StacksDraft.AlgebraicGeometry.F3b.Limits.ProperImageSystemModels`, whose
`eventually_isProper_morphismAt_of_exists_factorisation` is the conclusion of Tag 0CNV on the
single hypothesis of Tag 09ZR.

* Part (1) of Tag 01ZM is `AlgebraicGeometry.LimitDescent.hasFinitePresentationModels`, with no
  smallness and no flatness hypothesis.
* Tag 081F is `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`. An
  earlier
  version of this note said that it "rests on Chow's lemma
  (`AlgebraicGeometry.HasChowModification`), which nothing in this repository produces". Chow's
  lemma over a Noetherian base is now proved and tagged — Tag 0200,
  `AlgebraicGeometry.hasDenseChowModification`, with `AlgebraicGeometry.hasChowModification` its
  `HasChowModification` form — and the Noetherian case is the one this situation needs, the
  stages of the image system of a good diagram being Noetherian.

`StacksDraft.AlgebraicGeometry.F3b.Limits.ProperModelFromClosedImmersion` is what derives
`hmodel` from a 09ZR-shaped factorisation.

## References

* [Stacks Project, Tag 0CNV](https://stacks.math.columbia.edu/tag/0CNV)
* [Stacks Project, Tag 0CNS](https://stacks.math.columbia.edu/tag/0CNS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v u

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **Tag 0CNV, the transfer step.** Let `f : X ⟶ Y` be a morphism over the limit, realised by a
morphism `F` of the image systems of good diagrams `GX` and `GY`. Suppose that *some* good
diagrams `GX'` for `X` and `GY'` for `Y`, taken over a common stage, have their models related by
a proper morphism `m` lying over that stage and compatible with `f`. Then the stage morphisms of
the *given* `F` are proper at all sufficiently late stages.

The hypotheses on `GX'`, `GY'` and `m` are those of
`AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt_isProper_of_isProper_model`, which
produces a realisation of `f` all of whose stage morphisms are proper; Tag 0CNS transfers that to
`F`. -/
theorem eventually_isProper_morphismAt_of_isProper_model [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY)
    (GX' : GoodDiagram D pX) (GY' : GoodDiagram D pY)
    (hi : GX'.index = GY'.index) (m : GX'.W ⟶ GY'.W) [IsProper m]
    (hm : m ≫ GY'.modelMap = GX'.modelMap ≫ D.system.map (eqToHom (congrArg op hi)))
    (ht : GX'.toModel ≫ m = f ≫ GY'.toModel) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → IsProper (F.maps.app j) := by
  classical
  -- the realisation of `f` with proper stage morphisms, from the proper model
  obtain ⟨i₁, hx₁, hy₁, F', hF'⟩ :=
    exists_morphismAt_isProper_of_isProper_model D f hf GX' GY' hi m hm ht
  -- the comparisons of the two good diagrams for `X` and for `Y` (Tag 0CNS)
  obtain ⟨iA, hA₁, hA₂, Φ₀, Φ₀', hΦ₀⟩ := exists_eventual_iso_imageSystem D pX GX GX'
  obtain ⟨iB, hB₁, hB₂, Θ₀, Θ₀', hΘ₀⟩ := exists_eventual_iso_imageSystem D pY GY GY'
  -- a common tail of all four
  obtain ⟨a, ha₀, ha₁⟩ := exists_ge_ge i₀ i₁
  obtain ⟨b, hbA, hbB⟩ := exists_ge_ge iA iB
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  have hc₀ : i₀ ≤ c := ha₀.trans hca
  have hAc : iA ≤ c := hbA.trans hcb
  have hBc : iB ≤ c := hbB.trans hcb
  -- everything restricted to that tail
  let Fc := MorphismAt.restrict D f GX GY hc₀ F
  let F'c := MorphismAt.restrict D f GX' GY' (ha₁.trans hca) F'
  let Φ := MorphismAt.restrict D (𝟙 X) GX GX' hAc Φ₀
  let Φ' := MorphismAt.restrict D (𝟙 X) GX' GX hAc Φ₀'
  let Θ := MorphismAt.restrict D (𝟙 Y) GY GY' hBc Θ₀
  let Θ' := MorphismAt.restrict D (𝟙 Y) GY' GY hBc Θ₀'
  obtain ⟨i₃, hc₃, hnat⟩ :=
    eventually_natural_imageSystem_comparison D f GX GX' GY GY' c
      (hA₁.trans hAc) (hA₂.trans hAc) (hB₁.trans hBc) (hB₂.trans hBc) Φ Θ Fc F'c
  refine ⟨i₃, hc₀.trans hc₃, fun j hj => ?_⟩
  -- transport along an equality of stages, which is where the two tails are matched
  have transport : ∀ {o o' : Over (op i₀)}, o = o' →
      IsProper (F.maps.app o) → IsProper (F.maps.app o') := by
    rintro _ _ rfl h
    exact h
  have hcj : c ≤ unop j.left := hc₃.trans hj
  refine transport (o := (Over.map ((homOfLE hc₀).op)).obj (Over.mk ((homOfLE hcj).op))) ?_ ?_
  · apply CostructuredArrow.obj_ext
    · rfl
    · simp
  -- at the matched stage, the given realisation differs from `F'` by the two comparison isos
  set j' : Over (op c) := Over.mk ((homOfLE hcj).op)
  have hΦiso : IsIso (Φ.maps.app j') :=
    ⟨⟨Φ'.maps.app j', (hΦ₀ _).1, (hΦ₀ _).2⟩⟩
  have hΘiso : IsIso (Θ.maps.app j') :=
    ⟨⟨Θ'.maps.app j', (hΘ₀ _).1, (hΘ₀ _).2⟩⟩
  change IsProper (Fc.maps.app j')
  refine (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _
    (Θ.maps.app j')).mp ?_
  rw [hnat j' hj]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) _
    (F'c.maps.app j')).mpr (hF' _)

/-- **Tag 0CNV, reduced to one input.** The conclusion of Tag 0CNV for a given morphism of image
systems, on the single hypothesis that `f` has a *proper model*: good diagrams for `X` and `Y`
over a common stage whose models are related by a proper morphism compatible with `f`.

This is the statement of the tag with the one step of its Stacks proof that is not available
isolated as `hmodel`; see the module documentation. -/
theorem eventually_isProper_morphismAt_of_exists_model [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY)
    (hmodel : ∃ (GX' : GoodDiagram D pX) (GY' : GoodDiagram D pY)
      (hi : GX'.index = GY'.index) (m : GX'.W ⟶ GY'.W) (_ : IsProper m),
      m ≫ GY'.modelMap = GX'.modelMap ≫ D.system.map (eqToHom (congrArg op hi)) ∧
        GX'.toModel ≫ m = f ≫ GY'.toModel) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → IsProper (F.maps.app j) := by
  obtain ⟨GX', GY', hi, m, _, hm, ht⟩ := hmodel
  exact eventually_isProper_morphismAt_of_isProper_model D f hf GX GY i₀ hX hY F GX' GY' hi m hm ht

end LimitNoetherianSituation

end AlgebraicGeometry

end
