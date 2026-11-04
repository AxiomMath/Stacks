module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Pushforward

/-!
# Restricting a direct image to the small étale site of an algebraic space

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}` and
assume `𝒴` is representable by an algebraic space `G`, with a chosen equivalence presenting it.
Stacks 073M gives the functor `u_G : G_étale ⥤ 𝒴` and equation 075K the restriction
`ℋ|_{G_étale} = π_{G,*}ℋ = ℋ ∘ u_G` of a sheaf on `𝒴_étale` to the small étale site of `G`.

Equation 075M of the source asserts, for `𝒳` representable by an algebraic space `F` as well,
that
```
(f_*ℱ)|_{G_étale} = f_{small,*}(ℱ|_{F_étale}).
```
This file computes the **left-hand side** of that identity: at a chart `V` of `G_étale` its
sections are the global sections of `ℱ` pulled back to the 2-fibre product
`(Sch/V)_{fppf} ×_{u_G V, 𝒴} 𝒳`. That is the first step of the source's own derivation — the
display
`π_{G,*}f_*𝒢(V) = f_*𝒢(V/G) = Γ((Sch/V)_{fppf} ×_𝒴 𝒳, pr^{-1}𝒢)`
which opens the proof of Stacks 073N — and it needs nothing of `F`: only `𝒴` has to be
representable. The right-hand side is *not* computed here; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.etaleDirectImage`: the direct image `f_*` on sheaves of sets for the
  inherited étale topologies, the left-hand side's outer functor.
* `AlgebraicGeometry.Space.chartFiberObj`: the object of `𝒴` attached to a chart of `G`, read in
  the fibre over the scheme underlying that chart.

## Main results

* `AlgebraicGeometry.Space.etaleDirectImage_obj_obj`: the presheaf underlying `f_*ℱ` is the right
  Kan extension of the presheaf underlying `ℱ` along `f.op`, which is what makes the Stacks 06W6
  pushforward formula applicable to it.
* `AlgebraicGeometry.Space.restrictedDirectImageChartEquiv`: **equation 075M, left-hand side.**
  The sections of `(f_*ℱ)|_{G_étale}` at a chart `V` are the global sections of the pullback of
  `ℱ` to `(Sch/V)_{fppf} ×_{u_G V, 𝒴} 𝒳`.
* `AlgebraicGeometry.Space.restrictedDirectImageChartEquiv_naturality`: that identification is
  natural in the sheaf, so it identifies the two as functors of `ℱ` and not merely pointwise.

## Implementation notes

The identity 075M is stated by the source as a consequence of Stacks 073N, the commutation of
the square of ringed topoi formed by `f`, `f_{small}`, `π_F` and `π_G`. **Stacks 073N is not
proved in this library**, and neither is Stacks 0GQA, its étale-localization variant. Nothing
here assumes either, and nothing here supplies either: the right-hand side
`f_{small,*}(ℱ|_{F_étale})` does not appear below, and the tag carries a clause recording that
only the left-hand side is covered.

What 073N still needs is *not* the whole of its source proof. Against the library, the
pieces divide as follows.

* The **equalizer presentation of the right-hand side is in the library**, assembled at the
  chart appearing in equation 075M. Its ingredients are in the library too — Properties of Spaces
  03H7 is `AlgebraicGeometry.Space.exists_isLimit_fork_of_isSheaf`, Stacks 03G1 is
  `AlgebraicGeometry.Space.comparisonFunctor` with
  `AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`, and Stacks 03G2 is
  `AlgebraicGeometry.Space.spacesBaseChange` — and the presentation itself is
  `AlgebraicGeometry.Space.exists_smallEtaleDirectImageChartEqualizerEquiv`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDirectImageChartEqualizer.lean`), which is
  03H7 for the direct image on the small étale sites, specialized at the 075M chart by
  `AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonTarget_equalizer`. The small
  étale site also has `AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer` and
  `AlgebraicGeometry.Space.smallEtaleSectionsEquivEqualizer` (Stacks 03M8), which present
  Γ over the small étale site of an algebraic space as the equalizer over an atlas.
* The **identification of the 2-fibre product** `(Sch/V)_{fppf} ×_𝒴 𝒳` with a split category
  fibred in groupoids is available in substance — `CategoryTheory.PresheafOfCategories`'s
  `isEquivalence_toTwoFibreProduct`,
  `CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_twoFibreProductPresheaf` and
  `CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`
  (these are presheaf-of-categories statements; there are no `AlgebraicGeometry.Space` copies
  of them) — but it is available only *without the topology*: no declaration transports the
  inherited étale site across that equivalence, and none spells the apex as `V ×_G F`.
* What is genuinely **absent** is the matching equalizer presentation of the *left-hand side*:
  that the global sections of `pr^{-1}ℱ` over the 2-fibre product are the equalizer of
  `ℱ(W/F) ⇉ ℱ(W'/F)` over an étale scheme chart `W` of `V ×_G F`. Its two
  *category-theoretic* inputs are in the library. First, invariance of
  `CategoryTheory.Presheaf.globalSections` under an equivalence of the index category is
  `CategoryTheory.Presheaf.globalSectionsPrecompEquiv`, with the initial-functor generalization
  `CategoryTheory.Presheaf.globalSectionsPrecompEquivOfInitial` and the evaluation lemma
  `CategoryTheory.Presheaf.globalSectionsEquivSections_globalSectionsPrecompEquiv`.
  Second, Stacks 0792 is instantiated:
  `Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimitOfCoversTop` discharges the
  coequalizer hypothesis of
  `Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimit` from two conditions on the
  site — `GrothendieckTopology.CoversTop` of the one-element family of the atlas object, and
  `CategoryTheory.Presheaf.FactorsPairs` for the two projections of the relation — and
  `CategoryTheory.Presheaf.globalSectionsEquivEqualizer` is the same statement for the global
  sections of Stacks 06UN, which is the form this file's left-hand side takes. What is left is
  geometric: verifying those two conditions on the inherited étale site of the 2-fibre product,
  which is exactly the transport of the topology across the identification above.

`AlgebraicGeometry.Space.restrictionFunctor_coversTop` — that every object of `𝒳` is covered by
objects coming from étale charts of `F` — is in the library and is the natural starting point
for that last item.

What is proved is therefore the half of 075M that is independent of 073N, and it is proved in
the generality that half enjoys: `𝒳` is an arbitrary category fibred in groupoids over the site,
not required to be representable, and only the target `𝒴` is presented by an algebraic space.
The source states 075M only for `𝒳` representable, because the right-hand side needs `F`.

The direct image is `Functor.sheafPushforwardCocontinuous`, the right adjoint of restriction
along `f`, cocontinuity for the inherited topologies coming from
`CategoryTheory.Functor.IsFibredOneMorphism.isCocontinuous_inheritedTopology`. The source's size
condition appears as the hypothesis `[∀ H, f.op.HasPointwiseRightKanExtension H]`, exactly as it
does on `Functor.sheafPushforwardCocontinuous` and on
`AlgebraicGeometry.FibredSite.ringedToposMorphism`; it is a condition on the sites, not a
weakening of the content.

A choice of pullbacks on `q` is an explicit argument rather than `Functor.chosenPullbacks`,
matching `CategoryTheory.Presheaf.pushforwardSectionsEquiv`, whose statement names the
chosen pullbacks in the indexing category of the 2-fibre product; threading the same `c` through
keeps the two statements about one and the same category.

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)

/-! ### The direct image on the inherited étale sites -/

/-- The direct image `f_*` of sheaves of sets along a 1-morphism `f : 𝒳 ⥤ 𝒴` of categories
fibred in groupoids over `(Sch/S)_{fppf}`, for the étale topologies the two inherit from the
base: the right adjoint of restriction along `f`, which exists because a 1-morphism of fibred
categories is cocontinuous for the inherited topologies. -/
noncomputable abbrev etaleDirectImage (hp : p.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hf : p.IsFibredOneMorphism q f)
    [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H] :
    Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u) ⥤
      Sheaf (BigFppfOver.associatedTopology B S hS q .etale) (Type u) :=
  letI := hp.isFibered
  letI := hf.isCocontinuous_inheritedTopology (BigFppfOver.baseOverTopology B S hS .etale)
  f.sheafPushforwardCocontinuous (Type u)
    (BigFppfOver.associatedTopology B S hS p .etale)
    (BigFppfOver.associatedTopology B S hS q .etale)

/-- The presheaf underlying `f_*ℱ` is the right Kan extension along `f.op` of the presheaf
underlying `ℱ`. This is what lets the pushforward formula of Stacks 06W6, which is stated for
right Kan extensions of presheaves, compute the sections of `f_*ℱ`. -/
theorem etaleDirectImage_obj_obj (hp : p.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hf : p.IsFibredOneMorphism q f)
    [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) :
    ((etaleDirectImage B S hS p q hp f hf).obj ℱ).obj = f.op.ran.obj ℱ.obj :=
  rfl

/-! ### The left-hand side of equation 075M -/

/-- The object of `𝒴` attached by Stacks 073M to a chart `V` of the small étale site of `G`,
read in the fibre of `q` over the scheme underlying `V`. Membership of that fibre is
`AlgebraicGeometry.Space.restrictionFunctor_comp`, which says the functor `u_G : G_étale ⥤ 𝒴`
is strictly over the base. -/
noncomputable def chartFiberObj
    (eG : StacksRepresentableCFG.EquivalenceOver q (presheafOfCategories (G ⋙ typeToCat)).p)
    (V : SmallEtale B S hS G) :
    q.Fiber ((SmallEtale.toOver B S hS G).obj V) :=
  ⟨(restrictionFunctor B S hS G q eG).obj V,
    Functor.congr_obj (restrictionFunctor_comp B S hS G q eG) V⟩

/-- The object underlying `chartFiberObj` at a chart `V` is the image of `V` under the functor
`u_G : G_étale ⥤ 𝒴` of Stacks 073M. -/
@[simp] theorem chartFiberObj_coe
    (eG : StacksRepresentableCFG.EquivalenceOver q (presheafOfCategories (G ⋙ typeToCat)).p)
    (V : SmallEtale B S hS G) :
    (chartFiberObj B S hS G q eG V).1 = (restrictionFunctor B S hS G q eG).obj V :=
  rfl

/-- **Equation 075M, left-hand side.** The sections of the restriction `(f_*ℱ)|_{G_étale}` of a
direct image to the small étale site of the algebraic space `G` representing `𝒴`, at a chart `V`
of `G`, are the global sections of the pullback of `ℱ` to the 2-fibre product
`(Sch/V)_{fppf} ×_{u_G V, 𝒴} 𝒳`.

This is the opening display of the source's proof of Stacks 073N, from which equation 075M is
drawn: `π_{G,*}f_*ℱ(V) = f_*ℱ(V/G) = Γ((Sch/V)_{fppf} ×_𝒴 𝒳, pr^{-1}ℱ)`. The first step is
equation 075K, that restriction is evaluation at `u_G V`; the second is Stacks 06W6.

Only the left-hand side of 075M is covered. Identifying these sections with those of
`f_{small,*}(ℱ|_{F_étale})` is the content of Stacks 073N, which is not proved in this library;
the implementation notes of this file say which input to the identification is still
missing.
Accordingly `𝒳` is an arbitrary category fibred in groupoids here, with no representability
assumed of it. -/
@[stacks 075M "the left-hand side, as sections over the 2-fibre product at a chart"]
noncomputable def restrictedDirectImageChartEquiv (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids)
    (eG : StacksRepresentableCFG.EquivalenceOver q (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f) (c : q.ChoiceOfPullbacks)
    [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (V : SmallEtale B S hS G) :
    ((restrictionSheafFunctor B S hS G q hq eG).obj
        ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj.obj (op V) ≃
      Presheaf.globalSections
        ((TwoFibreProductOver.snd (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
          (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f).op ⋙ ℱ.obj) :=
  Presheaf.pushforwardSectionsEquiv p q f hq hf.comp_eq c
    (chartFiberObj B S hS G q eG V) ℱ.obj

/-- **Equation 075M, left-hand side.** The identification of the sections of `(f_*ℱ)|_{G_étale}`
at a chart with global sections over the 2-fibre product is natural in `ℱ`, so the two are
identified as functors of `ℱ` and not merely for each `ℱ` separately. -/
theorem restrictedDirectImageChartEquiv_naturality (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids)
    (eG : StacksRepresentableCFG.EquivalenceOver q (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f) (c : q.ChoiceOfPullbacks)
    [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]
    (ℱ 𝒢 : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) (η : ℱ ⟶ 𝒢)
    (V : SmallEtale B S hS G)
    (s : ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj.obj (op V)) :
    restrictedDirectImageChartEquiv B S hS G p q hp hq eG f hf c 𝒢 V
        (((restrictionSheafFunctor B S hS G q hq eG).map
          ((etaleDirectImage B S hS p q hp f hf).map η)).hom.app (op V) s) =
      restrictedDirectImageChartEquiv B S hS G p q hp hq eG f hf c ℱ V s ≫
        Functor.whiskerLeft
          (TwoFibreProductOver.snd (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
            (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f).op η.hom :=
  Presheaf.pushforwardSectionsEquiv_naturality p q f hq hf.comp_eq c
    (chartFiberObj B S hS G q eG V) ℱ.obj 𝒢.obj η.hom s

end AlgebraicGeometry.Space

end
