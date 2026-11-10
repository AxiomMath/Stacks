module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartLocalFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting

/-!
# Base change of étale charts along an integral universally injective morphism is locally full

Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. Base change along `f` carries étale scheme charts of `X` to étale scheme charts of
`Y` (`AlgebraicGeometry.Space.smallBaseChange`), and the resulting functor between the small
étale sites is *locally full*: a morphism over `Y` between the base changes of two étale charts
of `X` comes, locally on the source, from a morphism of charts of `X`.

The argument is that of Stacks 04FV, in the form in which it is carried out for a closed
immersion in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartLocalFullness.lean`. Given étale
charts `U` and `U'` of `X` and a morphism `φ : U ×_X Y ⟶ U' ×_X Y` over `Y`, the chart `W` is
an open subscheme of `U ×_X U'` cut out by the graph of `φ`: that graph lifts to a section of
the étale projection `(U ×_X U') ×_X Y ⟶ U ×_X Y`, a section of an étale morphism is an open
immersion, and its open image extends to an open subscheme of `U ×_X U'`.

The only property of a closed immersion that argument uses is that the represented base
changes of `f` are *topological embeddings*, which is what makes the open image of the section
extend. For an integral universally injective morphism that holds by
`AlgebraicGeometry.Space.isClosedEmbedding_toScheme_map_snd`, so the whole argument runs
unchanged, and it is carried out here under exactly that hypothesis.

## Main results

* `exists_isIso_smallBaseChange_map_of_isIntegralHom_of_universallyInjective`, in the namespace
  `AlgebraicGeometry.Space`, produces the open subchart of `U ×_X U'` and the morphism of
  charts with invertible base change; it is the form Stacks 04FV takes for an integral
  universally injective morphism of algebraic spaces.
* `AlgebraicGeometry.Space.smallBaseChange_isLocallyFull_of_isIntegralHom_of_universallyInjective`
  is the local fullness of chart base change along such a morphism.

## Implementation notes

All fibre products occurring here are the chosen representable pullbacks supplied by
representability: `CategoryTheory.Functor.relativelyRepresentable.pullback` for `f` and for the
étale chart `U`. Morphisms into them are built with
`CategoryTheory.Functor.relativelyRepresentable.lift` and `…lift'` and compared with
`…hom_ext`, so the combinatorial part of the argument takes place in the big fppf site of `S`
rather than in schemes.

Beyond the existence of the open subscheme, the only scheme-theoretic input is that the base
change `W ×_X Y ⟶ (U ×_X U') ×_X Y` of the open immersion `W ⟶ U ×_X U'` has image inside the
image of the graph section. The reverse inclusion is never needed: the retraction supplied by
the section already forces the base change of `a` to be invertible.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

/-! ### Preliminaries on schemes and on sieves -/

private lemma exists_open_extension_of_isInducing {A A' : Scheme.{u}}
    (j : A ⟶ A') (hj : Topology.IsInducing j.base) (V : A.Opens) :
    ∃ W : A'.Opens, j ⁻¹ᵁ W = V := by
  obtain ⟨W, hW, hpre⟩ := hj.isOpen_iff.mp V.2
  exact ⟨⟨W, hW⟩, TopologicalSpace.Opens.ext hpre⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Lifting a morphism of schemes to the site -/

/-! ### The algebraic-space form of Stacks 04FV -/

/-- **Stacks 04FV for a morphism whose represented base changes are topological embeddings.**
Let `f : Y ⟶ X` be a relatively representable morphism of algebraic spaces over `S` all of
whose represented base changes induce a topological embedding on underlying schemes, let `U`
and `U'` be étale scheme charts of `X`, and let `φ` be a morphism over `Y` between their base
changes along `f`. Then there is an étale scheme chart `W` of `X` and a morphism of charts
`a : W ⟶ U` whose base change along `f` is an isomorphism and which lies in the image sieve of
`φ`.

The chart `W` is an open subscheme of `U ×_X U'` containing the image of the graph of `φ`. -/
theorem exists_isIso_smallBaseChange_map_of_isInducing
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (hind : ∀ {A : BigFppfOver B S hS} (g : yoneda.obj A ⟶ X.1),
      Topology.IsInducing ((BigFppfOver.toScheme B S hS).map (hrep.snd g)).base)
    (U U' : SmallEtale B S hS X.1)
    (φ : (smallBaseChange B S hS f hrep).obj U ⟶ (smallBaseChange B S hS f hrep).obj U') :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U),
      IsIso ((smallBaseChange B S hS f hrep).map a) ∧
        ((smallBaseChange B S hS f hrep).imageSieve φ).arrows a := by
  -- the étale chart `U ×_X U'` of `X`
  let M := U.property.rep.pullback U'.1.hom
  let prU : M ⟶ U.1.left := U.property.rep.fst' U'.1.hom
  let prU' : M ⟶ U'.1.left := U.property.rep.snd U'.1.hom
  have hMw : yoneda.map prU ≫ U.1.hom = yoneda.map prU' ≫ U'.1.hom :=
    (U.property.rep.isPullback' U'.1.hom).w
  have hprU : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map prU) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (U.property.rep.isPullback' U'.1.hom).flip U'.property
  have hprUetale : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map prU) :=
    (presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.Etale.{u}) inferInstance prU).1 hprU
  let mChart : yoneda.obj M ⟶ X.1 := yoneda.map prU ≫ U.1.hom
  have hM : IsEtaleChart B S hS X.1 (CostructuredArrow.mk mChart) :=
    etale_comp_of_scheme B S hS prU U.1.hom hprUetale U.property
  let Mc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk mChart, hM⟩
  let kU : Mc ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk prU rfl)
  let kU' : Mc ⟶ U' := ObjectProperty.homMk (CostructuredArrow.homMk prU' hMw.symm)
  -- the projections of the base-changed charts, and the embedding above `U ×_X U'`
  let π : hrep.pullback mChart ⟶ hrep.pullback U.1.hom :=
    ((smallBaseChange B S hS f hrep).map kU).hom.left
  let π' : hrep.pullback mChart ⟶ hrep.pullback U'.1.hom :=
    ((smallBaseChange B S hS f hrep).map kU').hom.left
  let c : hrep.pullback mChart ⟶ M := hrep.snd mChart
  have hπw : yoneda.map π ≫ hrep.fst U.1.hom = hrep.fst mChart :=
    CostructuredArrow.w ((smallBaseChange B S hS f hrep).map kU).hom
  have hπsnd : π ≫ hrep.snd U.1.hom = c ≫ prU :=
    smallBaseChange_map_snd B S hS f hrep kU
  have hπ'w : yoneda.map π' ≫ hrep.fst U'.1.hom = hrep.fst mChart :=
    CostructuredArrow.w ((smallBaseChange B S hS f hrep).map kU').hom
  have hπ'snd : π' ≫ hrep.snd U'.1.hom = c ≫ prU' :=
    smallBaseChange_map_snd B S hS f hrep kU'
  have hπetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map π) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (representablePullbackMap_isPullback_scheme B S hS f hrep kU).flip hprUetale
  -- the graph of `φ`
  let ϕ : hrep.pullback U.1.hom ⟶ hrep.pullback U'.1.hom := φ.hom.left
  have hφw : yoneda.map ϕ ≫ hrep.fst U'.1.hom = hrep.fst U.1.hom :=
    CostructuredArrow.w φ.hom
  have hγcond : yoneda.map (hrep.snd U.1.hom) ≫ U.1.hom =
      yoneda.map (ϕ ≫ hrep.snd U'.1.hom) ≫ U'.1.hom := by
    rw [Functor.map_comp, Category.assoc, ← hrep.w U'.1.hom, ← Category.assoc, hφw,
      hrep.w U.1.hom]
  let γ : hrep.pullback U.1.hom ⟶ M :=
    U.property.rep.lift' (hrep.snd U.1.hom) (ϕ ≫ hrep.snd U'.1.hom) hγcond
  have hγfst : γ ≫ prU = hrep.snd U.1.hom := U.property.rep.lift'_fst _ _ _
  have hγsnd : γ ≫ prU' = ϕ ≫ hrep.snd U'.1.hom := U.property.rep.lift'_snd _ _ _
  -- the graph is a section of the projection `(U ×_X U') ×_X Y ⟶ U ×_X Y`
  have hδcond : hrep.fst U.1.hom ≫ f.hom = yoneda.map γ ≫ mChart := by
    rw [hrep.w U.1.hom, ← hγfst, Functor.map_comp, Category.assoc]
  let δ : hrep.pullback U.1.hom ⟶ hrep.pullback mChart :=
    hrep.lift (hrep.fst U.1.hom) γ hδcond
  have hδfst : yoneda.map δ ≫ hrep.fst mChart = hrep.fst U.1.hom := hrep.lift_fst _ _ _
  have hδsnd : δ ≫ c = γ := hrep.lift_snd _ _ _
  have hδπ : δ ≫ π = 𝟙 (hrep.pullback U.1.hom) := by
    refine hrep.hom_ext ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hπw, hδfst, CategoryTheory.Functor.map_id,
        Category.id_comp]
    · rw [Category.assoc, hπsnd, ← Category.assoc, hδsnd, hγfst, Category.id_comp]
  have hδπmap : (BigFppfOver.toScheme B S hS).map δ ≫
      (BigFppfOver.toScheme B S hS).map π = 𝟙 _ := by
    rw [← Functor.map_comp, hδπ, CategoryTheory.Functor.map_id]
  have hδopen : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map δ) :=
    AlgebraicGeometry.Unramified.section_isOpenImmersion ((BigFppfOver.toScheme B S hS).map π)
      ((BigFppfOver.toScheme B S hS).map δ) hδπmap
  -- extend the image of the graph to an open subscheme of `U ×_X U'`
  obtain ⟨O, hO⟩ := exists_open_extension_of_isInducing
    ((BigFppfOver.toScheme B S hS).map c) (hind mChart)
    ((BigFppfOver.toScheme B S hS).map δ).opensRange
  let MO := openSiteObject B S hS M O
  let ιO : MO ⟶ M := openSiteObjectHom B S hS M O
  have hιOmap : (BigFppfOver.toScheme B S hS).map ιO = O.ι := map_openSiteObjectHom B S hS M O
  have hιOetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ιO) := by
    rw [hιOmap]
    exact inferInstanceAs (AlgebraicGeometry.Etale O.ι)
  have hιOopen : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map ιO) := by
    rw [hιOmap]
    exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion O.ι)
  have hιOmono : Mono ((BigFppfOver.toScheme B S hS).map ιO) :=
    AlgebraicGeometry.IsOpenImmersion.mono ((BigFppfOver.toScheme B S hS).map ιO)
  have hιOrange : Set.range ((BigFppfOver.toScheme B S hS).map ιO) = (O : Set _) := by
    rw [hιOmap]
    exact Scheme.Opens.range_ι O
  let oChart : yoneda.obj MO ⟶ X.1 := yoneda.map ιO ≫ mChart
  have hoChart : oChart = yoneda.map ιO ≫ mChart := rfl
  have hWc : IsEtaleChart B S hS X.1 (CostructuredArrow.mk oChart) :=
    etale_comp_of_scheme B S hS ιO mChart hιOetale hM
  let Wc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk oChart, hWc⟩
  let kO : Wc ⟶ Mc := ObjectProperty.homMk (CostructuredArrow.homMk ιO rfl)
  let ρ : hrep.pullback oChart ⟶ hrep.pullback mChart :=
    ((smallBaseChange B S hS f hrep).map kO).hom.left
  have hρw : yoneda.map ρ ≫ hrep.fst mChart = hrep.fst oChart :=
    CostructuredArrow.w ((smallBaseChange B S hS f hrep).map kO).hom
  have hρsnd : ρ ≫ c = hrep.snd oChart ≫ ιO :=
    smallBaseChange_map_snd B S hS f hrep kO
  -- the two range conditions
  have hγmap : (BigFppfOver.toScheme B S hS).map γ =
      (BigFppfOver.toScheme B S hS).map δ ≫ (BigFppfOver.toScheme B S hS).map c := by
    rw [← Functor.map_comp, hδsnd]
  have hOγ : Set.range ((BigFppfOver.toScheme B S hS).map γ) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ιO) := by
    rw [hιOrange]
    rintro y ⟨w, rfl⟩
    have hw : (BigFppfOver.toScheme B S hS).map δ w ∈
        ((BigFppfOver.toScheme B S hS).map c) ⁻¹ᵁ O := by
      rw [hO]
      exact ⟨w, rfl⟩
    rw [hγmap, Scheme.Hom.comp_apply]
    exact hw
  have hρmap : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map c =
      (BigFppfOver.toScheme B S hS).map (hrep.snd oChart) ≫
        (BigFppfOver.toScheme B S hS).map ιO := by
    rw [← Functor.map_comp, ← Functor.map_comp, hρsnd]
  have hOρ : Set.range ((BigFppfOver.toScheme B S hS).map ρ) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map δ) := by
    rintro y ⟨w, rfl⟩
    have h₁ : ((BigFppfOver.toScheme B S hS).map ρ ≫
        (BigFppfOver.toScheme B S hS).map c) w ∈ (O : Set _) := by
      rw [hρmap, Scheme.Hom.comp_apply, ← hιOrange]
      exact ⟨_, rfl⟩
    have h₂ : (BigFppfOver.toScheme B S hS).map ρ w ∈
        ((BigFppfOver.toScheme B S hS).map c) ⁻¹ᵁ O := by
      rwa [Scheme.Hom.comp_apply] at h₁
    rwa [hO] at h₂
  -- the graph factors through the open subscheme
  obtain ⟨σ, hσ⟩ := exists_hom_of_toScheme_fac B S hS ιO γ
    (AlgebraicGeometry.IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map ιO)
      ((BigFppfOver.toScheme B S hS).map γ) hOγ)
    (AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _)
  -- the base change of the morphism of charts `W ⟶ U` is an isomorphism
  have hρδ : ρ ≫ π ≫ δ = ρ := by
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact comp_retraction_eq_of_range_subset ((BigFppfOver.toScheme B S hS).map δ)
      ((BigFppfOver.toScheme B S hS).map π) ((BigFppfOver.toScheme B S hS).map ρ) hδπmap hOρ
  have hαw : yoneda.map (ρ ≫ π) ≫ hrep.fst U.1.hom = hrep.fst oChart := by
    rw [Functor.map_comp, Category.assoc, hπw, hρw]
  have hαsnd : (ρ ≫ π) ≫ hrep.snd U.1.hom = hrep.snd oChart ≫ ιO ≫ prU := by
    rw [Category.assoc, hπsnd, ← Category.assoc, hρsnd, Category.assoc]
  have hαδ : (ρ ≫ π) ≫ δ = ρ := by rw [Category.assoc, hρδ]
  have hαγ : (ρ ≫ π) ≫ γ = hrep.snd oChart ≫ ιO := by
    rw [← hδsnd, ← Category.assoc, hαδ, hρsnd]
  have hψcond : hrep.fst U.1.hom ≫ f.hom = yoneda.map σ ≫ oChart := by
    rw [hoChart, hδcond, ← hσ, Functor.map_comp, Category.assoc]
  let ψ : hrep.pullback U.1.hom ⟶ hrep.pullback oChart :=
    hrep.lift (hrep.fst U.1.hom) σ hψcond
  have hψfst : yoneda.map ψ ≫ hrep.fst oChart = hrep.fst U.1.hom := hrep.lift_fst _ _ _
  have hψsnd : ψ ≫ hrep.snd oChart = σ := hrep.lift_snd _ _ _
  have hασ : (ρ ≫ π) ≫ σ = hrep.snd oChart :=
    (BigFppfOver.toScheme B S hS).map_injective <|
      (cancel_mono ((BigFppfOver.toScheme B S hS).map ιO)).mp <| by
        rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hσ, hαγ]
  let ψc : (smallBaseChange B S hS f hrep).obj U ⟶ (smallBaseChange B S hS f hrep).obj Wc :=
    ObjectProperty.homMk (CostructuredArrow.homMk ψ hψfst)
  have hone : (smallBaseChange B S hS f hrep).map (kO ≫ kU) ≫ ψc =
      𝟙 ((smallBaseChange B S hS f hrep).obj Wc) := by
    rw [Functor.map_comp]
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hrep.hom_ext ?_ ?_))
    · change yoneda.map ((ρ ≫ π) ≫ ψ) ≫ hrep.fst oChart =
        yoneda.map (𝟙 (hrep.pullback oChart)) ≫ hrep.fst oChart
      rw [Functor.map_comp, Category.assoc, hψfst, hαw, CategoryTheory.Functor.map_id,
        Category.id_comp]
    · change ((ρ ≫ π) ≫ ψ) ≫ hrep.snd oChart =
        𝟙 (hrep.pullback oChart) ≫ hrep.snd oChart
      rw [Category.assoc, hψsnd, hασ, Category.id_comp]
  have htwo : ψc ≫ (smallBaseChange B S hS f hrep).map (kO ≫ kU) =
      𝟙 ((smallBaseChange B S hS f hrep).obj U) := by
    rw [Functor.map_comp]
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hrep.hom_ext ?_ ?_))
    · change yoneda.map (ψ ≫ ρ ≫ π) ≫ hrep.fst U.1.hom =
        yoneda.map (𝟙 (hrep.pullback U.1.hom)) ≫ hrep.fst U.1.hom
      rw [Functor.map_comp, Category.assoc, hαw, hψfst, CategoryTheory.Functor.map_id,
        Category.id_comp]
    · change (ψ ≫ ρ ≫ π) ≫ hrep.snd U.1.hom =
        𝟙 (hrep.pullback U.1.hom) ≫ hrep.snd U.1.hom
      rw [Category.assoc, hαsnd, ← Category.assoc, hψsnd, ← Category.assoc, hσ, hγfst,
        Category.id_comp]
  have hsieve : (smallBaseChange B S hS f hrep).map (kO ≫ kU') =
      (smallBaseChange B S hS f hrep).map (kO ≫ kU) ≫ φ := by
    rw [Functor.map_comp, Functor.map_comp]
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hrep.hom_ext ?_ ?_))
    · change yoneda.map (ρ ≫ π') ≫ hrep.fst U'.1.hom =
        yoneda.map ((ρ ≫ π) ≫ ϕ) ≫ hrep.fst U'.1.hom
      have hL : yoneda.map (ρ ≫ π') ≫ hrep.fst U'.1.hom = hrep.fst oChart := by
        rw [Functor.map_comp, Category.assoc, hπ'w, hρw]
      have hR : yoneda.map ((ρ ≫ π) ≫ ϕ) ≫ hrep.fst U'.1.hom = hrep.fst oChart := by
        rw [Functor.map_comp, Category.assoc, hφw, hαw]
      rw [hL, hR]
    · change (ρ ≫ π') ≫ hrep.snd U'.1.hom = ((ρ ≫ π) ≫ ϕ) ≫ hrep.snd U'.1.hom
      have hL : (ρ ≫ π') ≫ hrep.snd U'.1.hom = hrep.snd oChart ≫ ιO ≫ prU' := by
        rw [Category.assoc, hπ'snd, ← Category.assoc, hρsnd, Category.assoc]
      have hR : ((ρ ≫ π) ≫ ϕ) ≫ hrep.snd U'.1.hom = hrep.snd oChart ≫ ιO ≫ prU' := by
        rw [Category.assoc, ← hγsnd, ← Category.assoc, hαγ, Category.assoc]
      rw [hL, hR]
  exact ⟨Wc, kO ≫ kU, ⟨ψc, hone, htwo⟩, kO ≫ kU', hsieve⟩

/-- **Stacks 04FV for an integral universally injective morphism of algebraic spaces.** Let
`f : Y ⟶ X` be such a morphism over a scheme `S`, let `U` and `U'` be étale scheme charts of
`X`, and let `φ` be a morphism over `Y` between their base changes along `f`. Then there is an
étale scheme chart `W` of `X` and a morphism of charts `a : W ⟶ U` whose base change along `f`
is an isomorphism and which lies in the image sieve of `φ`.

The represented base changes of `f` are homeomorphisms onto closed subsets, hence topological
embeddings, which is the only property of them the argument uses. -/
theorem exists_isIso_smallBaseChange_map_of_isIntegralHom_of_universallyInjective
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable f.hom) (hint : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) (U U' : SmallEtale B S hS X.1)
    (φ : (smallBaseChange B S hS f hrep).obj U ⟶ (smallBaseChange B S hS f hrep).obj U') :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U),
      IsIso ((smallBaseChange B S hS f hrep).map a) ∧
        ((smallBaseChange B S hS f hrep).imageSieve φ).arrows a :=
  exists_isIso_smallBaseChange_map_of_isInducing B S hS f hrep
    (fun g => (isClosedEmbedding_toScheme_map_snd B S hS Y.property X.property hrep hint hui
      g).isInducing) U U' φ

/-! ### Local fullness -/

/-- **Local fullness of chart base change along an integral universally injective morphism.**
For an integral and universally injective morphism `f : Y ⟶ X` of algebraic spaces over a
scheme `S`, base change along `f` of étale scheme charts is a locally full functor from the
small étale site of `X` to the small étale site of `Y`: a morphism over `Y` between the base
changes of two étale charts of `X` is, locally on the source, the base change of a morphism of
charts of `X`.

No covering family has to be produced: the chart of
`AlgebraicGeometry.Space.exists_isIso_smallBaseChange_map_of_isIntegralHom_of_universallyInjective`
already has invertible base change, so the sieve it generates is the whole sieve. -/
theorem smallBaseChange_isLocallyFull_of_isIntegralHom_of_universallyInjective
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable f.hom) (hint : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) :
    (smallBaseChange B S hS f hrep).IsLocallyFull (SmallEtale.topology B S hS Y.1) := by
  refine ⟨fun {U U'} φ => ?_⟩
  obtain ⟨W, a, hiso, ha⟩ :=
    exists_isIso_smallBaseChange_map_of_isIntegralHom_of_universallyInjective B S hS f hrep
      hint hui U U' φ
  have := hiso
  exact functorPushforward_imageSieve_mem (smallBaseChange B S hS f hrep)
    (SmallEtale.topology B S hS Y.1) φ a ha

end Space

end AlgebraicGeometry

end
