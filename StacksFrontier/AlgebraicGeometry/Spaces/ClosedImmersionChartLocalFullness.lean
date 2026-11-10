module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.LiftingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting

/-!
# Base change of étale charts along a closed immersion is locally full

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. Base change along
`i` carries étale scheme charts of `X` to étale scheme charts of `Z`
(`AlgebraicGeometry.Space.smallBaseChange`), and the resulting functor between the small étale
sites is *locally full*: a morphism over `Z` between the base changes of two étale charts of `X`
comes, locally on the source, from a morphism of charts of `X`.

The source of local fullness is the following statement about a single morphism: given étale
charts `U` and `U'` of `X` and a morphism `φ : U ×_X Z ⟶ U' ×_X Z` over `Z`, there is an étale
chart `W` of `X` together with morphisms of charts `a : W ⟶ U` and `b : W ⟶ U'` such that the
base change of `a` is an isomorphism and the base change of `b` is the base change of `a`
followed by `φ`. Since the base change of `a` is an isomorphism, the sieve it generates is the
whole sieve, so no covering family has to be produced at all.

The chart `W` is an open subscheme of `U ×_X U'`, cut out by the graph of `φ`. That graph is a
morphism `U ×_X Z ⟶ U ×_X U'` which lifts to a section of the projection
`(U ×_X U') ×_X Z ⟶ U ×_X Z`; the projection is étale, hence the section is an open immersion,
and since `(U ×_X U') ×_X Z ⟶ U ×_X U'` is a closed immersion of schemes, the open image of the
section extends to an open subscheme `W` of `U ×_X U'`. This is the argument of Stacks 04FV,
transferred from schemes to algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.exists_isIso_smallBaseChange_map_of_isClosedImmersion` produces the
  open subchart of `U ×_X U'` and the morphism of charts with invertible base change; it is the
  algebraic-space form of Stacks 04FV.
* `AlgebraicGeometry.Space.smallBaseChange_isLocallyFull_of_isClosedImmersion` is the local
  fullness of chart base change along a closed immersion, part of Stacks 04E5, part (1).

## Implementation notes

All fibre products occurring here are the chosen representable pullbacks supplied by
representability: `CategoryTheory.Functor.relativelyRepresentable.pullback` for the closed
immersion `i` and for the étale chart `U`. Morphisms into them are built with
`CategoryTheory.Functor.relativelyRepresentable.lift` and `…lift'` and compared with
`…hom_ext`, so the combinatorial part of the argument takes place in the big fppf site of `S`
rather than in schemes.

Beyond the existence of the open subscheme, the only scheme-theoretic input is that the base
change `W ×_X Z ⟶ (U ×_X U') ×_X Z` of the open immersion `W ⟶ U ×_X U'` has image inside the
image of the graph section. The reverse inclusion — which would say that the two open
subschemes agree — is never needed: the retraction supplied by the section already forces the
base change of `a` to be invertible.

The main argument is carried out for a representable morphism all of whose represented base
changes are closed immersions of schemes, with that condition spelled out rather than bundled,
because a bundled hypothesis of that shape blocks rewriting inside the proof. Likewise every
morphism between base-changed charts is introduced with its type written in terms of the chosen
representable pullbacks.

## References

* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

/-! ### Preliminaries on schemes and on sieves -/

/-- If an open immersion `d` has a retraction `p`, then every morphism `r` whose range lies in
the range of `d` satisfies `r ≫ p ≫ d = r`. -/
public lemma comp_retraction_eq_of_range_subset {A A' C : Scheme.{u}}
    (d : A ⟶ A') (p : A' ⟶ A) (r : C ⟶ A') [IsOpenImmersion d]
    (hdp : d ≫ p = 𝟙 A) (hr : Set.range r ⊆ Set.range d) :
    r ≫ p ≫ d = r := by
  rw [← IsOpenImmersion.lift_fac d r hr, Category.assoc, reassoc_of% hdp]

/-- If the image sieve of `f : F.obj U ⟶ F.obj V` contains a morphism `a` with `F.map a` an
isomorphism, then its pushforward along `F` is a covering sieve of `F.obj U` for every
Grothendieck topology. -/
public lemma functorPushforward_imageSieve_mem {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (K : GrothendieckTopology D)
    {U V W : C} (f : F.obj U ⟶ F.obj V) (a : W ⟶ U)
    (ha : (F.imageSieve f).arrows a) [IsIso (F.map a)] :
    (F.imageSieve f).functorPushforward F ∈ K (F.obj U) := by
  have htop : (F.imageSieve f).functorPushforward F = ⊤ := by
    rw [← Sieve.id_mem_iff_eq_top]
    have h₁ := Sieve.image_mem_functorPushforward F (F.imageSieve f) ha
    have h₂ := ((F.imageSieve f).functorPushforward F).downward_closed h₁ (inv (F.map a))
    rwa [IsIso.inv_hom_id] at h₂
  rw [htop]
  exact K.top_mem _

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Lifting a morphism of schemes to the site -/

/-- If `g : C ⟶ A` factors through `p : D ⟶ A` on underlying schemes, then it factors through `p`
in `BigFppfOver B S hS`. -/
public lemma exists_hom_of_toScheme_fac {A C D : BigFppfOver B S hS} (p : D ⟶ A) (g : C ⟶ A)
    (t : (BigFppfOver.toScheme B S hS).obj C ⟶ (BigFppfOver.toScheme B S hS).obj D)
    (ht : t ≫ (BigFppfOver.toScheme B S hS).map p = (BigFppfOver.toScheme B S hS).map g) :
    ∃ s : C ⟶ D, s ≫ p = g := by
  obtain ⟨v, hv⟩ := B.inclusion.map_surjective (X := C.left) (Y := D.left) t
  have hDhom : B.inclusion.map D.hom =
      (BigFppfOver.toScheme B S hS).map p ≫ B.inclusion.map A.hom := by
    change B.inclusion.map D.hom = B.inclusion.map p.left ≫ B.inclusion.map A.hom
    rw [← Functor.map_comp, Over.w p]
  have hChom : (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map A.hom =
      B.inclusion.map C.hom := by
    change B.inclusion.map g.left ≫ B.inclusion.map A.hom = B.inclusion.map C.hom
    rw [← Functor.map_comp, Over.w g]
  have hw : v ≫ D.hom = C.hom := by
    refine B.inclusion.map_injective ?_
    rw [Functor.map_comp, hv, hDhom, ← Category.assoc, ht, hChom]
  refine ⟨Over.homMk v hw, Over.OverMorphism.ext ?_⟩
  change v ≫ p.left = g.left
  refine B.inclusion.map_injective ?_
  rwa [Functor.map_comp, hv]

/-! ### The algebraic-space form of Stacks 04FV -/

private lemma exists_isIso_smallBaseChange_map_aux
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hrep : yoneda.relativelyRepresentable i.hom)
    (hclosed : ∀ {A : BigFppfOver B S hS} (g : yoneda.obj A ⟶ X.1),
      AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hrep.snd g)))
    (U U' : SmallEtale B S hS X.1)
    (φ : (smallBaseChange B S hS i hrep).obj U ⟶ (smallBaseChange B S hS i hrep).obj U') :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U),
      IsIso ((smallBaseChange B S hS i hrep).map a) ∧
        ((smallBaseChange B S hS i hrep).imageSieve φ).arrows a := by
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
  have hmChart : mChart = yoneda.map prU ≫ U.1.hom := rfl
  have hM : IsEtaleChart B S hS X.1 (CostructuredArrow.mk mChart) :=
    etale_comp_of_scheme B S hS prU U.1.hom hprUetale U.property
  let Mc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk mChart, hM⟩
  let kU : Mc ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk prU rfl)
  let kU' : Mc ⟶ U' := ObjectProperty.homMk (CostructuredArrow.homMk prU' hMw.symm)
  -- morphisms between base-changed charts are determined by their second components
  have hfw : ∀ {V W : SmallEtale B S hS X.1}
      (f : (smallBaseChange B S hS i hrep).obj V ⟶ (smallBaseChange B S hS i hrep).obj W),
      yoneda.map f.hom.left ≫ hrep.fst W.1.hom = hrep.fst V.1.hom :=
    fun f => CostructuredArrow.w f.hom
  have hext : ∀ {V W : SmallEtale B S hS X.1}
      (f g : (smallBaseChange B S hS i hrep).obj V ⟶ (smallBaseChange B S hS i hrep).obj W),
      f.hom.left ≫ hrep.snd W.1.hom = g.hom.left ≫ hrep.snd W.1.hom → f = g :=
    fun f g h => ObjectProperty.hom_ext _
      (CostructuredArrow.hom_ext _ _ (hrep.hom_ext ((hfw f).trans (hfw g).symm) h))
  -- the projections of the base-changed charts, and the closed immersion above `U ×_X U'`
  let π : hrep.pullback mChart ⟶ hrep.pullback U.1.hom :=
    ((smallBaseChange B S hS i hrep).map kU).hom.left
  let π' : hrep.pullback mChart ⟶ hrep.pullback U'.1.hom :=
    ((smallBaseChange B S hS i hrep).map kU').hom.left
  let c : hrep.pullback mChart ⟶ M := hrep.snd mChart
  have hπw : yoneda.map π ≫ hrep.fst U.1.hom = hrep.fst mChart :=
    hfw ((smallBaseChange B S hS i hrep).map kU)
  have hπsnd : π ≫ hrep.snd U.1.hom = c ≫ prU :=
    smallBaseChange_map_snd B S hS i hrep kU
  have hπ'snd : π' ≫ hrep.snd U'.1.hom = c ≫ prU' :=
    smallBaseChange_map_snd B S hS i hrep kU'
  have hπetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map π) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (representablePullbackMap_isPullback_scheme B S hS i hrep kU).flip hprUetale
  -- the graph of `φ`
  let ϕ : hrep.pullback U.1.hom ⟶ hrep.pullback U'.1.hom := φ.hom.left
  have hφw : yoneda.map ϕ ≫ hrep.fst U'.1.hom = hrep.fst U.1.hom :=
    hfw φ
  have hγcond : yoneda.map (hrep.snd U.1.hom) ≫ U.1.hom =
      yoneda.map (ϕ ≫ hrep.snd U'.1.hom) ≫ U'.1.hom := by
    rw [← hrep.w U.1.hom, ← hφw, Category.assoc, hrep.w U'.1.hom, Functor.map_comp,
      Category.assoc]
  let γ : hrep.pullback U.1.hom ⟶ M :=
    U.property.rep.lift' (hrep.snd U.1.hom) (ϕ ≫ hrep.snd U'.1.hom) hγcond
  have hγfst : γ ≫ prU = hrep.snd U.1.hom := U.property.rep.lift'_fst _ _ _
  have hγsnd : γ ≫ prU' = ϕ ≫ hrep.snd U'.1.hom := U.property.rep.lift'_snd _ _ _
  -- the graph is a section of the projection `(U ×_X U') ×_X Z ⟶ U ×_X Z`
  have hδcond : hrep.fst U.1.hom ≫ i.hom = yoneda.map γ ≫ mChart := by
    rw [hmChart, hrep.w U.1.hom, ← hγfst, Functor.map_comp, Category.assoc]
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
  have hcclosed : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map c) := hclosed mChart
  obtain ⟨O, hO⟩ := exists_open_extension_of_closedImmersion
    ((BigFppfOver.toScheme B S hS).map c)
    ((BigFppfOver.toScheme B S hS).map δ).opensRange
  let MO := openSiteObject B S hS M O
  let ιO : MO ⟶ M := openSiteObjectHom B S hS M O
  have hιOmap : (BigFppfOver.toScheme B S hS).map ιO = O.ι := map_openSiteObjectHom B S hS M O
  have hιOetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ιO) := by
    rw [hιOmap]; exact inferInstanceAs (AlgebraicGeometry.Etale O.ι)
  have hιOopen : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map ιO) := by
    rw [hιOmap]; exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion O.ι)
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
    ((smallBaseChange B S hS i hrep).map kO).hom.left
  have hρsnd : ρ ≫ c = hrep.snd oChart ≫ ιO :=
    smallBaseChange_map_snd B S hS i hrep kO
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
    have he : (BigFppfOver.toScheme B S hS).map γ w =
        (BigFppfOver.toScheme B S hS).map c ((BigFppfOver.toScheme B S hS).map δ w) := by
      rw [hγmap, Scheme.Hom.comp_apply]
    rwa [he]
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
  have hαsnd : (ρ ≫ π) ≫ hrep.snd U.1.hom = hrep.snd oChart ≫ ιO ≫ prU := by
    rw [Category.assoc, hπsnd, ← Category.assoc, hρsnd, Category.assoc]
  have hαδ : (ρ ≫ π) ≫ δ = ρ := by rw [Category.assoc, hρδ]
  have hαγ : (ρ ≫ π) ≫ γ = hrep.snd oChart ≫ ιO := by
    rw [← hδsnd, ← Category.assoc, hαδ, hρsnd]
  have hψcond : hrep.fst U.1.hom ≫ i.hom = yoneda.map σ ≫ oChart := by
    rw [hoChart, hδcond, ← hσ, Functor.map_comp, Category.assoc]
  let ψ : hrep.pullback U.1.hom ⟶ hrep.pullback oChart :=
    hrep.lift (hrep.fst U.1.hom) σ hψcond
  have hψfst : yoneda.map ψ ≫ hrep.fst oChart = hrep.fst U.1.hom := hrep.lift_fst _ _ _
  have hψsnd : ψ ≫ hrep.snd oChart = σ := hrep.lift_snd _ _ _
  have hασ : (ρ ≫ π) ≫ σ = hrep.snd oChart :=
    (BigFppfOver.toScheme B S hS).map_injective
      ((cancel_mono ((BigFppfOver.toScheme B S hS).map ιO)).mp (by
        rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hσ, hαγ]))
  let ψc : (smallBaseChange B S hS i hrep).obj U ⟶ (smallBaseChange B S hS i hrep).obj Wc :=
    ObjectProperty.homMk (CostructuredArrow.homMk ψ hψfst)
  have hone : (smallBaseChange B S hS i hrep).map (kO ≫ kU) ≫ ψc =
      𝟙 ((smallBaseChange B S hS i hrep).obj Wc) := by
    rw [Functor.map_comp]
    refine hext _ _ ?_
    change ((ρ ≫ π) ≫ ψ) ≫ hrep.snd oChart = 𝟙 (hrep.pullback oChart) ≫ hrep.snd oChart
    rw [Category.assoc, hψsnd, hασ, Category.id_comp]
  have htwo : ψc ≫ (smallBaseChange B S hS i hrep).map (kO ≫ kU) =
      𝟙 ((smallBaseChange B S hS i hrep).obj U) := by
    rw [Functor.map_comp]
    refine hext _ _ ?_
    change (ψ ≫ ρ ≫ π) ≫ hrep.snd U.1.hom = 𝟙 (hrep.pullback U.1.hom) ≫ hrep.snd U.1.hom
    rw [Category.assoc, hαsnd, reassoc_of% hψsnd, reassoc_of% hσ, hγfst, Category.id_comp]
  have hsieve : (smallBaseChange B S hS i hrep).map (kO ≫ kU') =
      (smallBaseChange B S hS i hrep).map (kO ≫ kU) ≫ φ := by
    rw [Functor.map_comp, Functor.map_comp]
    refine hext _ _ ?_
    change (ρ ≫ π') ≫ hrep.snd U'.1.hom = ((ρ ≫ π) ≫ ϕ) ≫ hrep.snd U'.1.hom
    rw [Category.assoc, hπ'snd, ← Category.assoc, hρsnd, Category.assoc, Category.assoc,
      ← hγsnd, ← Category.assoc (ρ ≫ π), hαγ, Category.assoc]
  exact ⟨Wc, kO ≫ kU, ⟨ψc, hone, htwo⟩, kO ≫ kU', hsieve⟩

/-- **Stacks 04FV** for algebraic spaces. Let `i : Z ⟶ X` be a closed immersion of algebraic
spaces over a scheme `S`, let `U` and `U'` be étale scheme charts of `X`, and let `φ` be a
morphism over `Z` between their base changes along `i`. Then there is an étale scheme chart `W`
of `X` and a morphism of charts `a : W ⟶ U` whose base change along `i` is an isomorphism and
which lies in the image sieve of `φ`: the base change of `a` followed by `φ` is the base change
of a morphism of charts `W ⟶ U'`.

The chart `W` is an open subscheme of `U ×_X U'` containing the image of the graph of `φ`. -/
@[stacks 04FV "for algebraic spaces"]
theorem exists_isIso_smallBaseChange_map_of_isClosedImmersion
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (U U' : SmallEtale B S hS X.1)
    (φ : (smallBaseChange B S hS i hi.rep).obj U ⟶ (smallBaseChange B S hS i hi.rep).obj U') :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U),
      IsIso ((smallBaseChange B S hS i hi.rep).map a) ∧
        ((smallBaseChange B S hS i hi.rep).imageSieve φ).arrows a :=
  exists_isIso_smallBaseChange_map_aux B S hS i hi.rep (fun g => hi.property_snd g) U U' φ

/-! ### Local fullness -/

/-- **Stacks 04E5, part (1)**, local fullness. For a closed immersion `i : Z ⟶ X` of algebraic
spaces over a scheme `S`, base change along `i` of étale scheme charts is a locally full functor
from the small étale site of `X` to the small étale site of `Z`: a morphism over `Z` between the
base changes of two étale charts of `X` is, locally on the source, the base change of a morphism
of charts of `X`.

No covering family has to be produced: the chart of
`AlgebraicGeometry.Space.exists_isIso_smallBaseChange_map_of_isClosedImmersion` already has
invertible base change, so the sieve it generates is the whole sieve. -/
@[stacks 04E5 "part (1), local fullness of base change on scheme charts"]
theorem smallBaseChange_isLocallyFull_of_isClosedImmersion
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (smallBaseChange B S hS i hi.rep).IsLocallyFull (SmallEtale.topology B S hS Z.1) := by
  refine ⟨fun {U U'} φ => ?_⟩
  obtain ⟨W, a, _, ha⟩ :=
    exists_isIso_smallBaseChange_map_of_isClosedImmersion B S hS i hi U U' φ
  exact functorPushforward_imageSieve_mem (smallBaseChange B S hS i hi.rep)
    (SmallEtale.topology B S hS Z.1) φ a ha

end Space

end AlgebraicGeometry

end
