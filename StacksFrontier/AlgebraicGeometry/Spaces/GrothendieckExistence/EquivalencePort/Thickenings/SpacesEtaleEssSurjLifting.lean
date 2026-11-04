module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Lifted étale presentations from the two lifting steps

This file continues `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj`. There
essential surjectivity of base change along `f : X ⟶ Y` on spaces-étale sites is proved through
lifted étale presentations, at a first-order thickening and at the inclusion of a thickening
subspace of arbitrary order. Here the construction is isolated from the hypothesis on `f`: it
needs only a chart-level closed immersion surjective on points, and unique extension of
morphisms into spaces étale over `Y` across base changes of `f`.

## Main results

* `AlgebraicGeometry.Space.C1573.exists_chart_isClosedImmersion_of_mono_of_isThickening`: a
  monomorphism whose range is a thickening of arbitrary order restricts to a closed immersion of
  objects of the site, surjective on points, over any étale chart of the ambient space.
* `AlgebraicGeometry.Space.C1573.exists_liftedEtalePresentation_charts_of_chart`: the charts, the
  kernel pair and the two étale lifts of a lifted étale presentation exist, given the chart-level
  closed immersion.
* `AlgebraicGeometry.Space.C1573.nonempty_liftedEtalePresentation_of_lifting` and
  `AlgebraicGeometry.Space.C1573.essSurj_spacesBaseChange_of_liftedEtalePresentation`: the
  reduction of essential surjectivity to the chart-level closed immersion and to unique extension.
  At a monomorphism whose range is a thickening of arbitrary order both inputs are supplied in
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEquivalenceGeneral.lean`.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart-level closed immersion of a monomorphism whose range is a thickening -/

/-- **The inclusion of a thickening of arbitrary order restricts to a thickening of any étale
chart of the ambient space.** Let `f : X ⟶ Y` be a monomorphism whose range is a thickening of
`Y`, of arbitrary order. For an étale chart `ζ` of `Y` by an object `Z` of the site, the base
change of `f` along `ζ` is represented by an object `J` of the site, the morphism `j : J ⟶ Z` is a
closed immersion of schemes, and it is surjective on points.

The range of `f` is a closed subspace, so its inclusion is representable by closed immersions,
and its base change along `ζ` is the closed immersion `j`; the square is read over `f` itself
through the inverse of the isomorphism `CategoryTheory.Subfunctor.toRange`, available because
`f.hom` is a monomorphism. Surjectivity on points is Stacks 03MH,
`AlgebraicGeometry.Space.isSurjective_of_isPullback`: `j` is a base change of the inclusion of
the range, which is surjective on points by the definition of a thickening, Stacks 05ZK, part (1).
No order of the thickening enters. -/
theorem C1573.exists_chart_isClosedImmersion_of_mono_of_isThickening
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) (_hζ : IsEtale B S hS ζ) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
      IsPullback (yoneda.map j) η ζ f.hom ∧
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map j) ∧
        Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base := by
  obtain ⟨hGc, hsurj⟩ := hT
  have hpb := hGc.2.rep.isPullback ζ
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hGc.2.rep.snd ζ)) :=
    hGc.2.property ζ _ _ hpb
  -- The chart-level morphism is surjective on points, being a base change of the inclusion.
  have hpbSp : IsPullback
      (ObjectProperty.homMk (hGc.2.rep.fst ζ) :
        (⟨_, isAlgebraicSpace_yoneda B S hS (hGc.2.rep.pullback ζ)⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨_, hGc.1⟩)
      (ObjectProperty.homMk (yoneda.map (hGc.2.rep.snd ζ)) :
        (⟨_, isAlgebraicSpace_yoneda B S hS (hGc.2.rep.pullback ζ)⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨_, isAlgebraicSpace_yoneda B S hS Z⟩)
      (ObjectProperty.homMk (Subfunctor.range f.hom).ι : (⟨_, hGc.1⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (ObjectProperty.homMk ζ : (⟨_, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS) ⟶
        Y) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hpb
  have hjsurj : Surjective ((BigFppfOver.toScheme B S hS).map (hGc.2.rep.snd ζ)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1
      ((surjective_yonedaMap_iff_surjective_pointsMap B S hS _).2
        (isSurjective_of_isPullback B S hS hpbSp hsurj))
  -- Read the square over `f` itself.
  have hinv : inv (Subfunctor.toRange f.hom) ≫ f.hom = (Subfunctor.range f.hom).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι f.hom).symm
  have hiso : IsPullback (inv (Subfunctor.toRange f.hom)) (Subfunctor.range f.hom).ι f.hom
      (𝟙 Y.1) :=
    IsPullback.of_horiz_isIso ⟨by rw [hinv, Category.comp_id]⟩
  have hpaste := hpb.paste_horiz hiso
  rw [Category.comp_id] at hpaste
  exact ⟨_, hGc.2.rep.snd ζ, hGc.2.rep.fst ζ ≫ inv (Subfunctor.toRange f.hom), hpaste.flip, hci,
    hjsurj.surj⟩

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The charts and the two étale lifts of a lifted étale presentation -/

/-- **The charts and the two étale lifts of a lifted étale presentation exist.** Let `f` be a
morphism which, over every étale chart `ζ` of `Y` by an object `Z` of the site, restricts to a
closed immersion `j : J ⟶ Z` of objects of the site surjective on points. For an object `C` of
the spaces-étale site of `X`, there are objects `V`, `W`, `U`, `R` of the site, structure
morphisms `v`, `w` making `V` and `W` étale over `Y`, a surjective étale chart `c` of `C` by `U`
with kernel pair `(s, t)` by `R`, and projections `a : U ⟶ V`, `b : R ⟶ W` exhibiting `U` and `R`
as the base changes of `V` and of `W` along `f`.

These are all the data and all the cartesian squares of
`AlgebraicGeometry.Space.LiftedEtalePresentation` except the two maps `k₁`, `k₂` of the relation
and the properties that mention them. The last cartesian square replaces
`AlgebraicGeometry.Space.LiftedEtalePresentation.isPullback_b`, which follows from it, from
`isPullback_a` and from `k₁` by `CategoryTheory.IsPullback.of_right`.

The construction: an étale chart `ζ` of `Y` by an object `Z` of the site restricts `f` to a
closed immersion `j : J ⟶ Z` of objects of the site which is surjective on points, by the
hypothesis — for a monomorphism whose range is a thickening of arbitrary order it is
`AlgebraicGeometry.Space.C1573.exists_chart_isClosedImmersion_of_mono_of_isThickening`. An étale
chart of `C` based changed to `J` gives `U`, whose kernel pair over `C` is `R`; both are étale
over `J`, so both lift across `j` by Stacks 039R in the form
`AlgebraicGeometry.Space.exists_etaleLift_isPullback_of_chart`, which also transports the
cartesian squares down to `f`. -/
theorem C1573.exists_liftedEtalePresentation_charts_of_chart (f : X ⟶ Y)
    (hJ : ∀ (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1), IsEtale B S hS ζ →
      ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
        IsPullback (yoneda.map j) η ζ f.hom ∧
          _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
          Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base)
    (C : SpacesEtale B S hS X) :
    ∃ (V W U R : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y.1) (w : yoneda.obj W ⟶ Y.1)
        (c : yoneda.obj U ⟶ C.1.left.1) (a : U ⟶ V) (b : R ⟶ W) (s t : R ⟶ U),
      IsEtale B S hS v ∧ IsEtale B S hS w ∧ IsEtale B S hS c ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) c ∧
        IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom ∧
        IsPullback (yoneda.map t) (yoneda.map s) c c ∧
        IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w f.hom := by
  -- An étale chart of `Y`, and the restriction of the thickening to it.
  obtain ⟨Z, ζ, hζS, hζE⟩ := Y.2.exists_atlas
  have hζI : IsEtale B S hS ζ := isEtale_of_presheaf_etale B S hS hζE
  obtain ⟨J, j, η, hchart, hci, hjsurj⟩ := hJ Z ζ hζI
  have hηE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf η :=
    etalePresheaf_of_isPullback B S hS hchart hζE
  have hηS : (SurjSite B S hS).presheaf η := surjectivePresheaf_of_isPullback B S hS hchart hζS
  -- An étale chart of `C`, and its base change to the chart of the thickening.
  obtain ⟨U', c', hc'S, hc'E⟩ := C.1.left.2.exists_atlas
  have hg₀E : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (c' ≫ C.1.hom.hom) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hc'E) C.2)
  obtain ⟨U, κ, m, hUpb⟩ :
      ∃ (U : BigFppfOver B S hS) (κ : yoneda.obj U ⟶ yoneda.obj J) (m : U ⟶ U'),
        IsPullback κ (yoneda.map m) η (c' ≫ C.1.hom.hom) :=
    ⟨_, _, _, hηE.rep.isPullback (c' ≫ C.1.hom.hom)⟩
  obtain ⟨k, rfl⟩ := yoneda.map_surjective κ
  have hmE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m) :=
    etalePresheaf_of_isPullback B S hS hUpb hηE
  have hmS : (SurjSite B S hS).presheaf (yoneda.map m) :=
    surjectivePresheaf_of_isPullback B S hS hUpb hηS
  have hkE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1
      (etalePresheaf_of_isPullback B S hS hUpb.flip hg₀E)
  -- The chart of `C` through the base change, and its kernel pair.
  have hcE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m ≫ c') :=
    etaleSite_presheaf_comp B S hS hmE hc'E
  have hcS : (SurjSite B S hS).presheaf (yoneda.map m ≫ c') :=
    surjSite_presheaf_comp B S hS hmS hc'S
  have hcw : yoneda.map k ≫ η = (yoneda.map m ≫ c') ≫ C.1.hom.hom :=
    hUpb.w.trans (Category.assoc _ _ _).symm
  obtain ⟨R, s₀, t₀, hker⟩ :
      ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) (yoneda.map m ≫ c') (yoneda.map m ≫ c') :=
    ⟨hcE.rep.pullback _, yoneda.preimage (hcE.rep.fst _), hcE.rep.snd _, by
      rw [yoneda.map_preimage]
      exact hcE.rep.isPullback _⟩
  have htE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (s₀ ≫ k)) := by
    have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s₀) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ s₀).1
        (etalePresheaf_of_isPullback B S hS hker.flip hcE)
    rw [Functor.map_comp]
    infer_instance
  -- The two étale lifts across the chart-level thickening.
  obtain ⟨V, q, a, -, hvE, -, hpresA⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart k hkE
  obtain ⟨W, qW, b, -, hwE, -, hpresB⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart (s₀ ≫ k) htE
  refine ⟨V, W, U, R, yoneda.map q ≫ ζ, yoneda.map qW ≫ ζ, yoneda.map m ≫ c', a, b, t₀, s₀,
    hvE, hwE, isEtale_of_presheaf_etale B S hS hcE, hcS, ?_, hker, ?_⟩
  · rwa [← hcw]
  · rw [Functor.map_comp, Category.assoc, hcw] at hpresB
    simpa only [Category.assoc] using hpresB

/-! ### Existence of a lifted étale presentation from the two lifting steps -/

/-- **A lifted étale presentation exists as soon as the two lifting steps are available.** Let
`f : X ⟶ Y` be a monomorphism such that

* over every étale chart `ζ` of `Y` by an object `Z` of the site, the base change of `f` is a
  closed immersion `j : J ⟶ Z` of objects of the site which is surjective on points, and
* every morphism `H ⟶ G` over `Y`, from a base change `H` of `f` along a morphism `F ⟶ Y` out of
  an algebraic space `F` into an algebraic space `G` étale over `Y`, extends uniquely to a
  morphism `F ⟶ G` over `Y`.

Then every object of the spaces-étale site of `X` admits a lifted étale presentation across `f`.

The first input produces the charts and the two étale lifts, by
`AlgebraicGeometry.Space.C1573.exists_liftedEtalePresentation_charts_of_chart`; the second produces
the two maps of the relation and proves that they form an étale equivalence relation, as
recorded in the implementation notes. Both inputs hold for the inclusion of a first-order
thickening, which is `AlgebraicGeometry.Space.nonempty_liftedEtalePresentation`, and for the
inclusion of a thickening of arbitrary order. -/
theorem C1573.nonempty_liftedEtalePresentation_of_lifting (f : X ⟶ Y) [Mono f.hom]
    (hJ : ∀ (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1), IsEtale B S hS ζ →
      ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
        IsPullback (yoneda.map j) η ζ f.hom ∧
          _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
          Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base)
    (hlift : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      IsAlgebraicSpace B S hS G → ∀ {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1},
      IsPullback π q v f.hom → ∀ (w : G ⟶ Y.1), IsEtale B S hS w → ∀ (d : H ⟶ G),
      d ≫ w = π ≫ v → ∃! α : F ⟶ G, π ≫ α = d ∧ α ≫ w = v)
    (C : SpacesEtale B S hS X) :
    Nonempty (LiftedEtalePresentation B S hS f C) := by
  have hext : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      IsAlgebraicSpace B S hS G → ∀ {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1},
      IsPullback π q v f.hom → ∀ (w : G ⟶ Y.1), IsEtale B S hS w → ∀ (α β : F ⟶ G),
      α ≫ w = v → β ≫ w = v → π ≫ α = π ≫ β → α = β := by
    intro F G H hF hG v π q hpb w hw α β hα hβ h
    obtain ⟨α₀, -, huniq⟩ := hlift hF hG hpb w hw (π ≫ α) (by rw [Category.assoc, hα])
    rw [huniq α ⟨rfl, hα⟩, huniq β ⟨h.symm, hβ⟩]
  obtain ⟨V, W, U, R, v, w, c, a, b, s, t, hv, hw, hc, hcS, hA, hC, hB⟩ :=
    exists_liftedEtalePresentation_charts_of_chart B S hS f hJ C
  have hVas := isAlgebraicSpace_yoneda B S hS V
  have hWas := isAlgebraicSpace_yoneda B S hS W
  have hmonoA : Mono (yoneda.map a) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) hA.flip
      (inferInstanceAs (Mono f.hom))
  -- The two maps of the relation, the unique extensions of `t ≫ a` and of `s ≫ a` over `Y`.
  have hd₁ : (yoneda.map t ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [Category.assoc]
  obtain ⟨κ₁, ⟨hκ₁b, hκ₁v⟩, -⟩ := hlift
    hWas hVas hB v hv (yoneda.map t ≫ yoneda.map a) hd₁
  obtain ⟨k₁, rfl⟩ := yoneda.map_surjective κ₁
  have hd₂ : (yoneda.map s ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [← Category.assoc]
    rw [← hC.w]
  obtain ⟨κ₂, ⟨hκ₂b, hκ₂v⟩, -⟩ := hlift
    hWas hVas hB v hv (yoneda.map s ≫ yoneda.map a) hd₂
  obtain ⟨k₂, rfl⟩ := yoneda.map_surjective κ₂
  have hbk₁ : b ≫ k₁ = t ≫ a :=
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact hκ₁b)
  have hbk₂ : b ≫ k₂ = s ≫ a :=
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact hκ₂b)
  -- `R` is the fibre product of `W` and of `U` over `V`.
  have hPB : IsPullback (yoneda.map b) (yoneda.map t) (yoneda.map k₁) (yoneda.map a) := by
    refine IsPullback.of_bot ?_ ?_ hA
    · rw [hκ₁v]; exact hB
    · rw [← Functor.map_comp, ← Functor.map_comp, hbk₁]
  have hbk₂' : yoneda.map b ≫ yoneda.map k₂ = yoneda.map s ≫ yoneda.map a := by
    rw [← Functor.map_comp, ← Functor.map_comp, hbk₂]
  -- The two maps of the relation are étale, by Stacks 03MJ on charts.
  have hwP : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf w :=
    etalePresheaf_of_isEtale_yonedaDomain B S hS w hw
  have hvP : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf v :=
    etalePresheaf_of_isEtale_yonedaDomain B S hS v hv
  have hk₁E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₁) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₁v
  have hk₂E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₂) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₂v
  -- Joint monicity of the pair inside the site.
  have hjm : ∀ (T : BigFppfOver B S hS) (x y : T ⟶ W), x ≫ k₂ = y ≫ k₂ → x ≫ k₁ = y ≫ k₁ →
      x = y := by
    intro T x y h₂ h₁
    apply yoneda.map_injective
    have hyw : yoneda.map y ≫ w = yoneda.map x ≫ w := by
      rw [← hκ₁v]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [h₁]
    obtain ⟨Q, πQ, qQ, hQ⟩ := exists_isPullback_range_of_mono B S hS f (yoneda.map x ≫ w)
    have hxQ : (πQ ≫ yoneda.map x) ≫ w = qQ ≫ f.hom := by
      rw [Category.assoc]; exact hQ.w
    have hyQ : (πQ ≫ yoneda.map y) ≫ w = qQ ≫ f.hom := by
      rw [Category.assoc, hyw]; exact hQ.w
    obtain ⟨ξx, hξx⟩ : ∃ ξ : Q ⟶ yoneda.obj R, ξ ≫ yoneda.map b = πQ ≫ yoneda.map x :=
      ⟨hB.lift _ _ hxQ, hB.lift_fst _ _ hxQ⟩
    obtain ⟨ξy, hξy⟩ : ∃ ξ : Q ⟶ yoneda.obj R, ξ ≫ yoneda.map b = πQ ≫ yoneda.map y :=
      ⟨hB.lift _ _ hyQ, hB.lift_fst _ _ hyQ⟩
    have hkey : ∀ (k : W ⟶ V) (p : R ⟶ U),
        yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a → x ≫ k = y ≫ k →
        ξx ≫ yoneda.map p = ξy ≫ yoneda.map p := by
      intro k p hkp hxy
      refine (cancel_mono (yoneda.map a)).1 ?_
      calc (ξx ≫ yoneda.map p) ≫ yoneda.map a
          = (ξx ≫ yoneda.map b) ≫ yoneda.map k := by
            simp only [Category.assoc, hkp]
        _ = (πQ ≫ yoneda.map x) ≫ yoneda.map k := by rw [hξx]
        _ = (πQ ≫ yoneda.map y) ≫ yoneda.map k := by
            simp only [Category.assoc, ← Functor.map_comp]
            rw [hxy]
        _ = (ξy ≫ yoneda.map b) ≫ yoneda.map k := by rw [hξy]
        _ = (ξy ≫ yoneda.map p) ≫ yoneda.map a := by
            simp only [Category.assoc, hkp]
    have hξ : ξx = ξy := hC.hom_ext (hkey k₁ t hPB.w h₁) (hkey k₂ s hbk₂' h₂)
    refine hext
      (isAlgebraicSpace_yoneda B S hS T) hWas hQ w hw (yoneda.map x) (yoneda.map y)
      rfl hyw ?_
    rw [← hξx, ← hξy, hξ]
  -- Reflexivity, symmetry and transitivity of the kernel pair upstairs.
  obtain ⟨ρ, hρt, hρs⟩ : ∃ ρ : U ⟶ R, ρ ≫ t = 𝟙 U ∧ ρ ≫ s = 𝟙 U := by
    refine ⟨yoneda.preimage (hC.lift (𝟙 _) (𝟙 _) rfl), yoneda.map_injective ?_,
      yoneda.map_injective ?_⟩
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_fst, CategoryTheory.Functor.map_id]
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_snd, CategoryTheory.Functor.map_id]
  obtain ⟨μ, hμt, hμs⟩ : ∃ μ : R ⟶ R, μ ≫ t = s ∧ μ ≫ s = t := by
    refine ⟨yoneda.preimage (hC.lift (yoneda.map s) (yoneda.map t) hC.w.symm),
      yoneda.map_injective ?_, yoneda.map_injective ?_⟩
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_fst]
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_snd]
  -- Reflexivity downstairs.
  have hdr : yoneda.map (ρ ≫ b) ≫ w = yoneda.map a ≫ v := by
    rw [Functor.map_comp, Category.assoc, hB.w, hA.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hρt, CategoryTheory.Functor.map_id, Category.id_comp]
  obtain ⟨r₀, ⟨hr₀a, hr₀w⟩, -⟩ := hlift
    hVas hWas hA w hw (yoneda.map (ρ ≫ b)) hdr
  obtain ⟨rr, rfl⟩ := yoneda.map_surjective r₀
  have hrefl : ∀ (k : W ⟶ V) (p : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ρ ≫ p = 𝟙 U → yoneda.map k ≫ v = w → rr ≫ k = 𝟙 V := by
    intro k p hkp hρp hkv
    apply yoneda.map_injective
    refine hext hVas hVas hA v hv
      (yoneda.map (rr ≫ k)) (yoneda.map (𝟙 V)) ?_ ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hr₀w
    · rw [CategoryTheory.Functor.map_id, Category.id_comp]
    · rw [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, ← Category.assoc, hr₀a]
      simp only [Functor.map_comp, Category.assoc, hkp]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hρp, Category.id_comp]
  -- Symmetry downstairs.
  have hds : yoneda.map (μ ≫ b) ≫ w = yoneda.map b ≫ w := by
    rw [Functor.map_comp, Category.assoc, hB.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hμt, hC.w]
  obtain ⟨σ₀, ⟨hσ₀b, hσ₀w⟩, -⟩ := hlift
    hWas hWas hB w hw (yoneda.map (μ ≫ b)) hds
  obtain ⟨σ, rfl⟩ := yoneda.map_surjective σ₀
  have hsymm : ∀ (k k' : W ⟶ V) (p p' : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      yoneda.map b ≫ yoneda.map k' = yoneda.map p' ≫ yoneda.map a →
      μ ≫ p = p' → yoneda.map k ≫ v = w → yoneda.map k' ≫ v = w → σ ≫ k = k' := by
    intro k k' p p' hkp hkp' hμp hkv hkv'
    apply yoneda.map_injective
    refine hext hWas hVas hB v hv
      (yoneda.map (σ ≫ k)) (yoneda.map k') ?_ hkv' ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hσ₀w
    · rw [Functor.map_comp, ← Category.assoc, hσ₀b]
      simp only [Functor.map_comp, Category.assoc, hkp, hkp']
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hμp]
  -- Transitivity downstairs.
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  obtain ⟨Q, πQ, qQ, hQ⟩ := exists_isPullback_range_of_mono B S hS f
    (yoneda.map (pullback.fst k₁ k₂) ≫ w)
  have hπ₂w : yoneda.map (pullback.snd k₁ k₂) ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w :=
    calc yoneda.map (pullback.snd k₁ k₂) ≫ w
        = yoneda.map (pullback.snd k₁ k₂ ≫ k₂) ≫ v := by
          rw [← hκ₂v, Functor.map_comp, Category.assoc]
      _ = yoneda.map (pullback.fst k₁ k₂ ≫ k₁) ≫ v := by rw [← pullback.condition]
      _ = yoneda.map (pullback.fst k₁ k₂) ≫ w := by
          rw [← hκ₁v, Functor.map_comp, Category.assoc]
  have hQ₁ : (πQ ≫ yoneda.map (pullback.fst k₁ k₂)) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc]; exact hQ.w
  have hQ₂ : (πQ ≫ yoneda.map (pullback.snd k₁ k₂)) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc, hπ₂w]; exact hQ.w
  obtain ⟨ζ₁, hζ₁b, hζ₁x⟩ : ∃ ζ : Q ⟶ yoneda.obj R,
      ζ ≫ yoneda.map b = πQ ≫ yoneda.map (pullback.fst k₁ k₂) ∧
        ζ ≫ (yoneda.map t ≫ c ≫ C.1.hom.hom) = qQ :=
    ⟨hB.lift _ _ hQ₁, hB.lift_fst _ _ hQ₁, hB.lift_snd _ _ hQ₁⟩
  obtain ⟨ζ₂, hζ₂b, hζ₂x⟩ : ∃ ζ : Q ⟶ yoneda.obj R,
      ζ ≫ yoneda.map b = πQ ≫ yoneda.map (pullback.snd k₁ k₂) ∧
        ζ ≫ (yoneda.map t ≫ c ≫ C.1.hom.hom) = qQ :=
    ⟨hB.lift _ _ hQ₂, hB.lift_fst _ _ hQ₂, hB.lift_snd _ _ hQ₂⟩
  have hcross : ζ₁ ≫ yoneda.map t = ζ₂ ≫ yoneda.map s := by
    refine (cancel_mono (yoneda.map a)).1 ?_
    calc (ζ₁ ≫ yoneda.map t) ≫ yoneda.map a
        = (ζ₁ ≫ yoneda.map b) ≫ yoneda.map k₁ := by simp only [Category.assoc, hPB.w]
      _ = πQ ≫ yoneda.map (pullback.fst k₁ k₂ ≫ k₁) := by
          rw [hζ₁b, Functor.map_comp, Category.assoc]
      _ = πQ ≫ yoneda.map (pullback.snd k₁ k₂ ≫ k₂) := by rw [pullback.condition]
      _ = (ζ₂ ≫ yoneda.map b) ≫ yoneda.map k₂ := by
          rw [hζ₂b, Functor.map_comp, Category.assoc]
      _ = (ζ₂ ≫ yoneda.map s) ≫ yoneda.map a := by simp only [Category.assoc, hbk₂']
  have hzc : (ζ₂ ≫ yoneda.map t) ≫ c = (ζ₁ ≫ yoneda.map s) ≫ c := by
    simp only [Category.assoc, ← hC.w]
    rw [← Category.assoc, ← Category.assoc, hcross]
    simp only [Category.assoc, hC.w]
  obtain ⟨ζ, hζt, hζs⟩ : ∃ ζ : Q ⟶ yoneda.obj R,
      ζ ≫ yoneda.map t = ζ₂ ≫ yoneda.map t ∧ ζ ≫ yoneda.map s = ζ₁ ≫ yoneda.map s :=
    ⟨hC.lift _ _ hzc, hC.lift_fst _ _ hzc, hC.lift_snd _ _ hzc⟩
  have hζx : ζ ≫ yoneda.map t ≫ c ≫ C.1.hom.hom = qQ := by
    rw [← Category.assoc ζ (yoneda.map t) (c ≫ C.1.hom.hom), hζt, Category.assoc]
    exact hζ₂x
  have hdt : (ζ ≫ yoneda.map b) ≫ w = πQ ≫ yoneda.map (pullback.fst k₁ k₂) ≫ w := by
    rw [Category.assoc, hB.w, ← Category.assoc, hζx]
    exact hQ.w.symm
  obtain ⟨τ₀, ⟨hτ₀Q, hτ₀w⟩, -⟩ := hlift
    (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hWas hQ w hw (ζ ≫ yoneda.map b) hdt
  obtain ⟨τ, rfl⟩ := yoneda.map_surjective τ₀
  have htrans : ∀ (k : W ⟶ V) (p : R ⟶ U) (π : pullback k₁ k₂ ⟶ W) (ζ' : Q ⟶ yoneda.obj R),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ζ ≫ yoneda.map p = ζ' ≫ yoneda.map p →
      ζ' ≫ yoneda.map b = πQ ≫ yoneda.map π →
      yoneda.map k ≫ v = w → yoneda.map π ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w →
      τ ≫ k = π ≫ k := by
    intro k p π ζ' hkp hζp hζ'b hkv hπw
    apply yoneda.map_injective
    refine hext
      (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hVas hQ v hv
      (yoneda.map (τ ≫ k)) (yoneda.map (π ≫ k)) ?_ ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hτ₀w
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hπw
    · rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hτ₀Q]
      calc (ζ ≫ yoneda.map b) ≫ yoneda.map k
          = ζ ≫ yoneda.map p ≫ yoneda.map a := by rw [Category.assoc, hkp]
        _ = (ζ ≫ yoneda.map p) ≫ yoneda.map a := (Category.assoc _ _ _).symm
        _ = (ζ' ≫ yoneda.map p) ≫ yoneda.map a := by rw [hζp]
        _ = ζ' ≫ yoneda.map b ≫ yoneda.map k := by rw [Category.assoc, hkp]
        _ = (ζ' ≫ yoneda.map b) ≫ yoneda.map k := (Category.assoc _ _ _).symm
        _ = (πQ ≫ yoneda.map π) ≫ yoneda.map k := by rw [hζ'b]
  -- The equivalence relation inside the site.
  have esite : EquivalenceRelation k₂ k₁ :=
    { right_cancellation := by
        intro T x y h₂ h₁
        exact hjm T x y h₂ h₁
      r := rr
      reflexivity₁ := hrefl k₂ s hbk₂' hρs hκ₂v
      reflexivity₂ := hrefl k₁ t hPB.w hρt hκ₁v
      s := σ
      symmetry₁ := hsymm k₂ k₁ s t hbk₂' hPB.w hμs hκ₂v hκ₁v
      symmetry₂ := hsymm k₁ k₂ t s hPB.w hbk₂' hμt hκ₁v hκ₂v
      c := pullback.cone k₁ k₂
      isLimit := pullback.isLimit k₁ k₂
      t := τ
      transitivity₁ := htrans k₂ s (pullback.fst k₁ k₂) ζ₁ hbk₂' hζs hζ₁b hκ₂v rfl
      transitivity₂ := htrans k₁ t (pullback.snd k₁ k₂) ζ₂ hPB.w hζt hζ₂b hκ₁v hπ₂w }
  refine ⟨{
    V := V
    W := W
    U := U
    R := R
    v := v
    w := w
    isEtale_v := hv
    isEtale_w := hw
    k₁ := k₁
    k₂ := k₂
    comp_k₁ := hκ₁v
    comp_k₂ := hκ₂v
    c := c
    isEtale_c := hc
    surjective_c := hcS
    a := a
    b := b
    s := s
    t := t
    isPullback_a := hA
    isPullback_b := hPB
    comp_b_k₂ := hbk₂
    isPullback_c := hC
    isEtaleEquivalenceRelation := ?_ }⟩
  have htarget : (relation B S hS k₁ k₂).target = (Over.post B.inclusion).map k₂ :=
    prod.lift_fst _ _
  have hsource : (relation B S hS k₁ k₂).source = (Over.post B.inclusion).map k₁ :=
    prod.lift_snd _ _
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [htarget, hsource]
    exact isEquivalenceRelation_post_inclusion B S hS esite
  · rw [hsource]
    exact hk₁E
  · rw [htarget]
    exact hk₂E

/-- **Essential surjectivity of base change from lifted étale presentations.** If every object of
the spaces-étale site of `X` admits a lifted étale presentation across `f : X ⟶ Y`, base change
`V ↦ X ×_Y V` is essentially surjective from the spaces-étale site of `Y` to that of `X`: the
quotient of such a presentation is an object of the spaces-étale site of `Y` whose base change
along `f` is the given object. -/
theorem C1573.essSurj_spacesBaseChange_of_liftedEtalePresentation (f : X ⟶ Y)
    (hP : ∀ C : SpacesEtale B S hS X, Nonempty (LiftedEtalePresentation B S hS f C)) :
    (spacesBaseChange B S hS f).functor.EssSurj where
  mem_essImage C := by
    obtain ⟨P⟩ := hP C
    exact exists_iso_functor_obj_of_liftedEtalePresentation B S hS P

end AlgebraicGeometry.Space

end
