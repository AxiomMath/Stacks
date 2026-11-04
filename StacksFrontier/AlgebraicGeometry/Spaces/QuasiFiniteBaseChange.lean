module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Base change of finite type and quasi-finiteness along an arbitrary morphism

The base change of a morphism of algebraic spaces over `S` which is locally of finite type,
of finite type, locally quasi-finite or quasi-finite along an *arbitrary* morphism of
algebraic spaces again has that property. These are Tags 03XH and 03XL, the latter also
being parts (3) and (4) of Tag 0ABM.

## Main results

* `AlgebraicGeometry.Space.presheaf_etale_of_postcomp` cancels an étale morphism of presheaves on
  the right of an étale chart.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isPullback_of_descent`: the every-étale-chart
  condition of Stacks 03MJ for a property of scheme morphisms which is stable under base change
  and composition, holds for the étale morphisms and descends along a surjective étale morphism
  of sources is inherited by an arbitrary base change.
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_representable_target` is the case of a
  representable target.
* `AlgebraicGeometry.Space.IsLocallyOfFiniteType.of_isPullback` and
  `AlgebraicGeometry.Space.IsFiniteType.of_isPullback` are Tag 03XH.
* `AlgebraicGeometry.Space.IsLocallyQuasiFinite.of_isPullback` and
  `AlgebraicGeometry.Space.IsQuasiFinite.of_isPullback` are Tag 03XL, equivalently parts (3)
  and (4) of Tag 0ABM.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 03XL](https://stacks.math.columbia.edu/tag/03XL)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0GWS](https://stacks.math.columbia.edu/tag/0GWS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cancelling an étale morphism of presheaves -/

/-- Étaleness of scheme morphisms, tested after every representable base change, is stable
under base change. -/
private theorem etale_presheaf_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _

/-- A morphism `a' : h_A ⟶ N` of presheaves on the big fppf site of `S` which factors an
étale chart `a : h_A ⟶ M` through a morphism `e : N ⟶ M` which is étale after every
representable base change is itself étale after every representable base change. -/
theorem presheaf_etale_of_postcomp
    {N M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : BigFppfOver B S hS}
    {e : N ⟶ M} {a : yoneda.obj A ⟶ M} {a' : yoneda.obj A ⟶ N}
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hcomm : a' ≫ e = a) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a' := by
  have hbc := etale_presheaf_isStableUnderBaseChange B S hS
  have hi : a' ≫ e = yoneda.map (𝟙 A) ≫ a := by simpa using hcomm
  have h1 : yoneda.map (he.rep.lift a' (𝟙 A) hi) ≫ he.rep.fst a = a' :=
    he.rep.lift_fst a' (𝟙 A) hi
  have h2 : he.rep.lift a' (𝟙 A) hi ≫ he.rep.snd a = 𝟙 A := he.rep.lift_snd a' (𝟙 A) hi
  have hk : Etale ((BigFppfOver.toScheme B S hS).map (he.rep.snd a)) := he.property_snd a
  have hsEtale : Etale ((BigFppfOver.toScheme B S hS).map (he.rep.lift a' (𝟙 A) hi)) := by
    refine MorphismProperty.of_postcomp (@Etale.{u} : MorphismProperty Scheme.{u}) _
      ((BigFppfOver.toScheme B S hS).map (he.rep.snd a)) hk ?_
    rw [← Functor.map_comp, h2, CategoryTheory.Functor.map_id]
    infer_instance
  have hys := presheaf_yoneda_map_of_inverseImage B S hS
    (P := @Etale.{u}) inferInstance (he.rep.lift a' (𝟙 A) hi) hsEtale
  rw [← h1]
  exact MorphismProperty.comp_mem _ _ _ hys (hbc.of_isPullback (he.rep.isPullback a).flip ha)

/-! ### Base change over a representable target -/

/-- The chart condition of Stacks 03MJ for the base change of a morphism `f : X ⟶ h_{Y₀}`
whose target is representable, at a chart square whose chart of the base is an identity.

Here `n₁ : N ⟶ h_V` is the base change of `f` along an arbitrary `yoneda.map v`, `e` is an
étale chart of `N` and `h` is the induced morphism of the site. The property `P` is required
to be stable under base change and composition, to hold for the étale morphisms, and to
descend along a surjective étale morphism of sources. -/
theorem holdsOnEveryEtaleChart_of_representable_target {P : MorphismProperty Scheme.{u}}
    (hPbc : MorphismProperty.IsStableUnderBaseChange P)
    (hPcomp : MorphismProperty.IsStableUnderComposition P)
    (hPet : ∀ {T₁ T₂ : Scheme.{u}} (i : T₁ ⟶ T₂), Etale i → P i)
    (hPdesc : ∀ {T₁ T₂ T₃ : Scheme.{u}} (α : T₁ ⟶ T₂) (k : T₂ ⟶ T₃), Surjective α → Etale α →
      P (α ≫ k) → P k)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ : BigFppfOver B S hS} {f : X ⟶ yoneda.obj Y₀}
    (hX : IsAlgebraicSpace B S hS X) (hf : HoldsOnEveryEtaleChart B S hS P f)
    {V U : BigFppfOver B S hS} {v : V ⟶ Y₀}
    {N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n₁ : N ⟶ yoneda.obj V} {nX : N ⟶ X}
    (sq1 : IsPullback n₁ nX (yoneda.map v) f)
    {e : yoneda.obj U ⟶ N}
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e)
    {h : U ⟶ V} (hcomm : e ≫ n₁ = yoneda.map h) :
    P ((BigFppfOver.toScheme B S hS).map h) := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hbc := etale_presheaf_isStableUnderBaseChange B S hS
  obtain ⟨T, c, hcs, hce⟩ := hX.exists_atlas
  obtain ⟨t, ht⟩ := yoneda.map_surjective (c ≫ f)
  have hPt : P ((BigFppfOver.toScheme B S hS).map t) :=
    hf T Y₀ c (𝟙 _) t hce (hmul.id_mem _) (by rw [ht]; simp)
  set π₁ := pullback.fst v t with hdefπ₁
  set π₂ := pullback.snd v t with hdefπ₂
  have sqCsite : IsPullback π₁ π₂ v t := IsPullback.of_hasPullback v t
  have hPπ₁ : P ((BigFppfOver.toScheme B S hS).map π₁) :=
    hPbc.of_isPullback (sqCsite.map (BigFppfOver.toScheme B S hS)).flip hPt
  have hvt : yoneda.map π₁ ≫ yoneda.map v = (yoneda.map π₂ ≫ c) ≫ f := by
    rw [Category.assoc, ← ht, ← Functor.map_comp, ← Functor.map_comp, sqCsite.w]
  set cN := sq1.lift (yoneda.map π₁) (yoneda.map π₂ ≫ c) hvt with hdefcN
  have hcN1 : cN ≫ n₁ = yoneda.map π₁ := sq1.lift_fst _ _ _
  have hcN2 : cN ≫ nX = yoneda.map π₂ ≫ c := sq1.lift_snd _ _ _
  have sqC : IsPullback cN (yoneda.map π₂) nX c := by
    refine IsPullback.of_right ?_ hcN2 sq1
    rw [hcN1, ← ht]
    exact sqCsite.map yoneda
  set ψ := hce.rep.snd (e ≫ nX) with hdefψ
  set τ := hce.rep.fst' (e ≫ nX) with hdefτ
  have sqA : IsPullback (yoneda.map τ) (yoneda.map ψ) c (e ≫ nX) := hce.rep.isPullback' _
  have hψs : Surjective ((BigFppfOver.toScheme B S hS).map ψ) :=
    hcs.property (e ≫ nX) _ _ sqA
  have hψe : Etale ((BigFppfOver.toScheme B S hS).map ψ) := hce.property (e ≫ nX) _ _ sqA
  have hωc : (ψ ≫ h) ≫ v = τ ≫ t := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, ht, ← hcomm, Category.assoc, sq1.w]
    rw [← Category.assoc (yoneda.map τ) c f, sqA.w]
    simp
  set ω := pullback.lift (ψ ≫ h) τ hωc with hdefω
  have hω1 : ω ≫ π₁ = ψ ≫ h := pullback.lift_fst _ _ _
  have hω2 : ω ≫ π₂ = τ := pullback.lift_snd _ _ _
  have hpω : yoneda.map ω ≫ cN = yoneda.map ψ ≫ e := by
    refine sq1.hom_ext ?_ ?_
    · rw [Category.assoc, hcN1, ← Functor.map_comp, hω1, Functor.map_comp, Category.assoc,
        hcomm]
    · rw [Category.assoc, hcN2, Category.assoc, ← Functor.map_comp_assoc, hω2, sqA.w]
  have sqω : IsPullback (yoneda.map ω) (yoneda.map ψ) cN e := by
    refine IsPullback.of_right ?_ hpω sqC.flip
    rw [← Functor.map_comp, hω2]
    exact sqA
  have hωEtale : Etale ((BigFppfOver.toScheme B S hS).map ω) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ω).1
      (hbc.of_isPullback sqω.flip he)
  have hcompP : P ((BigFppfOver.toScheme B S hS).map (ψ ≫ h)) := by
    rw [← hω1, Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (hPet _ hωEtale) hPπ₁
  rw [Functor.map_comp] at hcompP
  exact hPdesc _ _ hψs hψe hcompP

/-! ### Base change along an arbitrary morphism -/

/-- Let `P` be a property of
morphisms of schemes which is stable under base change and composition, holds for the étale
morphisms, and descends along a surjective étale morphism of sources. Then the every-étale-
chart condition of Stacks 03MJ for `P` is inherited by the base change of a morphism of
algebraic spaces along an arbitrary morphism.

The square is the one with `p` over `f` and `q` over `g`, so `p : W ⟶ Z` is the base change
of `f : X ⟶ Y` and `q : W ⟶ X` is the base change of `g : Z ⟶ Y`. Only the source and the
target of `f` are assumed to be algebraic spaces. -/
theorem holdsOnEveryEtaleChart_of_isPullback_of_descent {P : MorphismProperty Scheme.{u}}
    (hPbc : MorphismProperty.IsStableUnderBaseChange P)
    (hPcomp : MorphismProperty.IsStableUnderComposition P)
    (hPet : ∀ {T₁ T₂ : Scheme.{u}} (i : T₁ ⟶ T₂), Etale i → P i)
    (hPdesc : ∀ {T₁ T₂ T₃ : Scheme.{u}} (α : T₁ ⟶ T₂) (k : T₂ ⟶ T₃), Surjective α → Etale α →
      P (α ≫ k) → P k)
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P p := by
  have hbc := etale_presheaf_isStableUnderBaseChange B S hS
  intro U V a b h ha hb hcomm
  set βV := b ≫ g with hdefβV
  set n₁ := pullback.fst βV f with hdefn₁
  set nX := pullback.snd βV f with hdefnX
  have sq1 : IsPullback n₁ nX βV f := IsPullback.of_hasPullback βV f
  have hνc : (n₁ ≫ b) ≫ g = nX ≫ f := by rw [Category.assoc, ← hdefβV, sq1.w]
  set ν := sq.lift (n₁ ≫ b) nX hνc with hdefν
  have hν1 : ν ≫ p = n₁ ≫ b := sq.lift_fst _ _ _
  have hν2 : ν ≫ q = nX := sq.lift_snd _ _ _
  have sqν : IsPullback ν n₁ p b := by
    refine IsPullback.of_right ?_ hν1 sq.flip
    rw [hν2]
    exact sq1.flip
  have ha''c : yoneda.map h ≫ βV = (a ≫ q) ≫ f := by
    rw [hdefβV, ← Category.assoc, hcomm, Category.assoc, Category.assoc, sq.w]
  set a'' := sq1.lift (yoneda.map h) (a ≫ q) ha''c with hdefa''
  have ha''1 : a'' ≫ n₁ = yoneda.map h := sq1.lift_fst _ _ _
  have ha''2 : a'' ≫ nX = a ≫ q := sq1.lift_snd _ _ _
  have ha''ν : a'' ≫ ν = a := by
    refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, hν1, ← Category.assoc, ha''1, hcomm]
    · rw [Category.assoc, hν2, ha''2]
  have hEa'' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a'' :=
    presheaf_etale_of_postcomp B S hS (hbc.of_isPullback sqν.flip hb) ha ha''ν
  obtain ⟨V₁, d, hds, hde⟩ := hY.exists_atlas
  set ξ := hde.rep.snd βV with hdefξ
  set ζ := hde.rep.fst βV with hdefζ
  have sqB : IsPullback ζ (yoneda.map ξ) d βV := hde.rep.isPullback βV
  have hξs : Surjective ((BigFppfOver.toScheme B S hS).map ξ) := hds.property βV _ _ sqB
  have hξe : Etale ((BigFppfOver.toScheme B S hS).map ξ) := hde.property βV _ _ sqB
  obtain ⟨z, hz⟩ := yoneda.map_surjective ζ
  set f₁ := pullback.fst d f with hdeff₁
  set dX := pullback.snd d f with hdefdX
  have sqX₁ : IsPullback f₁ dX d f := IsPullback.of_hasPullback d f
  have hX₁ : IsAlgebraicSpace B S hS (pullback d f) :=
    isAlgebraicSpace_pullback B S hS d f (isAlgebraicSpace_yoneda B S hS V₁) hX hY
  have hf₁ : HoldsOnEveryEtaleChart B S hS P f₁ :=
    holdsOnEveryEtaleChart_of_isPullback B S hS sqX₁ hde hf
  set mN := pullback.fst n₁ (yoneda.map ξ) with hdefmN
  set n'₁ := pullback.snd n₁ (yoneda.map ξ) with hdefn'₁
  have sqN' : IsPullback mN n'₁ n₁ (yoneda.map ξ) := IsPullback.of_hasPullback _ _
  have hn'Xc : (n'₁ ≫ ζ) ≫ d = (mN ≫ nX) ≫ f := by
    rw [Category.assoc, sqB.w, ← Category.assoc, ← sqN'.w, Category.assoc, sq1.w,
      Category.assoc]
  set n'X := sqX₁.lift (n'₁ ≫ ζ) (mN ≫ nX) hn'Xc with hdefn'X
  have hn'X1 : n'X ≫ f₁ = n'₁ ≫ ζ := sqX₁.lift_fst _ _ _
  have hn'X2 : n'X ≫ dX = mN ≫ nX := sqX₁.lift_snd _ _ _
  have sq1' : IsPullback n'₁ n'X (yoneda.map z) f₁ := by
    refine IsPullback.of_bot ?_ ?_ sqX₁
    · rw [hn'X2, hz, sqB.w]
      exact sqN'.flip.paste_vert sq1
    · rw [hn'X1, hz]
  set χ := pullback.fst h ξ with hdefχ
  set h' := pullback.snd h ξ with hdefh'
  have sqU : IsPullback χ h' h ξ := IsPullback.of_hasPullback h ξ
  have hχs : Surjective ((BigFppfOver.toScheme B S hS).map χ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Surjective.{u} : MorphismProperty Scheme.{u}))
      (sqU.map (BigFppfOver.toScheme B S hS)).flip hξs
  have hχe : Etale ((BigFppfOver.toScheme B S hS).map χ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
      (sqU.map (BigFppfOver.toScheme B S hS)).flip hξe
  have he'c : (yoneda.map χ ≫ a'') ≫ n₁ = yoneda.map h' ≫ yoneda.map ξ := by
    rw [Category.assoc, ha''1, ← Functor.map_comp, ← Functor.map_comp, sqU.w]
  set e' := pullback.lift (yoneda.map χ ≫ a'') (yoneda.map h') he'c with hdefe'
  have he'1 : e' ≫ mN = yoneda.map χ ≫ a'' := pullback.lift_fst _ _ _
  have he'2 : e' ≫ n'₁ = yoneda.map h' := pullback.lift_snd _ _ _
  have sqe' : IsPullback (yoneda.map χ) e' a'' mN := by
    refine IsPullback.of_bot ?_ he'1.symm sqN'
    rw [he'2, ha''1]
    exact sqU.map yoneda
  have hPh' : P ((BigFppfOver.toScheme B S hS).map h') :=
    holdsOnEveryEtaleChart_of_representable_target B S hS hPbc hPcomp hPet hPdesc hX₁ hf₁
      sq1' (hbc.of_isPullback sqe' hEa'') he'2
  have hfin : P ((BigFppfOver.toScheme B S hS).map (χ ≫ h)) := by
    rw [sqU.w, Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ hPh' (hPet _ hξe)
  rw [Functor.map_comp] at hfin
  exact hPdesc _ _ hχs hχe hfin

/-! ### Finite type -/

/-- The base change of a morphism of algebraic spaces over
`S` which is locally of finite type along an arbitrary morphism of algebraic spaces is
locally of finite type.

The square is the one with `p` over `f`, so `p : W ⟶ Z` is the base change of
`f : X ⟶ Y`. -/
@[stacks 03XH "locally of finite type"]
theorem IsLocallyOfFiniteType.of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS p :=
  holdsOnEveryEtaleChart_of_isPullback_of_descent B S hS inferInstance inferInstance
    (fun i hi => by
      have : Etale i := hi
      exact inferInstanceAs (LocallyOfFiniteType i))
    (fun α k hs het hαk => locallyOfFiniteType_of_comp_surjective_etale α k hs het hαk)
    sq hX hY hf

/-- The base change of a morphism of algebraic spaces over
`S` which is of finite type along an arbitrary morphism of algebraic spaces is of finite
type. -/
@[stacks 03XH "finite type"]
theorem IsFiniteType.of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsFiniteType B S hS f) :
    IsFiniteType B S hS p :=
  ⟨IsLocallyOfFiniteType.of_isPullback B S hS sq hX hY hf.1,
    isQuasiCompact_of_isPullback B S hS sq.flip hf.2⟩

/-! ### Quasi-finiteness -/

/-- The base change of a locally quasi-finite morphism of algebraic spaces over `S` along an
arbitrary morphism of algebraic spaces is locally quasi-finite.

The square is the one with `p` over `f`, so `p : W ⟶ Z` is the base change of
`f : X ⟶ Y`. -/
@[stacks 03XL "locally quasi-finite", stacks 0ABM "part (3): locally quasi-finite"]
theorem IsLocallyQuasiFinite.of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyQuasiFinite B S hS f) :
    IsLocallyQuasiFinite B S hS p :=
  holdsOnEveryEtaleChart_of_isPullback_of_descent B S hS
    MorphismProperty.IsStableUnderBaseChange.inf
    MorphismProperty.IsStableUnderComposition.inf
    (fun i hi => have : Etale i := hi; locallyQuasiFinite_of_etale i)
    (fun α k hs het hαk => locallyQuasiFinite_of_comp_surjective_etale α k hs het hαk)
    sq hX hY hf

/-- The base change of a quasi-finite morphism of algebraic spaces over `S` along an arbitrary
morphism of algebraic spaces is quasi-finite. -/
@[stacks 03XL "quasi-finite", stacks 0ABM "part (4): quasi-finite"]
theorem IsQuasiFinite.of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsQuasiFinite B S hS f) :
    IsQuasiFinite B S hS p :=
  ⟨IsLocallyQuasiFinite.of_isPullback B S hS sq hX hY hf.1,
    isQuasiCompact_of_isPullback B S hS sq.flip hf.2⟩

end AlgebraicGeometry.Space

end
