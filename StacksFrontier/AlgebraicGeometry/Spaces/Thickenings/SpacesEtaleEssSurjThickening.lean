module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleHomLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSectionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleRangeEquivalence
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjSupplement

/-!
# SpacesEtaleEssSurjThickening

The generalizations made by this development of declarations of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj`. That module keeps its
statements as they are; each declaration here restating one of them carries its name with the
suffix `_of_isThickening` (or `OfIsThickening` for a definition), and the declarations that depend
on those restatements follow them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart-level closed immersion of a thickening, and the étale lift across it -/

/-- A pullback square over the range of a monomorphism `f` is one over `f` itself. -/
private theorem isPullback_comp_inv_toRange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [Mono f.hom] {Z J : BigFppfOver B S hS} {ζ : yoneda.obj Z ⟶ Y.1} {j : J ⟶ Z}
    {p : yoneda.obj J ⟶ (Subfunctor.range f.hom).toFunctor}
    (hpb : IsPullback p (yoneda.map j) (Subfunctor.range f.hom).ι ζ) :
    IsPullback (yoneda.map j) (p ≫ inv (Subfunctor.toRange f.hom)) ζ f.hom := by
  have hinv : inv (Subfunctor.toRange f.hom) ≫ f.hom = (Subfunctor.range f.hom).ι :=
    (cancel_epi (Subfunctor.toRange f.hom)).1 (by
      rw [IsIso.hom_inv_id_assoc]
      exact (Subfunctor.toRange_ι f.hom).symm)
  have hpaste := hpb.paste_horiz
    (IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hinv⟩ :
      IsPullback (inv (Subfunctor.toRange f.hom)) (Subfunctor.range f.hom).ι f.hom (𝟙 Y.1))
  rw [Category.comp_id] at hpaste
  exact hpaste.flip

/-- **The inclusion of a thickening of finite order restricts to a thickening of any étale chart
of the ambient space.** For an étale chart `ζ` of `Y` by an object `Z` of the site, the base
change of `f` along `ζ` is represented by an object `J` of the site, the morphism `j : J ⟶ Z` is
a closed immersion of schemes with nilpotent defining ideal, and it is surjective on points.

The cartesian square is the one
`AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback` produces over the subfunctor
`Subfunctor.range f.hom`, composed with the inverse of the isomorphism
`CategoryTheory.Subfunctor.toRange` — available because `f.hom` is a monomorphism — so that it
is read over `f` itself. Surjectivity on points is
`Stacks.Thickenings.isThickening_of_ker_pow_eq_bot`: the defining ideal of `j` has a vanishing
power, so the support of that ideal is the whole of `Z`. -/
theorem exists_chart_isClosedImmersion_of_isNthOrderThickening {n : ℕ}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom))
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) (hζ : IsEtale B S hS ζ) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
      IsPullback (yoneda.map j) η ζ f.hom ∧
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map j) ∧
        Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base := by
  obtain ⟨J, j, p, hpb, hci, hker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hT Z ζ
      ((isEtale_iff_presheaf_of_yoneda B S hS ζ).1 hζ)
  exact ⟨J, j, p ≫ inv (Subfunctor.toRange f.hom), isPullback_comp_inv_toRange B S hS f hpb, hci,
    (Stacks.Thickenings.isThickening_of_ker_pow_eq_bot _ hci hker).2⟩

/-- **The inclusion of a thickening restricts to a thickening of any scheme chart of the
ambient space, at unbounded order.** For a chart `ζ` of `Y` by an object `Z` of the site, the
base change of `f` along `ζ` is represented by an object `J` of the site, and `j : J ⟶ Z` is a
closed immersion of schemes which is surjective on points.

This is `AlgebraicGeometry.Space.exists_chart_isClosedImmersion_of_isNthOrderThickening` with
the order dropped. The cartesian square and both clauses come from
`AlgebraicGeometry.Space.exists_thickening_chart_pullback_subfunctor`, which reads a thickening
on charts with no order hypothesis and no étaleness hypothesis on the chart: the inclusion is
representable with closed-immersion base changes, and surjectivity on points is inherited by
every base change of it. The square is composed with the inverse of
`CategoryTheory.Subfunctor.toRange` — available because `f.hom` is a monomorphism — so that it
is read over `f` itself. -/
theorem exists_chart_isClosedImmersion_of_isThickening_range
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
      IsPullback (yoneda.map j) η ζ f.hom ∧
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map j) ∧
        Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base := by
  obtain ⟨J, j, p, hpb, hthick⟩ :=
    exists_thickening_chart_pullback_subfunctor B S hS hT Z ζ
  exact ⟨J, j, p ≫ inv (Subfunctor.toRange f.hom), isPullback_comp_inv_toRange B S hS f hpb,
    hthick.1, hthick.2⟩

/-! ### Unique extension of presheaf morphisms across a thickening of finite order -/

/-! ### Equivalence relations of the site, read in the slice over the base scheme -/

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The charts and the two étale lifts of a lifted étale presentation -/

/-- **The charts and the two étale lifts of a lifted étale presentation exist.** For the
inclusion `f` of a thickening of finite order and an object `C` of the spaces-étale site of
`X`,
there are objects `V`, `W`, `U`, `R` of the site, structure morphisms `v`, `w` making `V` and
`W` étale over `Y`, a surjective étale chart `c` of `C` by `U` with kernel pair `(s, t)` by `R`,
and projections `a : U ⟶ V`, `b : R ⟶ W` exhibiting `U` and `R` as the base changes of `V` and
of `W` along `f`.

These are all the data and all the cartesian squares of
`AlgebraicGeometry.Space.LiftedEtalePresentation` except the two maps `k₁`, `k₂` of the relation
and the properties that mention them. The last cartesian square replaces
`AlgebraicGeometry.Space.LiftedEtalePresentation.isPullback_b`, which follows from it, from
`isPullback_a` and from `k₁` by `CategoryTheory.IsPullback.of_right`.

The construction: an étale chart `ζ` of `Y` by an object `Z` of the site restricts the thickening
to a closed immersion `j : J ⟶ Z` of objects of the site which is surjective on points, by
`AlgebraicGeometry.Space.exists_chart_isClosedImmersion_of_isNthOrderThickening`. An étale
chart of `C` based changed to `J` gives `U`, whose kernel pair over `C` is `R`; both are étale
over `J`, so both lift across `j` by Stacks 039R in the form
`AlgebraicGeometry.Space.exists_etaleLift_isPullback_of_chart`, which also transports the
cartesian squares down to `f`. -/
theorem exists_liftedEtalePresentation_charts_of_isThickening_range (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
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
  obtain ⟨J, j, η, hchart, hci, hjsurj⟩ :=
    exists_chart_isClosedImmersion_of_isThickening_range B S hS f hT Z ζ
  have : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map j) := hci
  have hηE : (etaleOnSite B S hS).presheaf η := etalePresheaf_of_isPullback' B S hS hchart hζE
  have hηS : (surjectiveOnSite B S hS).presheaf η :=
    surjectivePresheaf_of_isPullback' B S hS hchart hζS
  -- An étale chart of `C`, and its base change to the chart of the thickening.
  obtain ⟨U', c', hc'S, hc'E⟩ := C.1.left.2.exists_atlas
  have hg₀E : (etaleOnSite B S hS).presheaf (c' ≫ C.1.hom.hom) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hc'E) C.2)
  obtain ⟨U, κ, m, hUpb⟩ :
      ∃ (U : BigFppfOver B S hS) (κ : yoneda.obj U ⟶ yoneda.obj J) (m : U ⟶ U'),
        IsPullback κ (yoneda.map m) η (c' ≫ C.1.hom.hom) :=
    ⟨_, _, _, hηE.rep.isPullback (c' ≫ C.1.hom.hom)⟩
  obtain ⟨k, rfl⟩ := yoneda.map_surjective κ
  have hmE : (etaleOnSite B S hS).presheaf (yoneda.map m) :=
    etalePresheaf_of_isPullback' B S hS hUpb hηE
  have hmS : (surjectiveOnSite B S hS).presheaf (yoneda.map m) :=
    surjectivePresheaf_of_isPullback' B S hS hUpb hηS
  have hkE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1
      (etalePresheaf_of_isPullback' B S hS hUpb.flip hg₀E)
  -- The chart of `C` through the base change, and its kernel pair.
  have hcE : (etaleOnSite B S hS).presheaf (yoneda.map m ≫ c') :=
    etaleSite_presheaf_comp' B S hS hmE hc'E
  have hcS : (surjectiveOnSite B S hS).presheaf (yoneda.map m ≫ c') :=
    surjectiveOnSite_presheaf_comp B S hS hmS hc'S
  have hcw : yoneda.map k ≫ η = (yoneda.map m ≫ c') ≫ C.1.hom.hom := by
    rw [Category.assoc]; exact hUpb.w
  obtain ⟨R, s₀, t₀, hker⟩ :
      ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) (yoneda.map m ≫ c') (yoneda.map m ≫ c') :=
    ⟨hcE.rep.pullback _, yoneda.preimage (hcE.rep.fst _), hcE.rep.snd _, by
      rw [yoneda.map_preimage]; exact hcE.rep.isPullback _⟩
  have htE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (s₀ ≫ k)) := by
    have h₁ : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s₀) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ s₀).1
        (etalePresheaf_of_isPullback' B S hS hker.flip hcE)
    have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) := hkE
    rw [Functor.map_comp]
    infer_instance
  -- The two étale lifts across the chart-level thickening.
  obtain ⟨V, q, a, -, hvE, -, hpresA⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart k hkE
  obtain ⟨W, qW, b, -, hwE, -, hpresB⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart (s₀ ≫ k) htE
  refine ⟨V, W, U, R, yoneda.map q ≫ ζ, yoneda.map qW ≫ ζ, yoneda.map m ≫ c', a, b, t₀, s₀,
    hvE, hwE, isEtale_of_presheaf_etale B S hS hcE, hcS, ?_, hker, ?_⟩
  · rw [← hcw]; exact hpresA
  · rw [Functor.map_comp, Category.assoc, hcw] at hpresB
    simpa only [Category.assoc] using hpresB

/-! ### Existence of a lifted étale presentation at a thickening of finite order -/

/-- **Every object of the spaces-étale site of `X` admits a lifted étale presentation across the
inclusion `f` of a thickening of finite order.** -/
theorem nonempty_liftedEtalePresentation_of_isThickening_range (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
    (C : SpacesEtale B S hS X) :
    Nonempty (LiftedEtalePresentation B S hS f C) := by
  obtain ⟨V, W, U, R, v, w, c, a, b, s, t, hv, hw, hc, hcS, hA, hC, hB⟩ :=
    exists_liftedEtalePresentation_charts_of_isThickening_range B S hS f hT C
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
  obtain ⟨κ₁, ⟨hκ₁b, hκ₁v⟩, -⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT
    hWas hVas hB v hv (yoneda.map t ≫ yoneda.map a) hd₁
  have hd₂ : (yoneda.map s ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [← Category.assoc]
    rw [← hC.w]
  obtain ⟨κ₂, ⟨hκ₂b, hκ₂v⟩, -⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT
    hWas hVas hB v hv (yoneda.map s ≫ yoneda.map a) hd₂
  obtain ⟨k₁, rfl⟩ := yoneda.map_surjective κ₁
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
  have hwP : (etaleOnSite B S hS).presheaf w := etalePresheaf_of_isEtale_yonedaDomain' B S hS w hw
  have hvP : (etaleOnSite B S hS).presheaf v := etalePresheaf_of_isEtale_yonedaDomain' B S hS v hv
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
    refine hom_ext_presheaf_of_isThickening_range B S hS f hT
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
  obtain ⟨r₀, ⟨hr₀a, hr₀w⟩, -⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT
    hVas hWas hA w hw (yoneda.map (ρ ≫ b)) hdr
  obtain ⟨rr, rfl⟩ := yoneda.map_surjective r₀
  have hrefl : ∀ (k : W ⟶ V) (p : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ρ ≫ p = 𝟙 U → yoneda.map k ≫ v = w → rr ≫ k = 𝟙 V := by
    intro k p hkp hρp hkv
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isThickening_range B S hS f hT hVas hVas hA v hv
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
  obtain ⟨σ₀, ⟨hσ₀b, hσ₀w⟩, -⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT
    hWas hWas hB w hw (yoneda.map (μ ≫ b)) hds
  obtain ⟨σ, rfl⟩ := yoneda.map_surjective σ₀
  have hsymm : ∀ (k k' : W ⟶ V) (p p' : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      yoneda.map b ≫ yoneda.map k' = yoneda.map p' ≫ yoneda.map a →
      μ ≫ p = p' → yoneda.map k ≫ v = w → yoneda.map k' ≫ v = w → σ ≫ k = k' := by
    intro k k' p p' hkp hkp' hμp hkv hkv'
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isThickening_range B S hS f hT hWas hVas hB v hv
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
  obtain ⟨τ₀, ⟨hτ₀Q, hτ₀w⟩, -⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT
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
    refine hom_ext_presheaf_of_isThickening_range B S hS f hT
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
  · rw [hsource]; exact hk₁E
  · rw [htarget]; exact hk₂E

variable {f : X ⟶ Y} {C : SpacesEtale B S hS X}

/-! ### Essential surjectivity, and the equivalence -/

/-- **Stacks 05ZH, essential surjectivity at a thickening of unbounded order.** Base change
`V ↦ X ×_Y V` is essentially surjective from the spaces-étale site of `Y` to that of `X`, for
the inclusion `f` of a thickening of algebraic spaces — a monomorphism whose range is a closed
subspace with the same points, with no hypothesis on its defining ideal.

Every object of the spaces-étale site of `X` admits a lifted étale presentation across `f`, by
`AlgebraicGeometry.Space.nonempty_liftedEtalePresentation_of_isThickening_range`, and the
quotient of such a presentation is an object of the spaces-étale site of `Y` whose base change
along `f` is the given object. -/
theorem essSurj_spacesBaseChange_of_isThickening_range (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.EssSurj where
  mem_essImage C := by
    obtain ⟨P⟩ := nonempty_liftedEtalePresentation_of_isThickening_range B S hS f hT C
    exact exists_iso_functor_obj_of_liftedEtalePresentation B S hS P

/-- **Stacks 05ZH, essential surjectivity at a thickening of algebraic spaces, in the morphism
form.** Base change `V ↦ X ×_Y V` is essentially surjective from the spaces-étale site of `Y` to
that of `X` for every thickening `f : X ⟶ Y` in the sense of
`AlgebraicGeometry.Space.IsThickeningHom`. -/
theorem essSurj_spacesBaseChange_of_isThickeningHom (f : X ⟶ Y)
    (hT : IsThickeningHom B S hS f) :
    (spacesBaseChange B S hS f).functor.EssSurj :=
  let := hT.mono
  essSurj_spacesBaseChange_of_isThickening_range B S hS f hT.2

/-- **Stacks 05ZH, essential surjectivity at a thickening of order `n`.** Base change
`V ↦ X ×_Y V` is essentially surjective from the spaces-étale site of `Y` to that of `X`, for
the inclusion `f` of an `n`th-order thickening, for every `n`.

The case of `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening_range` in which the
defining ideal has vanishing `(n+1)`st power. -/
theorem essSurj_spacesBaseChange_of_isNthOrderThickening {n : ℕ} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.EssSurj :=
  essSurj_spacesBaseChange_of_isThickening_range B S hS f hT.1

end AlgebraicGeometry.Space

end
