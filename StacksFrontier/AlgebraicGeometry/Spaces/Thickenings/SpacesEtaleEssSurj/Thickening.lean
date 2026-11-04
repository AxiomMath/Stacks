module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.LiftedEtalePresentation
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.Charts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essential surjectivity at a thickening of arbitrary order

Part of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj`. The chart-level
closed immersion of a thickening of arbitrary order, existence and uniqueness of extensions of
presheaf morphisms across its base changes, lifted étale presentations at such a thickening, and
essential surjectivity and the equivalence of spaces-étale sites; finally the general step from a
lifted étale presentation to the essential image, for an arbitrary morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

variable {f : X ⟶ Y} {C : SpacesEtale B S hS X}

/-! ### The chart-level closed immersion of a thickening of arbitrary order -/

/-- The inclusion of a thickening restricts to a thickening of any chart of the ambient space: for
a chart `ζ` of `Y` by an object `Z` of the site, the base change of the inclusion of a thickening
`G ⊂ Y` along `ζ` is represented by an object `J` of the site, and the morphism `j : J ⟶ Z` is a
closed immersion of schemes which is surjective on points. -/
theorem exists_chart_isClosedImmersion_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G) (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z)
        (η : yoneda.obj J ⟶ (IsThickening.space B S hS hG).1),
      IsPullback (yoneda.map j) η ζ (IsThickening.inclusion B S hS hG).hom ∧
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map j) ∧
        Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base := by
  obtain ⟨J, j, p, hpb, hci, hsurj⟩ :=
    exists_thickening_chart_pullback_subfunctor B S hS hG Z ζ
  exact ⟨J, j, p, hpb.flip, hci, hsurj⟩

/-! ### Unique extension of presheaf morphisms across a thickening of arbitrary order -/

/-- Two morphisms over `Y` into an algebraic space unramified over `Y` which agree after composing
with a base change of the inclusion of a thickening are equal. -/
theorem hom_ext_presheaf_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G)
    {F Gp H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hGp : IsAlgebraicSpace B S hS Gp)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ (IsThickening.space B S hS hG).1}
    (hpb : IsPullback π q v (IsThickening.inclusion B S hS hG).hom)
    (w : Gp ⟶ Y.1) (hw : IsUnramified B S hS w) (α β : F ⟶ Gp)
    (hα : α ≫ w = v) (hβ : β ≫ w = v) (h : π ≫ α = π ≫ β) : α = β := by
  have hH : IsAlgebraicSpace B S hS H :=
    isAlgebraicSpace_of_isPullback hF (IsThickening.space B S hS hG).2 Y.2.isSheaf
      Y.2.diagonal_representable hpb
  have hπ : IsSurjective B S hS π :=
    isSurjective_of_isPullback B S hS
      (p := (ObjectProperty.homMk q :
        (⟨H, hH⟩ : AlgebraicSpaces B S hS) ⟶ IsThickening.space B S hS hG))
      (q := (ObjectProperty.homMk π : (⟨H, hH⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩))
      (g := IsThickening.inclusion B S hS hG)
      (f := (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y))
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hpb.flip) hG.2
  exact eq_of_comp_eq_of_isSurjective B S hS hGp Y.2 w hw α β (by rw [hα, hβ]) π hπ h

/-- Let `G ⊂ Y` be a thickening of algebraic spaces over `S`, let `v : F ⟶ Y.1` and
`w : Gp ⟶ Y.1` be étale with `F` and `Gp` algebraic spaces, and let `π : H ⟶ F` be a base change
of the inclusion of the thickening. Every morphism `H ⟶ Gp` over `Y` extends to a morphism
`F ⟶ Gp` over `Y`. -/
@[sga "1 I 5.6" "existence clause"]
theorem exists_hom_presheaf_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G)
    {F Gp H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hGp : IsAlgebraicSpace B S hS Gp)
    {v : F ⟶ Y.1} (hv : IsEtale B S hS v)
    {π : H ⟶ F} {q : H ⟶ (IsThickening.space B S hS hG).1}
    (hpb : IsPullback π q v (IsThickening.inclusion B S hS hG).hom)
    (w : Gp ⟶ Y.1) (hw : IsEtale B S hS w)
    (d : H ⟶ Gp) (hd : d ≫ w = π ≫ v) :
    ∃ α : F ⟶ Gp, π ≫ α = d ∧ α ≫ w = v := by
  let V' : SpacesEtale B S hS Y :=
    ⟨Over.mk (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y), hv⟩
  let V : SpacesEtale B S hS Y :=
    ⟨Over.mk (ObjectProperty.homMk w : (⟨Gp, hGp⟩ : AlgebraicSpaces B S hS) ⟶ Y), hw⟩
  have sq : ∀ V : SpacesEtale B S hS Y, IsPullback
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app V).hom
      (((spacesBaseChange B S hS
        (IsThickening.inclusion B S hS hG)).functor.obj V).1.hom).hom V.1.hom.hom
      (IsThickening.inclusion B S hS hG).hom := fun V ↦
    AlgebraicSpaces.isPullback_hom B S hS
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).isPullback V)
  have sqV' := sq V'
  have sqV := sq V
  obtain ⟨θ, hθiso, hθ⟩ : ∃ θ : H ⟶ ((spacesBaseChange B S hS
      (IsThickening.inclusion B S hS hG)).functor.obj V').1.left.1,
      IsIso θ ∧ θ ≫ ((spacesBaseChange B S hS
        (IsThickening.inclusion B S hS hG)).projection.app V').hom = π :=
    ⟨(hpb.isoIsPullback _ _ sqV').hom, inferInstance,
      IsPullback.isoIsPullback_hom_fst _ _ hpb sqV'⟩
  have := hθiso
  have hcond : (inv θ ≫ d) ≫ w = (((spacesBaseChange B S hS
      (IsThickening.inclusion B S hS hG)).functor.obj V').1.hom).hom ≫
        (IsThickening.inclusion B S hS hG).hom := by
    rw [Category.assoc, hd, ← hθ, Category.assoc, IsIso.inv_hom_id_assoc]
    exact sqV'.w
  obtain ⟨cpre, hcpre₁, hcpre₂⟩ : ∃ cpre : ((spacesBaseChange B S hS
      (IsThickening.inclusion B S hS hG)).functor.obj V').1.left.1 ⟶
        ((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).functor.obj V).1.left.1,
      cpre ≫ ((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).projection.app V).hom = inv θ ≫ d ∧
        cpre ≫ (((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).functor.obj V).1.hom).hom =
            (((spacesBaseChange B S hS
              (IsThickening.inclusion B S hS hG)).functor.obj V').1.hom).hom :=
    ⟨sqV.lift _ _ hcond, sqV.lift_fst _ _ hcond, sqV.lift_snd _ _ hcond⟩
  have hc : (ObjectProperty.homMk cpre : ((spacesBaseChange B S hS
      (IsThickening.inclusion B S hS hG)).functor.obj V').1.left ⟶
        ((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).functor.obj V).1.left) ≫
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj V).1.hom =
        ((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).functor.obj V').1.hom :=
    ObjectProperty.hom_ext _ hcpre₂
  obtain ⟨a, ha⟩ := (full_spacesBaseChange_of_isThickening B S hS hG).map_surjective
    (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk cpre) hc))
  have hca : ((spacesBaseChange B S hS
      (IsThickening.inclusion B S hS hG)).functor.map a).hom.left.hom = cpre := by
    rw [ha]; rfl
  have hnat : ((spacesBaseChange B S hS
      (IsThickening.inclusion B S hS hG)).projection.app V').hom ≫ a.hom.left.hom =
      ((spacesBaseChange B S hS
        (IsThickening.inclusion B S hS hG)).functor.map a).hom.left.hom ≫
        ((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).projection.app V).hom :=
    (congrArg (fun k ↦ k.hom) ((spacesBaseChange B S hS
      (IsThickening.inclusion B S hS hG)).projection.naturality a)).symm
  refine ⟨a.hom.left.hom, ?_, congrArg (fun k ↦ k.hom) (Over.w a.hom)⟩
  calc π ≫ a.hom.left.hom
      = (θ ≫ ((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).projection.app V').hom) ≫ a.hom.left.hom := by
        rw [hθ]
    _ = θ ≫ cpre ≫ ((spacesBaseChange B S hS
          (IsThickening.inclusion B S hS hG)).projection.app V).hom := by
        rw [Category.assoc, hnat, hca]
    _ = θ ≫ inv θ ≫ d := by rw [hcpre₁]
    _ = d := by rw [IsIso.hom_inv_id_assoc]

/-! ### Lifted étale presentations at a thickening of arbitrary order -/

/-- For a thickening `G ⊂ Y` of arbitrary order and an object `C` of the spaces-étale site of `G`,
there are objects `V`, `W`, `U`, `R` of the site, structure morphisms `v`, `w` making `V` and `W`
étale over `Y`, a surjective étale chart `c` of `C` by `U` with kernel pair `(s, t)` by `R`, and
projections `a : U ⟶ V`, `b : R ⟶ W` exhibiting `U` and `R` as the base changes of `V` and of
`W` along the inclusion of the thickening. -/
theorem exists_liftedEtalePresentation_charts_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G)
    (C : SpacesEtale B S hS (IsThickening.space B S hS hG)) :
    ∃ (V W U R : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y.1) (w : yoneda.obj W ⟶ Y.1)
        (c : yoneda.obj U ⟶ C.1.left.1) (a : U ⟶ V) (b : R ⟶ W) (s t : R ⟶ U),
      IsEtale B S hS v ∧ IsEtale B S hS w ∧ IsEtale B S hS c ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) c ∧
        IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v (IsThickening.inclusion B S hS hG).hom ∧
        IsPullback (yoneda.map t) (yoneda.map s) c c ∧
        IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w
          (IsThickening.inclusion B S hS hG).hom := by
  obtain ⟨Z, ζ, hζS, hζE⟩ := Y.2.exists_atlas
  have hζI : IsEtale B S hS ζ := isEtale_of_presheaf_etale B S hS hζE
  obtain ⟨J, j, η, hchart, hci, hjsurj⟩ :=
    exists_chart_isClosedImmersion_of_isThickening B S hS hG Z ζ
  have : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map j) := hci
  have hηE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf η :=
    etalePresheaf_of_isPullback B S hS hchart hζE
  have hηS : (SurjSite B S hS).presheaf η :=
    surjectivePresheaf_of_isPullback B S hS hchart hζS
  obtain ⟨U', c', hc'S, hc'E⟩ := C.1.left.2.exists_atlas
  have hg₀E : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (c' ≫ C.1.hom.hom) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hc'E) C.2)
  obtain ⟨U, κ, m, hUpb⟩ :
      ∃ (U : BigFppfOver B S hS) (κ : yoneda.obj U ⟶ yoneda.obj J) (m : U ⟶ U'),
        IsPullback κ (yoneda.map m) η (c' ≫ C.1.hom.hom) :=
    ⟨_, _, _, hηE.rep.isPullback (c' ≫ C.1.hom.hom)⟩
  obtain ⟨k, hkmap⟩ := yoneda.map_surjective κ
  rw [← hkmap] at hUpb
  have hmE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m) :=
    etalePresheaf_of_isPullback B S hS hUpb hηE
  have hmS : (SurjSite B S hS).presheaf (yoneda.map m) :=
    surjectivePresheaf_of_isPullback B S hS hUpb hηS
  have hkE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1
      (etalePresheaf_of_isPullback B S hS hUpb.flip hg₀E)
  have hcE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m ≫ c') :=
    etaleSite_presheaf_comp B S hS hmE hc'E
  have hcS : (SurjSite B S hS).presheaf (yoneda.map m ≫ c') :=
    surjSite_presheaf_comp B S hS hmS hc'S
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
        (etalePresheaf_of_isPullback B S hS hker.flip hcE)
    have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) := hkE
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨V, q, a, -, hvE, -, hpresA⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart k hkE
  obtain ⟨W, qW, b, -, hwE, -, hpresB⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart (s₀ ≫ k) htE
  refine ⟨V, W, U, R, yoneda.map q ≫ ζ, yoneda.map qW ≫ ζ, yoneda.map m ≫ c', a, b, t₀, s₀,
    hvE, hwE, isEtale_of_presheaf_etale B S hS hcE, hcS, ?_, hker, ?_⟩
  · rwa [← hcw]
  · rw [Functor.map_comp, Category.assoc, hcw] at hpresB
    simp only [Category.assoc] at hpresB ⊢
    exact hpresB

/-- Every object of the spaces-étale site of `G` admits a lifted étale presentation across the
inclusion of a thickening `G ⊂ Y` of arbitrary order. -/
theorem nonempty_liftedEtalePresentation_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G)
    (C : SpacesEtale B S hS (IsThickening.space B S hS hG)) :
    Nonempty (LiftedEtalePresentation B S hS (IsThickening.inclusion B S hS hG) C) := by
  obtain ⟨V, W, U, R, v, w, c, a, b, s, t, hv, hw, hc, hcS, hA, hC, hB⟩ :=
    exists_liftedEtalePresentation_charts_of_isThickening B S hS hG C
  have hpbQ : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : F ⟶ Y.1),
      ∃ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (π : Q ⟶ F)
        (q : Q ⟶ (IsThickening.space B S hS hG).1),
        IsPullback π q φ (IsThickening.inclusion B S hS hG).hom :=
    fun φ ↦ ⟨_, _, _, (Subfunctor.isPullback_preimage φ G).flip⟩
  have hVas := isAlgebraicSpace_yoneda B S hS V
  have hWas := isAlgebraicSpace_yoneda B S hS W
  have hvU : IsUnramified B S hS v := isUnramified_of_isEtale B S hS hv
  have hwU : IsUnramified B S hS w := isUnramified_of_isEtale B S hS hw
  have hmonoA : Mono (yoneda.map a) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) hA.flip
      (show Mono (IsThickening.inclusion B S hS hG).hom from inferInstanceAs (Mono G.ι))
  have hd₁ : (yoneda.map t ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [Category.assoc]
  obtain ⟨κ₁, hκ₁b, hκ₁v⟩ := exists_hom_presheaf_of_isThickening B S hS hG
    hWas hVas hw hB v hv (yoneda.map t ≫ yoneda.map a) hd₁
  have hd₂ : (yoneda.map s ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [← Category.assoc]
    rw [← hC.w]
  obtain ⟨κ₂, hκ₂b, hκ₂v⟩ := exists_hom_presheaf_of_isThickening B S hS hG
    hWas hVas hw hB v hv (yoneda.map s ≫ yoneda.map a) hd₂
  obtain ⟨k₁, hk₁⟩ := yoneda.map_surjective κ₁
  obtain ⟨k₂, hk₂⟩ := yoneda.map_surjective κ₂
  rw [← hk₁] at hκ₁b hκ₁v
  rw [← hk₂] at hκ₂b hκ₂v
  have hbk₁ : b ≫ k₁ = t ≫ a :=
    yoneda.map_injective (by rwa [Functor.map_comp, Functor.map_comp])
  have hbk₂ : b ≫ k₂ = s ≫ a :=
    yoneda.map_injective (by rwa [Functor.map_comp, Functor.map_comp])
  have hPB : IsPullback (yoneda.map b) (yoneda.map t) (yoneda.map k₁) (yoneda.map a) := by
    refine IsPullback.of_bot ?_ ?_ hA
    · rwa [hκ₁v]
    · rw [← Functor.map_comp, ← Functor.map_comp, hbk₁]
  have hbk₂' : yoneda.map b ≫ yoneda.map k₂ = yoneda.map s ≫ yoneda.map a := by
    rw [← Functor.map_comp, ← Functor.map_comp, hbk₂]
  have hwP : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf w :=
    etalePresheaf_of_isEtale_yonedaDomain B S hS w hw
  have hvP : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf v :=
    etalePresheaf_of_isEtale_yonedaDomain B S hS v hv
  have hk₁E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₁) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₁v
  have hk₂E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₂) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₂v
  have hfstPB : IsPullback (yoneda.map (pullback.fst k₁ k₂)) (yoneda.map (pullback.snd k₁ k₂))
      (yoneda.map k₁) (yoneda.map k₂) := (IsPullback.of_hasPullback k₁ k₂).map yoneda
  have hfstI : IsEtale B S hS (yoneda.map (pullback.fst k₁ k₂) ≫ w) :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS
      (etalePresheaf_of_isPullback B S hS hfstPB.flip
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k₂).2 hk₂E))) hw
  have hjm : ∀ (T : BigFppfOver B S hS) (x y : T ⟶ W), x ≫ k₂ = y ≫ k₂ → x ≫ k₁ = y ≫ k₁ →
      x = y := by
    intro T x y h₂ h₁
    apply yoneda.map_injective
    have hyw : yoneda.map y ≫ w = yoneda.map x ≫ w := by
      rw [← hκ₁v]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [h₁]
    obtain ⟨Q, πQ, qQ, hQ⟩ := hpbQ (yoneda.map x ≫ w)
    have hxQ : (πQ ≫ yoneda.map x) ≫ w = qQ ≫ (IsThickening.inclusion B S hS hG).hom := by
      rw [Category.assoc]; exact hQ.w
    have hyQ : (πQ ≫ yoneda.map y) ≫ w = qQ ≫ (IsThickening.inclusion B S hS hG).hom := by
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
    refine hom_ext_presheaf_of_isThickening B S hS hG
      (isAlgebraicSpace_yoneda B S hS T) hWas hQ w hwU (yoneda.map x) (yoneda.map y)
      rfl hyw ?_
    rw [← hξx, ← hξy, hξ]
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
  have hdr : yoneda.map (ρ ≫ b) ≫ w = yoneda.map a ≫ v := by
    rw [Functor.map_comp, Category.assoc, hB.w, hA.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hρt, CategoryTheory.Functor.map_id, Category.id_comp]
  obtain ⟨rr₀, hr₀a, hr₀w⟩ := exists_hom_presheaf_of_isThickening B S hS hG
    hVas hWas hv hA w hw (yoneda.map (ρ ≫ b)) hdr
  obtain ⟨rr, hrr⟩ := yoneda.map_surjective rr₀
  rw [← hrr] at hr₀a hr₀w
  have hrefl : ∀ (k : W ⟶ V) (p : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ρ ≫ p = 𝟙 U → yoneda.map k ≫ v = w → rr ≫ k = 𝟙 V := by
    intro k p hkp hρp hkv
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isThickening B S hS hG hVas hVas hA v hvU
      (yoneda.map (rr ≫ k)) (yoneda.map (𝟙 V)) ?_ ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hr₀w
    · rw [CategoryTheory.Functor.map_id, Category.id_comp]
    · rw [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, ← Category.assoc,
        hr₀a]
      simp only [Functor.map_comp, Category.assoc, hkp]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hρp, Category.id_comp]
  have hds : yoneda.map (μ ≫ b) ≫ w = yoneda.map b ≫ w := by
    rw [Functor.map_comp, Category.assoc, hB.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hμt, hC.w]
  obtain ⟨σ₀, hσ₀b, hσ₀w⟩ := exists_hom_presheaf_of_isThickening B S hS hG
    hWas hWas hw hB w hw (yoneda.map (μ ≫ b)) hds
  obtain ⟨σ, hσ⟩ := yoneda.map_surjective σ₀
  rw [← hσ] at hσ₀b hσ₀w
  have hsymm : ∀ (k k' : W ⟶ V) (p p' : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      yoneda.map b ≫ yoneda.map k' = yoneda.map p' ≫ yoneda.map a →
      μ ≫ p = p' → yoneda.map k ≫ v = w → yoneda.map k' ≫ v = w → σ ≫ k = k' := by
    intro k k' p p' hkp hkp' hμp hkv hkv'
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isThickening B S hS hG hWas hVas hB v hvU
      (yoneda.map (σ ≫ k)) (yoneda.map k') ?_ hkv' ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hσ₀w
    · rw [Functor.map_comp, ← Category.assoc, hσ₀b]
      simp only [Functor.map_comp, Category.assoc, hkp, hkp']
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hμp]
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  obtain ⟨Q, πQ, qQ, hQ⟩ := hpbQ (yoneda.map (pullback.fst k₁ k₂) ≫ w)
  have hπ₂w : yoneda.map (pullback.snd k₁ k₂) ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w :=
    calc yoneda.map (pullback.snd k₁ k₂) ≫ w
        = yoneda.map (pullback.snd k₁ k₂ ≫ k₂) ≫ v := by
          rw [← hκ₂v, Functor.map_comp, Category.assoc]
      _ = yoneda.map (pullback.fst k₁ k₂ ≫ k₁) ≫ v := by rw [← pullback.condition]
      _ = yoneda.map (pullback.fst k₁ k₂) ≫ w := by
          rw [← hκ₁v, Functor.map_comp, Category.assoc]
  have hQ₁ :
      (πQ ≫ yoneda.map (pullback.fst k₁ k₂)) ≫ w = qQ ≫ (IsThickening.inclusion B S hS hG).hom := by
    rw [Category.assoc]; exact hQ.w
  have hQ₂ :
      (πQ ≫ yoneda.map (pullback.snd k₁ k₂)) ≫ w = qQ ≫ (IsThickening.inclusion B S hS hG).hom := by
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
  obtain ⟨τ₀, hτ₀Q, hτ₀w⟩ := exists_hom_presheaf_of_isThickening B S hS hG
    (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hWas hfstI hQ w hw
    (ζ ≫ yoneda.map b) hdt
  obtain ⟨τ, hτ⟩ := yoneda.map_surjective τ₀
  rw [← hτ] at hτ₀Q hτ₀w
  have htrans : ∀ (k : W ⟶ V) (p : R ⟶ U) (π : pullback k₁ k₂ ⟶ W) (ζ' : Q ⟶ yoneda.obj R),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ζ ≫ yoneda.map p = ζ' ≫ yoneda.map p →
      ζ' ≫ yoneda.map b = πQ ≫ yoneda.map π →
      yoneda.map k ≫ v = w → yoneda.map π ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w →
      τ ≫ k = π ≫ k := by
    intro k p π ζ' hkp hζp hζ'b hkv hπw
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isThickening B S hS hG
      (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hVas hQ v hvU
      (yoneda.map (τ ≫ k)) (yoneda.map (π ≫ k)) ?_ ?_ ?_
    · rwa [Functor.map_comp, Category.assoc, hkv]
    · rwa [Functor.map_comp, Category.assoc, hkv]
    · rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hτ₀Q]
      rw [Category.assoc, hkp, ← Category.assoc, hζp, Category.assoc, ← hkp, ← Category.assoc,
        hζ'b]
  have esite : EquivalenceRelation k₂ k₁ :=
    { right_cancellation := hjm
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
  · rwa [hsource]
  · rwa [htarget]

/-! ### Essential surjectivity, and the equivalence, at a thickening of arbitrary order -/

/-- Let `G ⊂ Y` be a thickening of algebraic spaces over `S`, of arbitrary order. Base change
along the inclusion, `V ↦ G ×_Y V`, is essentially surjective from the spaces-étale site of `Y`
to that of `G`. -/
@[stacks 05ZH "ESSENTIAL SURJECTIVITY ONLY, at a thickening of ARBITRARY order. This lifts the \
FIRST-ORDER restriction of \
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening`, which descends \
the two maps of the lifted etale equivalence relation by the square-zero lifting property of \
Stacks 0611; the route here is the source's own, where they are descended by FULLNESS at \
arbitrary order, `AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening`, and every \
uniqueness step is FAITHFULNESS at arbitrary order, \
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isThickening`. Together with \
`AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsThickening` this gives the \
EQUIVALENCE at arbitrary order, \
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening`. The source states \
the tag for an arbitrary INTEGRAL, UNIVERSALLY INJECTIVE and SURJECTIVE morphism, which is a \
wider class: the library proves only that a thickening inclusion belongs to it (Stacks 05ZL, \
`AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_ι_of_isThickening`) \
and not the converse, so that wider class is NOT covered"]
theorem essSurj_spacesBaseChange_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G) :
    (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.EssSurj where
  mem_essImage C := by
    obtain ⟨P⟩ := nonempty_liftedEtalePresentation_of_isThickening B S hS hG C
    exact exists_iso_functor_obj_of_liftedEtalePresentation B S hS P

/-- Let `G ⊂ Y` be a thickening of algebraic spaces over `S`, of arbitrary order. Base change
along the inclusion, `V ↦ G ×_Y V`, is an equivalence from the spaces-étale site of `Y` to that
of `G`. -/
@[stacks 05ZH "the EQUIVALENCE at a thickening of ARBITRARY order -- all three of \
faithfulness, fullness and essential surjectivity, with no hypothesis beyond the thickening \
and no monomorphism hypothesis. What is still NOT covered is the source's wider class of an \
arbitrary INTEGRAL, UNIVERSALLY INJECTIVE and SURJECTIVE morphism: the library proves only \
that a thickening inclusion lies in that class (Stacks 05ZL, \
`AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_ι_of_isThickening`), \
not the converse. The first-order statement \
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening` is \
subsumed up to the identification of the source of `f` with the range of `f.hom`"]
theorem isEquivalence_spacesBaseChange_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G) :
    (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.IsEquivalence :=
  let := full_spacesBaseChange_of_isThickening B S hS hG
  let := faithful_spacesBaseChange_of_isThickening B S hS hG
  let := essSurj_spacesBaseChange_of_isThickening B S hS hG
  ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The two general steps, for any morphism `f` -/

/-- For an arbitrary morphism `g` of algebraic spaces, an object `C'` of the spaces-étale site of
the source which admits a lifted étale presentation across `g` is in the essential image of base
change along `g`. -/
theorem mem_essImage_spacesBaseChange_of_liftedEtalePresentation
    {X' Y' : AlgebraicSpaces B S hS} {g : X' ⟶ Y'} {C' : SpacesEtale B S hS X'}
    (P : LiftedEtalePresentation B S hS g C') :
    (spacesBaseChange B S hS g).functor.essImage C' :=
  exists_iso_functor_obj_of_liftedEtalePresentation B S hS P

/-- An equivalence relation of the site is an equivalence relation over the base scheme: its image
under `CategoryTheory.Over.post` of the inclusion of the site is an equivalence relation. -/
alias isEquivalenceRelation_overPost_of_equivalenceRelation := isEquivalenceRelation_post_inclusion

end AlgebraicGeometry.Space

end
