module

public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.PresentationSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The chart of a slice point of an algebraic stack with quasi-affine diagonal

Let `𝒳` be an algebraic stack over `S` with quasi-affine diagonal and presentation
`g : 𝒮/P ⥤ 𝒳`, and let `X : 𝒮/W ⥤ 𝒳` be a slice point. With `T = W × P`, the presheaf of pairs
`(ψ : Z ⟶ T, m)` with `m : X (ψ ≫ pr₁) ⟶ g (ψ ≫ pr₂)` vertical is represented by a morphism
`π : Q ⟶ T` of the site which is quasi-affine, and `π ≫ pr₁ : Q ⟶ W` is smooth and surjective:
`Q` is the 2-fibre product `W ×_𝒳 P`.

## Main definitions

* `AlgebraicGeometry.Stack.chartComparison`: the comparison of the presheaf above with the base
  change presheaf of the presentation along `X`.

## Main results

* `AlgebraicGeometry.Stack.isIso_chartComparison`: it is an isomorphism.
* `AlgebraicGeometry.Stack.exists_chart`: the representing quasi-affine `π` with `π ≫ pr₁` smooth
  and surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- Surjectivity of the underlying morphism of schemes is stable under base change in the big
fppf site. -/
private instance chartSurjective_isStableUnderBaseChange :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun hs hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Surjective) (hs.map (BigFppfOver.toScheme B S hS)) hg⟩

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  {P W T : BigFppfOver B S hS} {g : Over P ⥤ 𝒳.val.obj} (hg : g ⋙ 𝒳.val.p = Over.forget P)
  {X : Over W ⥤ 𝒳.val.obj} (hX : X ⋙ 𝒳.val.p = Over.forget W)
  (pr₁ : T ⟶ W) (pr₂ : T ⟶ P)

/-- For a slice point `Y : 𝒮/A ⥤ 𝒳` and `q : T ⟶ A`, the composite `Over.map q ⋙ Y` lies over
`T`: composed with the structure functor of `𝒳` it is `Over.forget T`. -/
lemma overMap_comp_eq_forget {A : BigFppfOver B S hS} {Y : Over A ⥤ 𝒳.val.obj}
    (hY : Y ⋙ 𝒳.val.p = Over.forget A) (q : T ⟶ A) :
    (Over.map q ⋙ Y) ⋙ 𝒳.val.p = Over.forget T := by
  rw [Functor.assoc, hY]
  rfl

/-- Two sections of the coproduct presheaf of the base change presheaf agree when their
morphisms to `W` agree and their components agree up to the transport along that equality. -/
lemma presentation_sigma_ext {Z : BigFppfOver B S hS} {φ₁ φ₂ : Z ⟶ W} (e : φ₁ = φ₂)
    {s₁ : (slicePresentationPresheaf 𝒳 hg hX).obj (op (Over.mk φ₁))}
    {s₂ : (slicePresentationPresheaf 𝒳 hg hX).obj (op (Over.mk φ₂))}
    (hk : s₁.k = s₂.k)
    (hm : s₁.m ≫ g.map (eqToHom (by rw [hk])) = X.map (eqToHom (by rw [e])) ≫ s₂.m) :
    (⟨φ₁, s₁⟩ : (OverShriek.presheaf (slicePresentationPresheaf 𝒳 hg hX)).obj (op Z)) =
      ⟨φ₂, s₂⟩ := by
  subst e
  exact congrArg (Sigma.mk φ₁) (SliceSourceFibre.SliceHom.ext' hk (by simpa using hm))

/-- For a slice point `Y : 𝒮/A ⥤ 𝒳` and `a b : Z ⟶ A`, the image under `Y` of the transport along
an equality `Over.mk a = Over.mk b` lifts the identity of `Z`. -/
lemma isHomLift_map_eqToHom {A : BigFppfOver B S hS} {Y : Over A ⥤ 𝒳.val.obj}
    (hY : Y ⋙ 𝒳.val.p = Over.forget A) {Z : BigFppfOver B S hS} {a b : Z ⟶ A}
    (e : (Over.mk a : Over A) = Over.mk b) : 𝒳.val.p.IsHomLift (𝟙 Z) (Y.map (eqToHom e)) := by
  rw [eqToHom_map]
  exact IsHomLift.eqToHom_domain_lift_id _ (Functor.congr_obj hY (Over.mk a))

/-- The component of the naturality square of `AlgebraicGeometry.Stack.chartComparison`. -/
lemma chartComparison_restrict_m {Z Z' : BigFppfOver B S hS} (k : Z' ⟶ Z) (ψ : Z ⟶ T)
    (m : VertHom 𝒳.val.p (Over.forget T) (Over.map pr₁ ⋙ X) (Over.map pr₂ ⋙ g) (Over.mk ψ)) :
    (VertHom.restrict 𝒳.isFiberedInGroupoids (overMap_comp_eq_forget 𝒳 hX pr₁)
        (overMap_comp_eq_forget 𝒳 hg pr₂) (Over.homMk k : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) m).1 ≫
        g.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₂))) =
      X.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₁))) ≫
        (SliceSourceFibre.SliceHom.restrict 𝒳.isFiberedInGroupoids hX hg
          (Over.homMk k : Over.mk (k ≫ ψ ≫ pr₁) ⟶ Over.mk (ψ ≫ pr₁))
          ⟨ψ ≫ pr₂, m.1, m.2⟩).m := by
  have hp := 𝒳.isFiberedInGroupoids
  let u : (Over.mk (k ≫ ψ ≫ pr₂) : Over P) ⟶ Over.mk (ψ ≫ pr₂) := Over.homMk k
  have hu : 𝒳.val.p.IsHomLift k (g.map u) := SliceSourceFibre.SliceHom.isHomLift_g_map hg u
  have : 𝒳.val.p.IsStronglyCartesian k (g.map u) := hp.isStronglyCartesian_homLift _ _
  set l := (VertHom.restrict hp (overMap_comp_eq_forget 𝒳 hX pr₁)
        (overMap_comp_eq_forget 𝒳 hg pr₂) (Over.homMk k : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) m) with hl
  set r := SliceSourceFibre.SliceHom.restrict hp hX hg
          (Over.homMk k : Over.mk (k ≫ ψ ≫ pr₁) ⟶ Over.mk (ψ ≫ pr₁)) ⟨ψ ≫ pr₂, m.1, m.2⟩ with hr
  have : 𝒳.val.p.IsHomLift (𝟙 Z') l.1 := l.2
  have : 𝒳.val.p.IsHomLift (𝟙 Z')
      (g.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₂)))) :=
    isHomLift_map_eqToHom 𝒳 hg _
  have : 𝒳.val.p.IsHomLift (𝟙 Z')
      (X.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₁)))) :=
    isHomLift_map_eqToHom 𝒳 hX _
  have : 𝒳.val.p.IsHomLift (𝟙 Z') r.m := r.vert
  show l.1 ≫ g.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₂))) =
    (X.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₁))) ≫ r.m :
      X.obj (Over.mk ((k ≫ ψ) ≫ pr₁)) ⟶ g.obj (Over.mk (k ≫ ψ ≫ pr₂)))
  have : 𝒳.val.p.IsHomLift (𝟙 Z')
      (l.1 ≫ g.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₂)))) :=
    IsHomLift.comp_lift_id_right 𝒳.val.p (𝟙 Z') l.1 _
  have : 𝒳.val.p.IsHomLift (𝟙 Z')
      (X.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₁))) ≫ r.m :
        X.obj (Over.mk ((k ≫ ψ) ≫ pr₁)) ⟶ g.obj (Over.mk (k ≫ ψ ≫ pr₂))) :=
    IsHomLift.comp_lift_id_left 𝒳.val.p (𝟙 Z') r.m _
  refine Functor.IsCartesian.ext 𝒳.val.p k (g.map u) _ _ ?_
  have hL := VertHom.restrict_fac hp (overMap_comp_eq_forget 𝒳 hX pr₁)
    (overMap_comp_eq_forget 𝒳 hg pr₂) (Over.homMk k : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) m
  have hR := SliceSourceFibre.SliceHom.restrict_fac hp hX hg
    (Over.homMk k : Over.mk (k ≫ ψ ≫ pr₁) ⟶ Over.mk (ψ ≫ pr₁)) ⟨ψ ≫ pr₂, m.1, m.2⟩
  have key : ∀ {A : BigFppfOver B S hS} (Y : Over A ⥤ 𝒳.val.obj) (q : T ⟶ A),
      Y.map (eqToHom (congrArg Over.mk (Category.assoc k ψ q))) ≫
        Y.map (Over.homMk k : Over.mk (k ≫ ψ ≫ q) ⟶ Over.mk (ψ ≫ q)) =
      (Over.map q ⋙ Y).map (Over.homMk k : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) := by
    intro A Y q
    rw [← Functor.map_comp]
    congr 1
  refine (Category.assoc _ _ _).trans ?_
  calc l.1 ≫ g.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₂))) ≫ g.map u
      = l.1 ≫ (Over.map pr₂ ⋙ g).map (Over.homMk k : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) := by
        exact congrArg (l.1 ≫ ·) (key g pr₂)
    _ = (Over.map pr₁ ⋙ X).map (Over.homMk k : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) ≫ m.1 := hL
    _ = X.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₁))) ≫
          X.map (Over.homMk k : Over.mk (k ≫ ψ ≫ pr₁) ⟶ Over.mk (ψ ≫ pr₁)) ≫ m.1 := by
        rw [← Category.assoc, key X pr₁]
    _ = (X.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₁))) ≫ r.m) ≫ g.map u :=
        (congrArg (X.map (eqToHom (congrArg Over.mk (Category.assoc k ψ pr₁))) ≫ ·)
          hR.symm).trans (Category.assoc _ _ _).symm

/-- The comparison of the presheaf of `(ψ : Z ⟶ T, m)` with the coproduct presheaf of the base
change presheaf of the presentation along `X`: `(ψ, m) ↦ (ψ ≫ pr₁, ψ ≫ pr₂, m)`. -/
noncomputable def chartComparison :
    slicePairIsom 𝒳 T (overMap_comp_eq_forget 𝒳 hX pr₁) (overMap_comp_eq_forget 𝒳 hg pr₂) ⟶
      OverShriek.presheaf (slicePresentationPresheaf 𝒳 hg hX) where
  app Z := ↾fun z => ⟨z.1 ≫ pr₁, ⟨z.1 ≫ pr₂, z.2.1, z.2.2⟩⟩
  naturality {Z Z'} k := by
    ext ⟨ψ, m⟩
    exact presentation_sigma_ext 𝒳 hg hX (Category.assoc _ _ _) (Category.assoc _ _ _)
      (chartComparison_restrict_m 𝒳 hg hX pr₁ pr₂ k.unop ψ m)

/-- The morphism to `W` of the image of `(ψ, m)` under `AlgebraicGeometry.Stack.chartComparison`
is `ψ ≫ pr₁`. -/
@[simp] lemma chartComparison_app_fst {Z : (BigFppfOver B S hS)ᵒᵖ}
    (z : (slicePairIsom 𝒳 T (overMap_comp_eq_forget 𝒳 hX pr₁)
      (overMap_comp_eq_forget 𝒳 hg pr₂)).obj Z) :
    ((chartComparison 𝒳 hg hX pr₁ pr₂).app Z z).1 = z.1 ≫ pr₁ := rfl

/-- `AlgebraicGeometry.Stack.chartComparison` followed by the projection of the coproduct presheaf
to `yoneda.obj W` is the projection to `yoneda.obj T` followed by `yoneda.map pr₁`. -/
lemma chartComparison_comp_toYoneda :
    chartComparison 𝒳 hg hX pr₁ pr₂ ≫ OverShriek.presheafToYoneda _ =
      OverShriek.presheafToYoneda _ ≫ yoneda.map pr₁ := by
  ext Z z
  rfl

variable {pr₁ pr₂}

/-- The comparison is bijective on sections. -/
theorem chartComparison_bijective (hT : IsLimit (BinaryFan.mk pr₁ pr₂))
    (Z : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Bijective ((chartComparison 𝒳 hg hX pr₁ pr₂).app Z) := by
  constructor
  · rintro ⟨ψ, m⟩ ⟨ψ', m'⟩ h
    have h1 : ψ ≫ pr₁ = ψ' ≫ pr₁ := congrArg Sigma.fst h
    have h2 : ψ ≫ pr₂ = ψ' ≫ pr₂ :=
      congrArg (fun z => (z.2.k : Z.unop ⟶ P)) h
    obtain rfl : ψ = ψ' := BinaryFan.IsLimit.hom_ext hT h1 h2
    obtain ⟨-, h4⟩ := SliceSourceFibre.SliceHom.mk.inj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    exact congrArg (Sigma.mk ψ) (VertHom.ext (eq_of_heq h4))
  · rintro ⟨φ, s⟩
    let ψ : Z.unop ⟶ T := hT.lift (BinaryFan.mk φ s.k)
    have h1 : ψ ≫ pr₁ = φ := hT.fac _ ⟨WalkingPair.left⟩
    have h2 : ψ ≫ pr₂ = s.k := hT.fac _ ⟨WalkingPair.right⟩
    have e₁ : (Over.mk (ψ ≫ pr₁) : Over W) = Over.mk φ := by rw [h1]
    have e₂ : (Over.mk s.k : Over P) = Over.mk (ψ ≫ pr₂) := by rw [h2]
    have : 𝒳.val.p.IsHomLift (𝟙 Z.unop) (X.map (eqToHom e₁)) := isHomLift_map_eqToHom 𝒳 hX e₁
    have : 𝒳.val.p.IsHomLift (𝟙 Z.unop) (g.map (eqToHom e₂)) := isHomLift_map_eqToHom 𝒳 hg e₂
    have : 𝒳.val.p.IsHomLift (𝟙 Z.unop) s.m := s.vert
    have hv : 𝒳.val.p.IsHomLift (𝟙 Z.unop)
        (X.map (eqToHom e₁) ≫ s.m ≫ g.map (eqToHom e₂)) := by
      simpa using (inferInstance : 𝒳.val.p.IsHomLift (𝟙 Z.unop ≫ 𝟙 Z.unop ≫ 𝟙 Z.unop)
        (X.map (eqToHom e₁) ≫ s.m ≫ g.map (eqToHom e₂)))
    refine ⟨⟨ψ, ⟨X.map (eqToHom e₁) ≫ s.m ≫ g.map (eqToHom e₂), hv⟩⟩, ?_⟩
    refine presentation_sigma_ext 𝒳 hg hX h1 h2 ?_
    simp only [Category.assoc, eqToHom_map, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- **The chart of a slice point.** For an algebraic stack with quasi-affine diagonal and
presentation `g : 𝒮/P ⥤ 𝒳`, a slice point `X : 𝒮/W ⥤ 𝒳` and a product `T = W × P`, the presheaf of
pairs `(ψ : Z ⟶ T, m : X (ψ ≫ pr₁) ⟶ g (ψ ≫ pr₂))` is represented by a quasi-affine morphism
`π : Q ⟶ T` of the site with `π ≫ pr₁` smooth and surjective. -/
theorem exists_chart (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳))
    (hT : IsLimit (BinaryFan.mk pr₁ pr₂))
    (hA : IsAlgebraicSpace B S hS (OverShriek.presheaf (slicePresentationPresheaf 𝒳 hg hX)))
    (hsurj : Space.IsSurjective B S hS
      (OverShriek.presheafToYoneda (slicePresentationPresheaf 𝒳 hg hX)))
    (hsmooth : Space.IsSmooth B S hS
      (OverShriek.presheafToYoneda (slicePresentationPresheaf 𝒳 hg hX))) :
    ∃ (Q : BigFppfOver B S hS) (π : Q ⟶ T)
      (e : yoneda.obj Q ≅ slicePairIsom 𝒳 T (overMap_comp_eq_forget 𝒳 hX pr₁)
        (overMap_comp_eq_forget 𝒳 hg pr₂)),
      e.hom ≫ OverShriek.presheafToYoneda _ = yoneda.map π ∧
        _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map π) ∧
        Smooth ((BigFppfOver.toScheme B S hS).map (π ≫ pr₁)) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map (π ≫ pr₁)) := by
  obtain ⟨Q, π, e, he, hq⟩ := exists_slicePairIsom_representing 𝒳 T
    (overMap_comp_eq_forget 𝒳 hX pr₁) (overMap_comp_eq_forget 𝒳 hg pr₂) h𝒳 hΔ
  have hκ : IsIso (chartComparison 𝒳 hg hX pr₁ pr₂) := by
    have : ∀ Z, IsIso ((chartComparison 𝒳 hg hX pr₁ pr₂).app Z) := fun Z =>
      (isIso_iff_bijective _).mpr (chartComparison_bijective 𝒳 hg hX hT Z)
    exact NatIso.isIso_of_isIso_app _
  have hmap : yoneda.map (π ≫ pr₁) =
      (e.hom ≫ chartComparison 𝒳 hg hX pr₁ pr₂) ≫
        OverShriek.presheafToYoneda (slicePresentationPresheaf 𝒳 hg hX) := by
    rw [Functor.map_comp, ← he, Category.assoc, Category.assoc,
      chartComparison_comp_toYoneda]
  have hQ : IsAlgebraicSpace B S hS (yoneda.obj Q) := isAlgebraicSpace_yoneda B S hS Q
  refine ⟨Q, π, e, he, hq, ?_, ?_⟩
  · refine Space.smooth_toScheme_map_of_isSmooth_yoneda_map B S hS _ ?_
    rw [hmap]
    exact Space.isSmooth_comp B S hS hQ hA (isAlgebraicSpace_yoneda B S hS W) _ _
      (Space.isSmooth_of_isIso B S hS hQ hA _) hsmooth
  · have hs : Space.IsSurjective B S hS (yoneda.map (π ≫ pr₁)) := by
      rw [hmap]
      exact Space.isSurjective_comp B S hS (Space.isSurjective_of_isIso _) hsurj
    exact (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).mp
      ((Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS _).mpr hs)

end AlgebraicGeometry.Stack

end
