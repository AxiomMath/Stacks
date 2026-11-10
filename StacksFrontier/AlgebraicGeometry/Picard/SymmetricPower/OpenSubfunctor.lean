module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Open subfunctors of a functor on schemes

A morphism `ι : G ⟶ F` of presheaves of sets on schemes is an *open subfunctor* when it is
injective on sections and, for every section `p` of `F` over a scheme `T`, there is an open
`V ⊆ T` such that a base change of `p` along `g : T' ⟶ T` comes from `G` exactly when `g` lands
in `V`. This is the notion "representable by open immersions" of Stacks Tag 01JI(3), stated
pointwise. Open subfunctors compose, and when `G` is representable an open subfunctor satisfies
`IsOpenImmersion.presheaf`. A Zariski sheaf covered locally by open subfunctors out of
representable presheaves is representable, which is Stacks Tag 01JJ.

## Main definitions

* `AlgebraicGeometry.IsOpenSubfunctorHom`: the pointwise notion.

## Main results

* `AlgebraicGeometry.IsOpenSubfunctorHom.comp`: open subfunctors compose.
* `AlgebraicGeometry.IsOpenSubfunctorHom.isOpenImmersion_presheaf`: an open subfunctor out of a
  representable presheaf is representable by open immersions.
* `AlgebraicGeometry.isLocallySurjective_sigmaDesc_of_covers`: a family of open subfunctors
  covering every section locally is jointly locally surjective.
* `AlgebraicGeometry.isRepresentable_of_isOpenSubfunctor`: a Zariski sheaf covered locally by
  open subfunctors out of representable presheaves is representable (Stacks Tag 01JJ).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {F G H : Scheme.{u}ᵒᵖ ⥤ Type u}

/-- A section of `F` lies in the image of `ι`. -/
def InImage (ι : G ⟶ F) {T : Scheme.{u}} (p : F.obj (op T)) : Prop :=
  ∃ q, ι.app (op T) q = p

/-- **Open subfunctors.** `ι : G ⟶ F` is injective on sections, and for every section `p` of
`F` over `T` there is an open `V ⊆ T` such that the base change of `p` along `g : T' ⟶ T` lies
in the image of `ι` exactly when `g` factors through `V`. -/
structure IsOpenSubfunctorHom (ι : G ⟶ F) : Prop where
  /-- The map `ι` is injective on sections over every scheme. -/
  injective : ∀ T, Function.Injective (ι.app T)
  /-- For every section `p` of `F` over `T` there is an open `V ⊆ T` such that the base change
  of `p` along `g : T' ⟶ T` lies in the image of `ι` exactly when the range of `g` lies in
  `V`. -/
  locus : ∀ (T : Scheme.{u}) (p : F.obj (op T)), ∃ V : T.Opens, ∀ (T' : Scheme.{u}) (g : T' ⟶ T),
    InImage ι (F.map g.op p) ↔ Set.range g ⊆ V

/-- If a section `p` lies in the image of `ι`, so does its base change along any morphism. -/
theorem InImage.map {ι : G ⟶ F} {T T' : Scheme.{u}} {p : F.obj (op T)} (h : InImage ι p)
    (g : T' ⟶ T) : InImage ι (F.map g.op p) := by
  obtain ⟨q, rfl⟩ := h
  exact ⟨G.map g.op q, NatTrans.naturality_apply ι g.op q⟩

/-- A morphism whose range lies in an open `V` factors through `V`. -/
private theorem exists_comp_ι_eq_of_range_subset {X T : Scheme.{u}} (V : X.Opens) (g : T ⟶ X)
    (h : Set.range g ⊆ V) : ∃ g₁ : T ⟶ V, g₁ ≫ V.ι = g :=
  ⟨IsOpenImmersion.lift V.ι g (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩

/-- Naturality of `χ : yoneda.obj C ⟶ F` on a precomposition. -/
private theorem app_comp_eq_map {C : Scheme.{u}} (χ : yoneda.obj C ⟶ F) {A B : Scheme.{u}}
    (φ : A ⟶ B) (k : B ⟶ C) : χ.app (op A) (φ ≫ k) = F.map φ.op (χ.app (op B) k) :=
  NatTrans.naturality_apply χ φ.op k

namespace IsOpenSubfunctorHom

/-- **Open subfunctors compose.** -/
theorem comp {χ : H ⟶ G} {ι : G ⟶ F} (hχ : IsOpenSubfunctorHom χ) (hι : IsOpenSubfunctorHom ι) :
    IsOpenSubfunctorHom (χ ≫ ι) := by
  refine ⟨fun T => (hι.injective T).comp (hχ.injective T), fun T p => ?_⟩
  obtain ⟨V₁, hV₁⟩ := hι.locus T p
  obtain ⟨q, hq⟩ : InImage ι (F.map V₁.ι.op p) := (hV₁ _ V₁.ι).mpr (by rw [Scheme.Opens.range_ι])
  obtain ⟨V₂, hV₂⟩ := hχ.locus V₁ q
  have key : ∀ {T' : Scheme.{u}} (g₁ : T' ⟶ V₁),
      F.map (g₁ ≫ V₁.ι).op p = ι.app _ (G.map g₁.op q) := fun g₁ => by
    rw [NatTrans.naturality_apply ι g₁.op q, hq, op_comp, Functor.map_comp_apply]
  refine ⟨V₁.ι ''ᵁ V₂, fun T' g => ?_⟩
  constructor
  · rintro ⟨c, hc⟩
    have hg₁ : Set.range g ⊆ V₁ := (hV₁ T' g).mp ⟨χ.app _ c, hc⟩
    obtain ⟨g₁, hfac⟩ := exists_comp_ι_eq_of_range_subset V₁ g hg₁
    have e : F.map g.op p = ι.app _ (G.map g₁.op q) := by rw [← hfac, key]
    have hinj : χ.app _ c = G.map g₁.op q := hι.injective _ (hc.trans e)
    have hr : Set.range g₁ ⊆ V₂ := (hV₂ T' g₁).mp ⟨c, hinj⟩
    rintro _ ⟨x, rfl⟩
    refine ⟨g₁ x, hr ⟨x, rfl⟩, ?_⟩
    rw [← hfac]
    rfl
  · intro hg
    obtain ⟨g₁, hfac⟩ := exists_comp_ι_eq_of_range_subset V₁ g
      (hg.trans (V₁.ι.image_le_opensRange V₂ |>.trans (by rw [Scheme.Opens.opensRange_ι])))
    have hr : Set.range g₁ ⊆ V₂ := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hg ⟨x, rfl⟩
      have : V₁.ι y = V₁.ι (g₁ x) := by
        rwa [← Scheme.Hom.comp_apply, hfac]
      rwa [← V₁.ι.isOpenEmbedding.injective this]
    obtain ⟨c, hc⟩ := (hV₂ T' g₁).mpr hr
    refine ⟨c, ?_⟩
    change ι.app _ (χ.app _ c) = _
    rw [hc, ← hfac, key]

end IsOpenSubfunctorHom

/-- A commutative square of presheaves of sets which is a pullback at every object is a
pullback. -/
theorem isPullback_of_app {P X₂ X₃ X₄ : Scheme.{u}ᵒᵖ ⥤ Type u} {t : P ⟶ X₂} {l : P ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (w : t ≫ r = l ≫ b)
    (h : ∀ T, IsPullback (t.app T) (l.app T) (r.app T) (b.app T)) : IsPullback t l r b := by
  refine IsPullback.of_isLimit' ⟨w⟩ ?_
  apply evaluationJointlyReflectsLimits
  intro T
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (h T).isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cone.ext (Iso.refl _) ?_
    rintro (_ | _ | _)
    all_goals cat_disch

namespace IsOpenSubfunctorHom

/-- **An open subfunctor out of a representable presheaf is representable by open
immersions.** -/
theorem isOpenImmersion_presheaf {C : Scheme.{u}} {χ : yoneda.obj C ⟶ F}
    (h : IsOpenSubfunctorHom χ) : IsOpenImmersion.presheaf χ := by
  apply MorphismProperty.relative.of_exists
  intro a g
  let p := yonedaEquiv g
  obtain ⟨V, hV⟩ := h.locus a p
  obtain ⟨c, hc⟩ : InImage χ (F.map V.ι.op p) := (hV _ V.ι).mpr (by rw [Scheme.Opens.range_ι])
  have hg : ∀ (T' : Scheme.{u}) (ψ : T' ⟶ a), g.app (op T') ψ = F.map ψ.op p := fun T' ψ => by
    simp only [p, yonedaEquiv_apply]
    rw [← NatTrans.naturality_apply g ψ.op (𝟙 a)]
    simp
  have hsq : ∀ (T' : Scheme.{u}) (φ : T' ⟶ V.toScheme),
      χ.app (op T') (φ ≫ c) = g.app (op T') (φ ≫ V.ι) := fun T' φ => by
    rw [app_comp_eq_map, hc, hg, op_comp, Functor.map_comp_apply]
  refine ⟨V, yoneda.map c, V.ι, ?_, inferInstance⟩
  refine isPullback_of_app ?_ fun T' => ?_
  · ext T' φ
    exact hsq _ φ
  · rw [Types.isPullback_iff]
    refine ⟨?_, fun φ φ' ⟨_, h₂⟩ => ?_, fun c' ψ e => ?_⟩
    · ext φ
      exact hsq _ φ
    · exact (cancel_mono V.ι).mp h₂
    · change T'.unop ⟶ C at c'
      change T'.unop ⟶ a at ψ
      change χ.app _ c' = g.app _ ψ at e
      rw [hg] at e
      have hr : Set.range ψ ⊆ V := (hV _ ψ).mp ⟨c', e⟩
      obtain ⟨φ, hφ⟩ := exists_comp_ι_eq_of_range_subset V ψ hr
      refine ⟨φ, ?_, hφ⟩
      apply h.injective
      change χ.app _ (φ ≫ c) = _
      rw [app_comp_eq_map, hc, e, ← hφ, op_comp, Functor.map_comp_apply]

end IsOpenSubfunctorHom

/-- **A family of open subfunctors which covers every section locally is jointly locally
surjective.** -/
theorem isLocallySurjective_sigmaDesc_of_covers {ι : Type u} {C : ι → Scheme.{u}}
    (χ : ∀ i, yoneda.obj (C i) ⟶ F)
    (hcov : ∀ (T : Scheme.{u}) (p : F.obj (op T)) (t : T), ∃ (i : ι) (W : T.Opens), t ∈ W ∧
      InImage (χ i) (F.map W.ι.op p)) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc χ) := by
  constructor
  intro T p
  choose i W hW hin using hcov T p
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T (fun t => (W t).toScheme) (fun t => (W t).ι)
    (fun t => ⟨t, ⟨t, hW t⟩, rfl⟩), ?_⟩
  rintro _ _ ⟨t⟩
  obtain ⟨c, hc⟩ := hin t
  refine ⟨(Sigma.ι (fun j => yoneda.obj (C j)) (i t)).app _ c, ?_⟩
  change ((Sigma.ι (fun j => yoneda.obj (C j)) (i t)) ≫ Sigma.desc χ).app _ c = _
  rwa [Sigma.ι_comp_desc]

/-- **Stacks Tag 01JJ, for a family of open subfunctors.** A Zariski sheaf on schemes covered
locally by a family of open subfunctors out of representable presheaves is representable. -/
theorem isRepresentable_of_isOpenSubfunctor (hF : Presheaf.IsSheaf Scheme.zariskiTopology F)
    {ι : Type u} {C : ι → Scheme.{u}} (χ : ∀ i, yoneda.obj (C i) ⟶ F)
    (hχ : ∀ i, IsOpenSubfunctorHom (χ i))
    (hcov : ∀ (T : Scheme.{u}) (p : F.obj (op T)) (t : T), ∃ (i : ι) (W : T.Opens), t ∈ W ∧
      InImage (χ i) (F.map W.ι.op p)) :
    F.IsRepresentable := by
  have := isLocallySurjective_sigmaDesc_of_covers χ hcov
  exact Scheme.LocalRepresentability.isRepresentable
    (F := ⟨F, hF⟩) (f := χ)
    fun i => (hχ i).isOpenImmersion_presheaf

/-- **Lying in the image of an injective map out of a representable presheaf is local** on the
base, for a Zariski sheaf. -/
theorem inImage_of_openCover (hF : Presheaf.IsSheaf Scheme.zariskiTopology F) {C : Scheme.{u}}
    {χ : yoneda.obj C ⟶ F} (hinj : ∀ T, Function.Injective (χ.app T)) {T : Scheme.{u}}
    (p : F.obj (op T)) (𝒰 : T.OpenCover) (h : ∀ i, InImage χ (F.map (𝒰.f i).op p)) :
    InImage χ p := by
  choose c hc using h
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ c i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ c j :=
    fun i j => by
      apply hinj (op (pullback (𝒰.f i) (𝒰.f j)))
      change χ.app (op (pullback (𝒰.f i) (𝒰.f j))) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ c i) =
        χ.app (op (pullback (𝒰.f i) (𝒰.f j))) (pullback.snd (𝒰.f i) (𝒰.f j) ≫ c j)
      rw [app_comp_eq_map, app_comp_eq_map, hc i, hc j, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, ← op_comp, ← op_comp, pullback.condition]
  refine ⟨𝒰.glueMorphisms c hcompat, ?_⟩
  have hsh : Presieve.IsSheafFor F (Presieve.ofArrows 𝒰.X 𝒰.f) := by
    rw [isSheaf_iff_isSheaf_of_type,
      Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hF
    exact hF _ 𝒰.mem₀
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hx : Presieve.Arrows.Compatible F 𝒰.f (fun i => F.map (𝒰.f i).op p) := by
    intro i j Z gi gj e
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]
  obtain ⟨t, -, ht⟩ := hsh _ hx
  have h1 : χ.app _ (𝒰.glueMorphisms c hcompat) = t := ht _ fun i => by
    rw [← app_comp_eq_map, Scheme.Cover.ι_glueMorphisms, hc]
  have h2 : p = t := ht _ fun i => rfl
  rw [h1, h2]

/-- **Recognising an open subfunctor from its behaviour over affine schemes.** -/
theorem isOpenSubfunctor_of_affine (hF : Presheaf.IsSheaf Scheme.zariskiTopology F)
    {C : Scheme.{u}} (χ : yoneda.obj C ⟶ F)
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T], Function.Injective (χ.app (op T)))
    (hloc : ∀ (T : Scheme.{u}) [IsAffine T] (p : F.obj (op T)) (T' : Scheme.{u}) [IsAffine T']
      (g : T' ⟶ T), InImage χ (F.map g.op p) → ∀ t' : T',
        ∃ O : T.Opens, g t' ∈ O ∧ InImage χ (F.map O.ι.op p)) :
    IsOpenSubfunctorHom χ := by
  have hinj' : ∀ T, Function.Injective (χ.app T) := by
    intro T k k' h
    refine T.unop.affineCover.hom_ext _ _ fun i => hinj _ ?_
    rw [app_comp_eq_map, app_comp_eq_map, h]
  refine ⟨hinj', fun T p => ?_⟩
  refine ⟨sSup {O : T.Opens | InImage χ (F.map O.ι.op p)}, fun T' g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · rintro _ ⟨t', rfl⟩
    obtain ⟨W, hW, hgW, -⟩ := exists_isAffineOpen_mem_and_subset
      (show g t' ∈ (⊤ : T.Opens) from trivial)
    obtain ⟨W', hW', ht'W', hW'W⟩ := exists_isAffineOpen_mem_and_subset
      (show t' ∈ g ⁻¹ᵁ W from hgW)
    have : IsAffine W := hW
    have : IsAffine W' := hW'
    have hr : Set.range (W'.ι ≫ g) ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hW'W x.2
    let g' : W'.toScheme ⟶ W := IsOpenImmersion.lift W.ι (W'.ι ≫ g) hr
    have hg' : g' ≫ W.ι = W'.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
    have himg : InImage χ (F.map g'.op (F.map W.ι.op p)) := by
      rw [← Functor.map_comp_apply, ← op_comp, hg', op_comp, Functor.map_comp_apply]
      exact hg.map _
    obtain ⟨O, hO, hOim⟩ := hloc W (F.map W.ι.op p) W' g' himg ⟨t', ht'W'⟩
    refine TopologicalSpace.Opens.mem_sSup.mpr ⟨W.ι ''ᵁ O, ?_, ?_⟩
    · let e := IsOpenImmersion.isoOfRangeEq (O.ι ≫ W.ι) (W.ι ''ᵁ O).ι (by
        rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          Scheme.Opens.range_ι]
        rfl)
      have he : e.inv ≫ O.ι ≫ W.ι = (W.ι ''ᵁ O).ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
      change InImage χ (F.map (W.ι ''ᵁ O).ι.op p)
      rw [← he, op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply]
      exact hOim.map _
    · refine ⟨g' ⟨t', ht'W'⟩, hO, ?_⟩
      change (g' ≫ W.ι) ⟨t', ht'W'⟩ = g t'
      rw [hg']
      rfl
  · have hcov : ∀ t' : T', ∃ O : T.Opens, InImage χ (F.map O.ι.op p) ∧ g t' ∈ O :=
      fun t' => TopologicalSpace.Opens.mem_sSup.mp (hg ⟨t', rfl⟩)
    choose O hO hgO using hcov
    let 𝒰 : T'.OpenCover := Scheme.Cover.mkOfCovers T' (fun t' => (g ⁻¹ᵁ O t').toScheme)
      (fun t' => (g ⁻¹ᵁ O t').ι) (fun t' => ⟨t', ⟨t', hgO t'⟩, rfl⟩)
    refine inImage_of_openCover hF hinj' _ 𝒰 fun t' => ?_
    change InImage χ (F.map (g ⁻¹ᵁ O t').ι.op (F.map g.op p))
    rw [← Functor.map_comp_apply, ← op_comp, ← morphismRestrict_ι, op_comp,
      Functor.map_comp_apply]
    exact (hO t').map _

end AlgebraicGeometry

end
