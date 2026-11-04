module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModificationMap
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionChartDictionary
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLifting
public import StacksFrontier.AlgebraicGeometry.Size.ArtinianLocal

/-!
# Smoothness of the quotient stages and the lifting property

Let `S` be a scheme contained in a big fppf site `B`, let `V = Spec R` be a Noetherian affine
scheme of the site, `I ⊆ R` an ideal and `G : V_{/V(I)} ⟶ Spf C₀` a morphism to the formal
spectrum of an adic ring which is representable by algebraic spaces. By
`AlgebraicGeometry.FormalSpace.exists_continuousHom_completionComparison` it is `Spf φ` for a
taut `φ : C₀ → R^∧`, and over each quotient stage `Spec (C₀/J)` its base change is the quotient
stage `Spec (R^∧/K)`, `K` the closure of `J R^∧`. This file relates the lifting property of `G`
at a closed point `v` of `V` (`AlgebraicGeometry.FormalSpace.LiftsAtCompletion`) to smoothness of
the stage maps `Spec (R^∧/K) ⟶ Spec (C₀/J)` at the points over `v`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_presheafSection_eq_of_inclusion`: a section of the
  completion of a sheaf is the section given by its image in the sheaf.
* `AlgebraicGeometry.FormalSpace.smoothAt_stageMap_of_liftsAtCompletion`: the lifting property
  at `v` gives smoothness of every stage map at the points over `v`.

## References

* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section of the completion of a sheaf is the section given by its image.** If the image
in the ambient sheaf of a section `w` of `F_{/T}` over `U` is the section given by `x ∈ F(U)`,
then `x` has image in `T` and `w` is the section of the completion given by `x`. -/
theorem exists_presheafSection_eq_of_inclusion {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hFu : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F ⋙ uliftFunctor.{u + 1}))
    {T : Set (Space.points B S hS F)} {U : BigFppfOver B S hS}
    (w : (Space.completionSheaf B S hS F T).obj.obj (op U)) (x : F.obj (op U))
    (h : (Space.completionSheafInclusion B S hS F T).hom.app (op U) w =
      ((BigFppfOver.topology B S hS).toSheafify (F ⋙ uliftFunctor.{u + 1})).app (op U)
        (ULift.up x)) :
    ∃ hx : Space.HasImageIn B S hS F T U x, w = presheafSection B S hS x hx := by
  have hx := Artin.ContractionSituation.hasImageIn_of_completionSheafInclusion_app_eq hF hFu w x h
  refine ⟨hx, ?_⟩
  have hinj : Function.Injective ((Space.completionSheafInclusion B S hS F T).hom.app (op U)) := by
    have : Mono (Space.completionSheafInclusion B S hS F T).hom :=
      (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mp (Space.mono_completionSheafInclusion B S hS F T)
    exact (mono_iff_injective _).mp inferInstance
  apply hinj
  rw [h, inclusion_presheafSection]

/-! ### Lifting through a represented base change -/

section Abstract

/-- A lift through a pullback of sheafified representables comes from the site. -/
theorem exists_lift_of_isPullback_sheafifiedYoneda {X Y T T' : BigFppfOver B S hS}
    {A W : FppfSheaf B S hS}
    {ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X ⟶ A} {qs : X ⟶ Y}
    {G : A ⟶ W} {ιW : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Y ⟶ W}
    (hpb : IsPullback ι ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map qs) G ιW)
    (i : T ⟶ T') (αs : T ⟶ X) (βs : T' ⟶ Y) (hiβ : i ≫ βs = αs ≫ qs)
    (σ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T' ⟶ A)
    (hσG : σ ≫ G = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map βs ≫ ιW)
    (hσi : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i ≫ σ =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map αs ≫ ι) :
    ∃ γs : T' ⟶ X, i ≫ γs = αs ∧ γs ≫ qs = βs := by
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let ℓ := hpb.lift σ (sY.map βs) hσG
  refine ⟨sY.preimage ℓ, ?_, ?_⟩
  · apply sY.map_injective
    apply hpb.hom_ext
    · rw [sY.map_comp, Category.assoc, sY.map_preimage, hpb.lift_fst, hσi]
    · rw [sY.map_comp, Category.assoc, sY.map_preimage, hpb.lift_snd, ← sY.map_comp, hiβ,
        sY.map_comp]
  · apply sY.map_injective
    rw [sY.map_comp, sY.map_preimage, hpb.lift_snd]

/-- Restricting the morphism `h_{T'}^# ⟶ V_{/Z}` given by a section of `V` with image in `Z`. -/
theorem sheafifiedYoneda_map_comp_presheafSection {V T T' : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} (i : T ⟶ T') (x : T' ⟶ V)
    (hx : Space.HasImageIn B S hS (yoneda.obj V) Z T' x) (y : T ⟶ V) (hy : i ≫ x = y)
    (hy' : Space.HasImageIn B S hS (yoneda.obj V) Z T y) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i ≫
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (X := T')
          (F := Space.completionSheaf B S hS (yoneda.obj V) Z)).symm
          (presheafSection (F := yoneda.obj V) B S hS x hx) =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (X := T)
          (F := Space.completionSheaf B S hS (yoneda.obj V) Z)).symm
          (presheafSection (F := yoneda.obj V) B S hS y hy') := by
  subst hy
  rw [← Sheaf.sectionEquiv_symm_map]
  congr 1
  exact presheafSection_map (F := yoneda.obj V) (TF := Z) B S hS i x hx hy'

variable {V X Y : BigFppfOver B S hS} {Z : Set (Space.points B S hS (yoneda.obj V))}
  {W : FppfSheaf B S hS} {G : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W}
  {ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X ⟶
    Space.completionSheaf B S hS (yoneda.obj V) Z}
  {qs : X ⟶ Y} {ιW : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Y ⟶ W}
  {c : X ⟶ V}

/-- A morphism of the site over `S` commutes with the structure morphisms to `S`, also after
precomposing with a morphism of schemes. -/
private theorem comp_map_comp_over_hom {X Y : BigFppfOver B S hS} (f : X ⟶ Y) {P : Scheme.{u}}
    (g : P ⟶ ((Over.post B.inclusion).obj X : Over S).left) :
    (g ≫ (BigFppfOver.toScheme B S hS).map f) ≫ ((Over.post B.inclusion).obj Y : Over S).hom =
      g ≫ ((Over.post B.inclusion).obj X : Over S).hom := by
  exact (Category.assoc _ _ _).trans (congrArg (g ≫ ·) (congrArg B.inclusion.map (Over.w f)))

/-- **Lifting a small extension through a represented base change.** Let the base change of
`G : V_{/Z} ⟶ W` along `ιW : h_Y ⟶ W` be represented by `qs : X ⟶ Y`, with `X ⟶ V_{/Z}` given on
sections by `c : X ⟶ V`. If `G` has the lifting property at `v`, then for a small extension
`D' ⟶ D` of Artinian local rings in the site, every commutative square from `Spec D ⟶ Spec D'` to
`qs` whose top edge, followed by `c`, sends the closed point to `v` with finite residue field
extension admits a diagonal. -/
theorem exists_lift_of_isPullback_of_liftsAtCompletion
    (hpb : IsPullback ι ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map qs) G ιW)
    (hsecX : ∀ {T : BigFppfOver B S hS} (αs : T ⟶ X),
      ∃ ha : Space.HasImageIn B S hS (yoneda.obj V) Z T (αs ≫ c),
        Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map αs ≫ ι) =
          presheafSection B S hS _ ha)
    (v : ((Over.post B.inclusion).obj V : Over S).left)
    (hlift : LiftsAtCompletion B S hS V Z W G v)
    {D' D₁ : CommRingCat.{u}} (φ' : D' ⟶ D₁) (hφ' : InfinitesimalLifting.IsSmallExtension φ')
    [IsLocalRing D₁] (hcD₁ : B.Contains (Spec (.of D₁))) (hcD' : B.Contains (Spec (.of D')))
    (α : Spec (.of D₁) ⟶ ((Over.post B.inclusion).obj X : Over S).left)
    (β : Spec (.of D') ⟶ ((Over.post B.inclusion).obj Y : Over S).left)
    (hcomm : α ≫ (BigFppfOver.toScheme B S hS).map qs = Spec.map φ' ≫ β)
    (hpt : (α ≫ (BigFppfOver.toScheme B S hS).map c).base (IsLocalRing.closedPoint D₁) = v)
    (hfin : ((α ≫ (BigFppfOver.toScheme B S hS).map c).residueFieldMap
      (IsLocalRing.closedPoint D₁)).hom.Finite) :
    ∃ γ : Spec (.of D') ⟶ ((Over.post B.inclusion).obj X : Over S).left,
      Spec.map φ' ≫ γ = α ∧ γ ≫ (BigFppfOver.toScheme B S hS).map qs = β := by
  let 𝒥 := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda 𝒥
  let s' : Spec (.of D') ⟶ S := β ≫ ((Over.post B.inclusion).obj Y : Over S).hom
  let T' := affineOver B S hS hcD' s'
  let T := affineOver B S hS hcD₁ (Spec.map φ' ≫ s')
  let i : T ⟶ T' := affineOverHom B S hS hcD₁ (Spec.map φ' ≫ s') (V := T') (Spec.map φ') rfl
  have hαover : α ≫ ((Over.post B.inclusion).obj X : Over S).hom = Spec.map φ' ≫ s' := by
    rw [← comp_map_comp_over_hom B S hS qs, hcomm]
    exact Category.assoc _ _ _
  let αs : T ⟶ X := affineOverHom B S hS hcD₁ _ (V := X) α hαover
  let βs : T' ⟶ Y := affineOverHom B S hS hcD' s' (V := Y) β rfl
  have hiβ : i ≫ βs = αs ≫ qs := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hcomm.symm)
  obtain ⟨ha, hsec⟩ := hsecX αs
  have hαV : (α ≫ (BigFppfOver.toScheme B S hS).map c) ≫
      ((Over.post B.inclusion).obj V : Over S).hom = Spec.map φ' ≫ s' :=
    (comp_map_comp_over_hom B S hS c α).trans hαover
  let z : W.obj.obj (op T') := Sheaf.sectionEquiv 𝒥 (sY.map βs ≫ ιW)
  have hz : W.obj.map i.op z = G.hom.app _ (presheafSection B S hS _ ha) := by
    rw [← Sheaf.sectionEquiv_map_comp, ← hsec, ← Sheaf.sectionEquiv_comp]
    congr 1
    rw [← Category.assoc, ← sY.map_comp, hiβ, sY.map_comp, Category.assoc, ← hpb.w,
      Category.assoc]
  obtain ⟨b, hb, hbI, hbα, hbz⟩ :=
    hlift φ' hφ' hcD₁ hcD' s' (α ≫ (BigFppfOver.toScheme B S hS).map c) hαV hpt hfin ha z hz
  let bs := affineOverHom B S hS hcD' s' b hb
  let σ : (Sheaf.sheafifiedYoneda 𝒥).obj T' ⟶ Space.completionSheaf B S hS (yoneda.obj V) Z :=
    (Sheaf.sectionEquiv 𝒥 (X := T') (F := Space.completionSheaf B S hS (yoneda.obj V) Z)).symm
      (presheafSection (F := yoneda.obj V) B S hS bs hbI)
  have hσG : σ ≫ G = sY.map βs ≫ ιW := by
    apply (Sheaf.sectionEquiv 𝒥).injective
    rwa [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply]
  have hib : i ≫ bs = αs ≫ c := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hbα)
  have hσi : sY.map i ≫ σ = sY.map αs ≫ ι := by
    rw [sheafifiedYoneda_map_comp_presheafSection B S hS i bs hbI (αs ≫ c) hib ha,
      ← hsec, Equiv.symm_apply_apply]
  obtain ⟨γs, h1, h2⟩ :=
    exists_lift_of_isPullback_sheafifiedYoneda B S hS hpb i αs βs hiβ σ hσG hσi
  exact ⟨(BigFppfOver.toScheme B S hS).map γs, congrArg (BigFppfOver.toScheme B S hS).map h1,
    congrArg (BigFppfOver.toScheme B S hS).map h2⟩

/-- The section of a completion given by a section of the ambient sheaf determines it. -/
theorem eq_of_presheafSection_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hFu : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F ⋙ uliftFunctor.{u + 1}))
    {T : Set (Space.points B S hS F)} {U : BigFppfOver B S hS} {x y : F.obj (op U)}
    (hx : Space.HasImageIn B S hS F T U x) (hy : Space.HasImageIn B S hS F T U y)
    (h : presheafSection (F := F) B S hS x hx = presheafSection (F := F) B S hS y hy) : x = y := by
  have h2 := congrArg ((Space.completionSheafInclusion B S hS F T).hom.app (op U)) h
  rw [inclusion_presheafSection, inclusion_presheafSection] at h2
  have h3 := congrArg (ambientRead B S hS hFu) h2
  rwa [ambientRead_toSheafify, ambientRead_toSheafify] at h3

/-- **A compatible pair of sections lifts through a represented base change.** With `qs : X ⟶ Y`
representing the base change of `G : V_{/Z} ⟶ W` along `ιW`, a section `a` of `V_{/Z}` and a
morphism `u : T ⟶ Y` with the same image in `W` come from a morphism `T ⟶ X`. -/
private theorem exists_hom_of_isPullback_of_presheafSection
    (hpb : IsPullback ι ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map qs) G ιW)
    (hsecX : ∀ {T : BigFppfOver B S hS} (αs : T ⟶ X),
      ∃ ha : Space.HasImageIn B S hS (yoneda.obj V) Z T (αs ≫ c),
        Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map αs ≫ ι) =
          presheafSection B S hS _ ha)
    {T : BigFppfOver B S hS} (a : T ⟶ V) (ha : Space.HasImageIn B S hS (yoneda.obj V) Z T a)
    (u : T ⟶ Y)
    (hcompat : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (X := T)
        (F := Space.completionSheaf B S hS (yoneda.obj V) Z)).symm
        (presheafSection (F := yoneda.obj V) B S hS a ha) ≫ G =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map u ≫ ιW) :
    ∃ αX : T ⟶ X, αX ≫ qs = u ∧ αX ≫ c = a := by
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have hαX := sY.map_preimage (hpb.lift _ _ hcompat)
  refine ⟨sY.preimage (hpb.lift _ _ hcompat), sY.map_injective ?_, ?_⟩
  · rw [sY.map_comp, hαX, hpb.lift_snd]
  · obtain ⟨haX, hsecα⟩ := hsecX (sY.preimage (hpb.lift _ _ hcompat))
    rw [hαX, hpb.lift_fst, Equiv.apply_symm_apply] at hsecα
    exact eq_of_presheafSection_eq B S hS
      (upliftedSheaf (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).property haX ha hsecα.symm

/-- **Smoothness of a represented base change gives the lifting property.** Let the base change
of `G : V_{/Z} ⟶ W` along `ιW : h_Y ⟶ W` be represented by `qs : X ⟶ Y`, with `X ⟶ V_{/Z}` given on
sections by `c : X ⟶ V`, and let `qs` be smooth at every point of `X` over `v`. Then every small
extension lifting problem for `G` at `v` whose section of `W` comes from `Y` has a solution. -/
theorem exists_lift_of_isPullback_of_smoothAt
    (hpb : IsPullback ι ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map qs) G ιW)
    (hsecX : ∀ {T : BigFppfOver B S hS} (αs : T ⟶ X),
      ∃ ha : Space.HasImageIn B S hS (yoneda.obj V) Z T (αs ≫ c),
        Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map αs ≫ ι) =
          presheafSection B S hS _ ha)
    [AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map qs)]
    (v : ((Over.post B.inclusion).obj V : Over S).left)
    (hsm : ∀ x : (BigFppfOver.toScheme B S hS).obj X,
      (BigFppfOver.toScheme B S hS).map c x = v →
        InfinitesimalLifting.SmoothAt ((BigFppfOver.toScheme B S hS).map qs) x)
    {D' D : CommRingCat.{u}} (φ : D' ⟶ D) (hφ : InfinitesimalLifting.IsSmallExtension φ)
    [IsLocalRing D] (hD : B.Contains (Spec (.of D))) (hD' : B.Contains (Spec (.of D')))
    (s : Spec (.of D') ⟶ S)
    (α : Spec (.of D) ⟶ ((Over.post B.inclusion).obj V : Over S).left)
    (hα : α ≫ ((Over.post B.inclusion).obj V : Over S).hom = Spec.map φ ≫ s)
    (hpt : α.base (IsLocalRing.closedPoint D) = v)
    (ha : Space.HasImageIn B S hS (yoneda.obj V) Z
      (affineOver B S hS hD (Spec.map φ ≫ s)) (affineOverHom B S hS hD _ α hα))
    (z : W.obj.obj (op (affineOver B S hS hD' s)))
    (hz : W.obj.map (affineOverHom B S hS hD (Spec.map φ ≫ s) (V := affineOver B S hS hD' s)
      (Spec.map φ) rfl).op z = G.hom.app _ (presheafSection B S hS _ ha))
    (t : affineOver B S hS hD' s ⟶ Y)
    (hzt : z = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫ ιW)) :
    ∃ (β : Spec (.of D') ⟶ ((Over.post B.inclusion).obj V : Over S).left)
      (hβ : β ≫ ((Over.post B.inclusion).obj V : Over S).hom = s)
      (hb : Space.HasImageIn B S hS (yoneda.obj V) Z
        (affineOver B S hS hD' s) (affineOverHom B S hS hD' s β hβ)),
      Spec.map φ ≫ β = α ∧ G.hom.app _ (presheafSection B S hS _ hb) = z := by
  let 𝒥 := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda 𝒥
  have : 𝒥.Subcanonical := bigFppfOver_subcanonical B S hS
  let T' := affineOver B S hS hD' s
  let T := affineOver B S hS hD (Spec.map φ ≫ s)
  let i : T ⟶ T' := affineOverHom B S hS hD (Spec.map φ ≫ s) (V := T') (Spec.map φ) rfl
  let a : T ⟶ V := affineOverHom B S hS hD _ α hα
  let σa : sY.obj T ⟶ Space.completionSheaf B S hS (yoneda.obj V) Z :=
    (Sheaf.sectionEquiv 𝒥 (X := T) (F := Space.completionSheaf B S hS (yoneda.obj V) Z)).symm
      (presheafSection (F := yoneda.obj V) B S hS a ha)
  have hcompat : σa ≫ G = sY.map (i ≫ t) ≫ ιW := by
    apply (Sheaf.sectionEquiv 𝒥).injective
    rw [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply, ← hz, hzt, sY.map_comp,
      Category.assoc]
    exact (Sheaf.sectionEquiv_map_comp 𝒥 i _).symm
  obtain ⟨αX, hαXq, hαXc⟩ :=
    exists_hom_of_isPullback_of_presheafSection B S hS hpb hsecX a ha (i ≫ t) hcompat
  let αs := (BigFppfOver.toScheme B S hS).map αX
  have hαsc : αs ≫ (BigFppfOver.toScheme B S hS).map c = α :=
    congrArg (BigFppfOver.toScheme B S hS).map hαXc
  have hsmx : InfinitesimalLifting.SmoothAt ((BigFppfOver.toScheme B S hS).map qs)
      (αs.base (IsLocalRing.closedPoint D)) := by
    apply hsm
    rw [← hpt, ← hαsc]
    rfl
  have hlift := ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness
    ((BigFppfOver.toScheme B S hS).map qs) (αs.base (IsLocalRing.closedPoint D))).out 1 3).mp hsmx
  obtain ⟨γ, hγ₁, hγ₂⟩ := hlift φ hφ αs ((BigFppfOver.toScheme B S hS).map t)
    (congrArg (BigFppfOver.toScheme B S hS).map hαXq) rfl
  have hγover : γ ≫ ((Over.post B.inclusion).obj X : Over S).hom = s := by
    have ht' : (BigFppfOver.toScheme B S hS).map t ≫ ((Over.post B.inclusion).obj Y : Over S).hom =
        s := congrArg B.inclusion.map (Over.w t)
    exact (comp_map_comp_over_hom B S hS qs γ).symm.trans ((congrArg (· ≫ _) hγ₂).trans ht')
  let γs : T' ⟶ X := affineOverHom B S hS hD' s (V := X) γ hγover
  have hγq : γs ≫ qs = t := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hγ₂)
  obtain ⟨hb, hsecγ⟩ := hsecX γs
  have hβover : (γ ≫ (BigFppfOver.toScheme B S hS).map c) ≫
      ((Over.post B.inclusion).obj V : Over S).hom = s :=
    (comp_map_comp_over_hom B S hS c γ).trans hγover
  refine ⟨γ ≫ (BigFppfOver.toScheme B S hS).map c, hβover, hb, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hγ₁).trans hαsc)
  · have h3 : (sY.map γs ≫ ι) ≫ G = sY.map t ≫ ιW := by
      rw [Category.assoc, hpb.w, ← Category.assoc, ← sY.map_comp, hγq]
    exact ((congrArg (G.hom.app _) hsecγ.symm).trans
      (Sheaf.sectionEquiv_comp 𝒥 _ _).symm).trans ((congrArg _ h3).trans hzt.symm)

end Abstract

/-! ### The quotient stages of the completion of an affine scheme -/

section Adic

/-- The `I`-adic topology on the `I`-adic completion `AdicCompletion I A`, viewed as an
`A`-module. -/
local instance instTopologicalSpaceAdicCompletion' {A : Type u} [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

/-- The quotient of the `I`-adic completion by an open ideal is a quotient of the ring itself,
for `I` finitely generated. -/
theorem adicCompletion_quotient_surjective {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (J : { K : Ideal (AdicCompletion I A) // IsOpen (K : Set (AdicCompletion I A)) }) :
    Function.Surjective ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))) := by
  let : TopologicalSpace A := I.adicTopology
  obtain ⟨-, ⟨n, rfl⟩, hn⟩ :=
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis
      (AdicCompletion I A))).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp
      (J.2.mem_nhds J.1.zero_mem)
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := (I ^ n • (⊤ : Submodule A A)).mkQ_surjective
    (AdicCompletion.eval I A n x)
  refine ⟨a, Ideal.Quotient.eq.mpr (hn ?_)⟩
  change algebraMap A (AdicCompletion I A) a - x ∈
    I ^ n • (⊤ : Submodule A (AdicCompletion I A))
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
  change AdicCompletion.eval I A n (algebraMap A (AdicCompletion I A) a - x) = 0
  rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
  exact sub_eq_zero.mpr ha

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
  (s : Spec (.of R) ⟶ S) (I : Ideal R)

/-- **A morphism into a quotient stage of `Spf (R^∧)` is a section of the completion.** For a
weak ideal of definition `K` of `R^∧` and a morphism `α : T ⟶ Spec (R^∧/K)` of the site, the
section of `V_{/V(I)}` over `T` obtained through the comparison `Spf (R^∧) ≅ V_{/V(I)}` is the
section given by the composite `T ⟶ Spec (R^∧/K) ⟶ Spec R`. -/
theorem exists_presheafSection_eq_stage
    (K : { K : Ideal (AdicCompletion I R) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I R)) K })
    {T : BigFppfOver B S hS}
    (α : T ⟶ (BigAffineFppf.inclusion B S hS).obj
      ((adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing).stage K)) :
    ∃ ha : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hR s))
        (zeroLocusPoints B S hS hR s I) T
        (α ≫ quotientStageToAffine B S hS hR s I
          (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)
          (quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing) K),
      Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map α ≫
            colimit.ι (formalSpectrumDiagram
              (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)) (OrderDual.toDual K) ≫
            completionComparison B S hS hR s I
              (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)
              (quotientSystemCompatible_adicQuotientSystem B S hS hR s I
                I.fg_of_isNoetherianRing)) =
        presheafSection B S hS _ ha := by
  have hV := isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s)
  have hVu : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj (affineOver B S hS hR s) ⋙ uliftFunctor.{u + 1}) :=
    (upliftedSheaf (yoneda.obj (affineOver B S hS hR s)) hV).property
  refine exists_presheafSection_eq_of_inclusion B S hS hV.isSheaf hVu _ _ ?_
  have hb := completionComparison_overAffine B S hS hR s I
    (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)
    (quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing) K
  refine (Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) _
    (Space.completionSheafInclusion B S hS (yoneda.obj (affineOver B S hS hR s))
      (zeroLocusPoints B S hS hR s I))).symm.trans ?_
  refine (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))).trans ?_
  refine (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) α _).trans ?_
  refine (congrArg _ hb).trans ?_
  exact (NatTrans.naturality_apply ((BigFppfOver.topology B S hS).toSheafify
    (yoneda.obj (affineOver B S hS hR s) ⋙ uliftFunctor.{u + 1})) α.op _).symm

/-- The morphism of residue fields induced by a closed immersion is surjective. -/
theorem surjective_residueFieldMap_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion f] (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨w, rfl⟩ := X.residue_surjective x z
  obtain ⟨y, rfl⟩ := f.stalkMap_surjective x w
  refine ⟨Y.residue (f x) y, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-- The spectra of a small extension of Artinian local rings, the smaller one mapping to a scheme
of the site with trivial residue field extension at the closed point, lie in the site. -/
theorem contains_spec_of_isSmallExtension {X : Scheme.{u}} (hX : B.Contains X)
    {D' D₁ : CommRingCat.{u}} (φ' : D' ⟶ D₁) (hφ' : InfinitesimalLifting.IsSmallExtension φ')
    [IsLocalRing D₁] (α : Spec D₁ ⟶ X)
    (hres : IsIso (α.residueFieldMap (IsLocalRing.closedPoint D₁))) :
    B.Contains (Spec (.of D₁)) ∧ B.Contains (Spec (.of D')) := by
  obtain ⟨hlD', hlD₁, hArtD', hArtD₁, hsurj, -⟩ := hφ'
  have hres_card : Cardinal.mk ((Spec D₁).residueField (IsLocalRing.closedPoint D₁)) ≤
      X.size := by
    have e := (@asIso _ _ _ _ (α.residueFieldMap (IsLocalRing.closedPoint D₁))
      hres).commRingCatIsoToRingEquiv
    rw [← Cardinal.mk_congr e.toEquiv]
    exact Scheme.mk_residueField_le_size _ _
  refine ⟨B.contains_spec_of_isArtinianRing' hX D₁ hres_card, ?_⟩
  have := hlD'
  have : IsLocalHom φ'.hom := IsLocalHom.of_surjective φ'.hom hsurj
  apply B.contains_spec_of_isArtinianRing hX D'
  refine (Cardinal.mk_le_of_injective (IsLocalRing.ResidueField.map φ'.hom).injective).trans ?_
  rwa [← Scheme.mk_residueField_closedPoint D₁]

/-- Followed by a closed immersion, a morphism with bijective residue field map at a point has a
finite residue field map there. -/
theorem finite_residueFieldMap_comp_of_isClosedImmersion {X Y Z : Scheme.{u}} (α : X ⟶ Y)
    (f : Y ⟶ Z) [AlgebraicGeometry.IsClosedImmersion f] (x : X)
    (hres : IsIso (α.residueFieldMap x)) : ((α ≫ f).residueFieldMap x).hom.Finite := by
  rw [Scheme.residueFieldMap_comp]
  exact .of_surjective _ ((ConcreteCategory.bijective_of_isIso (α.residueFieldMap x)).2.comp
    (surjective_residueFieldMap_of_isClosedImmersion f _))

variable {C₀ : Type u} [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀]
  [IsLinearTopology C₀ C₀]

/-- **The lifting property at a closed point gives smoothness of the stage maps there.** Let
`G : V_{/V(I)} ⟶ Spf C₀` be `Spf φ` on `Spf (R^∧)`, with base change `Spec (R^∧/K)` over a
quotient stage `Spec (C₀/J)`. If `G` has the lifting property at a closed point `v` of `V`, then
the stage map `Spec (R^∧/K) ⟶ Spec (C₀/J)` is smooth at every point over `v`. -/
theorem smoothAt_stageMap_of_liftsAtCompletion [LocallyOfFiniteType s] [IsNoetherianRing C₀]
    (hC₀ : TopologicalRing.IsWeaklyAdmissible C₀) (E : QuotientSystem B S hS C₀)
    (G : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s))
      (zeroLocusPoints B S hS hR s I) ⟶ formalSpectrum E)
    (φ : ContinuousHom E (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing))
    (hφ : formalSpectrumMap hC₀ φ =
      completionComparison B S hS hR s I
        (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)
        (quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing) ≫
        G)
    (J : { J : Ideal C₀ // TopologicalRing.IsWeakIdealOfDefinition J })
    (K : { K : Ideal (AdicCompletion I R) // TopologicalRing.IsWeakIdealOfDefinition K })
    (hJK : J.1 ≤ Ideal.comap φ.toRingHom K.1)
    (hsq : IsPullback
      (colimit.ι (formalSpectrumDiagram
        (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)) (OrderDual.toDual K))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (φ.stageMap J K hJK)))
      (formalSpectrumMap hC₀ φ) (colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual J)))
    (v : ((Over.post B.inclusion).obj (affineOver B S hS hR s) : Over S).left)
    (hlift : LiftsAtCompletion B S hS (affineOver B S hS hR s) (zeroLocusPoints B S hS hR s I)
      (formalSpectrum E) G v)
    (x : Spec (.of (AdicCompletion I R ⧸ K.1)))
    (hx : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K.1).comp
      (algebraMap R (AdicCompletion I R)))) x = v) :
    InfinitesimalLifting.SmoothAt
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJK))) x := by
  let 𝒥 := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda 𝒥
  let incl := BigAffineFppf.inclusion B S hS
  let Dq := adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing
  let hDq := quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing
  let cmp := completionComparison B S hS hR s I Dq hDq
  let ρ : R →+* AdicCompletion I R ⧸ K.1 :=
    (Ideal.Quotient.mk K.1).comp (algebraMap R (AdicCompletion I R))
  let c := quotientStageToAffine B S hS hR s I Dq hDq K
  let qs := incl.map (φ.stageMap J K hJK)
  let q := Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJK))
  let ι : sY.obj (incl.obj (Dq.stage K)) ⟶ Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS hR s)) (zeroLocusPoints B S hS hR s I) :=
    colimit.ι (formalSpectrumDiagram Dq) (OrderDual.toDual K) ≫ cmp
  let ιE : sY.obj (incl.obj (E.stage J)) ⟶ formalSpectrum E :=
    colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual J)
  have hcmp : IsIso cmp := isIso_completionComparison_adicQuotientSystem B S hS hR s I
    I.fg_of_isNoetherianRing
  have hpb : IsPullback ι (sY.map qs) G ιE := by
    rw [hφ] at hsq
    exact IsPullback.of_iso hsq (Iso.refl _) (@asIso _ _ _ _ cmp hcmp) (Iso.refl _) (Iso.refl _)
      (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hover : q ≫ E.overS J = Spec.map (CommRingCat.ofHom ρ) ≫ s := φ.overS J K hJK
  have : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ)) :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      (adicCompletion_quotient_surjective I I.fg_of_isNoetherianRing ⟨K.1, K.2.1⟩)
  have : LocallyOfFiniteType (q ≫ E.overS J) := by
    rw [hover]
    infer_instance
  have : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q (E.overS J)
  refine ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness q x).out 1 4).mpr
    (fun D' D₁ φ' hφ' hloc α β hcomm hcl hres => ?_)
  have := hloc
  obtain ⟨hcD₁, hcD'⟩ := contains_spec_of_isSmallExtension B (Dq.inSite K) φ' hφ' α hres
  have hfin := finite_residueFieldMap_comp_of_isClosedImmersion α
    (Spec.map (CommRingCat.ofHom ρ)) (IsLocalRing.closedPoint D₁) hres
  have hpt : (α ≫ Spec.map (CommRingCat.ofHom ρ)).base (IsLocalRing.closedPoint D₁) = v := by
    change (Spec.map (CommRingCat.ofHom ρ)).base (α.base (IsLocalRing.closedPoint D₁)) = v
    rwa [show α.base (IsLocalRing.closedPoint D₁) = x from hcl]
  exact exists_lift_of_isPullback_of_liftsAtCompletion B S hS (c := c) hpb
    (fun αs => exists_presheafSection_eq_stage B S hS hR s I K αs) v hlift φ' hφ' hcD₁ hcD'
    α β hcomm hpt hfin

end Adic

end AlgebraicGeometry.FormalSpace
