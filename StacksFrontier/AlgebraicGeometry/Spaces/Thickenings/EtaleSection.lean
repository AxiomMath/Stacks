module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleIsoDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.EtaleIsoAlongSurjection

/-!
# Sections of an étale morphism across a thickening of algebraic spaces

Let `G ⊂ U` be a thickening of algebraic spaces over a scheme `S`, that is a closed subspace
with the same points, and let `p : W ⟶ U` be étale. A section of `p` over `G` extends uniquely
to a section of `p` over `U`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_section_of_isThickening`: a section of an étale
  morphism prescribed over a thickening of the base exists and is unique.
* `AlgebraicGeometry.Space.bijective_restrict_section_of_isThickening`: the same statement read
  as bijectivity of the restriction map on sections.

## References

* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a subfunctor `V` of `F'` is the inverse image of a subfunctor `Z` of `F` along `p`, then
`V` is the pullback of `Z` along `p`. -/
private theorem exists_isPullback_of_preimage_eq
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F' ⟶ F) (Z : Subfunctor F)
    (V : Subfunctor F') (h : Z.preimage p = V) :
    ∃ a : V.toFunctor ⟶ Z.toFunctor, IsPullback a V.ι Z.ι p := by
  subst h
  exact ⟨Z.fromPreimage p, Subfunctor.isPullback_preimage p Z⟩

/-- The range of an open immersion whose source is an algebraic space over `S` is an open
subspace of the target. -/
private theorem isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace'
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ F')
    (hf : IsOpenImmersion B S hS f) : IsOpenSubspace B S hS (Subfunctor.range f) := by
  have _ : Mono f := mono_of_isOpenImmersion B S hS f hf
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange f)) hF, ?_⟩
  have hfac : inv (Subfunctor.toRange f) ≫ f = (Subfunctor.range f).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι f).symm
  have hpre := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (inv (Subfunctor.toRange f)) f hf
  rwa [hfac] at hpre

variable {U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pointwise form of an equation `f ≫ g = h` of morphisms of presheaves. -/
private theorem app_app_eq_of_comp_eq {A A' C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : A ⟶ A'} {g : A' ⟶ C} {h : A ⟶ C} (e : f ≫ g = h) (T : (BigFppfOver B S hS)ᵒᵖ)
    (y : A.obj T) : g.app T (f.app T y) = h.app T y := by
  simpa using congrArg (fun k : A ⟶ C ↦ k.app T y) e

/-- Let `G ⊂ U` be a thickening of algebraic spaces over `S` — a closed subspace with the same
points, of no prescribed order — and let `p : W ⟶ U` be étale. Every morphism `σ' : G ⟶ W` over
`U` is the restriction of a unique section of `p`. -/
theorem existsUnique_section_of_isThickening
    (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
    {G : Subfunctor U} (hG : IsThickening B S hS ⟨U, hU⟩ G)
    {p : W ⟶ U} (hp : IsEtale B S hS p)
    (σ' : G.toFunctor ⟶ W) (hσ : σ' ≫ p = G.ι) :
    ∃! σ : U ⟶ W, σ ≫ p = 𝟙 U ∧ G.ι ≫ σ = σ' := by
  classical
  have hGalg : IsAlgebraicSpace B S hS G.toFunctor := hG.1.1
  have hH : IsThickening B S hS (⟨W, hW⟩ : AlgebraicSpaces B S hS) (G.preimage p) :=
    isThickening_preimage B S hS G
      (ObjectProperty.homMk p : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩) hG
  have hHalg : IsAlgebraicSpace B S hS (G.preimage p).toFunctor := hH.1.1
  have hHpb : IsPullback (G.fromPreimage p) (G.preimage p).ι G.ι p :=
    Subfunctor.isPullback_preimage p G
  have hσapp : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (y : G.toFunctor.obj T),
      p.app T (σ'.app T y) = (y : U.obj T) :=
    app_app_eq_of_comp_eq B S hS hσ
  have hle : Subfunctor.range σ' ≤ G.preimage p := by
    intro T x hx
    obtain ⟨y, rfl⟩ := hx
    show p.app T (σ'.app T y) ∈ G.obj T
    rw [hσapp T y]
    exact y.2
  have hsι : Subfunctor.lift σ' hle ≫ (G.preimage p).ι = σ' := Subfunctor.lift_ι _ _
  have hsfp : Subfunctor.lift σ' hle ≫ G.fromPreimage p = 𝟙 G.toFunctor := by
    ext T y
    exact Subtype.ext (hσapp T y)
  have hfpE : IsEtale B S hS (G.fromPreimage p) := by
    have hsq : IsPullback
        (ObjectProperty.homMk (G.preimage p).ι :
          (⟨(G.preimage p).toFunctor, hHalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩)
        (ObjectProperty.homMk (G.fromPreimage p) :
          (⟨(G.preimage p).toFunctor, hHalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G.toFunctor, hGalg⟩)
        (ObjectProperty.homMk p : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩)
        (ObjectProperty.homMk G.ι :
          (⟨G.toFunctor, hGalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) hHpb.flip
    exact isEtale_of_isPullback B S hS _ _ _ _ hsq hp
  have hsOI : IsOpenImmersion B S hS (Subfunctor.lift σ' hle) :=
    isOpenImmersion_of_isEtale_of_section B S hS hHalg hGalg (G.fromPreimage p) hfpE _ hsfp
  have hsMono : Mono (Subfunctor.lift σ' hle) :=
    mono_of_isOpenImmersion B S hS _ hsOI
  have hVopen : IsOpenSubspace B S hS (Subfunctor.range (Subfunctor.lift σ' hle)) :=
    isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace' B S hS hGalg _ hsOI
  obtain ⟨Z, ⟨hZ, hZpre⟩, hZuniq⟩ :=
    existsUnique_isOpenSubspace_preimage_eq_of_isThickening B S hS hH _ hVopen
  obtain ⟨a, hsq⟩ := exists_isPullback_of_preimage_eq B S hS (G.preimage p).ι Z _ hZpre
  have hqE : IsEtale B S hS (Z.ι ≫ p) :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS
      (presheaf_etale_of_isOpenImmersion B S hS hZ.2)) hp
  have hπeq : (Subfunctor.range (Subfunctor.lift σ' hle)).ι ≫ G.fromPreimage p =
      inv (Subfunctor.toRange (Subfunctor.lift σ' hle)) := by
    rw [← cancel_epi (Subfunctor.toRange (Subfunctor.lift σ' hle)), IsIso.hom_inv_id,
      ← Category.assoc, Subfunctor.toRange_ι]
    exact hsfp
  have hπiso : IsIso ((Subfunctor.range (Subfunctor.lift σ' hle)).ι ≫ G.fromPreimage p) := by
    rw [hπeq]; infer_instance
  have hpaste : IsPullback a
      ((Subfunctor.range (Subfunctor.lift σ' hle)).ι ≫ G.fromPreimage p) (Z.ι ≫ p) G.ι :=
    hsq.paste_vert hHpb.flip
  have hqiso : IsIso (Z.ι ≫ p) :=
    isIso_of_isEtale_of_isIso_pullback_of_isSurjective B S hS hU hGalg hZ.1 hpaste.flip hπiso
      hG.2 hqE
  have hw : ((Subfunctor.range (Subfunctor.lift σ' hle)).ι ≫ G.fromPreimage p) ≫ G.ι =
      a ≫ Z.ι ≫ p := hpaste.w.symm
  have hrestrict : G.ι ≫ inv (Z.ι ≫ p) ≫ Z.ι = σ' := by
    rw [← cancel_epi ((Subfunctor.range (Subfunctor.lift σ' hle)).ι ≫ G.fromPreimage p),
      ← Category.assoc, hw, Category.assoc, IsIso.hom_inv_id_assoc, hsq.w, hπeq,
      ← cancel_epi (Subfunctor.toRange (Subfunctor.lift σ' hle)), IsIso.hom_inv_id_assoc,
      ← Category.assoc, Subfunctor.toRange_ι]
    exact hsι
  refine ⟨inv (Z.ι ≫ p) ≫ Z.ι, ⟨by simp, hrestrict⟩, ?_⟩
  rintro σ ⟨hσp, hσG⟩
  have hσOI : IsOpenImmersion B S hS σ :=
    isOpenImmersion_of_isEtale_of_section B S hS hW hU p hp σ hσp
  have hσopen : IsOpenSubspace B S hS (Subfunctor.range σ) :=
    isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace' B S hS hU σ hσOI
  have hσapp' : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (y : G.toFunctor.obj T),
      σ.app T (y : U.obj T) = σ'.app T y :=
    app_app_eq_of_comp_eq B S hS hσG
  have hσpapp : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (y : U.obj T), p.app T (σ.app T y) = y :=
    app_app_eq_of_comp_eq B S hS hσp
  have hkey : (Subfunctor.range σ).preimage (G.preimage p).ι =
      Subfunctor.range (Subfunctor.lift σ' hle) := by
    ext T x
    constructor
    · rintro ⟨y, hy⟩
      have hyG : y ∈ G.obj T := by
        rw [← hσpapp T y, hy]
        exact x.2
      refine ⟨(⟨y, hyG⟩ : G.toFunctor.obj T), Subtype.ext ?_⟩
      exact (hσapp' T (⟨y, hyG⟩ : G.toFunctor.obj T)).symm.trans hy
    · rintro ⟨g, rfl⟩
      exact ⟨(g : U.obj T), hσapp' T g⟩
  have hZeq : Subfunctor.range σ = Z := hZuniq _ ⟨hσopen, hkey⟩
  have hτ : Subfunctor.lift σ (le_of_eq hZeq) ≫ Z.ι = σ := Subfunctor.lift_ι _ _
  have hτq : Subfunctor.lift σ (le_of_eq hZeq) ≫ (Z.ι ≫ p) = 𝟙 U := by
    rw [← Category.assoc, hτ, hσp]
  rw [← hτ, IsIso.eq_inv_of_inv_hom_id hτq]

/-- For `p : W ⟶ U` étale and `G ⊂ U` a thickening of algebraic spaces over `S`, restricting a
section of `p` to `G` is a bijection onto the morphisms `G ⟶ W` over `U`. -/
theorem bijective_restrict_section_of_isThickening
    (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
    {G : Subfunctor U} (hG : IsThickening B S hS ⟨U, hU⟩ G)
    {p : W ⟶ U} (hp : IsEtale B S hS p) :
    Function.Bijective (fun σ : {σ : U ⟶ W // σ ≫ p = 𝟙 U} ↦
      (⟨G.ι ≫ σ.1, by rw [Category.assoc, σ.2, Category.comp_id]⟩ :
        {σ' : G.toFunctor ⟶ W // σ' ≫ p = G.ι})) := by
  constructor
  · rintro ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ hres
    obtain ⟨σ₀, -, huniq⟩ :=
      existsUnique_section_of_isThickening B S hS hU hW hG hp (G.ι ≫ σ₁) (by
        rw [Category.assoc, h₁, Category.comp_id])
    exact Subtype.ext ((huniq σ₁ ⟨h₁, rfl⟩).trans
      (huniq σ₂ ⟨h₂, (congrArg Subtype.val hres).symm⟩).symm)
  · rintro ⟨σ', hσ'⟩
    obtain ⟨σ, ⟨hσ1, hσ2⟩, -⟩ :=
      existsUnique_section_of_isThickening B S hS hU hW hG hp σ' hσ'
    exact ⟨⟨σ, hσ1⟩, Subtype.ext hσ2⟩

end AlgebraicGeometry.Space

end
