module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.HenselianSection
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsLocalBase
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhoodFlatness
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DiagonalConormal

/-!
# Projective sections near a flat point over a henselian local base

Let `S` be the spectrum of a henselian local ring, `f : X ⟶ S` a morphism locally of finite
presentation, `F` a quasi-coherent `𝒪_X`-module of finite type and `x ∈ X` a point over the closed
point at which `F` is flat over `S`. Then every open neighbourhood of `x` contains an affine open
neighbourhood `U` of `x` such that `Γ(U, F)` is a projective `Γ(S, 𝒪_S)`-module.

This is Stacks 05MF over a henselian base, where the elementary étale neighbourhoods of the source
become trivial. The proof follows the source: Stacks 05I5 makes `F` of finite presentation near
`x` after base change to the local scheme of an elementary étale neighbourhood, Stacks 05ME gives
projective sections over an affine elementary étale neighbourhood, and over a henselian base both
neighbourhoods have sections through their distinguished points
(`AlgebraicGeometry.EtaleNeighborhood.exists_section_of_henselian`), along which everything is
pulled back to `X` itself.

## Main definitions

* `AlgebraicGeometry.sectionsPullbackOpenImmersionLinearEquiv`: the sections of the pullback of a
  module along an open immersion `j` over `W` are the sections over `j ''ᵁ W`, compatibly with the
  scalars of a base.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_projective_sections_of_henselian`: the statement above.

## References

* [Stacks Project, Tag 05MF](https://stacks.math.columbia.edu/tag/05MF)
* [Stacks Project, Tag 05ME](https://stacks.math.columbia.edu/tag/05ME)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Sections of the pullback of a module along an open immersion `j` over an open `W` are the
sections of the module over `j ''ᵁ W`, compatibly with the actions of the global sections of a
base `S` through `f` and through `j ≫ f`. -/
def sectionsPullbackOpenImmersionLinearEquiv {X X' S : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ S) (F : X.Modules) (W : X'.Opens) :
    letI : Module Γ(S, ⊤) Γ(F, j ''ᵁ W) :=
      Module.compHom _ (f.appLE ⊤ (j ''ᵁ W) (by simp)).hom
    letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback j).obj F, W) :=
      Module.compHom _ ((j ≫ f).appLE ⊤ W (by simp)).hom
    Γ(F, j ''ᵁ W) ≃ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback j).obj F, W) :=
  letI : Module Γ(S, ⊤) Γ(F, j ''ᵁ W) :=
    Module.compHom _ (f.appLE ⊤ (j ''ᵁ W) (by simp)).hom
  letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback j).obj F, W) :=
    Module.compHom _ ((j ≫ f).appLE ⊤ W (by simp)).hom
  let E1 := sectionsLinearEquivOfIso ((Scheme.Modules.restrictFunctorIsoPullback j).app F) W
  let e := (F.restrictAppIso j W).symm
  have hφ (r : Γ(S, ⊤)) : (j.appIso W).hom ((f.appLE ⊤ (j ''ᵁ W) (by simp)).hom r) =
      ((j ≫ f).appLE ⊤ W (by simp)).hom r := by
    rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  { toFun := fun a => E1 (e.hom a)
    invFun := fun b => e.inv (E1.symm b)
    left_inv := fun a => by simp
    right_inv := fun b => by simp
    map_add' := fun a b => by simp
    map_smul' := fun r a => by
      change E1 (e.hom ((f.appLE ⊤ (j ''ᵁ W) (by simp)).hom r • a)) =
        ((j ≫ f).appLE ⊤ W (by simp)).hom r • E1 (e.hom a)
      rw [← hφ, ← E1.map_smul]
      congr 1
      exact Scheme.Modules.smul_restrictAppIso_inv_apply j F W _ a }

/-- Over a henselian local base, a quasi-coherent module of finite type that is flat over the base
at a point `x` over the closed point is of finite presentation on an open neighbourhood of `x`
inside any given open neighbourhood `V` of `x`. -/
theorem exists_isFinitePresentation_pullback_ι_of_henselian {X S : Scheme.{u}} [IsAffine S]
    {s : S} [HenselianLocalRing (S.presheaf.stalk s)] [IsIso (S.fromSpecStalk s)]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (x : X) (hx : f x = s) (hflat : IsFlatOverAt f.toLRSHom.toShHom F x)
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ V₀ : X.Opens, V₀ ≤ V ∧ x ∈ V₀ ∧
      ((Scheme.Modules.pullback V₀.ι).obj F).IsFinitePresentation := by
  subst hx
  -- Stacks 05I5: the module is of finite presentation near the point over the local scheme of an
  -- elementary étale neighbourhood
  obtain ⟨N₁, hN₁, V₁, v₁, hfib, hfp, -⟩ :=
    (show ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} from
          @existsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u}) f F x hflat
  obtain ⟨ρ₁, hρ₁, -⟩ := N₁.exists_section_of_henselian hN₁
  set b₁ := N₁.scheme.fromSpecStalk N₁.point ≫ N₁.toBase with hb₁
  let c : X ⟶ pullback f b₁ := pullback.lift (𝟙 X) (f ≫ ρ₁)
    (by rw [Category.id_comp, Category.assoc, hρ₁, Category.comp_id])
  have hcfst : c ≫ pullback.fst f b₁ = 𝟙 X := pullback.lift_fst _ _ _
  have hcx : c x ∈ V₁ := by
    have h1 : pullback.fst f b₁ (c x) = x := by
      rw [← Scheme.Hom.comp_apply, hcfst]
      rfl
    have hmem : c x ∈ pullback.fst f b₁ ⁻¹' {x} := h1
    rw [hfib] at hmem
    rw [hmem]
    exact v₁.2
  let V₀ : X.Opens := c ⁻¹ᵁ V₁ ⊓ V
  refine ⟨V₀, inf_le_right, ⟨hcx, hxV⟩, ?_⟩
  let c' : V₀.toScheme ⟶ V₁.toScheme := c.resLE V₁ V₀ inf_le_left
  have hc' : c' ≫ V₁.ι = V₀.ι ≫ c := Scheme.Hom.resLE_comp_ι c _
  have h1 := @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
    (c'.toLRSHom.toShHom : V₀.toScheme.toRingedSpace ⟶ V₁.toScheme.toRingedSpace) _ hfp
  have hcomp : c' ≫ V₁.ι ≫ pullback.fst f b₁ = V₀.ι := by
    rw [← Category.assoc, hc', Category.assoc, hcfst, Category.comp_id]
  exact (SheafOfModules.isFinitePresentation V₀.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pullbackComp c' (V₁.ι ≫ pullback.fst f b₁)).app F ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app F) h1

/-- Let `S` be the spectrum of a henselian local ring with closed point `s`, `f : X ⟶ S` locally
of finite presentation, `F` a quasi-coherent `𝒪_X`-module of finite type and `x ∈ X` a point over
`s` at which `F` is flat over `S`. Then every open neighbourhood `V` of `x` contains an affine open
neighbourhood `U` of `x` such that `Γ(U, F)` is a projective `Γ(S, 𝒪_S)`-module. -/
theorem exists_isAffineOpen_projective_sections_of_henselian {X S : Scheme.{u}} [IsAffine S]
    {s : S} [HenselianLocalRing (S.presheaf.stalk s)] [IsIso (S.fromSpecStalk s)]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (x : X) (hx : f x = s) (hflat : IsFlatOverAt f.toLRSHom.toShHom F x)
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V ∧
      letI : Module Γ(S, ⊤) Γ(F, U) := Module.compHom _ (f.appLE ⊤ U (by simp)).hom
      Module.Projective Γ(S, ⊤) Γ(F, U) := by
  obtain ⟨V₀, hV₀V, hxV₀, hF₀fp⟩ :=
    exists_isFinitePresentation_pullback_ι_of_henselian f F x hx hflat V hxV
  subst hx
  let F₀ := (Scheme.Modules.pullback V₀.ι).obj F
  have hF₀qc : F₀.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F
  let x₀ : V₀.toScheme := ⟨x, hxV₀⟩
  have hflat₀ : IsFlatOverAt (V₀.ι ≫ f).toLRSHom.toShHom F₀ x₀ :=
    (isFlatOverAt_pullback_ι_iff f V₀ F x₀).mpr hflat
  -- Stacks 05ME on the shrunken `X`
  obtain ⟨N₂, hN₂, hN₂aff, x', hx'fst, hx'snd, U', hU'aff, hx'U', hproj⟩ :=
    exists_affineOpen_projective_sections_of_chart (V₀.ι ≫ f) F₀ (f x) x₀ rfl hflat₀
  obtain ⟨ρ₂', hρ₂', hρ₂s⟩ := N₂.exists_section_of_henselian hN₂
  let ρ₂ : S ⟶ N₂.scheme := ρ₂' ≫ N₂.scheme.fromSpecStalk N₂.point
  have hρ₂ : ρ₂ ≫ N₂.toBase = 𝟙 S := (Category.assoc _ _ _).trans hρ₂'
  have hρ₂pt : ρ₂ (f x) = N₂.point := by
    rw [Scheme.Hom.comp_apply, hρ₂s, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨x'', W, hx''fst, -, hWaff, hx''W, hprojW⟩ :=
    exists_affineOpen_projective_sections_baseChange (V₀.ι ≫ f) N₂.toBase ρ₂ F₀ x₀ (f x) x'
      hx'fst (by rw [hx'snd, hρ₂pt]) U' hU'aff hx'U' hproj
  have : IsIso (ρ₂ ≫ N₂.toBase) := by rw [hρ₂]; infer_instance
  let j := pullback.fst (V₀.ι ≫ f) (ρ₂ ≫ N₂.toBase) ≫ V₀.ι
  have hjx : j x'' = x := by rw [Scheme.Hom.comp_apply, hx''fst]; rfl
  refine ⟨j ''ᵁ W, hWaff.image_of_isOpenImmersion j, ⟨x'', hx''W, hjx⟩, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact hV₀V (pullback.fst (V₀.ι ≫ f) (ρ₂ ≫ N₂.toBase) y).2
  · let : Module Γ(S, ⊤) Γ(F, j ''ᵁ W) :=
      Module.compHom _ (f.appLE ⊤ (j ''ᵁ W) (by simp)).hom
    set q := pullback.snd (V₀.ι ≫ f) (ρ₂ ≫ N₂.toBase) with hq
    have key : j ≫ f = q := by
      rw [← Category.comp_id q, ← hρ₂]
      simp only [j, hq, Category.assoc]
      exact pullback.condition
    have hring (r : Γ(S, ⊤)) :
        ((j ≫ f).appLE ⊤ W (by simp)).hom r = (q.appLE ⊤ W (by simp)).hom r :=
      congrArg (fun φ => φ.hom r) (Stacks.Conormal.appLE_eq_of_eq key ⊤ W _ _)
    let G := (Scheme.Modules.pullback (pullback.fst (V₀.ι ≫ f) (ρ₂ ≫ N₂.toBase))).obj F₀
    let : Module Γ(S, ⊤) Γ(G, W) := Module.compHom _ (q.appLE ⊤ W (by simp)).hom
    have : Module.Projective Γ(S, ⊤) Γ(G, W) := hprojW
    let : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback j).obj F, W) :=
      Module.compHom _ ((j ≫ f).appLE ⊤ W (by simp)).hom
    let E₂ := sectionsLinearEquivOfIso
      ((Scheme.Modules.pullbackComp (pullback.fst (V₀.ι ≫ f) (ρ₂ ≫ N₂.toBase)) V₀.ι).app F).symm W
    let E₂' : Γ((Scheme.Modules.pullback j).obj F, W) ≃ₗ[Γ(S, ⊤)] Γ(G, W) :=
      { E₂ with
        map_smul' := fun r a => by
          change E₂ (((j ≫ f).appLE ⊤ W (by simp)).hom r • a) =
            (q.appLE ⊤ W (by simp)).hom r • E₂ a
          rw [E₂.map_smul, hring] }
    exact Module.Projective.of_equiv ((sectionsPullbackOpenImmersionLinearEquiv j f F W).trans
      E₂').symm

end AlgebraicGeometry
