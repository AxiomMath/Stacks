module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.RelativelyAmpleNeighbourhood
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.FiniteOrder
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase

/-!
# Stacks 0D2N for an algebraic space which is a scheme

Let `f' : X' ⟶ h_T` be a proper morphism of algebraic spaces whose target is a Noetherian scheme
`T` of the big fppf site and whose source is representable, by a scheme `Z`.  If an invertible
module `L'` restricts to an ample module on a scheme fibre `X'_t`, presented by any cartesian
square over a morphism `K ⟶ T` identified with `Spec κ(t) ⟶ T`, then `L'` is ample over an open
neighbourhood `V` of `t`: the pullback of `L'` is ample on every base change of `f'` along a
morphism factoring through `V`.

This is the scheme case Stacks 0D2N transported to algebraic spaces through Stacks 0D32 and
Stacks 0893; it is the last step of the proof of Stacks 0D3A, once `X` is known to be a scheme
near the fibre.

## Main results

* `AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_of_isRepresentable`.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- A cartesian square over `yoneda.map κ` with source `h_U` descends along `e : h_Z ≅ X` and
`f₀ : Z ⟶ T` to a cartesian square of the underlying site objects. -/
private theorem exists_isPullback_of_isPullback_yoneda {Z T K U : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ yoneda.obj T} (e : yoneda.obj Z ≅ X)
    (f₀ : Z ⟶ T) (hf₀ : yoneda.map f₀ = e.hom ≫ f) {j : yoneda.obj U ⟶ X} {q : U ⟶ K}
    {κ : K ⟶ T} (hsq : IsPullback j (yoneda.map q) f (yoneda.map κ)) :
    ∃ u : U ⟶ Z, yoneda.map u ≫ e.hom = j ∧ IsPullback u q f₀ κ := by
  let u : U ⟶ Z := Yoneda.fullyFaithful.preimage (j ≫ e.inv)
  have hu : yoneda.map u = j ≫ e.inv := Yoneda.fullyFaithful.map_preimage _
  have hsite : IsPullback (yoneda.map u) (yoneda.map q) (yoneda.map f₀) (yoneda.map κ) := by
    refine hsq.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hu]
    · simp
    · simp [hf₀]
    · simp
  exact ⟨u, by rw [hu]; simp,
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa using hsite.w)) hsite⟩

/-- **Relative ampleness over an open of the base, from relative ampleness of the restriction of a
scheme model.**  Let `f' : X' ⟶ h_T` be presented on a scheme `Z` by `e : h_Z ≅ X'` and
`f₀ : Z ⟶ T`.  If the reading `L₀` of `L'` on `Z` is ample relative to `f₀ ∣_ V`, then the
pullback of `L'` is ample on every base change of `f'` along `openSub T V ⟶ T`. -/
theorem isRelativelyAmple_of_isRelativelyAmple_morphismRestrict {T Z : BigFppfOver B S hS}
    {X' : AlgebraicSpaces B S hS} (f' : X' ⟶ representedAlgebraicSpace B S hS T)
    (L' : Modules.{u, u} B S hS X'.1 X'.2)
    (hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X'.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).property
        L')
    (e : yoneda.obj Z ≅ X'.1) (f₀ : Z ⟶ T) (hf₀ : yoneda.map f₀ = e.hom ≫ f'.hom)
    (V : ((𝒯).obj T).Opens)
    [Stacks.Ample.IsInvertibleModule _ (baseChangeModule B S hS L' Z e.hom)]
    (hamp : Stacks.RelativeAmple.IsRelativelyAmple ((𝒯).map f₀ ∣_ V)
      (pullbackModule ((𝒯).map f₀ ⁻¹ᵁ V).ι
        (baseChangeModule B S hS L' Z e.hom)))
    ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X')
    (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub T V))
    (hsq₁ : IsPullback p₁ f₁ f' (ObjectProperty.homMk (yoneda.map (openSubHom T V)))) :
    IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L') := by
  have hsq₁' := AlgebraicSpaces.isPullback_hom B S hS hsq₁
  have hf' : f'.hom = e.inv ≫ yoneda.map f₀ := by rw [hf₀, Iso.inv_hom_id_assoc]
  have hrep : yoneda.relativelyRepresentable f'.hom := by
    rw [hf']
    exact (MorphismProperty.cancel_left_of_respectsIso _ e.inv _).mpr
      (Functor.relativelyRepresentable.map yoneda f₀)
  refine ⟨(Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    hsq₁' hrep, fun T₂ U₂ g₂ p₂ q₂ htest => ?_⟩
  have hout := htest.paste_horiz hsq₁'
  -- the morphisms of the site underlying the outer square
  let s' : T₂ ⟶ openSub T V := Yoneda.fullyFaithful.preimage g₂
  have hs' : yoneda.map s' = g₂ := Yoneda.fullyFaithful.map_preimage g₂
  obtain ⟨r, hpe, hsite⟩ := exists_isPullback_of_isPullback_yoneda e f₀ hf₀
    (κ := s' ≫ openSubHom T V) (by simpa [hs'] using hout)
  have hsch := hsite.map 𝒯
  rw [Functor.map_comp, toScheme_map_openSubHom] at hsch
  -- the square through the restriction of `f₀` to `V`
  have hright := (isPullback_morphismRestrict ((𝒯).map f₀) V).flip
  let r' := hright.lift ((𝒯).map r) ((𝒯).map q₂ ≫ (𝒯).map s') (by
    rw [hsch.w]; exact (Category.assoc _ _ _).symm)
  have hr'₁ : r' ≫ ((𝒯).map f₀ ⁻¹ᵁ V).ι = (𝒯).map r := hright.lift_fst _ _ _
  have hleft : IsPullback r' ((𝒯).map q₂) ((𝒯).map f₀ ∣_ V) ((𝒯).map s') :=
    IsPullback.of_right (by rw [hr'₁]; exact hsch) (hright.lift_snd _ _ _) hright
  have hamp₂ := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hleft _ hamp
  -- identifying the module
  obtain ⟨eb⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L' hL' Z U₂ e.hom r
  rw [hpe] at eb
  let E : pullbackModule r' (pullbackModule ((𝒯).map f₀ ⁻¹ᵁ V).ι
      (baseChangeModule B S hS L' Z e.hom)) ≅
      baseChangeModule B S hS ((modulePullback B S hS p₁).obj L') U₂ p₂ :=
    (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso _ _ _).symm ≪≫
      Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hr'₁ _ ≪≫ eb.symm ≪≫
      baseChangeModuleCompIso B S hS p₁ L' U₂ p₂
  have : Stacks.Ample.IsInvertibleModule ((𝒯).obj U₂)
      (baseChangeModule B S hS ((modulePullback B S hS p₁).obj L') U₂ p₂) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E
  exact ⟨inferInstance, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mp hamp₂⟩

/-- **Stacks 0D2N for a representable proper algebraic space over a Noetherian scheme.**  Let
`f' : X' ⟶ h_T` be proper with `T` Noetherian and `X'` representable, `L'` an invertible
`𝒪_{X'}`-module, and `t` a point of `T` whose fibre is presented by a cartesian square
`h_U = X' ×_T K` over a morphism `K ⟶ T` identified with `Spec κ(t) ⟶ T`.  If the reading of `L'`
on `U` is ample, then there is an open neighbourhood `V` of `t` such that the pullback of `L'` is
ample on every base change of `f'` along `openSub T V ⟶ T`. -/
theorem exists_mem_isRelativelyAmple_of_isRepresentable {T : BigFppfOver B S hS}
    [_root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj T)]
    {X' : AlgebraicSpaces B S hS} (f' : X' ⟶ representedAlgebraicSpace B S hS T)
    (hf' : IsProper B S hS f'.hom) [X'.1.IsRepresentable]
    (L' : Modules.{u, u} B S hS X'.1 X'.2)
    (hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X'.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).property
        L')
    {K U : BigFppfOver B S hS} (κ : K ⟶ T) (j : yoneda.obj U ⟶ X'.1) (q : U ⟶ K)
    (hsq : IsPullback j (yoneda.map q) f'.hom (yoneda.map κ))
    (t : (𝒯).obj T)
    (eK : (𝒯).obj K ≅
      Spec (((𝒯).obj T).residueField t))
    (heK : eK.hom ≫ ((𝒯).obj T).fromSpecResidueField t =
      (𝒯).map κ)
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj U)
        (baseChangeModule B S hS L' U j), @Stacks.Ample.IsAmple _ _ hL) :
    ∃ V : ((𝒯).obj T).Opens, t ∈ V ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X')
        (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub T V)),
        IsPullback p₁ f₁ f' (ObjectProperty.homMk (yoneda.map (openSubHom T V))) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L') := by
  let Z := X'.1.reprX
  let e : yoneda.obj Z ≅ X'.1 := X'.1.reprW
  let f₀ : Z ⟶ T := Yoneda.fullyFaithful.preimage (e.hom ≫ f'.hom)
  have hf₀ : yoneda.map f₀ = e.hom ≫ f'.hom := Yoneda.fullyFaithful.map_preimage _
  -- `f₀` is proper
  have hpr : IsProper B S hS (yoneda.map f₀) := by
    rw [hf₀]
    exact isProper_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS Z) X'.2
      (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS T)
      (IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩ : IsPullback e.hom (e.hom ≫ f'.hom)
        f'.hom (𝟙 _)) hf'
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map f₀) := by
    have hstab : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
          𝒯).IsStableUnderBaseChange :=
      ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @_root_.AlgebraicGeometry.IsProper) (hsq.map 𝒯) hg⟩
    exact (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u}) 𝒯)).mp
      ((presheaf_isProper_iff B S hS (yoneda.map f₀) (isAlgebraicSpace_yoneda B S hS Z)
        (isAlgebraicSpace_yoneda B S hS T) (Functor.relativelyRepresentable.map yoneda f₀)).mp hpr)
  have := isInvertibleModule_baseChangeModule L' hL' Z e.hom
  -- the fibre, as a cartesian square of schemes
  obtain ⟨u, hue, hsite⟩ := exists_isPullback_of_isPullback_yoneda e f₀ hf₀ hsq
  have hsch : IsPullback ((𝒯).map u) ((𝒯).map q ≫ eK.hom) ((𝒯).map f₀)
      (((𝒯).obj T).fromSpecResidueField t) :=
    (hsite.map 𝒯).of_iso (Iso.refl _) (Iso.refl _) eK (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp only [Iso.refl_hom, Category.comp_id]; exact heK.symm)
  let E := hsch.isoPullback
  have hE : E.hom ≫ ((𝒯).map f₀).fiberι t = (𝒯).map u := hsch.isoPullback_hom_fst
  -- the fibre is ample
  obtain ⟨hLU, hampU⟩ := hamp
  obtain ⟨eb⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L' hL' Z U e.hom u
  rw [hue] at eb
  have h₁ : Stacks.Ample.IsAmple ((𝒯).obj U)
      (pullbackModule (E.hom ≫ ((𝒯).map f₀).fiberι t) (baseChangeModule B S hS L' Z e.hom)) := by
    rw [hE]
    have := hLU
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eb).mp hampU
  have hfib : Stacks.Ample.IsAmple (((𝒯).map f₀).fiber t)
      (pullbackModule (((𝒯).map f₀).fiberι t)
        (baseChangeModule B S hS L' Z e.hom)) := by
    have hinv : Stacks.Ample.IsInvertibleModule (((𝒯).map f₀).fiber t)
        (pullbackModule (((𝒯).map f₀).fiberι t)
          (baseChangeModule B S hS L' Z e.hom)) := inferInstance
    exact @Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isIso _ _ E.hom _ _ hinv
      ((Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_comp_iff _ _ _).mpr h₁)
  obtain ⟨V, htV, hrel⟩ :=
    Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre ((𝒯).map f₀) _ t
      hfib
  exact ⟨V, htV, fun X₁ p₁ f₁ h ↦
    isRelativelyAmple_of_isRelativelyAmple_morphismRestrict f' L' hL' e f₀ hf₀ V hrel p₁ f₁ h⟩

end AlgebraicGeometry.Space

end
