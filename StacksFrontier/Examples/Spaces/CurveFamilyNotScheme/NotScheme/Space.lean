module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.NotScheme.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedProperSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# The contracted algebraic space is not a scheme

This is the space-level form of the non-representability step of Stacks 0D5E. Let `X` be an
algebraic space over an affine scheme `S`, proper over `S`, and let `F : h_Z ⟶ X` be a morphism
from (the space of) a scheme `Z` over `S` which is surjective on points, collapses a subset
`C ⊆ Z` to one point and is injective on points off `C`. Suppose `Z ⟶ S` factors as
`Z ⟶ Y ⟶ S` through a closed map `π : Z ⟶ Y` satisfying the hypotheses of
`Stacks.Examples.CurveFamilyNotScheme.not_exists_scheme_of_transport`, and that every fibre of
`Z ∖ C ⟶ S` is infinite. Then `X` is not representable by a scheme.

Indeed, if `X ≅ h_U`, Yoneda turns `F` into a morphism of schemes `φ : Z ⟶ U` over `S`; it is
surjective, collapses `C` to a point, and the fibres of the proper morphism `U ⟶ S` are infinite,
contradicting `not_exists_scheme_of_transport`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isProper_toScheme_map_toBaseObj_of_iso_yoneda`: a proper
  algebraic space over `S` represented by a scheme `U` makes `U ⟶ S` proper.
* `Stacks.Examples.CurveFamilyNotScheme.not_exists_iso_yoneda_of_transport`: the
  non-representability.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The base `S` as the terminal object of the big fppf site over `S`. -/
abbrev baseObj : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The structure morphism of an object of the big fppf site over `S`, as a morphism to the
terminal object `baseObj`. -/
abbrev toBaseObj (V : BigFppfOver B S hS) : V ⟶ baseObj := Over.homMk V.hom (by simp)

/-- A proper algebraic space over `S` represented by an object `U` of the site has `U ⟶ S`
proper. -/
theorem isProper_toScheme_map_toBaseObj_of_iso_yoneda {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXproper : ∀ g : X ⟶ yoneda.obj (baseObj (B := B) (hS := hS)), Space.IsProper B S hS g)
    {U : BigFppfOver B S hS} (e : X ≅ yoneda.obj U) :
    IsProper ((BigFppfOver.toScheme B S hS).map (toBaseObj U)) := by
  apply isProper_toScheme_of_isProper_yoneda
  have h : yoneda.map (toBaseObj U) = e.inv ≫ (e.hom ≫ yoneda.map (toBaseObj U)) := by simp
  rw [h]
  exact isProper_comp' B S hS _ _ hX (isAlgebraicSpace_yoneda B S hS _)
    (isProper_of_isIso B S hS _) (hXproper _)

/-- **The contracted space is not a scheme.** Let `X` be a proper algebraic space over the affine
scheme `S` and `F : h_Z ⟶ X` a morphism from a scheme `Z` over `S`, surjective on points,
collapsing `C ⊆ Z` to the point `x` and injective on points off `C`. Let `Z ⟶ S` factor as
`π ≫ p` with `π : Z ⟶ Y` a closed map, and suppose: the preimage of the fibre `p⁻¹(s₀)` lies in
`E ∪ C`, `E` maps to `y`, the fibre `p⁻¹(s₀)` has a point other than `y`, every proper closed
subset of `Y` surjecting onto `S` meets `p⁻¹(s₀)` in a point other than `y`, and every fibre of
`Z ∖ C` over `S` is infinite. Then `X` is not representable. -/
theorem not_exists_iso_yoneda_of_transport [IsAffine S] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXproper : ∀ g : X ⟶ yoneda.obj (baseObj (B := B) (hS := hS)), Space.IsProper B S hS g)
    {Zo : BigFppfOver B S hS} (F : yoneda.obj Zo ⟶ X)
    (hF : Function.Surjective (pointsMap B S hS _ F))
    {Y : Scheme.{u}} (π : (BigFppfOver.toScheme B S hS).obj Zo ⟶ Y) (hπ : IsClosedMap π)
    (p : Y ⟶ S) (hπp : π ≫ p = (BigFppfOver.toScheme B S hS).map (toBaseObj Zo))
    {s₀ : S} {y : Y} {E C : Set ((BigFppfOver.toScheme B S hS).obj Zo)}
    (hfib : ∀ z, p (π z) = s₀ → z ∈ E ∪ C) (hE : ∀ z ∈ E, π z = y) (y' : Y)
    (hy' : p y' = s₀) (hy'y : y' ≠ y)
    (hprop : ∀ T : Set Y, IsClosed T → T ≠ Set.univ → (∀ s, ∃ w ∈ T, p w = s) →
      ∃ w ∈ T, p w = s₀ ∧ w ≠ y)
    (x : points B S hS X)
    (hC : ∀ z ∈ C, pointsMap B S hS _ F ((pointsEquivScheme B S hS Zo).symm z) = x)
    (hinf : ∀ s : S, Set.Infinite {z | p (π z) = s ∧ z ∉ C})
    (hinj : ∀ z₁ z₂, z₁ ∉ C → z₂ ∉ C →
      pointsMap B S hS _ F ((pointsEquivScheme B S hS Zo).symm z₁) =
        pointsMap B S hS _ F ((pointsEquivScheme B S hS Zo).symm z₂) → z₁ = z₂) :
    ¬ ∃ U : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj U) := by
  rintro ⟨U, ⟨e⟩⟩
  set φ : Zo ⟶ U := yoneda.preimage (F ≫ e.hom) with hφdef
  have hφ : yoneda.map φ = F ≫ e.hom := yoneda.map_preimage _
  set Φ := (BigFppfOver.toScheme B S hS).map φ with hΦ
  have key : ∀ w, pointsToScheme B S hS U (pointsMap B S hS _ e.hom (pointsMap B S hS _ F w)) =
      Φ (pointsToScheme B S hS Zo w) := fun w => by
    rw [← pointsToScheme_pointsMap_yoneda, hφ, pointsMap_comp]
    rfl
  have hsymm : ∀ z, pointsToScheme B S hS Zo ((pointsEquivScheme B S hS Zo).symm z) = z :=
    fun z => (pointsEquivScheme B S hS Zo).apply_symm_apply z
  have hcomm : π ≫ p = Φ ≫ (BigFppfOver.toScheme B S hS).map (toBaseObj U) := by
    rw [hπp, hΦ, ← Functor.map_comp]
    congr 1
    ext
    simp [φ]
  have hcomm' : ∀ z, p (π z) = (BigFppfOver.toScheme B S hS).map (toBaseObj U) (Φ z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  -- `e.hom` is bijective on points
  have he : Function.Bijective (pointsMap B S hS _ e.hom) :=
    (pointsHomeomorphOfIso B S hS e).bijective
  have hU := bijective_pointsToScheme B S hS U
  refine not_exists_scheme_of_transport π hπ p hfib hE y' hy' hy'y hprop
    ⟨(BigFppfOver.toScheme B S hS).obj U, (BigFppfOver.toScheme B S hS).map (toBaseObj U),
      isProper_toScheme_map_toBaseObj_of_iso_yoneda hX hXproper e, Φ,
      pointsToScheme B S hS U (pointsMap B S hS _ e.hom x), fun s => ?_, fun u => ?_, hcomm,
      fun z hz => ?_⟩
  · -- the fibres of `U ⟶ S` are infinite
    intro hfin
    refine Set.Infinite.image (f := Φ) (fun z₁ hz₁ z₂ hz₂ h12 => ?_) (hinf s) (hfin.subset ?_)
    · rw [← hsymm z₁, ← hsymm z₂, ← key, ← key] at h12
      exact hinj z₁ z₂ hz₁.2 hz₂.2 (he.1 (hU.1 h12))
    · rintro _ ⟨z, hz, rfl⟩
      exact (hcomm' z).symm.trans hz.1
  · -- `φ` is surjective
    obtain ⟨w, rfl⟩ := hU.2 u
    obtain ⟨ξ, rfl⟩ := he.2 w
    obtain ⟨w', rfl⟩ := hF ξ
    exact ⟨_, (key w').symm⟩
  · -- `φ` collapses `C` to the image of `x`
    rw [← hsymm z, ← key, hC z hz]

end Stacks.Examples.CurveFamilyNotScheme

end
