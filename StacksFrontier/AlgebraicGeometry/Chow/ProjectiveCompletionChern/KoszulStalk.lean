module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.KoszulSections

/-!
# The stalks of the Koszul complex of the projective completion

Let `E = Proj_X(Sym^*(𝒞)[T])`, with tautological surjection `u : π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1)`, its
kernel `𝒦` and `φ : 𝒦 ⟶ 𝒪_E` the restriction of the projection to `π^*𝒪_X = 𝒪_E`. This file
computes the functional `φ_ξ : 𝒦_ξ ⟶ 𝒪_{E,ξ}` at the points `ξ` of `E`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.exists_stalkDual_eq_one`: `φ_ξ` takes the value `1` at the
  points of the standard open `D₊(m)` of a chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] {V : X.Opens}
  (hV : IsAffineOpen V)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The pullback `π^*x` of a section `x` of `𝒞 ⊕ 𝒪_X` over `V`, restricted to an open
`Q ⊆ π⁻¹V`. -/
def pullRes {Q : (space 𝒞).Opens} (hQ : Q ≤ proj 𝒞 ⁻¹ᵁ V) (x : Γ(module 𝒞, V)) :
    Γ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞), Q) :=
  ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.map (homOfLE hQ).op
    (unitSection (proj 𝒞) (module 𝒞) V x)

/-- `u(π^*x) = ψ₁(x)` on an open `Q ⊆ π⁻¹V`. -/
theorem taut_pullRes {Q : (space 𝒞).Opens} (hQ : Q ≤ proj 𝒞 ⁻¹ᵁ V) (x : Γ(module 𝒞, V)) :
    Scheme.Modules.Hom.app (taut 𝒞) Q (pullRes 𝒞 hQ x) =
      (twist 𝒞).presheaf.map (homOfLE hQ).op
        (((twistData 𝒞).ψ 1).val.app (op V)
          ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V) x)) :=
  (PresheafOfModules.naturality_apply (taut 𝒞).val (homOfLE hQ).op _).trans
    (congrArg _ (taut_unitSection 𝒞 V x))

/-- The projection to `𝒪_E` sends `π^*x` to the pullback of the function `snd(x)`, on an open
`Q ⊆ π⁻¹V`. -/
theorem sndUnit_pullRes {Q : (space 𝒞).Opens} (hQ : Q ≤ proj 𝒞 ⁻¹ᵁ V) (x : Γ(module 𝒞, V)) :
    Scheme.Modules.Hom.app (sndUnit 𝒞) Q (pullRes 𝒞 hQ x) =
      (space 𝒞).presheaf.map (homOfLE hQ).op
        ((proj 𝒞).app V (Scheme.Modules.Hom.app (snd 𝒞) V x)) :=
  (PresheafOfModules.naturality_apply (sndUnit 𝒞).val (homOfLE hQ).op _).trans
    (congrArg _ (sndUnit_unitSection 𝒞 V x))

omit [SheafOfModules.IsFiniteLocallyFree 𝒞] in
/-- The function `snd(T) = 1`. -/
theorem snd_sectionT :
    Scheme.Modules.Hom.app (snd 𝒞) V
        ((module 𝒞).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (sectionT 𝒞)) = toUnitM V 1 := by
  rw [sectionT_restrict, ← app_comp, inr_snd]
  rfl

omit [SheafOfModules.IsFiniteLocallyFree 𝒞] in
/-- The function `snd(m) = 0` for a section `m` of `𝒞`. -/
theorem snd_inl (m : Γ(𝒞, V)) :
    Scheme.Modules.Hom.app (snd 𝒞) V (Scheme.Modules.Hom.app (inl 𝒞) V m) = 0 := by
  rw [← app_comp, inl_snd]
  rfl

/-- **`φ_ξ` takes the value `1` on the standard open `D₊(m)` of a chart**: for a section `m` of
`𝒞` over an affine open `V` and a point `ξ` of `D₊(m)`, some `k ∈ 𝒦_ξ` has `φ_ξ(k) = 1`. -/
theorem exists_stalkDual_eq_one (m : Γ(𝒞, V)) (ξ : space 𝒞)
    (hξ : ξ ∈ chartOpen 𝒞 hV (chartE 𝒞 m)) :
    ∃ k, Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞)
      (koszulMap 𝒞) ξ k = 1 := by
  have hQ : chartOpen 𝒞 hV (chartE 𝒞 m) ≤ proj 𝒞 ⁻¹ᵁ V := chartOpen_le 𝒞 hV _
  set s1 := (module 𝒞).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (sectionT 𝒞)
  set ρ := chartRatio 𝒞 hV (chartT 𝒞 V) (chartE 𝒞 m)
  set v := pullRes 𝒞 hQ s1 - ρ • pullRes 𝒞 hQ (Scheme.Modules.Hom.app (inl 𝒞) V m) with hvdef
  have hv : Scheme.Modules.Hom.app (taut 𝒞) (chartOpen 𝒞 hV (chartE 𝒞 m)) v = 0 := by
    rw [hvdef, map_sub, Scheme.Modules.Hom.app_smul, taut_pullRes, taut_pullRes]
    exact sub_eq_zero.2 (psi_ratio 𝒞 hV _ _)
  obtain ⟨k, hk⟩ := exists_kernel_germ 𝒞 ξ _ hξ v hv
  refine ⟨k, ?_⟩
  rw [stalkDual_koszulMap, hk]
  refine (Stacks.KoszulStalk.stalkDual_germ (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ _ hξ
    v).trans ?_
  have h1 : Scheme.Modules.Hom.app (sndUnit 𝒞) (chartOpen 𝒞 hV (chartE 𝒞 m)) v =
      toUnitM _ 1 := by
    rw [hvdef, map_sub, Scheme.Modules.Hom.app_smul, sndUnit_pullRes, sndUnit_pullRes,
      snd_sectionT, snd_inl]
    change (space 𝒞).presheaf.map (homOfLE hQ).op ((proj 𝒞).app V (1 : Γ(X, V))) -
      ρ • (space 𝒞).presheaf.map (homOfLE hQ).op ((proj 𝒞).app V (0 : Γ(X, V))) =
        (1 : Γ(space 𝒞, chartOpen 𝒞 hV (chartE 𝒞 m)))
    simp
  exact (congrArg (TopCat.Presheaf.germ (space 𝒞).presheaf _ ξ hξ) h1).trans (map_one _)

end Stacks.Chow.ProjectiveCompletion
